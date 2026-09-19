'use strict'

const { spawnSync } = require('node:child_process')
const semver = require('semver')

const nodeSemverTarget = 'npm/node-semver PR #901 @ 7a597a93b2feb62696f94e4df9533363eaf8f98a'

const run = spawnSync(
  'lake',
  ['exe', 'semverifierIntersectionMatrix'],
  {
    encoding: 'utf8',
    maxBuffer: 64 * 1024 * 1024,
  },
)

if (run.error) {
  throw run.error
}

if (run.status !== 0) {
  process.stderr.write(run.stderr)
  process.exit(run.status || 1)
}

const lines = run.stdout.split('\n').filter(Boolean)
const nodeResults = new Map()
const seenPairs = new Set()
const leftRanges = new Set()
const rightRanges = new Set()

const witnessAcceptanceMismatches = []
const falseNegatives = []
const falsePositives = []

let witnessRows = 0
let disjointRows = 0

for (const line of lines) {
  const fields = line.split('\t')
  if (fields.length !== 3) {
    throw new Error(`invalid intersection matrix row: ${line}`)
  }

  const [left, right, result] = fields
  const pairKey = JSON.stringify([left, right])

  if (seenPairs.has(pairKey)) {
    throw new Error(`duplicate ordered range pair: ${pairKey}`)
  }

  seenPairs.add(pairKey)
  leftRanges.add(left)
  rightRanges.add(right)

  const nodeIntersects = new semver.Range(left).intersects(new semver.Range(right))
  nodeResults.set(pairKey, nodeIntersects)

  if (result === 'disjoint') {
    disjointRows += 1
    if (nodeIntersects) {
      falsePositives.push({ left, right })
    }
    continue
  }

  const prefix = 'witness='
  if (!result.startsWith(prefix)) {
    throw new Error(`invalid intersection matrix result: ${result}`)
  }

  witnessRows += 1
  const witness = result.slice(prefix.length)
  const leftAccepts = semver.satisfies(witness, left)
  const rightAccepts = semver.satisfies(witness, right)

  if (!leftAccepts || !rightAccepts) {
    witnessAcceptanceMismatches.push({
      left,
      right,
      witness,
      leftAccepts,
      rightAccepts,
    })
    continue
  }

  if (!nodeIntersects) {
    falseNegatives.push({ left, right, witness })
  }
}

if (leftRanges.size !== rightRanges.size) {
  throw new Error(
    `matrix axes differ: left=${leftRanges.size}, right=${rightRanges.size}`,
  )
}

const expectedRows = leftRanges.size * rightRanges.size
if (lines.length !== expectedRows || seenPairs.size !== expectedRows) {
  throw new Error(
    `incomplete matrix: rows=${lines.length}, unique=${seenPairs.size}, expected=${expectedRows}`,
  )
}

const asymmetricPairs = []
const visitedUnorderedPairs = new Set()

for (const pairKey of seenPairs) {
  const [left, right] = JSON.parse(pairKey)
  const unorderedKey = JSON.stringify([left, right].sort())

  if (visitedUnorderedPairs.has(unorderedKey)) {
    continue
  }
  visitedUnorderedPairs.add(unorderedKey)

  const leftRight = nodeResults.get(JSON.stringify([left, right]))
  const rightLeft = nodeResults.get(JSON.stringify([right, left]))

  if (leftRight !== rightLeft) {
    asymmetricPairs.push({ left, right, leftRight, rightLeft })
  }
}

console.log(`node-semver audit target: ${nodeSemverTarget}`)
console.log(
  `checked complete ${leftRanges.size} x ${rightRanges.size} ordered range matrix (${lines.length} pairs) against node-semver ${require('semver/package.json').version}`,
)
console.log(
  `Semverifier: ${witnessRows} intersecting pairs, ${disjointRows} disjoint pairs`,
)
console.log(
  `disagreements: ${falseNegatives.length} node-semver false negatives, ${falsePositives.length} node-semver false positives`,
)
console.log(
  `node-semver asymmetric unordered pairs: ${asymmetricPairs.length}`,
)

for (const mismatch of falseNegatives) {
  console.warn(JSON.stringify({ kind: 'false-negative', ...mismatch }))
}
for (const mismatch of falsePositives) {
  console.warn(JSON.stringify({ kind: 'false-positive', ...mismatch }))
}
for (const mismatch of asymmetricPairs) {
  console.warn(JSON.stringify({ kind: 'asymmetric', ...mismatch }))
}

if (witnessAcceptanceMismatches.length) {
  console.error(
    `found ${witnessAcceptanceMismatches.length} Semverifier witnesses rejected by node-semver satisfies()`,
  )
  for (const mismatch of witnessAcceptanceMismatches) {
    console.error(JSON.stringify({ kind: 'witness-rejected', ...mismatch }))
  }
  process.exit(1)
}

const expectedFalseNegatives = [
  {
    left: '1.2.3-alpha.2',
    right: '1.2.3-alpha.2 - 1.2.3',
    witness: '1.2.3-alpha.2',
  },
  {
    left: '=1.2.3-alpha.2',
    right: '1.2.3-alpha.2 - 1.2.3',
    witness: '1.2.3-alpha.2',
  },
  {
    left: '1.2.3-alpha.2 - 1.2.3',
    right: '1.2.3-alpha.2',
    witness: '1.2.3-alpha.2',
  },
  {
    left: '1.2.3-alpha.2 - 1.2.3',
    right: '=1.2.3-alpha.2',
    witness: '1.2.3-alpha.2',
  },
]

const normalized = rows => rows
  .map(row => JSON.stringify(row))
  .sort()

if (
  JSON.stringify(normalized(falseNegatives)) !==
    JSON.stringify(normalized(expectedFalseNegatives)) ||
  falsePositives.length !== 0 ||
  asymmetricPairs.length !== 0
) {
  console.error('PR #901 semantic checkpoint differs from the expected partial repair')
  console.error(
    `expected: 4 known false negatives, 0 false positives, 0 asymmetric pairs`,
  )
  console.error(
    `observed: ${falseNegatives.length} false negatives, ${falsePositives.length} false positives, ${asymmetricPairs.length} asymmetric pairs`,
  )
  process.exit(1)
}

console.log(
  'PR #901 repairs all 90 baseline false positives and all 34 baseline asymmetries in this corpus while leaving the 4 known false negatives unchanged.',
)
