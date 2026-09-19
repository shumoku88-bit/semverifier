'use strict'

const { spawnSync } = require('node:child_process')
const semver = require('semver')

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

  if (result === 'disjoint') {
    disjointRows += 1

    if (nodeIntersects) {
      falsePositives.push({
        left,
        right,
        semverifier: 'disjoint',
        nodeSemver: true,
      })
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
    falseNegatives.push({
      left,
      right,
      witness,
      semverifier: true,
      nodeSemver: false,
    })
  }
}

if (leftRanges.size !== rightRanges.size) {
  throw new Error(
    `matrix axes differ: left=${leftRanges.size}, right=${rightRanges.size}`,
  )
}

for (const range of leftRanges) {
  if (!rightRanges.has(range)) {
    throw new Error(`matrix right axis is missing range: ${range}`)
  }
}

const expectedRows = leftRanges.size * rightRanges.size
if (lines.length !== expectedRows || seenPairs.size !== expectedRows) {
  throw new Error(
    `incomplete matrix: rows=${lines.length}, unique=${seenPairs.size}, expected=${expectedRows}`,
  )
}

console.log(
  `checked complete ${leftRanges.size} x ${rightRanges.size} ordered range matrix (${lines.length} pairs) against node-semver ${require('semver/package.json').version}`,
)
console.log(
  `Semverifier: ${witnessRows} intersecting pairs, ${disjointRows} disjoint pairs`,
)
console.log(
  `disagreements: ${falseNegatives.length} node-semver false negatives, ${falsePositives.length} node-semver false positives`,
)

if (witnessAcceptanceMismatches.length) {
  console.error(
    `found ${witnessAcceptanceMismatches.length} Semverifier witnesses rejected by node-semver satisfies()`,
  )
  for (const mismatch of witnessAcceptanceMismatches) {
    console.error(JSON.stringify({ kind: 'witness-rejected', ...mismatch }))
  }
  process.exit(1)
}

for (const mismatch of falseNegatives) {
  console.warn(JSON.stringify({ kind: 'false-negative', ...mismatch }))
}

for (const mismatch of falsePositives) {
  console.warn(JSON.stringify({ kind: 'false-positive', ...mismatch }))
}
