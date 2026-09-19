'use strict'

const { createHash } = require('node:crypto')
const { spawnSync } = require('node:child_process')
const semver = require('semver')

const nodeSemverMainSha = '6e05b7637396ac66522cff8731f07cfe0ef49a29'

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
const nodeResults = new Map()

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
    asymmetricPairs.push({
      left,
      right,
      leftRight,
      rightLeft,
    })
  }
}

const falsePositiveUnorderedPairs = new Set(
  falsePositives.map(({ left, right }) => JSON.stringify([left, right].sort())),
)

const exactPrereleaseForms = new Set([
  '1.2.3-alpha.2',
  '=1.2.3-alpha.2',
])

const stableOpenGapPairs = new Set([
  JSON.stringify(['<0.0.1', '>0.0.0'].sort()),
  JSON.stringify(['>0.0.0', '^0.0.0'].sort()),
  JSON.stringify(['>0.0.1', '^0.0.1'].sort()),
])

const classifyFalsePositivePair = (left, right) => {
  const unordered = [left, right].sort()
  const unorderedKey = JSON.stringify(unordered)

  if (unordered.includes('<0.0.0')) {
    return 'null-below-zero'
  }

  const leftRight = nodeResults.get(JSON.stringify([left, right]))
  const rightLeft = nodeResults.get(JSON.stringify([right, left]))
  if (
    leftRight !== rightLeft &&
    unordered.some(range => exactPrereleaseForms.has(range))
  ) {
    return 'exact-prerelease-asymmetry'
  }

  if (stableOpenGapPairs.has(unorderedKey)) {
    return 'stable-open-gap'
  }

  if (unordered.includes('<1.2.3')) {
    return 'prerelease-boundary-overlap'
  }

  return 'unclassified'
}

const falsePositiveFamilies = new Map()
for (const unorderedKey of falsePositiveUnorderedPairs) {
  const [left, right] = JSON.parse(unorderedKey)
  const family = classifyFalsePositivePair(left, right)
  if (!falsePositiveFamilies.has(family)) {
    falsePositiveFamilies.set(family, [])
  }
  falsePositiveFamilies.get(family).push(unorderedKey)
}

for (const pairs of falsePositiveFamilies.values()) {
  pairs.sort()
}

const familySummary = Object.fromEntries(
  [...falsePositiveFamilies.entries()]
    .sort(([left], [right]) => left.localeCompare(right))
    .map(([family, pairs]) => [
      family,
      {
        count: pairs.length,
        fingerprint: createHash('sha256')
          .update(pairs.join('\n'))
          .digest('hex'),
      },
    ]),
)

const mismatchFingerprintInput = [
  ...falseNegatives.map(({ left, right, witness }) =>
    `false-negative\t${left}\t${right}\t${witness}`
  ),
  ...falsePositives.map(({ left, right }) =>
    `false-positive\t${left}\t${right}`
  ),
].sort().join('\n')

const mismatchFingerprint = createHash('sha256')
  .update(mismatchFingerprintInput)
  .digest('hex')

console.log(`node-semver audit target: ${nodeSemverMainSha}`)
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
  `false-positive unordered pairs: ${falsePositiveUnorderedPairs.size}; node-semver asymmetric unordered pairs: ${asymmetricPairs.length}`,
)
console.log(`disagreement fingerprint: sha256:${mismatchFingerprint}`)
console.log(`false-positive families: ${JSON.stringify(familySummary)}`)

const expectedFamilyCounts = {
  'exact-prerelease-asymmetry': 34,
  'null-below-zero': 17,
  'prerelease-boundary-overlap': 8,
  'stable-open-gap': 3,
}

const observedFamilyCounts = Object.fromEntries(
  Object.entries(familySummary).map(([family, summary]) => [
    family,
    summary.count,
  ]),
)

if (JSON.stringify(observedFamilyCounts) !== JSON.stringify(expectedFamilyCounts)) {
  console.error('false-positive family partition changed')
  console.error(`expected: ${JSON.stringify(expectedFamilyCounts)}`)
  console.error(`observed: ${JSON.stringify(observedFamilyCounts)}`)
  process.exit(1)
}

if (falsePositiveFamilies.has('unclassified')) {
  console.error(
    `found ${falsePositiveFamilies.get('unclassified').length} unclassified false-positive pairs`,
  )
  for (const pair of falsePositiveFamilies.get('unclassified')) {
    console.error(pair)
  }
  process.exit(1)
}

const expectedCheckpoint = {
  ranges: 202,
  pairs: 40804,
  witnessRows: 23410,
  disjointRows: 17394,
  falseNegatives: 4,
  falsePositives: 90,
  falsePositiveUnorderedPairs: 62,
  asymmetricPairs: 34,
  fingerprint: '483d882f69ac5c2184fcec2e7873da7d5d0e6bbe5785371a53a89f03c1d90ee2',
}

const observedCheckpoint = {
  ranges: leftRanges.size,
  pairs: lines.length,
  witnessRows,
  disjointRows,
  falseNegatives: falseNegatives.length,
  falsePositives: falsePositives.length,
  falsePositiveUnorderedPairs: falsePositiveUnorderedPairs.size,
  asymmetricPairs: asymmetricPairs.length,
  fingerprint: mismatchFingerprint,
}

if (JSON.stringify(observedCheckpoint) !== JSON.stringify(expectedCheckpoint)) {
  console.error('full intersection audit checkpoint changed')
  console.error(`expected: ${JSON.stringify(expectedCheckpoint)}`)
  console.error(`observed: ${JSON.stringify(observedCheckpoint)}`)
  process.exit(1)
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

for (const mismatch of falseNegatives) {
  console.warn(JSON.stringify({ kind: 'false-negative', ...mismatch }))
}

for (const mismatch of falsePositives) {
  console.warn(JSON.stringify({ kind: 'false-positive', ...mismatch }))
}

for (const mismatch of asymmetricPairs) {
  console.warn(JSON.stringify({ kind: 'asymmetric', ...mismatch }))
}
