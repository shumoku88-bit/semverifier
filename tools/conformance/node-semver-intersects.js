'use strict'

const { spawnSync } = require('node:child_process')
const semver = require('semver')

const run = spawnSync(
  'lake',
  ['exe', 'semverifierIntersectionProbe'],
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
const witnessMismatches = []
const intersectionMismatches = []

const knownNodeSemverContradictions = new Set([
  JSON.stringify(['1.2.3-alpha.2', '1.2.3-alpha.2 - 1.2.3', '1.2.3-alpha.2']),
  JSON.stringify(['=1.2.3-alpha.2', '1.2.3-alpha.2 - 1.2.3', '1.2.3-alpha.2']),
  JSON.stringify(['1.2.3-alpha.2 - 1.2.3', '1.2.3-alpha.2', '1.2.3-alpha.2']),
  JSON.stringify(['1.2.3-alpha.2 - 1.2.3', '=1.2.3-alpha.2', '1.2.3-alpha.2']),
])

for (const line of lines) {
  const fields = line.split('\t')
  if (fields.length !== 3) {
    throw new Error(`invalid intersection probe row: ${line}`)
  }

  const [left, right, witness] = fields
  const leftAccepts = semver.satisfies(witness, left)
  const rightAccepts = semver.satisfies(witness, right)

  if (!leftAccepts || !rightAccepts) {
    witnessMismatches.push({
      left,
      right,
      witness,
      leftAccepts,
      rightAccepts,
    })
    continue
  }

  const leftRange = new semver.Range(left)
  const rightRange = new semver.Range(right)
  const leftRight = leftRange.intersects(rightRange)
  const rightLeft = rightRange.intersects(leftRange)

  if (!leftRight || !rightLeft) {
    intersectionMismatches.push({
      left,
      right,
      witness,
      leftRight,
      rightLeft,
    })
  }
}

console.log(
  `checked ${lines.length} concrete Semverifier witnesses against node-semver ${require('semver/package.json').version}`,
)

if (witnessMismatches.length) {
  console.error(
    `found ${witnessMismatches.length} witness satisfaction mismatches`,
  )
  for (const mismatch of witnessMismatches.slice(0, 50)) {
    console.error(JSON.stringify(mismatch))
  }
  if (witnessMismatches.length > 50) {
    console.error(
      `... ${witnessMismatches.length - 50} additional witness mismatches omitted`,
    )
  }
  process.exit(1)
}

const knownContradictions = []
const unexpectedContradictions = []

for (const mismatch of intersectionMismatches) {
  const key = JSON.stringify([mismatch.left, mismatch.right, mismatch.witness])
  if (knownNodeSemverContradictions.has(key)) {
    knownContradictions.push(mismatch)
  } else {
    unexpectedContradictions.push(mismatch)
  }
}

if (knownContradictions.length) {
  console.warn(
    `observed ${knownContradictions.length} known node-semver Range.intersects prerelease-licensing contradictions`,
  )
  for (const mismatch of knownContradictions) {
    console.warn(JSON.stringify(mismatch))
  }
  console.warn(
    'tracked upstream by the closed, unmerged npm/node-semver PR #884; current main still uses the affected pairwise comparator-set check',
  )
}

if (unexpectedContradictions.length) {
  console.error(
    `found ${unexpectedContradictions.length} unexpected concrete Range.intersects contradictions`,
  )
  for (const mismatch of unexpectedContradictions.slice(0, 50)) {
    console.error(JSON.stringify(mismatch))
  }
  if (unexpectedContradictions.length > 50) {
    console.error(
      `... ${unexpectedContradictions.length - 50} additional contradictions omitted`,
    )
  }
  process.exit(1)
}

console.log(
  `no unexpected Range.intersects contradictions; ${knownContradictions.length} known upstream divergences remain`,
)
