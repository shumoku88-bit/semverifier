'use strict'

const { spawnSync } = require('node:child_process')
const semver = require('semver')

const nodeSemverMainSha = '6e05b7637396ac66522cff8731f07cfe0ef49a29'

const cases = [
  {
    name: 'known',
    left: '1.2.3-alpha.2',
    right: '1.2.3-alpha.2 - 1.2.3',
  },
  {
    name: 'simpler-text-prerelease',
    left: '1.0.0-a',
    right: '1.0.0-a - 1.0.0',
  },
  {
    name: 'simpler-numeric-prerelease',
    left: '1.0.0-0',
    right: '1.0.0-0 - 1.0.0',
  },
]

const oracle = (left, right) => {
  const run = spawnSync(
    'lake',
    ['exe', 'semverifier', 'intersect', left, right],
    { encoding: 'utf8' },
  )

  if (run.error) {
    throw run.error
  }
  if (run.status !== 0) {
    process.stderr.write(run.stderr)
    throw new Error(`Semverifier oracle failed for ${left} / ${right}`)
  }

  const output = run.stdout.trim()
  const prefix = 'witness\t'
  if (!output.startsWith(prefix)) {
    throw new Error(`expected witness from Semverifier, got: ${output}`)
  }
  return output.slice(prefix.length)
}

console.log(`node-semver current-main audit target: ${nodeSemverMainSha}`)
console.log(`installed package version: ${require('semver/package.json').version}`)

const observations = cases.map(({ name, left, right }) => {
  const witness = oracle(left, right)
  const leftAccepts = semver.satisfies(witness, left)
  const rightAccepts = semver.satisfies(witness, right)
  const leftRight = new semver.Range(left).intersects(new semver.Range(right))
  const rightLeft = new semver.Range(right).intersects(new semver.Range(left))

  const observation = {
    name,
    left,
    right,
    witness,
    leftAccepts,
    rightAccepts,
    leftRight,
    rightLeft,
  }
  console.log(JSON.stringify(observation))
  return observation
})

for (const observation of observations) {
  if (!observation.leftAccepts || !observation.rightAccepts) {
    throw new Error(
      `node-semver rejects Semverifier witness for ${observation.name}`,
    )
  }
}

const known = observations.find((observation) => observation.name === 'known')
if (!known || known.leftRight !== false || known.rightLeft !== false) {
  throw new Error(
    'current node-semver main no longer reproduces the known symmetric false negative',
  )
}

console.log(
  'reproduced current-main Range.intersects() false negative with a concrete Semverifier witness',
)
