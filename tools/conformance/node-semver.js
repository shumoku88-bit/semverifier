'use strict'

const { spawnSync } = require('node:child_process')
const semver = require('semver')

const run = spawnSync(
  'lake',
  ['exe', 'semverifierConformanceCorpus'],
  {
    encoding: 'utf8',
    maxBuffer: 32 * 1024 * 1024,
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
const mismatches = []

for (const line of lines) {
  const fields = line.split('\t')
  if (fields.length !== 3) {
    throw new Error(`invalid corpus row: ${line}`)
  }

  const [range, version, leanRaw] = fields
  const lean = leanRaw === 'true'
  const node = semver.satisfies(version, range)

  if (lean !== node) {
    mismatches.push({ range, version, lean, node })
  }
}

console.log(
  `checked ${lines.length} judgments against node-semver ${require('semver/package.json').version}`,
)

if (mismatches.length) {
  console.error(`found ${mismatches.length} conformance mismatches`)
  for (const mismatch of mismatches.slice(0, 50)) {
    console.error(JSON.stringify(mismatch))
  }
  if (mismatches.length > 50) {
    console.error(`... ${mismatches.length - 50} additional mismatches omitted`)
  }
  process.exit(1)
}

console.log('all judgments agree')
