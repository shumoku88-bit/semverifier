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

const rows = run.stdout.split('\n').filter(Boolean).map((line) => {
  const fields = line.split('\t')
  if (fields.length !== 3) {
    throw new Error(`invalid intersection matrix row: ${line}`)
  }

  const [leftRaw, rightRaw, result] = fields
  const witnessPrefix = 'witness='
  const intersects = result.startsWith(witnessPrefix)

  if (!intersects && result !== 'disjoint') {
    throw new Error(`invalid matrix result: ${result}`)
  }

  return {
    leftRaw,
    rightRaw,
    expected: intersects,
    witness: intersects ? result.slice(witnessPrefix.length) : null,
  }
})

const ranges = [...new Set(rows.map(({ leftRaw }) => leftRaw))]
const parsed = new Map(ranges.map((raw) => [raw, new semver.Range(raw)]))

const currentSetSatisfiable = (comparators) => {
  let result = true
  const remainingComparators = comparators.slice()
  let testComparator = remainingComparators.pop()

  while (result && remainingComparators.length) {
    result = remainingComparators.every((otherComparator) =>
      testComparator.intersects(otherComparator)
    )
    testComparator = remainingComparators.pop()
  }

  return result
}

const setRange = (comparators) =>
  new semver.Range(comparators.map((comparator) => comparator.value).join(' '))

const setMinVersion = (comparators) =>
  semver.minVersion(setRange(comparators))

const symmetricComparatorPair = (left, right) =>
  left.intersects(right) && right.intersects(left)

const baseline = (left, right) => left.intersects(right)

const symmetricPairwise = (left, right) =>
  left.set.some((leftSet) =>
    currentSetSatisfiable(leftSet) &&
    right.set.some((rightSet) =>
      currentSetSatisfiable(rightSet) &&
      leftSet.every((leftComparator) =>
        rightSet.every((rightComparator) =>
          symmetricComparatorPair(leftComparator, rightComparator)
        )
      )
    )
  )

const symmetricPairwiseWithNonemptySets = (left, right) =>
  left.set.some((leftSet) =>
    setMinVersion(leftSet) !== null &&
    right.set.some((rightSet) =>
      setMinVersion(rightSet) !== null &&
      leftSet.every((leftComparator) =>
        rightSet.every((rightComparator) =>
          symmetricComparatorPair(leftComparator, rightComparator)
        )
      )
    )
  )

const setMinWitness = (left, right) =>
  left.set.some((leftSet) => {
    const leftSetRange = setRange(leftSet)
    const leftMin = semver.minVersion(leftSetRange)

    if (leftMin === null) {
      return false
    }

    return right.set.some((rightSet) => {
      const rightSetRange = setRange(rightSet)
      const rightMin = semver.minVersion(rightSetRange)

      if (rightMin === null) {
        return false
      }

      const candidates = [leftMin, rightMin]
      return candidates.some((candidate) =>
        leftSetRange.test(candidate) && rightSetRange.test(candidate)
      )
    })
  })

const combinedSetMinWitness = (left, right) =>
  left.set.some((leftSet) => {
    const leftSetRange = setRange(leftSet)

    return right.set.some((rightSet) => {
      const rightSetRange = setRange(rightSet)
      const combinedRaw = [...leftSet, ...rightSet]
        .map((comparator) => comparator.value)
        .join(' ')
      const candidate = semver.minVersion(combinedRaw)

      return candidate !== null &&
        leftSetRange.test(candidate) &&
        rightSetRange.test(candidate)
    })
  })

const renderVersion = (version) => {
  const prerelease = version.prerelease.length
    ? `-${version.prerelease.join('.')}`
    : ''
  return `${version.major}.${version.minor}.${version.patch}${prerelease}`
}

const strictLowerSuccessor = (version) => {
  if (version.prerelease.length) {
    return new semver.SemVer(`${renderVersion(version)}.0`)
  }
  return new semver.SemVer(
    `${version.major}.${version.minor}.${version.patch + 1}`
  )
}

const boundaryCandidates = (leftSet, rightSet) => {
  const candidates = new Map()

  const add = (candidate) => {
    candidates.set(candidate.version, candidate)
  }

  add(new semver.SemVer('0.0.0-0'))
  add(new semver.SemVer('0.0.0'))

  for (const comparator of [...leftSet, ...rightSet]) {
    if (comparator.value === '') {
      continue
    }

    add(new semver.SemVer(comparator.semver.version))

    if (comparator.semver.prerelease.length) {
      add(new semver.SemVer(
        `${comparator.semver.major}.${comparator.semver.minor}.${comparator.semver.patch}`
      ))
    }

    if (comparator.operator === '>') {
      add(strictLowerSuccessor(comparator.semver))
    }
  }

  return [...candidates.values()]
}

const boundaryWitness = (left, right) =>
  left.set.some((leftSet) => {
    const leftSetRange = setRange(leftSet)

    return right.set.some((rightSet) => {
      const rightSetRange = setRange(rightSet)

      return boundaryCandidates(leftSet, rightSet).some((candidate) =>
        leftSetRange.test(candidate) &&
        rightSetRange.test(candidate)
      )
    })
  })

const strategies = [
  ['baseline', baseline],
  ['symmetric-pairwise', symmetricPairwise],
  ['symmetric-pairwise+nonempty-sets', symmetricPairwiseWithNonemptySets],
  ['set-min-witness', setMinWitness],
  ['combined-set-min-witness', combinedSetMinWitness],
  ['boundary-witness', boundaryWitness],
]

const evaluate = (name, strategy) => {
  let falseNegatives = 0
  let falsePositives = 0
  let baselineFalseToTrue = 0
  let baselineTrueToFalse = 0
  let repairedBaselineErrors = 0
  let introducedErrors = 0
  const introducedExamples = []
  const remainingFalseNegativeExamples = []
  const remainingFalsePositiveExamples = []

  const results = new Map()

  for (const row of rows) {
    const left = parsed.get(row.leftRaw)
    const right = parsed.get(row.rightRaw)
    const actual = strategy(left, right)
    const baselineResult = baseline(left, right)
    const key = JSON.stringify([row.leftRaw, row.rightRaw])

    results.set(key, actual)

    if (row.expected && !actual) {
      falseNegatives += 1
      if (remainingFalseNegativeExamples.length < 8) {
        remainingFalseNegativeExamples.push({
          left: row.leftRaw,
          right: row.rightRaw,
          witness: row.witness,
        })
      }
    }
    if (!row.expected && actual) {
      falsePositives += 1
      if (remainingFalsePositiveExamples.length < 8) {
        remainingFalsePositiveExamples.push({
          left: row.leftRaw,
          right: row.rightRaw,
        })
      }
    }

    if (!baselineResult && actual) {
      baselineFalseToTrue += 1
    }
    if (baselineResult && !actual) {
      baselineTrueToFalse += 1
    }

    const baselineWrong = baselineResult !== row.expected
    const strategyWrong = actual !== row.expected

    if (baselineWrong && !strategyWrong) {
      repairedBaselineErrors += 1
    }
    if (!baselineWrong && strategyWrong) {
      introducedErrors += 1
      if (introducedExamples.length < 12) {
        introducedExamples.push({
          left: row.leftRaw,
          right: row.rightRaw,
          expected: row.expected,
          witness: row.witness,
          baseline: baselineResult,
          strategy: actual,
        })
      }
    }
  }

  let asymmetricUnorderedPairs = 0
  const visited = new Set()

  for (const row of rows) {
    const unordered = JSON.stringify(
      [row.leftRaw, row.rightRaw].sort()
    )
    if (visited.has(unordered)) {
      continue
    }
    visited.add(unordered)

    const leftRight = results.get(JSON.stringify([row.leftRaw, row.rightRaw]))
    const rightLeft = results.get(JSON.stringify([row.rightRaw, row.leftRaw]))

    if (leftRight !== rightLeft) {
      asymmetricUnorderedPairs += 1
    }
  }

  const summary = {
    name,
    falseNegatives,
    falsePositives,
    totalErrors: falseNegatives + falsePositives,
    asymmetricUnorderedPairs,
    baselineFalseToTrue,
    baselineTrueToFalse,
    repairedBaselineErrors,
    introducedErrors,
  }

  console.log(JSON.stringify(summary))
  if (introducedExamples.length) {
    console.log(JSON.stringify({
      name: `${name}:introduced-examples`,
      examples: introducedExamples,
    }))
  }
  if (remainingFalseNegativeExamples.length) {
    console.log(JSON.stringify({
      name: `${name}:false-negative-examples`,
      examples: remainingFalseNegativeExamples,
    }))
  }
  if (remainingFalsePositiveExamples.length) {
    console.log(JSON.stringify({
      name: `${name}:false-positive-examples`,
      examples: remainingFalsePositiveExamples,
    }))
  }
  return summary
}

const summaries = strategies.map(([name, strategy]) =>
  evaluate(name, strategy)
)

const baselineSummary = summaries.find(({ name }) => name === 'baseline')
if (
  baselineSummary.falseNegatives !== 4 ||
  baselineSummary.falsePositives !== 90 ||
  baselineSummary.asymmetricUnorderedPairs !== 34
) {
  throw new Error(
    `baseline checkpoint changed: ${JSON.stringify(baselineSummary)}`
  )
}
