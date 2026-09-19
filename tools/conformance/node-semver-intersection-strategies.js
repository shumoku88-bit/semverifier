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

const provedBoundaryCandidates = (leftSet, rightSet) => {
  const candidates = new Map()

  const add = (candidate) => {
    candidates.set(candidate.version, candidate)
  }

  add(new semver.SemVer('0.0.0'))

  for (const comparator of [...leftSet, ...rightSet]) {
    if (comparator.value === '') {
      continue
    }

    const bound = comparator.semver
    const core = `${bound.major}.${bound.minor}.${bound.patch}`
    const stable = new semver.SemVer(core)
    const nextStable = new semver.SemVer(
      `${bound.major}.${bound.minor}.${bound.patch + 1}`
    )

    add(stable)
    add(nextStable)

    if (bound.prerelease.length) {
      add(new semver.SemVer(`${core}-0`))
      add(new semver.SemVer(bound.version))
      add(new semver.SemVer(`${renderVersion(bound)}.0`))
    }
  }

  return [...candidates.values()]
}

const provedBoundaryWitness = (left, right) =>
  left.set.some((leftSet) => {
    const leftSetRange = setRange(leftSet)

    return right.set.some((rightSet) => {
      const rightSetRange = setRange(rightSet)

      return provedBoundaryCandidates(leftSet, rightSet).some((candidate) =>
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
  ['proved-boundary-shape', provedBoundaryWitness],
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

const checkpointFields = ({
  name,
  falseNegatives,
  falsePositives,
  totalErrors,
  asymmetricUnorderedPairs,
  baselineFalseToTrue,
  baselineTrueToFalse,
  repairedBaselineErrors,
  introducedErrors,
}) => ({
  name,
  falseNegatives,
  falsePositives,
  totalErrors,
  asymmetricUnorderedPairs,
  baselineFalseToTrue,
  baselineTrueToFalse,
  repairedBaselineErrors,
  introducedErrors,
})

const expectedSummaries = [
  {
    name: 'baseline',
    falseNegatives: 4,
    falsePositives: 90,
    totalErrors: 94,
    asymmetricUnorderedPairs: 34,
    baselineFalseToTrue: 0,
    baselineTrueToFalse: 0,
    repairedBaselineErrors: 0,
    introducedErrors: 0,
  },
  {
    name: 'symmetric-pairwise',
    falseNegatives: 4,
    falsePositives: 56,
    totalErrors: 60,
    asymmetricUnorderedPairs: 0,
    baselineFalseToTrue: 0,
    baselineTrueToFalse: 34,
    repairedBaselineErrors: 34,
    introducedErrors: 0,
  },
  {
    name: 'symmetric-pairwise+nonempty-sets',
    falseNegatives: 4,
    falsePositives: 22,
    totalErrors: 26,
    asymmetricUnorderedPairs: 0,
    baselineFalseToTrue: 0,
    baselineTrueToFalse: 68,
    repairedBaselineErrors: 68,
    introducedErrors: 0,
  },
  {
    name: 'set-min-witness',
    falseNegatives: 1292,
    falsePositives: 0,
    totalErrors: 1292,
    asymmetricUnorderedPairs: 0,
    baselineFalseToTrue: 4,
    baselineTrueToFalse: 1382,
    repairedBaselineErrors: 94,
    introducedErrors: 1292,
  },
  {
    name: 'combined-set-min-witness',
    falseNegatives: 1292,
    falsePositives: 0,
    totalErrors: 1292,
    asymmetricUnorderedPairs: 0,
    baselineFalseToTrue: 4,
    baselineTrueToFalse: 1382,
    repairedBaselineErrors: 94,
    introducedErrors: 1292,
  },
  {
    name: 'boundary-witness',
    falseNegatives: 0,
    falsePositives: 0,
    totalErrors: 0,
    asymmetricUnorderedPairs: 0,
    baselineFalseToTrue: 4,
    baselineTrueToFalse: 90,
    repairedBaselineErrors: 94,
    introducedErrors: 0,
  },
  {
    name: 'proved-boundary-shape',
    falseNegatives: 0,
    falsePositives: 0,
    totalErrors: 0,
    asymmetricUnorderedPairs: 0,
    baselineFalseToTrue: 4,
    baselineTrueToFalse: 90,
    repairedBaselineErrors: 94,
    introducedErrors: 0,
  },
]

const observedSummaries = summaries.map(checkpointFields)

if (JSON.stringify(observedSummaries) !== JSON.stringify(expectedSummaries)) {
  console.error('repair strategy checkpoint changed')
  console.error(`expected: ${JSON.stringify(expectedSummaries)}`)
  console.error(`observed: ${JSON.stringify(observedSummaries)}`)
  process.exit(1)
}
