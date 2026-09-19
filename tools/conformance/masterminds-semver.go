package main

import (
	"bufio"
	"fmt"
	"os"
	"sort"
	"strings"

	semver "github.com/Masterminds/semver/v3"
)

type mismatch struct {
	rangeText string
	version   string
	lean      bool
	goResult  bool
}

type rangeCount struct {
	rangeText string
	count     int
}

func printExamples(label string, examples []mismatch) {
	fmt.Printf("%s examples: %d\n", label, len(examples))
	for _, example := range examples {
		fmt.Printf(
			"mismatch\trange=%q\tversion=%q\tsemverifier=%t\tmasterminds=%t\n",
			example.rangeText,
			example.version,
			example.lean,
			example.goResult,
		)
	}
}

func main() {
	scanner := bufio.NewScanner(os.Stdin)
	scanner.Buffer(make([]byte, 64*1024), 1024*1024)

	totalRows := 0
	compared := 0
	stableMismatches := 0
	prereleaseMismatches := 0
	falsePositives := 0
	falseNegatives := 0
	constraintParseErrors := 0
	versionParseErrors := 0
	stableExamples := make([]mismatch, 0, 20)
	prereleaseExamples := make([]mismatch, 0, 20)
	parseExamples := make([]string, 0, 10)
	byRange := make(map[string]int)

	for scanner.Scan() {
		line := scanner.Text()
		if line == "" {
			continue
		}
		totalRows++

		fields := strings.Split(line, "\t")
		if len(fields) != 3 {
			fmt.Fprintf(os.Stderr, "invalid corpus row: %q\n", line)
			os.Exit(1)
		}

		rangeText, versionText, leanRaw := fields[0], fields[1], fields[2]
		if leanRaw != "true" && leanRaw != "false" {
			fmt.Fprintf(os.Stderr, "invalid Lean result %q in row: %q\n", leanRaw, line)
			os.Exit(1)
		}
		lean := leanRaw == "true"

		constraint, err := semver.NewConstraint(rangeText)
		if err != nil {
			constraintParseErrors++
			if len(parseExamples) < cap(parseExamples) {
				parseExamples = append(parseExamples, rangeText)
			}
			continue
		}

		version, err := semver.StrictNewVersion(versionText)
		if err != nil {
			versionParseErrors++
			if versionParseErrors <= 20 {
				fmt.Fprintf(os.Stderr, "version parse error: version=%q error=%v\n", versionText, err)
			}
			continue
		}

		compared++
		goResult := constraint.Check(version)
		if lean == goResult {
			continue
		}

		item := mismatch{
			rangeText: rangeText,
			version:   versionText,
			lean:      lean,
			goResult:  goResult,
		}
		byRange[rangeText]++

		if version.Prerelease() == "" {
			stableMismatches++
			if len(stableExamples) < cap(stableExamples) {
				stableExamples = append(stableExamples, item)
			}
		} else {
			prereleaseMismatches++
			if len(prereleaseExamples) < cap(prereleaseExamples) {
				prereleaseExamples = append(prereleaseExamples, item)
			}
		}
		if goResult {
			falsePositives++
		} else {
			falseNegatives++
		}
	}

	if err := scanner.Err(); err != nil {
		fmt.Fprintf(os.Stderr, "read corpus: %v\n", err)
		os.Exit(1)
	}

	counts := make([]rangeCount, 0, len(byRange))
	for rangeText, count := range byRange {
		counts = append(counts, rangeCount{rangeText: rangeText, count: count})
	}
	sort.Slice(counts, func(i, j int) bool {
		if counts[i].count != counts[j].count {
			return counts[i].count > counts[j].count
		}
		return counts[i].rangeText < counts[j].rangeText
	})

	fmt.Printf("corpus rows: %d\n", totalRows)
	fmt.Printf("compared judgments: %d\n", compared)
	fmt.Printf("constraint parse incompatibilities: %d\n", constraintParseErrors)
	fmt.Printf("version parse errors: %d\n", versionParseErrors)
	fmt.Printf("mismatches: %d\n", stableMismatches+prereleaseMismatches)
	fmt.Printf("  stable-version mismatches: %d\n", stableMismatches)
	fmt.Printf("  prerelease-version mismatches: %d\n", prereleaseMismatches)
	fmt.Printf("  Masterminds true / Semverifier false: %d\n", falsePositives)
	fmt.Printf("  Masterminds false / Semverifier true: %d\n", falseNegatives)

	fmt.Printf("parse-incompatible range examples: %q\n", parseExamples)

	limit := 15
	if len(counts) < limit {
		limit = len(counts)
	}
	fmt.Printf("top mismatch ranges: %d\n", limit)
	for _, entry := range counts[:limit] {
		fmt.Printf("range-mismatches\tcount=%d\trange=%q\n", entry.count, entry.rangeText)
	}

	printExamples("stable", stableExamples)
	printExamples("prerelease", prereleaseExamples)

	if versionParseErrors != 0 {
		os.Exit(1)
	}
}
