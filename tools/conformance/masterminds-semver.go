package main

import (
	"bufio"
	"fmt"
	"os"
	"strings"

	semver "github.com/Masterminds/semver/v3"
)

type mismatch struct {
	rangeText string
	version   string
	lean      bool
	goResult  bool
}

func main() {
	scanner := bufio.NewScanner(os.Stdin)
	scanner.Buffer(make([]byte, 64*1024), 1024*1024)

	total := 0
	stableMismatches := 0
	prereleaseMismatches := 0
	falsePositives := 0
	falseNegatives := 0
	parseErrors := 0
	examples := make([]mismatch, 0, 50)

	for scanner.Scan() {
		line := scanner.Text()
		if line == "" {
			continue
		}

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
			parseErrors++
			if parseErrors <= 20 {
				fmt.Fprintf(os.Stderr, "constraint parse error: range=%q error=%v\n", rangeText, err)
			}
			continue
		}

		version, err := semver.StrictNewVersion(versionText)
		if err != nil {
			parseErrors++
			if parseErrors <= 20 {
				fmt.Fprintf(os.Stderr, "version parse error: version=%q error=%v\n", versionText, err)
			}
			continue
		}

		goResult := constraint.Check(version)
		total++
		if lean == goResult {
			continue
		}

		if version.Prerelease() == "" {
			stableMismatches++
		} else {
			prereleaseMismatches++
		}
		if goResult {
			falsePositives++
		} else {
			falseNegatives++
		}

		if len(examples) < cap(examples) {
			examples = append(examples, mismatch{
				rangeText: rangeText,
				version:   versionText,
				lean:      lean,
				goResult:  goResult,
			})
		}
	}

	if err := scanner.Err(); err != nil {
		fmt.Fprintf(os.Stderr, "read corpus: %v\n", err)
		os.Exit(1)
	}

	fmt.Printf("checked %d judgments against Masterminds/semver\n", total)
	fmt.Printf("mismatches: %d\n", stableMismatches+prereleaseMismatches)
	fmt.Printf("  stable-version mismatches: %d\n", stableMismatches)
	fmt.Printf("  prerelease-version mismatches: %d\n", prereleaseMismatches)
	fmt.Printf("  Masterminds true / Semverifier false: %d\n", falsePositives)
	fmt.Printf("  Masterminds false / Semverifier true: %d\n", falseNegatives)
	fmt.Printf("parse errors: %d\n", parseErrors)

	for _, example := range examples {
		fmt.Printf(
			"mismatch\trange=%q\tversion=%q\tsemverifier=%t\tmasterminds=%t\n",
			example.rangeText,
			example.version,
			example.lean,
			example.goResult,
		)
	}

	if parseErrors != 0 {
		os.Exit(1)
	}
}
