package main

import (
	"fmt"

	semver "github.com/Masterminds/semver/v3"
)

func main() {
	constraint, err := semver.NewConstraint("^*")
	if err != nil {
		panic(err)
	}

	stable := semver.MustParse("0.0.1")
	prerelease := semver.MustParse("0.0.0-alpha")

	stableResult := constraint.Check(stable)
	defaultPrereleaseResult := constraint.Check(prerelease)

	constraint.IncludePrerelease = true
	includedPrereleaseResult := constraint.Check(prerelease)

	fmt.Printf(
		"stable=%t default-prerelease=%t included-prerelease=%t\n",
		stableResult,
		defaultPrereleaseResult,
		includedPrereleaseResult,
	)
}
