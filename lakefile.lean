import Lake
open Lake DSL

package semverifier

@[default_target]
lean_lib Semverifier

lean_exe semverifier where
  root := `Semverifier.Cli

lean_exe semverifierConformanceCorpus where
  root := `Semverifier.Conformance.Main


lean_exe semverifierIntersectionProbe where
  root := `Semverifier.Conformance.IntersectionMain


lean_exe semverifierIntersectionCoverage where
  root := `Semverifier.Conformance.IntersectionCoverageMain


lean_exe semverifierIntersectionMatrix where
  root := `Semverifier.Conformance.IntersectionMatrixMain
