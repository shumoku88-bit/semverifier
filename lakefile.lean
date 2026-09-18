import Lake
open Lake DSL

package semverifier

@[default_target]
lean_lib Semverifier

lean_exe semverifierConformanceCorpus where
  root := `Semverifier.Conformance.Main
