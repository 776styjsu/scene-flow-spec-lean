import Lake
open Lake DSL

package «scene-flow-spec-lean» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «SceneFlowSpec» where
  srcDir := "."
