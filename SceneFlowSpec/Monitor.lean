/-
  SceneFlowSpec.Monitor
  Runtime monitor that checks a SceneFlow property against a finite trace.
-/
import SceneFlowSpec.Semantics

namespace SceneFlowSpec

/-- Verdict of property monitoring. -/
inductive Verdict where
  | satisfied
  | violated
  deriving DecidableEq, Repr, BEq

instance : ToString Verdict where
  toString
    | .satisfied => "✓ SATISFIED"
    | .violated  => "✗ VIOLATED"

/-- Run the monitor: evaluate formula `φ` from position 0 of trace `τ`. -/
def monitor (τ : Trace) (φ : SFProp) : Verdict :=
  if satisfies τ φ then .satisfied else .violated

/-- Named property for nicer reporting. -/
structure NamedProperty where
  name    : String
  formula : SFProp

/-- Check a named property against a trace and produce a report string. -/
def checkProperty (τ : Trace) (prop : NamedProperty) : String :=
  let verdict := monitor τ prop.formula
  s!"[{verdict}] {prop.name} (trace length = {τ.length})"

/-- Check multiple properties against a trace. -/
def checkAll (τ : Trace) (props : List NamedProperty) : List String :=
  props.map (checkProperty τ)

/-- Monitor with per-frame detail: returns the verdict at each position. -/
def monitorFrames (τ : Trace) (φ : SFProp) : List (Nat × Bool) :=
  List.range τ.length |>.map fun i => (i, eval τ i φ)

end SceneFlowSpec
