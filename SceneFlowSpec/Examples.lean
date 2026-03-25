/-
  SceneFlowSpec.Examples
  Concrete driving safety properties and example traces demonstrating the monitor.
-/
import SceneFlowSpec.Monitor

namespace SceneFlowSpec

open SFProp

----------------------------------------------------------------------
-- § 1. Building blocks: entity & scene helpers
----------------------------------------------------------------------

/-- Make an entity with the given id, type, and optional attributes. -/
def mkEntity (id : Nat) (ty : EntityType) (attrs : List (String × String) := []) : Entity :=
  { id := ⟨id⟩, type := ty, attrs := attrs }

/-- Make a relation. -/
def mkRel (src : Nat) (lbl : RelLabel) (tgt : Nat) : Relation :=
  { src := ⟨src⟩, label := lbl, tgt := ⟨tgt⟩ }

----------------------------------------------------------------------
-- § 2. Atomic predicates (scene-level tests)
----------------------------------------------------------------------

/-- Is entity `eid` present in the scene? -/
def entityPresent (eid : Nat) : AtomicPred :=
  { label := s!"present({eid})", test := fun s => s.hasEntity ⟨eid⟩ }

/-- Is entity `eid` of type `ty`? -/
def entityHasType (eid : Nat) (ty : EntityType) : AtomicPred :=
  { label := s!"hasType({eid})",
    test  := fun s => match s.getEntity ⟨eid⟩ with
      | some e => e.type == ty
      | none   => false }

/-- Does the relation `src --lbl--> tgt` exist? -/
def hasRelation (src : Nat) (lbl : RelLabel) (tgt : Nat) : AtomicPred :=
  { label := s!"rel({src},{tgt})",
    test  := fun s => s.hasRelation ⟨src⟩ lbl ⟨tgt⟩ }

/-- Does entity `eid` have attribute `k = v`? -/
def entityAttr (eid : Nat) (k v : String) : AtomicPred :=
  { label := s!"attr({eid},{k}={v})",
    test  := fun s => s.hasAttr ⟨eid⟩ k v }

/-- Are there any entities of type `ty` in the scene? -/
def anyOfType (ty : EntityType) : AtomicPred :=
  { label := s!"anyOfType",
    test  := fun s => !(s.entitiesOfType ty).isEmpty }

----------------------------------------------------------------------
-- § 3. Example properties
----------------------------------------------------------------------

/-!
### Property 1: Yield at intersection

"If vehicle 1 is in a junction and vehicle 2 enters the junction in the
 next step, then vehicle 2 must not be in the junction until vehicle 1
 has left."

  (v1_in_junc ∧ ◯ v2_in_junc) → ◯(¬v2_in_junc 𝒰 ¬v1_in_junc)
-/

def v1InJunction : SFProp := .atom (hasRelation 1 .isIn 100)
def v2InJunction : SFProp := .atom (hasRelation 2 .isIn 100)

def yieldAtIntersection : NamedProperty :=
  { name := "Yield at intersection"
    formula := (v1InJunction ⋀ ◯ v2InJunction) ⟹ ◯ (¬ₛ v2InJunction 𝒰 ¬ₛ v1InJunction) }

/-!
### Property 2: Safe following distance

"Once vehicle 2 starts following vehicle 1 too closely, it must stop
 doing so within 5 frames."

  (near ∧ behind ∧ same_lane) → ¬ bounded 5 (near ∧ behind ∧ same_lane)

  Equivalently: it's never the case that (near ∧ behind ∧ same_lane)
  persists for 5 consecutive steps.
-/

def tooClose : SFProp := .atom (hasRelation 2 .near 1)
def isBehind : SFProp := .atom (hasRelation 2 .behind 1)
def sameLane : SFProp :=
  .atom { label := "sameLane(1,2)",
          test  := fun s =>
            let v1lanes := s.relatedTo ⟨1⟩ .isIn
            let v2lanes := s.relatedTo ⟨2⟩ .isIn
            v1lanes.any (fun l => v2lanes.contains l) }

def followingCondition : SFProp := tooClose ⋀ isBehind ⋀ sameLane

def safeFollowingDistance : NamedProperty :=
  { name := "Safe following distance (5 frames)"
    formula := □ (¬ₛ (.bounded 5 followingCondition)) }

/-!
### Property 3: Opposing lane clear when passing

"Whenever a vehicle is in an opposing lane, there must be no oncoming
 vehicle in that lane."

  □ (in_opp_lane → opp_clear)
-/

def inOppLane : SFProp := .atom (hasRelation 1 .opposes 200)
def oppClear : SFProp :=
  .atom { label := "oppClear",
          test := fun s =>
            -- No vehicle is related to lane 200 via isIn
            (s.relations.filter (fun r =>
              r.tgt == ⟨200⟩ && r.label == .isIn &&
              match s.getEntity r.src with
              | some e => e.type == .vehicle
              | none   => false)).isEmpty }

def oppLaneClear : NamedProperty :=
  { name := "Opposing lane clear when passing"
    formula := □ (inOppLane ⟹ oppClear) }

----------------------------------------------------------------------
-- § 4. Example traces
----------------------------------------------------------------------

/-- A 4-frame trace where vehicle 1 is in a junction for frames 0-2,
    and vehicle 2 enters the junction at frame 1 and leaves at frame 3.
    Vehicle 2 properly yields (leaves before vehicle 1). -/
def yieldTrace_good : Trace :=
  let junc := mkEntity 100 .junction
  let v1   := mkEntity 1 .vehicle
  let v2   := mkEntity 2 .vehicle
  [ -- Frame 0: only v1 in junction
    { entities := [junc, v1, v2],
      relations := [mkRel 1 .isIn 100] },
    -- Frame 1: both in junction (v2 enters)
    { entities := [junc, v1, v2],
      relations := [mkRel 1 .isIn 100, mkRel 2 .isIn 100] },
    -- Frame 2: v1 still in junction, v2 has left
    { entities := [junc, v1, v2],
      relations := [mkRel 1 .isIn 100] },
    -- Frame 3: both out
    { entities := [junc, v1, v2],
      relations := [] }
  ]

/-- A trace where vehicle 2 fails to yield — stays in junction
    while vehicle 1 is still there. -/
def yieldTrace_bad : Trace :=
  let junc := mkEntity 100 .junction
  let v1   := mkEntity 1 .vehicle
  let v2   := mkEntity 2 .vehicle
  [ -- Frame 0: v1 in junction
    { entities := [junc, v1, v2],
      relations := [mkRel 1 .isIn 100] },
    -- Frame 1: both in junction
    { entities := [junc, v1, v2],
      relations := [mkRel 1 .isIn 100, mkRel 2 .isIn 100] },
    -- Frame 2: both still in junction (violation!)
    { entities := [junc, v1, v2],
      relations := [mkRel 1 .isIn 100, mkRel 2 .isIn 100] },
    -- Frame 3: both in junction
    { entities := [junc, v1, v2],
      relations := [mkRel 1 .isIn 100, mkRel 2 .isIn 100] }
  ]

----------------------------------------------------------------------
-- § 5. Demonstrations
----------------------------------------------------------------------

-- These #eval calls demonstrate the monitor at elaboration time.

#eval checkProperty yieldTrace_good yieldAtIntersection
-- Expected: ✓ SATISFIED

#eval checkProperty yieldTrace_bad yieldAtIntersection
-- Expected: ✗ VIOLATED

-- Empty trace: always-properties are vacuously true
#eval monitor ([] : Trace) safeFollowingDistance.formula
-- Expected: satisfied

-- Demonstrate bounded operator: following for exactly 3 frames then stopping
def followingTrace : Trace :=
  let lane := mkEntity 10 .lane
  let v1   := mkEntity 1 .vehicle
  let v2   := mkEntity 2 .vehicle
  [ -- Frames 0-2: v2 is near, behind, same lane as v1
    { entities := [lane, v1, v2],
      relations := [mkRel 2 .near 1, mkRel 2 .behind 1,
                    mkRel 1 .isIn 10, mkRel 2 .isIn 10] },
    { entities := [lane, v1, v2],
      relations := [mkRel 2 .near 1, mkRel 2 .behind 1,
                    mkRel 1 .isIn 10, mkRel 2 .isIn 10] },
    { entities := [lane, v1, v2],
      relations := [mkRel 2 .near 1, mkRel 2 .behind 1,
                    mkRel 1 .isIn 10, mkRel 2 .isIn 10] },
    -- Frame 3: v2 moves to different lane
    { entities := [lane, v1, v2],
      relations := [mkRel 1 .isIn 10] },
    -- Frame 4: normal driving
    { entities := [lane, v1, v2],
      relations := [mkRel 1 .isIn 10] }
  ]

#eval checkProperty followingTrace safeFollowingDistance
-- Expected: ✓ SATISFIED (following for only 3 frames, limit is 5)

-- Per-frame monitoring detail
#eval monitorFrames followingTrace followingCondition
-- Shows which frames the following condition holds at

end SceneFlowSpec
