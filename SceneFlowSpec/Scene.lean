/-
  SceneFlowSpec.Scene
  Core types modelling driving scene graphs: entities, relations, scenes, and traces.
-/

namespace SceneFlowSpec

/-- Types of entities that can appear in a driving scene graph. -/
inductive EntityType where
  | vehicle
  | lane
  | junction
  | pedestrian
  | sign
  | bicycle
  | other
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Unique identity of an entity within a scene. -/
structure EntityId where
  val : Nat
  deriving DecidableEq, Repr, BEq, Hashable, Inhabited

instance : ToString EntityId where
  toString eid := s!"e{eid.val}"

/-- An entity node in the scene graph. -/
structure Entity where
  id    : EntityId
  type  : EntityType
  attrs : List (String × String) := []
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Labels for directed edges between entities. -/
inductive RelLabel where
  | isIn
  | toLeftOf
  | toRightOf
  | behind
  | inFrontOf
  | opposes
  | near
  | controls
  | laneChange
  | sameDirection
  deriving DecidableEq, Repr, BEq, Inhabited

/-- A directed, labelled edge in the scene graph. -/
structure Relation where
  src   : EntityId
  label : RelLabel
  tgt   : EntityId
  deriving DecidableEq, Repr, BEq

/-- A scene graph: a snapshot of the driving world at one point in time. -/
structure Scene where
  entities  : List Entity
  relations : List Relation
  deriving Repr

instance : Inhabited Scene where
  default := ⟨[], []⟩

/-- A finite trace of scenes (index 0 = earliest frame). -/
abbrev Trace := List Scene

----------------------------------------------------------------------
-- Scene query helpers
----------------------------------------------------------------------

namespace Scene

/-- Look up an entity by id. -/
def getEntity (s : Scene) (eid : EntityId) : Option Entity :=
  s.entities.find? (fun e => decide (e.id = eid))

/-- Does the scene contain an entity with this id? -/
def hasEntity (s : Scene) (eid : EntityId) : Bool :=
  s.entities.any (fun e => decide (e.id = eid))

/-- All entities whose type matches `t`. -/
def entitiesOfType (s : Scene) (t : EntityType) : List Entity :=
  s.entities.filter (fun e => decide (e.type = t))

/-- Does entity `eid` have attribute key `k` with value `v`? -/
def hasAttr (s : Scene) (eid : EntityId) (k v : String) : Bool :=
  match s.getEntity eid with
  | some e => e.attrs.any (fun ⟨ak, av⟩ => decide (ak = k) && decide (av = v))
  | none   => false

/-- All targets reachable from `src` along edges with label `lbl`. -/
def relatedTo (s : Scene) (src : EntityId) (lbl : RelLabel) : List EntityId :=
  (s.relations.filter (fun r => decide (r.src = src) && decide (r.label = lbl))).map Relation.tgt

/-- All sources that have an edge with label `lbl` to `tgt`. -/
def relatedFrom (s : Scene) (tgt : EntityId) (lbl : RelLabel) : List EntityId :=
  (s.relations.filter (fun r => decide (r.tgt = tgt) && decide (r.label = lbl))).map Relation.src

/-- Does a relation `src --lbl--> tgt` exist? -/
def hasRelation (s : Scene) (src : EntityId) (lbl : RelLabel) (tgt : EntityId) : Bool :=
  s.relations.any (fun r => decide (r.src = src) && decide (r.label = lbl) && decide (r.tgt = tgt))

end Scene

----------------------------------------------------------------------
-- Trace helpers
----------------------------------------------------------------------

/-- Get the scene at position `i`, or the empty scene if out of bounds. -/
def Trace.getScene (τ : Trace) (i : Nat) : Scene :=
  τ.getD i default

end SceneFlowSpec
