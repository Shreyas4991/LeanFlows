import Mathlib
import Flows.Walk

/-!
# Basic definitions of flow networks

We are following the wikipedia definitions here to adapt a widely
accepted set of definitions. All definitions can be found in
the wikipedia page.

References:
- [Wikipedia page on flow network](https://en.wikipedia.org/wiki/Flow_network)

-/


open Digraph

#print Digraph



/--
The standard flow network consists of a digraph `G`,
a capacity function `c : V → ℝ≥0`, a source node `s`
and a sink node `t`
-/
structure FlowNetwork (V : Type u) where
  G : Digraph V
  edgeCap : V → V → ℝ -- arc capacity function
  s : V -- source
  t : V -- sink



variable [Fintype V]
/--
The flow leaving a node v under a flow function `flow`
-/
def outFlow (flow : V → V → ℝ) (v : V) : ℝ :=
  ∑ w : V, flow v w

/--
The flow entering a node v under a flow function `flow`
-/
def inFlow (flow : V → V → ℝ) (v : V) : ℝ :=
  ∑ w : V, flow w v

def excessInFlow (flow : V → V → ℝ) (v : V) : ℝ :=
  inFlow flow v - outFlow flow v

abbrev IsActive (flow : V → V → ℝ) (v : V) : Prop :=
  excessInFlow flow v > 0

abbrev IsDeficient (flow : V → V → ℝ) (v : V) : Prop :=
  excessInFlow flow v < 0

abbrev IsConserving (flow : V → V → ℝ) (v : V) : Prop :=
  excessInFlow flow v = 0

/--
A Pseudo flow is a flow where for each edge `(v,w)`, `flow v w = - flow w v`
-/
abbrev AntiSymm (flow : V → V → ℝ) (v w : V) :=
  flow v w = - flow w v

abbrev EdgeCapacityConstrained (N : FlowNetwork V)
  (flow : V → V → ℝ) (v w : V) :=
  flow v w ≤ N.edgeCap v w

abbrev PseudoFlow (N : FlowNetwork V) (flow : V → V → ℝ) : Prop :=
  ∀ v w : V, N.G.Adj v w →
    AntiSymm flow v w ∧ EdgeCapacityConstrained N flow v w

abbrev PreFlow (N : FlowNetwork V) (flow : V → V → ℝ) : Prop :=
  PseudoFlow N flow
  ∧ ∀ v : V, v ≠ N.s → inFlow flow v > 0
  ∧ inFlow flow N.s = 0

abbrev FlowConstraint (flow : V → V → ℝ) (v : V) : Prop :=
  inFlow flow v = outFlow flow v


abbrev FeasibleFlow (N : FlowNetwork V) (flow : V → V → ℝ) : Prop :=
  ∀ v : V, v ≠ N.s → v ≠ N.t →
    PseudoFlow N flow
    ∧ FlowConstraint flow v
    ∧ inFlow flow N.t = outFlow flow N.s


def flowValue (N : FlowNetwork V)
  (flow : V → V → ℝ)
  (_ : FeasibleFlow N flow) :=
  outFlow flow N.s

omit [Fintype V] in
def residualCapacity (N : FlowNetwork V) (flow : V → V → ℝ) (v w : V) : ℝ :=
  N.edgeCap v w - flow v w

abbrev ResidualNetwork
  (N : FlowNetwork V) (flow : V → V → ℝ) : FlowNetwork V where
  G := N.G
  s := N.s
  t := N.t
  edgeCap := residualCapacity N flow



/--
An `s-t` path is augmenting, if for every pair of vertices in the support
of the underlying walk (i.e. they are a directed edge along the path),
the flow across this edge is strictly less than its capacity
-/
def IsAugmentingPath
  {N : FlowNetwork V}
  (P : N.G.Path)
  (flow : V → V → ℝ) : Prop :=
  let pathVerts := P.support
  ∀ u ∈ pathVerts,
    ∀ v ∈ pathVerts,
      N.G.Adj u v → residualCapacity N flow u v > 0



@[simp]
noncomputable def Digraph.Walk.bottleneckEdge
  {N : FlowNetwork V}
  (W : N.G.Walk) (flow : V → V → ℝ) : Option (V × V) :=
  W.edgeList.argmin (fun (v,w) => residualCapacity N flow v w)

@[simp]
noncomputable def bottleneckWeight
  (N : FlowNetwork V)
  (W : N.G.Walk) (flow : V → V → ℝ) : ℝ :=

  let argminEdge := W.bottleneckEdge flow
  match argminEdge with
  | some (v,w) => residualCapacity N flow v w
  | none => 0

omit [Fintype V] in
lemma Digraph.Walk.bottleneckWeight_emptyWalk
  (N : FlowNetwork V)
  (W : N.G.Walk) (flow : V → V → ℝ)
  (hW : W.support = []) : bottleneckWeight N W flow = 0 := by
  simp [bottleneckWeight]
  fun_induction edgeList <;> simp_all

omit [Fintype V] in
lemma Digraph.Walk.bottleneckWeight_singleton
  (N : FlowNetwork V)
  (W : N.G.Walk) (flow : V → V → ℝ)
  (hW : ∃ x : V, W.support = [x]) : bottleneckWeight N W flow = 0 := by
  simp [bottleneckWeight]
  fun_induction edgeList <;> simp_all

def uncurryFlow (flow : V → V → ℝ) : V × V → ℝ := fun (v,w) => flow v w
