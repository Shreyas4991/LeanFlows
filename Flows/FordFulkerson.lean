import Mathlib
import Flows.Walk
import Flows.FlowDefs

/-#
# The Ford Fulkerson method
The ford-fulkerson "method" is simple. It says,
1. Find augmenting paths
2. Augment their flow
3. Repeat until there are no augmenting paths.

Per textbooks and wikipedia this is distinct from
the Edmonds Karp algorithm in the sense that Edmonds-Karp
fills in the unspecified details of the Ford-Fulkerson method,
specifically on how the find augmenting paths.

We (well... I) write the algorithm's basic steps in mathematical form
that closely resembles the conceptual content of the pseudocode.
This should suffice for the purposes of verifying correctness
and serving as a target for refinement proofs of a more
algorithmic specification
#-/

def initFlow : V → V → ℝ :=
  fun _ _ => 0


def IsUnsaturatedWalk (N : FlowNetwork V)
  (W : N.G.Path) (flow : V → V → ℝ) :=
    ∀ e ∈ W.edgeList, residualCapacity N flow e.fst e.snd > 0


open Classical in
noncomputable def augmentFlow
  (N : FlowNetwork V)
  (P : N.G.Path)
  (flow : V → V → ℝ) :
  V → V → ℝ :=
    let bottleneckWeight := bottleneckWeight N P.toWalk flow
    fun u v =>
      if P.isPathEdge u v
      then (flow u v) + bottleneckWeight
      else flow u v

#check List.argmin_eq_some_iff


lemma augmentedFlow_is_EdgeCapacityConstrained
  [DecidableEq V]
  (N : FlowNetwork V)
  (P : N.G.Path)
  (flow : V → V → ℝ)
  (hWCap : ∀ v w : V, EdgeCapacityConstrained N flow v w):
  ∀ v w : V, EdgeCapacityConstrained N (augmentFlow N P flow) v w := by
  intro v w
  simp_all [augmentFlow]
  split
  · set bestEdge := List.argmin (fun x ↦ residualCapacity N flow x.1 x.2) P.edgeList with hBestEdge
    cases hb : bestEdge with
    | none =>
        simp
        apply hWCap
    | some val =>
        simp_all
        -- simp_rw [residualCapacity.eq_def] at hb
        -- simp_rw [residualCapacity.eq_def]
        have min_proof : residualCapacity N flow val.1 val.2
          ≤ residualCapacity N flow v w := by
            rename_i hWalkEdge
            have h₂ := (List.argmin_eq_some_iff.mp hBestEdge.symm).2.1 (v,w) hWalkEdge
            simp at h₂
            exact h₂
        trans (flow v w + residualCapacity N flow v w)
        · linarith
        · rw [residualCapacity.eq_def]
          ring_nf
          rfl
  · apply hWCap


open Classical in
noncomputable def augmentationStep
  (N : FlowNetwork V)
  (currentFlow : V → V → ℝ)
  (P : N.G.Path) :
  V → V → ℝ :=
    if IsUnsaturatedWalk N P currentFlow
    then augmentFlow N P currentFlow
    else currentFlow



noncomputable def FordFulkersonRec
  (N : FlowNetwork V) (search_paths : List N.G.Path)
  (currentFlow : V → V → ℝ) : (V → V → ℝ) :=
  match search_paths with
  | [] => currentFlow
  | w :: rest => FordFulkersonRec N rest (augmentationStep N currentFlow w)

/--
Recall that Ford Fulkerson doesn't actually specify how to find paths.
Thus we just find all paths and filter out the unsaturated ones.
-/
noncomputable def FordFulkerson
  (N : FlowNetwork V) (iF : Fintype (N.G.Path)) :=
  FordFulkersonRec N iF.elems.toList initFlow
