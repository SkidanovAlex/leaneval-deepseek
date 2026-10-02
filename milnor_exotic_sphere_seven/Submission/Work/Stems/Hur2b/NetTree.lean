import Mathlib
import Submission.Work.Stems.Hur2b.NetTau

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The tree of the walk, and its contraction to the base vertex

The image of the walk in `∂I³` is the union of the seven spikes
`{y=0,z=0}`, `{x=1,z=0}`, `{x=1,y=1}`, `{y=1,z=0}`, `{x=1,z=1}`, `{y=1,z=1}`, `{y=0,z=1}`,
which is a tree.  This file defines it (`Tree`) and gives the explicit contraction

* `prune` folds the three *exterior* spikes `{y=1,z=0}`, `{y=1,z=1}`, `{y=0,z=1}` onto the path
  `v → a → b → c₁ → f`,
* `fold1`, `fold2`, `fold3`, `fold4` successively fold the segments `c₁ → f`, `b → c₁`, `a → b`,
  `v → a` of that path onto their first endpoints,

and `rho` assembles them into a homotopy from the identity of `Tree` to the constant `v`.  All the
maps are given by *continuous formulas on the cube*, so no gluing lemma is needed: only the
behaviour on `Tree` has to be checked, and this is a finite case analysis.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2b

open Work.Stems.Cubical Work.Stems.Hur2

noncomputable section

/-- The point of `I³` with coordinates `a`, `b`, `c`. -/
def triple (a b c : unitInterval) : IC 3 := ![a, b, c]

@[simp] theorem triple_zero (a b c : unitInterval) : (triple a b c) 0 = a := rfl
@[simp] theorem triple_one (a b c : unitInterval) : (triple a b c) 1 = b := rfl
@[simp] theorem triple_two (a b c : unitInterval) : (triple a b c) 2 = c := rfl

theorem triple_eta' (p : IC 3) : triple (p 0) (p 1) (p 2) = p := by
  funext i; fin_cases i <;> rfl

/-- The union of the seven spikes of the walk, as a subset of `∂I³`. -/
def Tree (p : IC 3) : Prop :=
  (p 1 = 0 ∧ p 2 = 0) ∨ (p 0 = 1 ∧ p 2 = 0) ∨ (p 0 = 1 ∧ p 1 = 1) ∨
  (p 1 = 1 ∧ p 2 = 0) ∨ (p 0 = 1 ∧ p 2 = 1) ∨ (p 1 = 1 ∧ p 2 = 1) ∨ (p 1 = 0 ∧ p 2 = 1)

/-- A point of the tree lies on `∂I³`. -/
theorem Tree_boundary {p : IC 3} (h : Tree p) : p ∈ Cube.boundary (Fin 3) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨1, Or.inl h1⟩
  · exact ⟨0, Or.inr h1⟩
  · exact ⟨0, Or.inr h1⟩
  · exact ⟨1, Or.inr h1⟩
  · exact ⟨0, Or.inr h1⟩
  · exact ⟨1, Or.inr h1⟩
  · exact ⟨1, Or.inl h1⟩

/-- A point of the tree, as an element of `∂I³`. -/
def treeBdy (p : IC 3) (h : Tree p) : Bdy3 := ⟨p, Tree_boundary h⟩

/-- A point of the tree lies on the `1`-skeleton. -/
theorem Tree_skel {p : IC 3} (h : Tree p) : Skel3 (treeBdy p h) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨1, 2, by decide, 0, 0, h1, h2⟩
  · exact ⟨0, 2, by decide, 1, 0, h1, h2⟩
  · exact ⟨0, 1, by decide, 1, 1, h1, h2⟩
  · exact ⟨1, 2, by decide, 1, 0, h1, h2⟩
  · exact ⟨0, 2, by decide, 1, 1, h1, h2⟩
  · exact ⟨1, 2, by decide, 1, 1, h1, h2⟩
  · exact ⟨1, 2, by decide, 0, 1, h1, h2⟩

/-- The base vertex `(0,0,0)`. -/
def treeRoot : IC 3 := triple 0 0 0

@[simp] theorem treeRoot_apply (i : Fin 3) : treeRoot i = 0 := by
  fin_cases i <;> rfl

/-- The path `v → a → b → c₁ → f`. -/
def pathSet : Set (IC 3) :=
  {p | (p 1 = 0 ∧ p 2 = 0) ∨ (p 0 = 1 ∧ p 2 = 0) ∨ (p 0 = 1 ∧ p 1 = 1) ∨ (p 0 = 1 ∧ p 2 = 1)}

/-- The path `v → a → b → c₁`. -/
def pathSet2 : Set (IC 3) :=
  {p | (p 1 = 0 ∧ p 2 = 0) ∨ (p 0 = 1 ∧ p 2 = 0) ∨ (p 0 = 1 ∧ p 1 = 1)}

/-- The path `v → a → b`. -/
def pathSet3 : Set (IC 3) := {p | (p 1 = 0 ∧ p 2 = 0) ∨ (p 0 = 1 ∧ p 2 = 0)}

/-- The segment `v → a`. -/
def pathSet4 : Set (IC 3) := {p | p 1 = 0 ∧ p 2 = 0}

theorem Tree_imp {p : IC 3} (h : Tree p) : pathSet p ∨ p ∈ {q | q 1 = 1 ∧ q 2 = 0} ∨
    p ∈ {q | q 1 = 1 ∧ q 2 = 1} ∨ p ∈ {q | q 1 = 0 ∧ q 2 = 1} := by
  rcases h with h | h | h | h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inl h)
  · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-! ## The folding of the three exterior spikes onto the path -/

theorem continuous_clampReal : Continuous fun r : ℝ => ((clamp r : unitInterval) : ℝ) :=
  continuous_subtype_val.comp continuous_clamp

/-- The folding of the three exterior spikes onto the path `v → a → b → c₁ → f`. -/
def prune (t : ℝ) (p : IC 3) : IC 3 :=
  triple (clamp ((p 0 : ℝ) +
      t * (1 - (p 0 : ℝ)) * (1 - (1 - (p 1 : ℝ)) * (1 - (p 2 : ℝ)))))
    (p 1) (p 2)

theorem continuous_triple {X : Type*} [TopologicalSpace X] {f g h : X → unitInterval}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    Continuous fun x => triple (f x) (g x) (h x) := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact hf
  · exact hg
  · exact hh

theorem continuous_prune : Continuous fun q : ℝ × IC 3 => prune q.1 q.2 := by
  unfold prune
  refine continuous_triple ?_ ((continuous_apply 1).comp continuous_snd)
    ((continuous_apply 2).comp continuous_snd)
  refine continuous_clamp.comp ?_
  fun_prop

theorem prune_zero {p : IC 3} (h : Tree p) : prune 0 p = p := by
  unfold prune
  rw [show (0:ℝ) * (1 - (p 0 : ℝ)) * (1 - (1 - (p 1 : ℝ)) * (1 - (p 2 : ℝ))) = 0 by ring,
    add_zero]
  have hcl : clamp (p 0 : ℝ) = p 0 := by
    rw [clamp]; exact clamp_of_mem (p 0).2
  rw [hcl]
  exact triple_eta' p

/-! ## The path contraction -/

/-- Fold the spike `c₁ → f` onto `c₁`. -/
def fold1 (t : ℝ) (p : IC 3) : IC 3 :=
  triple (p 0) (clamp ((p 1 : ℝ) + t * (1 - (p 1 : ℝ)) * ((p 0 : ℝ) * (p 2 : ℝ)))) (p 2)

/-- Fold the spike `b → c₁` onto `b`. -/
def fold2 (t : ℝ) (p : IC 3) : IC 3 :=
  triple (p 0) (p 1) (clamp ((p 2 : ℝ) * (1 - t * ((p 0 : ℝ) * (p 1 : ℝ)))))

/-- Fold the spike `a → b` onto `a`. -/
def fold3 (t : ℝ) (p : IC 3) : IC 3 :=
  triple (p 0) (clamp ((p 1 : ℝ) * (1 - t * (p 0 : ℝ)))) (p 2)

/-- Contract the segment `v → a` onto `v`. -/
def fold4 (t : ℝ) (p : IC 3) : IC 3 :=
  triple (clamp ((p 0 : ℝ) * (1 - t))) (p 1) (p 2)

/-- The contraction of the tree to the base vertex. -/
def rho (t : ℝ) (p : IC 3) : IC 3 :=
  if t ≤ 1/5 then prune (5 * t) p
  else if t ≤ 2/5 then fold1 (5 * t - 1) (prune 1 p)
  else if t ≤ 3/5 then fold2 (5 * t - 2) (fold1 1 (prune 1 p))
  else if t ≤ 4/5 then fold3 (5 * t - 3) (fold2 1 (fold1 1 (prune 1 p)))
  else fold4 (5 * t - 4) (fold3 1 (fold2 1 (fold1 1 (prune 1 p))))

end

end Work.Stems.Hur2b
