/-
  WilG4c / ClampDefs — the vocabulary of the "clamp into `(0,1)`" lemma.

  BNZ's §5.2 device: replace a family member `f` by its clamped version
  `clampFun f = if f ∈ (0,1) then f else 1/2`.  The point of `clampFamGraph` is that the graph
  of the clamped member is still `Ω`-bounded, with format and degree increases that are
  *additive* in the degree `D` of the original graph.

  The construction (all of it additive in `D`): put the value of `f` into an extra coordinate
  `s` (a coordinate substitution = pullback of `famGraph f`, costing `D + 2`), intersect with
  the *fixed* (degree-`O(1)`) relation `t = clamp s` between the second-to-last coordinate `t`
  and the last coordinate `s`, and project `s` away.  Since `f`'s graph is used **once**, the
  degree grows by a constant only — this is why the clamp relation has to be built as one set
  rather than as a union of "`f ∈ (0,1)`" and "`f ∉ (0,1)`" pieces (which would cost `2D`).

  This file only fixes the vocabulary; the `Ω`-membership of `clampRel` and the set-theoretic
  identity of the projection are proved in sibling files.
-/
import Mathlib
import Submission.Work.Wilkies.CG.Spec

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign

/-- Clamp a real number into the open unit interval: the identity on `(0,1)`, the constant
`1/2` elsewhere. -/
def clamp01 (t : ℝ) : ℝ := if t ∈ Set.Ioo (0 : ℝ) 1 then t else 1 / 2

@[simp] theorem clamp01_of_mem {t : ℝ} (h : t ∈ Set.Ioo (0 : ℝ) 1) : clamp01 t = t := by
  simp [clamp01, h]

@[simp] theorem clamp01_of_not_mem {t : ℝ} (h : t ∉ Set.Ioo (0 : ℝ) 1) : clamp01 t = 1 / 2 := by
  simp [clamp01, h]

theorem clamp01_mem (t : ℝ) : clamp01 t ∈ Set.Ioo (0 : ℝ) 1 := by
  by_cases h : t ∈ Set.Ioo (0 : ℝ) 1
  · simpa [clamp01, h] using h
  · simp only [clamp01, h, ite_false]
    norm_num

/-- The clamped version of a family member. -/
def clampFun {p m : ℕ} (f : (Fin p → ℝ) → (Fin m → ℝ) → ℝ) :
    (Fin p → ℝ) → (Fin m → ℝ) → ℝ :=
  fun l u => clamp01 (f l u)

@[simp] theorem clampFun_apply {p m : ℕ} (f : (Fin p → ℝ) → (Fin m → ℝ) → ℝ)
    (l : Fin p → ℝ) (u : Fin m → ℝ) : clampFun f l u = clamp01 (f l u) := rfl

/-- The substitution `Fin (N+1) → Fin (N+2)` which skips the second-to-last coordinate
(index `N`, the `t`-slot) and keeps the `N` parameter coordinates together with the last
coordinate (index `N+1`, the `s`-slot carrying the value of `f`). -/
def dropSecondLast (N : ℕ) : Fin (N + 1) → Fin (N + 2) :=
  Fin.snoc (fun j : Fin N => Fin.castSucc (Fin.castSucc j)) (Fin.last (N + 1))

@[simp] theorem dropSecondLast_castSucc {N : ℕ} (j : Fin N) :
    dropSecondLast N (Fin.castSucc j) = Fin.castSucc (Fin.castSucc j) := by
  simp [dropSecondLast]

@[simp] theorem dropSecondLast_last (N : ℕ) :
    dropSecondLast N (Fin.last N) = Fin.last (N + 1) := by
  simp [dropSecondLast]

/-- On a vector `Fin.snoc x s` (coordinates `x` followed by the value `s`), the substitution
`dropSecondLast N` returns the vector `Fin.snoc (Fin.init x) s` — i.e. it deletes the
`t`-coordinate `x (Fin.last N)` and leaves the remaining coordinates in order. -/
theorem dropSecondLast_comp_snoc {N : ℕ} (x : Fin (N + 1) → ℝ) (s : ℝ) :
    Fin.snoc x s ∘ dropSecondLast N = Fin.snoc (Fin.init x) s := by
  funext k
  refine Fin.lastCases ?_ ?_ k
  · simp
  · intro j
    simp [Fin.init]

/-- The clamped-graph relation on `ℝ^{N+2}`: the second-to-last coordinate equals the clamp of
the last coordinate. -/
def clampRel (N : ℕ) : Set (Fin (N + 2) → ℝ) :=
  {z | z (Fin.castSucc (Fin.last N)) = clamp01 (z (Fin.last (N + 1)))}

@[simp] theorem mem_clampRel {N : ℕ} {z : Fin (N + 2) → ℝ} :
    z ∈ clampRel N ↔ z (Fin.castSucc (Fin.last N)) = clamp01 (z (Fin.last (N + 1))) :=
  Iff.rfl

end Work.WilG4c
