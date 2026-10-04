import Mathlib
import Submission.Work.Diff.EXT.evolX.ladderAtoms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The base partition of the curvature action

`Work.Diff.EXT.evX.baseGDN`: the index maps `baseK j s`, `baseXi j s` of the `s`-th *base atom* of
the curvature action `Work.Diff.EXT.curvActT` satisfy `GoodDataN` (they are injective, mutually
disjoint and cover the tuple positions).

The three values of `baseXi` are recorded separately (`baseXi_zero`, `baseXi_one`, `baseXi_two`)
because the `![…]` notation of the definition does not reduce by `simp`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Work.Diff.EXT.evolX

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

/-- The three values of `baseXi`, recorded one by one. -/
lemma baseXi_zero (j : ℕ) (s : Fin (j + 4)) : baseXi j s 0 = (0 : Fin (j + 6)) := rfl

lemma baseXi_one (j : ℕ) (s : Fin (j + 4)) : baseXi j s 1 = (1 : Fin (j + 6)) := rfl

lemma baseXi_two (j : ℕ) (s : Fin (j + 4)) :
    baseXi j s 2 = ⟨s.val + 2, by omega⟩ := rfl

/-- The value of `baseK j s` away from the special slot. -/
lemma baseK_val_of_ne {j : ℕ} {s i : Fin (j + 4)} (hi : i ≠ s) :
    (baseK j s i).val = i.val + 2 := by
  simp only [baseK]
  rw [if_neg hi]

/-- The value of `baseXi`, as an explicit case distinction on `r.val`. -/
lemma baseXi_val (j : ℕ) (s : Fin (j + 4)) (r : Fin 3) :
    (baseXi j s r).val
      = if r.val = 0 then 0 else if r.val = 1 then 1 else s.val + 2 := by
  fin_cases r <;> simp [baseXi]

/-- **The base partition.**  `GoodDataN` for the index maps of the curvature action. -/
theorem baseGDN (j : ℕ) (s : Fin (j + 4)) :
    Work.Diff.EXT.evolX.GoodDataN j 0 (j + 6) s (baseK j s) (baseXi j s) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i i' hi hi' h
    have h1 := baseK_val_of_ne (j := j) (s := s) hi
    have h2 := baseK_val_of_ne (j := j) (s := s) hi'
    have h3 : (baseK j s i).val = (baseK j s i').val := by rw [h]
    apply Fin.ext
    omega
  · intro r r' h
    fin_cases r <;> fin_cases r' <;> simp_all [baseXi]
  · intro i r hi h
    have h1 := baseK_val_of_ne (j := j) (s := s) hi
    have hv : (baseK j s i).val = (baseXi j s r).val := congrArg Fin.val h
    rw [h1, baseXi_val] at hv
    have hr : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 := by omega
    rcases hr with h0 | h0 | h0
    · rw [h0] at hv
      simp at hv
      try omega
    · rw [h0] at hv
      simp at hv
      try omega
    · rw [h0] at hv
      simp at hv
      exact hi (Fin.ext (by omega))
  · intro u
    by_cases h0 : u.val = 0
    · refine Or.inr ⟨0, ?_⟩
      rw [baseXi_zero]
      apply Fin.ext
      rw [Fin.val_zero]
      omega
    by_cases h1 : u.val = 1
    · refine Or.inr ⟨1, ?_⟩
      rw [baseXi_one]
      apply Fin.ext
      rw [Fin.val_one]
      omega
    · have h2 : 2 ≤ u.val := by omega
      by_cases hk : u.val - 2 = s.val
      · refine Or.inr ⟨2, ?_⟩
        rw [baseXi_two]
        apply Fin.ext
        rw [Fin.val_mk]
        omega
      · refine Or.inl ⟨⟨u.val - 2, by have := u.isLt; omega⟩, ?_, ?_⟩
        · intro h
          exact hk (congrArg Fin.val h)
        · apply Fin.ext
          rw [show (baseK j s ⟨u.val - 2, by have := u.isLt; omega⟩).val
              = (⟨u.val - 2, by have := u.isLt; omega⟩ : Fin (j + 4)).val + 2 from
            baseK_val_of_ne (j := j) (s := s) (by
              intro h
              exact hk (congrArg Fin.val h))]
          rw [Fin.val_mk]
          omega

end Work.Diff.EXT.evolX
