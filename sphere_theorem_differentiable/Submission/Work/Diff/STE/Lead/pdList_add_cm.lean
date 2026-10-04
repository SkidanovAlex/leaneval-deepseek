import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.pdList_mul_sub

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

/-- **Iterated partial derivatives lower the regularity level by the order of derivation.**

If `f` is `C^(j + |L|)` (with `j : ℕ`) then `pdList L f` is `C^j`. -/
lemma pdList_contDiff_le {n j : ℕ} (L : List (Fin n)) {f : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ (((j + L.length : ℕ)) : WithTop ℕ∞) f) :
    ContDiff ℝ ((j : ℕ) : WithTop ℕ∞) (Work.Diff.STE.pdList L f) := by
  induction L generalizing j with
  | nil =>
      simpa [Work.Diff.STE.pdList] using hf
  | cons a L ih =>
      simp only [List.length_cons] at hf
      have hre : (j + 1) + L.length = j + (L.length + 1) := by omega
      rw [← hre] at hf
      have hih := ih (j := j + 1) hf
      rw [Nat.cast_add, Nat.cast_one] at hih
      have hpdc : Work.Diff.STE.pdList (a :: L) f
          = Work.Diff.STE.pd a (Work.Diff.STE.pdList L f) := by
        simp only [Work.Diff.STE.pdList, List.foldr_cons]
      rw [hpdc]
      show ContDiff ℝ ((j : ℕ) : WithTop ℕ∞)
        (fun x : Fin n → ℝ => (fderiv ℝ (Work.Diff.STE.pdList L f) x) (Pi.single a (1 : ℝ)))
      have h1 : ContDiff ℝ ((j : ℕ) : WithTop ℕ∞) (fderiv ℝ (Work.Diff.STE.pdList L f)) :=
        hih.fderiv_right (m := ((j : ℕ) : WithTop ℕ∞)) le_rfl
      exact h1.continuousLinearMap_comp
        (ContinuousLinearMap.apply ℝ ℂ (Pi.single a (1 : ℝ)))

/-- A `C^(M+1)` function has differentiable iterated partial derivatives of order `≤ M`. -/
lemma differentiable_pdList_of_contDiff {n M : ℕ} (L : List (Fin n)) (hL : L.length ≤ M)
    {f : (Fin n → ℝ) → ℂ} (hf : ContDiff ℝ (((M + 1 : ℕ)) : WithTop ℕ∞) f) :
    Differentiable ℝ (Work.Diff.STE.pdList L f) := by
  have hle : (M + 1 - L.length) + L.length = M + 1 := by omega
  rw [← hle] at hf
  have h1 := pdList_contDiff_le (n := n) (j := M + 1 - L.length) L hf
  have hne : (((M + 1 - L.length : ℕ)) : WithTop ℕ∞) ≠ 0 := by
    have hpos : 1 ≤ M + 1 - L.length := by omega
    have hc : ((1 : ℕ) : WithTop ℕ∞) ≤ (((M + 1 - L.length : ℕ)) : WithTop ℕ∞) := by
      exact_mod_cast hpos
    intro h
    rw [h] at hc
    simp at hc
  exact h1.differentiable hne

/-- **Additivity of the iterated partial derivatives of a sum, at a finite regularity level.**

If `f` and `g` are `C^(M+1)` and `L` has length at most `M`, then
`pdList L (f + g) = pdList L f + pdList L g`. -/
theorem pdList_add_cm {n M : ℕ} (L : List (Fin n)) (hL : L.length ≤ M)
    {f g : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ (((M + 1 : ℕ)) : WithTop ℕ∞) f)
    (hg : ContDiff ℝ (((M + 1 : ℕ)) : WithTop ℕ∞) g) :
    Work.Diff.STE.pdList L (f + g) = Work.Diff.STE.pdList L f + Work.Diff.STE.pdList L g := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      have hL' : L.length ≤ M := by
        simp only [List.length_cons] at hL
        omega
      have ih' := ih hL'
      have hpdcong : ∀ h : (Fin n → ℝ) → ℂ,
          Work.Diff.STE.pdList (a :: L) h = Work.Diff.STE.pd a (Work.Diff.STE.pdList L h) := by
        intro h
        simp only [Work.Diff.STE.pdList, List.foldr_cons]
      rw [hpdcong (f + g), ih', hpdcong f, hpdcong g]
      exact Work.Diff.STE.pd_add_fn a (Work.Diff.STE.pdList L f) (Work.Diff.STE.pdList L g)
        (differentiable_pdList_of_contDiff L hL' hf)
        (differentiable_pdList_of_contDiff L hL' hg)

end Work.Diff.STE.Lead
