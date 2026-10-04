import Mathlib
import Submission.Work.Diff.Alg.PA.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The scalar curvature of an algebraic curvature tensor

(`Work.Diff.Alg.PA.scal_basis`, contract `PA`.)

Two elementary facts about `scalAlg R = ∑ᵢⱼ Rᵢⱼᵢⱼ` for an algebraic curvature tensor `R`
(`IsAlgCurv`), in the frame convention of `Submission.Diff.Alg`, where
`secK R u v = R4 R u v u v` and `secK R (stdB n i) (stdB n j) = R i j i j`
(`Work.Diff.Alg.PA.secK_stdB`):

* the diagonal components `Rᵢᵢᵢᵢ` vanish, because `R` is antisymmetric in the first pair; hence
  the scalar curvature is the sum of the *off-diagonal* components `∑ᵢ ∑_{j ≠ i} R i j i j`
  (statement 1);
* if every sectional curvature of `R` is nonnegative, then so is the scalar curvature: each
  off-diagonal component `R i j i j = secK R (eᵢ) (eⱼ)` is the sectional curvature of the
  orthonormal pair `(eᵢ, eⱼ)` of standard basis vectors (`i ≠ j`), and the diagonal components
  vanish (statement 2).
-/

namespace Work.Diff.Alg.PA

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- The diagonal components of an algebraic curvature tensor vanish: antisymmetry in the first
pair gives `R i i i i = - R i i i i`. -/
theorem algCurv_self_eq_zero {R : Curv4 n} (hR : IsAlgCurv R) (i : Fin n) : R i i i i = 0 := by
  have h := hR.1 i i i i
  linarith

/-- **The scalar curvature is the sum of the off-diagonal components.**  For an algebraic
curvature tensor `R`, `scalAlg R = ∑ᵢ ∑_{j ≠ i} R i j i j`. -/
theorem scalAlg_eq_sum_erase {R : Curv4 n} (hR : IsAlgCurv R) :
    scalAlg R = ∑ i, ∑ j ∈ Finset.univ.erase i, R i j i j := by
  have hinner : ∀ i : Fin n, (∑ j ∈ Finset.univ.erase i, R i j i j) = ∑ j, R i j i j := by
    intro i
    have h := Finset.sum_erase_add (Finset.univ : Finset (Fin n)) (fun j => R i j i j)
      (Finset.mem_univ i)
    rw [algCurv_self_eq_zero hR i, add_zero] at h
    exact h
  rw [scalAlg]
  exact Finset.sum_congr rfl (fun i _ => (hinner i).symm)

/-- **Nonnegative sectional curvature implies nonnegative scalar curvature.** -/
theorem scalAlg_nonneg_of_secK_nonneg {R : Curv4 n} (hR : IsAlgCurv R)
    (hsec : ∀ u v : Fin n → ℝ, IsONPair u v → 0 ≤ secK R u v) : 0 ≤ scalAlg R := by
  have hterm : ∀ i j : Fin n, 0 ≤ R i j i j := by
    intro i j
    by_cases h : i = j
    · subst h
      rw [algCurv_self_eq_zero hR i]
    · have h' := hsec (stdB n i) (stdB n j) (isONPair_stdB h)
      rwa [secK_stdB] at h'
  rw [scalAlg]
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hterm i j))

theorem scal_basis (n : ℕ) :
    (∀ R : Curv4 n, IsAlgCurv R → scalAlg R = ∑ i, ∑ j ∈ Finset.univ.erase i, R i j i j) ∧
    (∀ R : Curv4 n, IsAlgCurv R → (∀ u v : Fin n → ℝ, IsONPair u v → 0 ≤ secK R u v) →
      0 ≤ scalAlg R) :=
  ⟨fun _ hR => scalAlg_eq_sum_erase hR, fun _ hR hsec => scalAlg_nonneg_of_secK_nonneg hR hsec⟩

end Work.Diff.Alg.PA
