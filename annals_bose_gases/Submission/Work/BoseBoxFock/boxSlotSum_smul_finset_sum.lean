import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.frkD4Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open Work.BoseDict

/-! ## `boxSlotSum` is `ℝ`-linear in its one-body operator

`Work.BoseDict.boxSlotSum e T Θ = Σ_j Σ_l Σ_{l'} (T (evec l'))_l • boxSlotOf e (evec l) (evec l') j Θ`
is a finite sum of rank-one slots whose (real) coefficients are the matrix elements
`(T (evec l'))_l` of the one-body operator.  Each matrix element is `ℝ`-linear in `T`, so the slot
sum is -- with **no** hypothesis on `e` or on the state `Θ` (everything is a finite sum).  We record
additivity and `ℝ`-homogeneity in `T`, then the finite-sum form.

The bookkeeping is: unfold the definition and push the application to the point `x` inside the
sums (`Finset.sum_apply`, `Pi.smul_apply`), expand the matrix element of a sum / scalar multiple of
linear maps (`LinearMap.sum_apply` / `LinearMap.smul_apply`, `Finset.sum_apply`, `Pi.smul_apply`),
convert the real scalar action on `ℂ` into multiplication (`Complex.real_smul`, `Complex.ofReal_mul`,
`Complex.ofReal_add`), and finish with the distributivity of the finite sums. -/

private lemma boxSlotSum_add_T {m d : ℕ} {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (T T' : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (Θ : Work.BoseDict.Xn d → ℂ) :
    Work.BoseDict.boxSlotSum e (T + T') Θ
      = Work.BoseDict.boxSlotSum e T Θ + Work.BoseDict.boxSlotSum e T' Θ := by
  funext x
  simp only [Work.BoseDict.boxSlotSum, Finset.sum_apply, LinearMap.add_apply, Pi.add_apply,
    Pi.smul_apply, Complex.real_smul, Complex.ofReal_add, add_mul, Finset.sum_add_distrib]

private lemma boxSlotSum_smul_T {m d : ℕ} {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (a : ℝ) (Θ : Work.BoseDict.Xn d → ℂ) :
    Work.BoseDict.boxSlotSum e (a • T) Θ = a • Work.BoseDict.boxSlotSum e T Θ := by
  funext x
  simp only [Work.BoseDict.boxSlotSum, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply,
    smul_eq_mul, Complex.real_smul, Complex.ofReal_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ =>
    Finset.sum_congr rfl (fun l' _ => ?_)))
  ring

private lemma boxSlotSum_finset_T {m d : ℕ} {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    {κ : Type*} (s : Finset κ) (w : κ → ℝ)
    (A : κ → (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (Θ : Work.BoseDict.Xn d → ℂ) :
    Work.BoseDict.boxSlotSum e (∑ k ∈ s, w k • A k) Θ
      = ∑ k ∈ s, w k • Work.BoseDict.boxSlotSum e (A k) Θ := by
  classical
  induction s using Finset.induction with
  | empty =>
      funext x
      simp only [Finset.sum_empty, Work.BoseDict.boxSlotSum, Finset.sum_apply,
        LinearMap.zero_apply, Pi.zero_apply, zero_smul]
      simp
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [boxSlotSum_add_T, boxSlotSum_smul_T, ih]

theorem boxSlotSum_smul_finset_sum {m d : ℕ} {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    {κ : Type*} (s : Finset κ) (c : ℝ) (A : κ → (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (w : κ → ℝ) (Θ : Work.BoseDict.Xn d → ℂ) :
    Work.BoseDict.boxSlotSum e (c • ∑ k ∈ s, w k • A k) Θ
      = c • ∑ k ∈ s, w k • Work.BoseDict.boxSlotSum e (A k) Θ := by
  rw [boxSlotSum_smul_T, boxSlotSum_finset_T]

end Work.BoseBoxFock
