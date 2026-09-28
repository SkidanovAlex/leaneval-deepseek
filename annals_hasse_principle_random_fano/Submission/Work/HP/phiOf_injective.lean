import Mathlib
import Submission.Work.HP.GonLib

set_option autoImplicit false

noncomputable section

namespace Work.HP

/-- `phiOf v` is the linear combination map `x ↦ ∑ i, x i • w i`, where `w i` is the
realification of `v i`, transported along the identification `(ι → ℝ) ≃ EuclideanSpace ℝ ι`. -/
theorem phiOf_eq_toLp_linearCombination {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ℕ} (v : Fin R → (ι → ℤ)) (x : Fin R → ℝ) :
    phiOf v x =
      WithLp.toLp 2 (Fintype.linearCombination ℝ (fun i : Fin R => (fun k : ι => ((v i) k : ℝ))) x) := by
  rw [Fintype.linearCombination_apply, ← WithLp.toLp_ofLp (p := 2) (phiOf v x)]
  congr 1
  funext k
  rw [WithLp.ofLp_toLp, phiOf_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Pi.smul_apply, smul_eq_mul, mul_comm]

theorem phiOf_injective {ι : Type*} [Fintype ι] [DecidableEq ι] {R : ℕ}
    (v : Fin R → (ι → ℤ)) (hv : LinearIndependent ℤ v) :
    Function.Injective (phiOf v) := by
  let W : Fin R → (ι → ℝ) := fun i k => ((v i) k : ℝ)
  have hW : LinearIndependent ℝ W := by
    have h := (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℝ) (v := v)).mpr hv
    convert h using 2
    · ext k
      rfl
  have hcomp : Function.Injective
      (fun x : Fin R → ℝ => WithLp.toLp 2 (Fintype.linearCombination ℝ W x)) :=
    (WithLp.toLp_injective 2).comp hW.fintypeLinearCombination_injective
  intro x y hxy
  have h : WithLp.toLp 2 (Fintype.linearCombination ℝ W x) =
      WithLp.toLp 2 (Fintype.linearCombination ℝ W y) := by
    rw [← phiOf_eq_toLp_linearCombination v x, ← phiOf_eq_toLp_linearCombination v y]
    exact hxy
  exact hcomp h

end Work.HP
