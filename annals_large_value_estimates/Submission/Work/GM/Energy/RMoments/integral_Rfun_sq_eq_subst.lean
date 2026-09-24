import Mathlib
import Submission.Work.GM.Energy.Defs

/-!
# Change of variables `v = exp u` for the second moment of `R`

`Rfun W v = Σ_{t ∈ W} |v|^{it}`, so `v ↦ ‖Rfun W v‖²` is continuous on `(0, ∞)` and

`∫_0^{log 2} exp u * ‖Rfun W (exp u)‖² du = ∫_1^2 ‖Rfun W v‖² dv`

by the substitution `v = exp u` (`du = dv / v`).
-/

namespace Work.GM.Energy.RMoments

open Complex Finset
open scoped BigOperators

/-- `v ↦ ‖Rfun W v‖²` is continuous on the positive reals. -/
private lemma continuousOn_norm_Rfun_sq (W : Finset ℝ) :
    ContinuousOn (fun v : ℝ => ‖Submission.GM.Rfun W v‖ ^ 2) (Set.Ioi 0) := by
  have hbase : ContinuousOn (fun v : ℝ => ((|v| : ℝ) : ℂ)) (Set.Ioi 0) :=
    (Complex.continuous_ofReal.comp continuous_abs).continuousOn
  have hR : ContinuousOn (fun v : ℝ => Submission.GM.Rfun W v) (Set.Ioi 0) := by
    simp only [Submission.GM.Rfun]
    refine continuousOn_finsetSum W (fun t _ => ?_)
    exact hbase.cpow_const (fun a ha => by
      rw [Complex.mem_slitPlane_iff]
      exact Or.inl (by rw [Complex.ofReal_re, abs_of_pos ha]; exact ha))
  exact (hR.norm).pow 2

theorem integral_Rfun_sq_eq_subst (W : Finset ℝ) :
    (∫ u in (0 : ℝ)..Real.log 2, Real.exp u * ‖Submission.GM.Rfun W (Real.exp u)‖ ^ 2)
      = ∫ v in (1 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 2 := by
  have hcont := continuousOn_norm_Rfun_sq W
  have himg : Real.exp '' Set.uIcc (0 : ℝ) (Real.log 2) ⊆ Set.Ioi 0 := by
    rintro y ⟨x, _, rfl⟩; exact Real.exp_pos x
  have h := intervalIntegral.integral_comp_mul_deriv'
      (f := Real.exp) (f' := Real.exp) (g := fun v : ℝ => ‖Submission.GM.Rfun W v‖ ^ 2)
      (a := (0 : ℝ)) (b := Real.log 2)
      (fun x _ => Real.hasDerivAt_exp x) Real.continuous_exp.continuousOn (hcont.mono himg)
  rw [Real.exp_zero, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [Function.comp_apply]
  ring

end Work.GM.Energy.RMoments
