import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

theorem shift_diff_ftc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : E → ℝ}
    (hG : ContDiff ℝ 1 G) (y p : E) :
    G (y + p) - G (y - p) = ∫ t in (-1 : ℝ)..1, (fderiv ℝ G (y + t • p)) p := by
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => G (y + s • p)) ((fderiv ℝ G (y + t • p)) p) t := by
    intro t
    have hcurve : HasDerivAt (fun s : ℝ => y + s • p) p t := by
      simpa using ((hasDerivAt_id t).smul_const p).const_add y
    have hl : HasFDerivAt G (fderiv ℝ G (y + t • p)) (y + t • p) :=
      (hG.differentiable_one (y + t • p)).hasFDerivAt
    exact hl.comp_hasDerivAt (f := fun s : ℝ => y + s • p) (x := t) hcurve
  have hcont : Continuous fun t : ℝ => (fderiv ℝ G (y + t • p)) p := by
    have h := hG.continuous_fderiv_apply (𝕜 := ℝ) (n := 1) (by simp)
    have h2 : Continuous fun t : ℝ => (y + t • p, p) :=
      (continuous_const.add (continuous_id.smul continuous_const)).prodMk continuous_const
    exact h.comp h2
  have hint : IntervalIntegrable (fun t : ℝ => (fderiv ℝ G (y + t • p)) p)
      MeasureTheory.volume (-1) 1 :=
    hcont.intervalIntegrable (-1) 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hint]
  simp [sub_eq_add_neg]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
