import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Construction.Defs
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.n5Bound
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The unweighted slice of `D_z^b f` and the `H^k`-integrand

The `i = b` summand of `HkIntegrand` is `(D_z^b f · w / sin(2θ)^{η/2})^2`, and on the *open*
quadrant both the radial weight `w z` and the angular factor `sin(2θ)^{-η/2}` are `≥ 1`, so
this summand dominates `(D_z^b f)^2` there.  This is all that is needed to transport the
`H^k`-membership of `f` to integrability of the plain squared slice. -/

/-- On the open quadrant, the `i = b` summand of `HkIntegrand` dominates `(D_z^b f)^2`. -/
private lemma dzIter_sq_le_HkIntegrand {α : ℝ} {f : ℝ → ℝ → ℝ} {k : ℕ} (b : ℕ) (hb : b ≤ k)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.DzIter b f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k f z θ := by
  have hsinpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsinle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hw1 : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, one_le_div (by positivity : (0 : ℝ) < z ^ 2)]
    nlinarith
  have hW1 : 1 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
    rw [one_le_div (Real.rpow_pos_of_pos hsinpos _)]
    exact le_trans (Real.rpow_le_one hsinpos.le hsinle (by norm_num [Work.Spaces.eta])) hw1
  have hWsq : 1 ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
    nlinarith [hW1]
  have hsq := Work.Spaces.sq_le_HkIntegrand_z α k f z θ b hb
  calc (Work.Spaces.DzIter b f z θ) ^ 2
      = (Work.Spaces.DzIter b f z θ) ^ 2 * 1 := (mul_one _).symm
    _ ≤ (Work.Spaces.DzIter b f z θ) ^ 2
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
        mul_le_mul_of_nonneg_left hWsq (sq_nonneg _)
    _ = (Work.Spaces.DzIter b f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α k f z θ := hsq

/-- The angular moment of the `b`-th radial derivative of `f`, bounded by the angular
`L²`-energy of that derivative (`n5_FK_abs_le` with `g := DzIter b f`).  The hypotheses are
exactly what makes the slice `θ ↦ (DzIter b f z θ)^2` integrable on `Iθ` at `z > 0`:
`SmoothOpen f` for the a.e. strong measurability and `HkMem α k f` with `b ≤ k` for the
domination by the `i = b` summand of `HkIntegrand α k f` (which is `≥ (DzIter b f)^2` because
`w z ≥ 1` and `sin(2θ)^(-η/2) ≥ 1` on the open quadrant). -/
theorem FKdzIter_sq_le {α : ℝ} {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f)
    {k : ℕ} (hmem : Work.Spaces.HkMem α k f) (b : ℕ) (hb : b ≤ k) {z : ℝ} (hz : 0 < z) :
    (Work.Construction.FK (Work.Spaces.DzIter b f) z) ^ 2
      ≤ 16 * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2 := by
  -- a.e. strong measurability of the angular slice of `D_z^b f`
  have haesm : AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.DzIter b f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.DzIter b f p.1 p.2)
      (hF.DzIter b).continuousOn hz
  -- `Iθ` and the open interval have the same measure, the two endpoints being null
  have hcongr : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := Real.pi / 2))).symm
  -- integrability of the squared slice, dominated by the `H^k`-integrand
  have hint : MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.DzIter b f z θ) ^ 2)
      Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono'
      (hmem.1 z (Set.mem_Ici.mpr hz.le)) (haesm.pow 2) ?_
    rw [hcongr]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact dzIter_sq_le_HkIntegrand b hb hz hθ
  -- the `θ`-Cauchy–Schwarz bound for the angular moment
  have hFK := Work.FTS.Nonlinear.Pieces.Rl1.n5_FK_abs_le
    (g := Work.Spaces.DzIter b f) hz hint haesm
  have hP0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2 :=
    MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  calc (Work.Construction.FK (Work.Spaces.DzIter b f) z) ^ 2
      = |Work.Construction.FK (Work.Spaces.DzIter b f) z| ^ 2 := (sq_abs _).symm
    _ ≤ (4 * Real.sqrt (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter b f z θ) ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hFK 2
    _ = 16 * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hP0]
        norm_num

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
