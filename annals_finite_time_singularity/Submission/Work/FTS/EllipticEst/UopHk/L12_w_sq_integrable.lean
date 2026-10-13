import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.UopHk.L12_contDiffOn_reg
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.EllipticEst.GbarSin.FstarDzIter_chain_open
import Submission.Work.FTS.EllipticEst.HkMem_FstarSin_open
import Submission.Work.Elliptic.L12k0

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.UopHk

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1000000

/-!
# Integrability of `w²·L₁₂(F)²` for a source of the interior class

For `0 < α ≤ 1`, a source `F` which is `C^∞` on the open quadrant
(`Work.FTS.EllipticEst.SmoothOpen F`) and lies in the weighted space `ℋ^k`
(`Work.Spaces.HkMem α k F`, `k ≥ 2`), whose associated singular term vanishes at the origin
(`Work.Elliptic.L12 F 0 = 0`), the function `z ↦ w(z)²·L₁₂(F)(z)²` is integrable on
`Iz = [0,∞)`.

## The route

Write `U := L₁₂(F)` and `f := 3 F_*(F)` (the angular moment, so that
`L₁₂dens F z = f z / z`, `Work.Elliptic.L12dens_eq_three_Fstar_div`).

* `Work.FTS.EllipticEst.integrableOn_Fstar_div_of_smoothOpen_Hk` makes the density
  `L₁₂dens F` integrable on `(0,∞)`; hence `Work.Elliptic.L12_values` gives the decay
  `U → 0` at `+∞` and the continuity of `U` on `[0,1]`, while
  `Work.FTS.EllipticEst.contDiffOn_L12_of_smoothOpen_Hk` gives
  `U' = -f z/z` at every `z > 0`.
* The numerator is controlled by `ℋ^k`-membership: `(f z)² w(z)² ≤ 9·(π/2)·A_0(z)`, where
  `A_0 = AjF F 0` is the `θ = 0` weighted slice of the `ℋ^k`-integrand of `F`
  (`Work.FTS.EllipticEst.FstarDzIter_sq_mul_w_le_open`), and `A_0` is integrable
  (`Work.FTS.EllipticEst.AjF_integrableOn`).
* The two weighted Hardy inequalities `Work.Elliptic.HardyLeftW` (on `(0,1)`, using `U 0 = 0`)
  and `Work.Elliptic.HardyRightW` (on `(1,∞)`, using the decay) then bound `∫ U² w²` on each
  half by the integrable `∫ f² w²`, and the two halves reassemble to `Iz`.
-/

theorem L12_w_sq_integrable {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) (hk : 2 ≤ k)
    (h0 : Work.Elliptic.L12 F 0 = 0) :
    MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * (Work.Elliptic.L12 F z) ^ 2) Work.Spaces.Iz := by
  -- ## the `L₁₂` density is integrable
  have hFstarDiv : MeasureTheory.IntegrableOn
      (fun r : ℝ => Work.Elliptic.Fstar F r / r) (Set.Ioi 0) :=
    integrableOn_Fstar_div_of_smoothOpen_Hk α k F hF hmem
  have hint : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens F) (Set.Ioi 0) :=
    MeasureTheory.IntegrableOn.congr_fun (hFstarDiv.const_mul 3)
      (fun r _ => (Work.Elliptic.L12dens_eq_three_Fstar_div F r).symm) measurableSet_Ioi
  -- ## derivative, decay and continuity of `L₁₂(F)`
  have hderiv : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 F) (-((3 * Work.Elliptic.Fstar F z) / z)) z :=
    fun z hz => (contDiffOn_L12_of_smoothOpen_Hk α k F hF hmem hk).2 z hz
  obtain ⟨-, htend, hcont⟩ := Work.Elliptic.L12_values F hint h0
  -- ## integrability of the numerator `(Qang F 0)² w² = (3 F_*)² w²`
  have hQint : MeasureTheory.IntegrableOn
      (fun z => (3 * Work.Elliptic.Fstar F z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
    have hmaj : MeasureTheory.IntegrableOn
        (fun z => 9 * ((π / 2) * Work.FTS.EllipticEst.AjF F 0 z)) (Set.Ioi 0) :=
      ((Work.FTS.EllipticEst.AjF_integrableOn α k F hF hmem 0 (Nat.zero_le k)).const_mul
        (π / 2)).const_mul 9
    have haesmF : MeasureTheory.AEStronglyMeasurable
        (fun z => Work.Elliptic.Fstar F z) (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
      Work.FTS.EllipticEst.PsiInt_aesm F hF 0
    have hwmeas : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2) := by
      have h1 : Measurable (fun z : ℝ => ((1 + z) ^ 2 : ℝ)) :=
        (measurable_const.add measurable_id).pow_const 2
      have h2 : Measurable (fun z : ℝ => ((z ^ 2)⁻¹ : ℝ)) := (measurable_id.pow_const 2).inv
      have h3 : Measurable (fun z : ℝ => ((1 + z) ^ 2 : ℝ) * (z ^ 2)⁻¹) := h1.mul h2
      have h4 : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
          = (fun z : ℝ => (((1 + z) ^ 2 : ℝ) * (z ^ 2)⁻¹) ^ 2) := by
        funext z
        rw [Work.Spaces.w, div_eq_mul_inv]
      rw [h4]
      exact h3.pow_const 2
    have haesm : MeasureTheory.AEStronglyMeasurable
        (fun z => (3 * Work.Elliptic.Fstar F z) ^ 2 * (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
      have h5 : MeasureTheory.AEStronglyMeasurable
          (fun z => 9 * ((Work.Elliptic.Fstar F z) ^ 2 * (Work.Spaces.w z) ^ 2))
          (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
        ((haesmF.pow 2).mul hwmeas.aestronglyMeasurable).const_mul 9
      refine h5.congr ?_
      filter_upwards with z
      ring
    have hle : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        ‖(3 * Work.Elliptic.Fstar F z) ^ 2 * (Work.Spaces.w z) ^ 2‖
          ≤ 9 * ((π / 2) * Work.FTS.EllipticEst.AjF F 0 z) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      have hkey := Work.FTS.EllipticEst.FstarDzIter_sq_mul_w_le_open α k F hF hmem 0
        (Nat.zero_le k) hz
      have hAj : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 0 F z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
          = Work.FTS.EllipticEst.AjF F 0 z := rfl
      rw [hAj] at hkey
      simp only [Work.Spaces.DzIter_zero] at hkey
      rw [Real.norm_of_nonneg (by positivity)]
      have hn := Work.FTS.EllipticEst.AjF_nonneg F 0 z
      nlinarith [hkey, hn]
    have hmain : MeasureTheory.IntegrableOn
        (fun z => (3 * Work.Elliptic.Fstar F z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0) :=
      MeasureTheory.Integrable.mono' hmaj haesm hle
    have hae : Work.Spaces.Iz =ᵐ[MeasureTheory.volume] Set.Ioi 0 := by
      simpa only [Work.Spaces.Iz] using (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ))).symm
    exact (MeasureTheory.integrableOn_congr_set_ae hae).mpr hmain
  -- ## the two weighted Hardy inequalities
  have hderiv01 : ∀ z ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun z => Work.Elliptic.L12 F z)
      (-((3 * Work.Elliptic.Fstar F z) / z)) z :=
    fun z hz => hderiv z (Set.mem_Ioi.mpr hz.1)
  have hderiv1 : ∀ z ∈ Set.Ioi (1 : ℝ), HasDerivAt (fun z => Work.Elliptic.L12 F z)
      (-((3 * Work.Elliptic.Fstar F z) / z)) z := by
    intro z hz
    exact hderiv z (Set.mem_Ioi.mpr (lt_trans one_pos (Set.mem_Ioi.mp hz)))
  have hQIoo : MeasureTheory.IntegrableOn
      (fun z => (3 * Work.Elliptic.Fstar F z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioo 0 1) :=
    hQint.mono_set (fun z hz => Set.mem_Ici.mpr (le_of_lt hz.1))
  have hQIoi : MeasureTheory.IntegrableOn
      (fun z => (3 * Work.Elliptic.Fstar F z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 1) :=
    hQint.mono_set (fun z hz => Set.mem_Ici.mpr (le_of_lt (lt_trans one_pos hz)))
  obtain ⟨hIntL, -⟩ := Work.Elliptic.HardyLeftW (fun z => 3 * Work.Elliptic.Fstar F z)
    (fun z => Work.Elliptic.L12 F z) hderiv01 hcont h0 hQIoo
  obtain ⟨hIntR, -⟩ := Work.Elliptic.HardyRightW (fun z => 3 * Work.Elliptic.Fstar F z)
    (fun z => Work.Elliptic.L12 F z) hderiv1 htend hQIoi
  have hae2 := Work.Elliptic.Ioo_union_Ioi_ae_eq_Iz
  have hIntIz : MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.L12 F z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    (MeasureTheory.integrableOn_congr_set_ae hae2).mp (hIntL.union hIntR)
  exact MeasureTheory.IntegrableOn.congr_fun hIntIz (fun z _ => by ring)
    (by simpa only [Work.Spaces.Iz] using measurableSet_Ici)

end Work.FTS.EllipticEst.UopHk
