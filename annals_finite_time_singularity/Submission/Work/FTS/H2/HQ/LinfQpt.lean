import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.LinfQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.Spaces

namespace Work.FTS.H2.HQ

/-- **Elgindi's Corollary `SecondDerivativesBounded` (tex 1094) in the interior class `RegQ`,
pointwise form.**

For `f` in the interior class `Work.FTS.Nonlin.RegQ α 4` (`= SmoothQuad f ∧ HkMem α 4 f ∧
BdryTraces α 4 f`) and `a + b ≤ 2`, every mixed derivative of order `≤ 2` is bounded on the
*open* quadrant by `C/√(γ-1)·|f|_{ℋ⁴}`, `C` universal.  The bound is claimed only inside the
quadrant: `RegQ` leaves the values on the lines `θ = 0`, `θ = π/2` (and at `z = 0`) free.

The second and third arguments are the interior one-dimensional Hardy inequalities
(`Work.FTS.H2.HQ.HardyThetaQ` — angular, with the `θ → 0⁺` limit of the function as its
vanishing hypothesis — and `Work.FTS.H2.HQ.HardyZQ` — radial, `C¹` on `(0,∞)` with decay at
`∞`), taken as hypotheses so that this statement is independent of them; they are instantiated
from those two files at the point of use.  Everything else the proof needs is in
`Submission/Work/FTS/H2/HQ/Glue.lean`.

Route (as in `Work.Spaces.SupMixedLeH4`/`Linf_H2`, but with the boundary behaviour supplied by
`BdryTraces` instead of `SmoothNbhd`/`VanishTheta`): for `z > 0` and `0 < θ < π/2`,
* apply the angular Hardy inequality to the `θ`-slice `σ ↦ mixed b a f z σ`: its limit at
  `0⁺` is `0` by `Work.FTS.H2.HQ.BdryTraces.tendsto_theta_zero` (the angular clause of
  `BdryTraces` carries the *singular* weight `sin(2θ)^{1-γ}`, hence forces the vanishing), and
  the Hardy integrand `(pth (mixed b a f) z σ)² sin(2σ)^{2-γ}` is integrable because it equals
  `(mixed b (a+1) f z σ · Wt(z,σ))²/w(z)²` on the open quadrant
  (`Work.FTS.H2.HQ.Wt_sq_quad`, the `D_θ`-commutation of `D_z^b` from
  `Work.FTS.LocData.DzDthIterCommOn`/`Work.FTS.H2.HQ.DthIter_mul_quad`, and the slot
  integrability `Work.FTS.H2.HQ.integrableOn_slice_mixed_Wt_sq`);
* apply the radial Hardy inequality to the `z`-slice of `pth (mixed b a f)` (equivalently to
  `mixed b (a+1) f · Wt`), whose decay at `z → ∞` is
  `Work.FTS.H2.HQ.BdryTraces.tendsto_atTop_zero`;
* conclude `(mixed b a f z θ)² ≤ C/(γ-1)·∫∫ (mixed (b+1) (a+1) f · Wt)²` (an `ℋ⁴`-slot,
  `≤ HkSq α 4 f` by `Work.Spaces.L2Sq_mixed_le_HkSq`/`slotM_quad`), using
  `sin(2θ)·sin(2θ)^{-γ} = sin(2θ)^{1-γ}`-type weight algebra and `(b+1)+(a+1) ≤ 4`.
The case `a = 0` is the same chain with the `D_θ`-derivative taken first and the slots
`(b+1, 1)` (for `b ≤ 2`, total order `≤ 4`). -/
theorem LinfQpt : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : Work.FTS.Galerkin.Fn) (b a : ℕ),
    0 < α → α ≤ 1 → a + b ≤ 2 → Work.FTS.Nonlin.RegQ α 4 f →
    (∀ (u : ℝ → ℝ → ℝ) (z : ℝ), Work.FTS.LocData.SmoothQuad u → z ∈ Set.Ioi (-1) →
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      MeasureTheory.IntegrableOn (fun σ => (Work.Spaces.pth u z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ →
      ∀ θ ∈ Set.Ioo 0 (π / 2), (u z θ) ^ 2 ≤
        (100 / (Work.Spaces.gam α - 1)) * MeasureTheory.integral
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)
          (fun σ => (Work.Spaces.pth u z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))) →
    (∀ (v : ℝ → ℝ), ContDiffOn ℝ 1 v (Set.Ioi (0 : ℝ)) →
      Filter.Tendsto v Filter.atTop (nhds 0) →
      MeasureTheory.IntegrableOn (fun s => (s * deriv v s) ^ 2 * (Work.Spaces.w s) ^ 2)
        Work.Spaces.Iz →
      ∀ z ∈ Set.Ioi (0 : ℝ), (v z) ^ 2 ≤ MeasureTheory.integral
        (MeasureTheory.volume.restrict Work.Spaces.Iz)
        (fun s => (s * deriv v s) ^ 2 * (Work.Spaces.w s) ^ 2)) →
    ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a f z θ| ≤ C / Real.sqrt (Work.Spaces.gam α - 1)
        * Work.FTS.Nonlin.Xn α f := by
  refine ⟨10, by norm_num, ?_⟩
  intro α f b a hα hα1 hab hreg hAng hRad z hz θ hθ0 hθ1
  obtain ⟨hsq, hmem, hbd⟩ := hreg
  have hγ1 : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hγne : gam α ≠ 0 := ne_of_gt (gam_pos hα)
  -- the `θ`-first slot of the `ℋ⁴`-norm at order `(b+1, a+1)`
  obtain ⟨hTle, hTint, hTae⟩ :=
    Work.FTS.H2.slotM_quad α f hsq hmem (b + 1) (a + 1) (by omega) (by omega)
  have hptslot : ∀ σ ∈ Iθ, ∀ z : ℝ, (mixed (b + 1) (a + 1) f z σ * Wt α z σ) ^ 2
      = (Real.sin (2 * σ)) ^ (-(gam α))
        * ((mixed (b + 1) (a + 1) f z σ) ^ 2 * (w z) ^ 2) := by
    intro σ hσ z
    rw [show Wt α z σ = w z * (Real.sin (2 * σ)) ^ (-(gam α / 2)) from rfl, mul_pow,
      Work.FTS.H2.Wt_sq α hα z σ hσ]
    ring
  set B : ℝ → ℝ := fun σ => ∫ z in Iz, (mixed (b + 1) (a + 1) f z σ) ^ 2 * (w z) ^ 2
    with hBdef
  have hBae : (fun σ => (Real.sin (2 * σ)) ^ (-(gam α)) * B σ)
      =ᵐ[volume.restrict Iθ]
      fun σ => ∫ z in Iz, (mixed (b + 1) (a + 1) f z σ * Wt α z σ) ^ 2 := by
    filter_upwards [hTae, ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)]
      with σ _hσint hσI
    rw [hBdef]
    have hstep : (Real.sin (2 * σ)) ^ (-(gam α))
          * (∫ z in Iz, (mixed (b + 1) (a + 1) f z σ) ^ 2 * (w z) ^ 2)
        = ∫ z in Iz, (mixed (b + 1) (a + 1) f z σ * Wt α z σ) ^ 2 := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ici fun z _ => (hptslot σ hσI z).symm
    exact hstep
  have hTint' : Integrable (fun σ => (Real.sin (2 * σ)) ^ (-(gam α)) * B σ)
      (volume.restrict Iθ) := hTint.congr hBae.symm
  set T : ℝ := ∫ σ in Iθ, (Real.sin (2 * σ)) ^ (-(gam α)) * B σ with hTdef
  have hTle' : T ≤ HkSq α 4 f := by
    rw [hTdef]
    rw [show (∫ σ in Iθ, (Real.sin (2 * σ)) ^ (-(gam α)) * B σ)
        = ∫ σ in Iθ, ∫ z in Iz, (mixed (b + 1) (a + 1) f z σ * Wt α z σ) ^ 2
        from integral_congr_ae hBae]
    exact hTle
  have hKnn : 0 ≤ 100 / (gam α - 1) := div_nonneg (by norm_num) hγ1.le
  -- the boundary limit at `θ → 0⁺`, from the angular clause of `BdryTraces`
  have hlim0 : Tendsto (fun θ' => mixed b a f z θ') (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    BdryTraces.tendsto_theta_zero hα hbd (by omega) hz
  -- integrability of the angular Hardy integrand, from the mixed slot
  have hDth_int := Work.FTS.H2.integrableOn_Dth_mixed_slice α f hsq hmem b a (by omega) hz
  have hDth_int2 : IntegrableOn
      (fun σ => (Real.sin (2 * σ)) ^ (-(gam α)) * (Dth (mixed b a f) z σ) ^ 2) Iθ :=
    hDth_int.congr_fun (fun σ _ => by ring) measurableSet_Icc
  have hint_ang : IntegrableOn
      (fun σ => (pth (mixed b a f) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) Iθ :=
    hDth_int2.congr_fun (fun σ hσ => by
      calc (Real.sin (2 * σ)) ^ (-(gam α)) * (Dth (mixed b a f) z σ) ^ 2
          = (Dth (mixed b a f) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(gam α)) := by ring
        _ = (pth (mixed b a f) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α) :=
            (Work.FTS.H2.pth_sq_mul_sin_eq α hα hα1 (mixed b a f) z σ hσ).symm)
      measurableSet_Icc
  -- the angular Hardy inequality (hypothesis)
  have hHT := hAng (mixed b a f) z (hsq.mixed b a) (Set.mem_Ioi.mpr (by linarith)) hlim0
    hint_ang θ ⟨hθ0, hθ1⟩
  have hI1 : (∫ σ in Iθ, (pth (mixed b a f) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α))
      = ∫ σ in Iθ, (Real.sin (2 * σ)) ^ (-(gam α)) * (Dth (mixed b a f) z σ) ^ 2 := by
    refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
    rw [Work.FTS.H2.pth_sq_mul_sin_eq α hα hα1 (mixed b a f) z σ hσ]
    ring
  -- the radial Hardy inequality (hypothesis) on almost every `θ`-slice
  have hrad : ∀ᵐ σ ∂(volume.restrict Iθ),
      (Real.sin (2 * σ)) ^ (-(gam α)) * (Dth (mixed b a f) z σ) ^ 2
        ≤ (Real.sin (2 * σ)) ^ (-(gam α)) * B σ := by
    filter_upwards [hTae, ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)]
      with σ hσint hσI
    rcases eq_or_lt_of_le hσI.1 with hσeq | hσpos
    · have hsin0 : Real.sin (2 * σ) = 0 := by rw [← hσeq]; simp
      have hz0 : (Real.sin (2 * σ)) ^ (-(gam α)) = 0 := by
        rw [hsin0]; exact Real.zero_rpow (neg_ne_zero.mpr hγne)
      simp [hz0]
    rcases eq_or_lt_of_le hσI.2 with hσeq | hσlt
    · have hsin0 : Real.sin (2 * σ) = 0 := by
        rw [hσeq, show 2 * (π / 2) = π by ring, Real.sin_pi]
      have hz0 : (Real.sin (2 * σ)) ^ (-(gam α)) = 0 := by
        rw [hsin0]; exact Real.zero_rpow (neg_ne_zero.mpr hγne)
      simp [hz0]
    · have hσ' : σ ∈ Set.Ioo 0 (π / 2) := ⟨hσpos, hσlt⟩
      rw [Work.FTS.H2.Dth_mixed_quad hsq b a hz hσ']
      refine mul_le_mul_of_nonneg_left ?_
        (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg hσI) _)
      have hcd : ContDiffOn ℝ 1 (fun s => mixed b (a + 1) f s σ) (Set.Ioi (0 : ℝ)) :=
        ((hsq.mixed b (a + 1)).curry_z hσ').of_le (by simp [Work.Stability.smoothOrder])
          |>.mono (Set.Ioi_subset_Ioi (by norm_num))
      have hdec : Tendsto (fun s => mixed b (a + 1) f s σ) atTop (nhds 0) :=
        BdryTraces.tendsto_atTop_zero hbd (by omega) hσ'
      exact hRad (fun s => mixed b (a + 1) f s σ) hcd hdec hσint z (Set.mem_Ioi.mpr hz)
  have hIntLe : (∫ σ in Iθ, (pth (mixed b a f) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α))
      ≤ T := by
    rw [hI1, hTdef]
    exact integral_mono_ae hDth_int2 hTint' hrad
  have hfin : (mixed b a f z θ) ^ 2 ≤ (100 / (gam α - 1)) * T :=
    le_trans hHT (mul_le_mul_of_nonneg_left hIntLe hKnn)
  have hsqrt : Real.sqrt (100 / (gam α - 1)) = 10 / Real.sqrt (gam α - 1) := by
    have h2 : (0 : ℝ) ≤ 10 / Real.sqrt (gam α - 1) :=
      div_nonneg (by norm_num) (Real.sqrt_nonneg _)
    rw [← Real.sqrt_sq h2]
    congr 1
    rw [div_pow, Real.sq_sqrt hγ1.le]
    norm_num
  have hfinal : Real.sqrt ((100 / (gam α - 1)) * HkSq α 4 f)
      = 10 / Real.sqrt (gam α - 1) * HkNorm α 4 f := by
    rw [Real.sqrt_mul hKnn, hsqrt]
    simp only [HkNorm]
  calc |mixed b a f z θ| = Real.sqrt ((mixed b a f z θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((100 / (gam α - 1)) * T) := Real.sqrt_le_sqrt hfin
    _ ≤ Real.sqrt ((100 / (gam α - 1)) * HkSq α 4 f) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hTle' hKnn)
    _ = 10 / Real.sqrt (gam α - 1) * HkNorm α 4 f := hfinal
    _ = 10 / Real.sqrt (gam α - 1) * Work.FTS.Nonlin.Xn α f := rfl

end Work.FTS.H2.HQ
