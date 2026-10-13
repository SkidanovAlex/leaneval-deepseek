import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.GalBasis.cc.Defs
import Submission.Work.FTS.GalBasis.cc.abs_L12_le_HkNorm
import Submission.Work.FTS.LocData.L12_add_mul
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Elementary angular bounds

`Sw θ = sin(2θ)^{η/2}` is bounded by `1` on the angular interval (its base `sin(2θ)` lies in
`[0,1]` and the exponent is nonnegative), so `|K · Sw| ≤ 3` there. -/

theorem Sw_le_one_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : Sw θ ≤ 1 := by
  have h0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have h1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h2 : (0 : ℝ) ≤ Work.Spaces.eta / 2 := by norm_num [Work.Spaces.eta]
  have hle := Real.rpow_le_rpow h0 h1 h2
  rwa [Real.one_rpow] at hle

/-- On the angular interval, `|K(θ)·Sw θ| ≤ 3`. -/
theorem abs_K_mul_Sw_le_three {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.K θ * Sw θ| ≤ 3 := by
  rw [abs_mul, abs_of_nonneg (K_nonneg_of_mem_Iθ hθ), abs_of_nonneg (Sw_nonneg_of_mem_Iθ hθ)]
  calc Work.Spaces.K θ * Sw θ ≤ 3 * 1 :=
        mul_le_mul (K_le_three_of_mem_Iθ hθ) (Sw_le_one_of_mem_Iθ hθ)
          (Sw_nonneg_of_mem_Iθ hθ) (by norm_num)
    _ = 3 := by norm_num

/-- The elementary bound `√x ≤ (1+x)/2` for `x ≥ 0` (AM–GM). -/
theorem sqrt_le_half_one_add {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ (1 + x) / 2 := by
  rw [Real.sqrt_le_iff]
  refine ⟨by linarith, ?_⟩
  nlinarith [sq_nonneg (1 - x)]

/-! ## A.e. strong measurability on a closed interval from continuity on the open one -/

/-- A function continuous on the open interval `(a,b)` is a.e. strongly measurable for
`volume.restrict (Icc a b)`: the two intervals differ by the two null endpoints. -/
theorem aesm_Icc_of_continuousOn_Ioo {a b : ℝ} {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioo a b)) :
    AEStronglyMeasurable g (volume.restrict (Set.Icc a b)) := by
  have h1 : AEStronglyMeasurable g (volume.restrict (Set.Ioo a b)) :=
    hg.aestronglyMeasurable measurableSet_Ioo
  have hset : (Set.Ioo a b) =ᵐ[volume] (Set.Icc a b) := MeasureTheory.Ioo_ae_eq_Icc
  have hmeas : volume.restrict (Set.Icc a b) = volume.restrict (Set.Ioo a b) :=
    (MeasureTheory.Measure.restrict_congr_set hset).symm
  rw [hmeas]
  exact h1

/-! ## The angular slice of the `L₁₂`-integrand is integrable

For `s > 0` the identity `K θ · F s θ / s = Wlam s · (K θ · Sw θ · Gaz F s θ)` converts the
slice of the density into the pairing of the angular profile `K·Sw` against the weighted datum
`Gaz F s = F s · w s / Sw`, which is dominated by `√(HkIntegrand α 4 F s ·)` on the angular
interval.  Since `|K·Sw| ≤ 3` there, the slice is dominated by the integrable function
`Wlam s · (3/2)·(1 + HkIntegrand α 4 F s ·)`. -/

/-- The pointwise domination on the angular interval. -/
theorem abs_K_mul_F_div_s_le {α s : ℝ} {F : ℝ → ℝ → ℝ} (hs : 0 < s) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.K θ * F s θ / s|
      ≤ Wlam s * (3 * (1 + Work.Spaces.HkIntegrand α 4 F s θ) / 2) := by
  have hx : 0 ≤ Work.Spaces.HkIntegrand α 4 F s θ := Work.Spaces.HkIntegrand_nonneg α 4 F s θ
  have hb : |Work.Spaces.K θ * Sw θ * Gaz F s θ|
      ≤ 3 * Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ) := by
    rw [abs_mul]
    exact mul_le_mul (abs_K_mul_Sw_le_three hθ) (abs_Gaz_le_sqrt_HkIntegrand α F s θ)
      (abs_nonneg _) (by norm_num)
  have h3 : 3 * Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ)
      ≤ 3 * (1 + Work.Spaces.HkIntegrand α 4 F s θ) / 2 := by
    have h := sqrt_le_half_one_add hx
    linarith
  rw [K_mul_h_div_s_eq F hs θ hθ, abs_mul, abs_of_nonneg (Wlam_nonneg hs.le)]
  exact mul_le_mul_of_nonneg_left (le_trans hb h3) (Wlam_nonneg hs.le)

/-- **The angular slice of the `L₁₂`-integrand is integrable**, for every `s > 0`, from
`s ∈ ℋ⁴_α` alone (with `SmoothOpen F` only for the a.e. strong measurability of the slice). -/
theorem integrableOn_slice_of_SmoothOpen_HkMem {α s : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α 4 F) (hs : 0 < s) :
    IntegrableOn (fun θ => Work.Spaces.K θ * F s θ / s) Work.Spaces.Iθ := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hcontK : Continuous Work.Spaces.K := by
    change Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
    fun_prop
  have hslice : ContinuousOn (fun θ => F s θ) (Set.Ioo 0 (π / 2)) :=
    (hF.curry_θ hs).continuousOn
  have haesm : AEStronglyMeasurable (fun θ => Work.Spaces.K θ * F s θ / s)
      (volume.restrict Work.Spaces.Iθ) :=
    aesm_Icc_of_continuousOn_Ioo ((hcontK.continuousOn.mul hslice).div_const s)
  have hHk : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 F s θ) Work.Spaces.Iθ :=
    hmem.1 s hs.le
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    continuous_const.integrableOn_Icc
  have hdom : IntegrableOn
      (fun θ => Wlam s * (3 * (1 + Work.Spaces.HkIntegrand α 4 F s θ) / 2)) Work.Spaces.Iθ := by
    have h1 : IntegrableOn
        (fun θ => (Wlam s * (3 / 2)) * (1 + Work.Spaces.HkIntegrand α 4 F s θ)) Work.Spaces.Iθ :=
      (hconst.add hHk).const_mul _
    refine h1.congr_fun (fun θ _ => ?_) hIθ
    ring
  refine hdom.mono' haesm ?_
  rw [ae_restrict_iff' hIθ]
  exact Eventually.of_forall fun θ hθ => by
    rw [Real.norm_eq_abs]
    exact abs_K_mul_F_div_s_le (α := α) hs hθ

/-! ## The `L₁₂`-density is integrable

The density is the parametric integral `s ↦ ∫_θ K θ · F s θ / s`, so its a.e. strong
measurability comes from the joint continuity of the integrand on the open quadrant
(`Work.Spaces.aesm_of_continuousOn_Qd` + Fubini measurability of the partial integral), and
its integrability from the pointwise bound `cc.abs_L12dens_le` together with AM–GM against the
two square-integrable factors `Wlam` and `s ↦ √(∫_θ HkIntegrand α 4 F s θ)`. -/

/-- A.e. strong measurability of the `L₁₂`-density on `(0,∞)` for data smooth on the open
quadrant. -/
theorem aesm_L12dens_of_SmoothOpen {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    AEStronglyMeasurable (Work.Construction.L12dens F) (volume.restrict (Set.Ioi 0)) := by
  have hcontK : Continuous Work.Spaces.K := by
    change Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
    fun_prop
  have hFc : ContinuousOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hF.continuousOn
  have hK : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := (hcontK.comp continuous_snd).continuousOn
  have hdiv : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2 * F p.1 p.2 / p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (hK.mul hFc).div continuousOn_fst (fun p hp => ne_of_gt (Set.mem_prod.mp hp).1)
  have hjoint := Work.Spaces.aesm_of_continuousOn_Qd
    (fun p : ℝ × ℝ => Work.Spaces.K p.2 * F p.1 p.2 / p.1) hdiv
  have h := hjoint.integral_prod_right' (μ := volume.restrict Work.Spaces.Iz)
  have h3 : AEStronglyMeasurable (Work.Construction.L12dens F) (volume.restrict Work.Spaces.Iz) := by
    convert h using 1
    funext z
    rfl
  have hset : Set.Ioi (0 : ℝ) =ᵐ[volume] Work.Spaces.Iz := MeasureTheory.Ioi_ae_eq_Ici
  rw [MeasureTheory.Measure.restrict_congr_set hset]
  exact h3

/-- **The `L₁₂`-density of an `ℋ⁴`-datum is integrable on `(0,∞)`.** -/
theorem integrableOn_L12dens_of_SmoothOpen_HkMem {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α 4 F) :
    IntegrableOn (Work.Construction.L12dens F) (Set.Ioi 0) := by
  set H : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 F s θ with hH
  set A : ℝ → ℝ := fun s => Real.sqrt (H s) with hA
  have hHnn : ∀ s, 0 ≤ H s :=
    fun s => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 F s θ
  have hH_int : IntegrableOn H (Set.Ioi 0) :=
    hmem.2.mono_set Set.Ioi_subset_Ici_self
  have hA_aesm : AEStronglyMeasurable A (volume.restrict (Set.Ioi 0)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hH_int.aestronglyMeasurable
  have hA2_int : IntegrableOn (fun s => A s ^ 2) (Set.Ioi 0) :=
    hH_int.congr (Eventually.of_forall fun s => (Real.sq_sqrt (hHnn s)).symm)
  have hWlam_aesm : AEStronglyMeasurable Wlam (volume.restrict (Set.Ioi 0)) := by
    have hc : ContinuousOn (fun s : ℝ => s / (1 + s) ^ 2) (Set.Ioi 0) := by
      refine ContinuousOn.div continuousOn_id ?_ ?_
      · exact (continuousOn_const.add continuousOn_id).pow 2
      · intro s hs
        have h1 : (0 : ℝ) < 1 + s := by linarith [Set.mem_Ioi.mp hs]
        exact pow_ne_zero 2 (ne_of_gt h1)
    exact (show ContinuousOn Wlam (Set.Ioi 0) from hc).aestronglyMeasurable measurableSet_Ioi
  have hWlam2_int : IntegrableOn (fun s => Wlam s ^ 2) (Set.Ioi 0) := by
    simpa only [Wlam] using Work.Elliptic.psi_sq_integrable_aux
  have hWlamA_int : IntegrableOn (fun s => Wlam s * A s) (Set.Ioi 0) := by
    refine (hWlam2_int.add hA2_int).mono' (hWlam_aesm.mul hA_aesm) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    have h1 : 0 ≤ Wlam s := Wlam_nonneg hs.le
    have h2 : 0 ≤ A s := Real.sqrt_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 h2), Pi.add_apply]
    nlinarith [sq_nonneg (Wlam s - A s)]
  have hbd : ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)),
      ‖Work.Construction.L12dens F s‖ ≤ BK * (Wlam s * A s) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun s hs => ?_
    have hb := abs_L12dens_le α F hmem hs
    rw [Real.norm_eq_abs]
    calc |Work.Construction.L12dens F s| ≤ Wlam s * (BK * A s) := by
          simpa only [hA, hH] using hb
      _ = BK * (Wlam s * A s) := by ring
  exact (hWlamA_int.const_mul BK).mono' (aesm_L12dens_of_SmoothOpen hF) hbd

/-! ## The theorem -/

/-- Route.  Instantiate `Work.FTS.LocData.L12_add_mul` (with `c = 0`, `z = 0`) and derive its
four integrability inputs from `HkMem`:

* the θ-slice `θ ↦ K θ · h s θ / s` is `Wlam s • (θ ↦ K θ · Sw θ · Gaz h s θ)` and
  `|K θ Sw θ Gaz h s θ| ≤ |K θ Sw θ| · sqrt (HkIntegrand α 4 h s θ)`
  (`Work.FTS.GalBasis.cc.abs_Gaz_le_sqrt_HkIntegrand`), so Cauchy–Schwarz in θ with
  `K·Sw ∈ L²(Iθ)` (it is continuous) and `HkIntegrand α 4 h s · ∈ L¹(Iθ)` (`HkMem.1`) gives both
  the bound of `cc.abs_integral_K_S_Gaz_le` and the `L¹`-property of the slice;
* the density bound is `cc.abs_L12dens_le`, and its majorant `Wlam s · BK · sqrt(∫_θ HkIntegrand)`
  is `L¹((0,∞))` because `Wlam ∈ L²((0,∞))` and `s ↦ ∫_θ HkIntegrand α 4 h s θ ∈ L¹(Iz)`
  (`HkMem.2`), so `cc.integral_abs_L12dens_le` gives the density integrability (and also the
  `AEStronglyMeasurable` needed for `IntegrableOn`: the slices are continuous on the open
  quadrant, and the boundary lines are null).

`SmoothOpen` is used exactly for that a.e. strong measurability of the slices/densities. -/
theorem L12_add_of_HkMem {α : ℝ} {a b : Work.FTS.Galerkin.Fn}
    (hsa : Work.FTS.EllipticEst.SmoothOpen a) (hsb : Work.FTS.EllipticEst.SmoothOpen b)
    (hma : Work.Spaces.HkMem α 4 a) (hmb : Work.Spaces.HkMem α 4 b) :
    Work.Construction.L12 (fun z θ => a z θ + b z θ) 0
      = Work.Construction.L12 a 0 + Work.Construction.L12 b 0 :=
  (Work.FTS.LocData.L12_add_mul (c := 0) (z := 0)
    (fun s hs => integrableOn_slice_of_SmoothOpen_HkMem hsa hma hs)
    (fun s hs => integrableOn_slice_of_SmoothOpen_HkMem hsb hmb hs)
    (integrableOn_L12dens_of_SmoothOpen_HkMem hsa hma)
    (integrableOn_L12dens_of_SmoothOpen_HkMem hsb hmb)).1

end Work.FTS.GalBasis.cc
