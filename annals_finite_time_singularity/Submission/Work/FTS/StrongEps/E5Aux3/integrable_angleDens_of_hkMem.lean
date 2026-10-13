import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.FTS.GalBasis.cc.abs_L12_le_HkNorm
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.GalBasis.cc.integral_abs_L12dens_le
import Submission.Work.FTS.StrongEps.E5Aux3.AngSlicePairLe
import Submission.Work.FTS.StrongEps.E5Aux3.WlamSqrtMarginal

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the angular density `K θ · F r θ / r` of an `ℋ⁴_α`-datum

For `F ∈ ℋ⁴_α` (i.e. `Work.Spaces.HkMem α 4 F`), the function
`p ↦ K p.2 · F p.1 p.2 / p.1` is integrable for the product measure on `(0,∞) × Iθ`, with

`∫ ‖K θ · F r θ / r‖ ≤ 3·√(π/2)·√W2 · HkNorm α 4 F`.

**Route.**  On `Iθ` the identity `K θ · F r θ / r = Wlam r · (K θ·Sw θ·Gaz F r θ)` of
`GalBasis.cc` together with `|K·Sw| ≤ 3` and `|Gaz| ≤ √(HkIntegrand)` gives the *pointwise*
bound

`|K θ · F r θ / r| ≤ 3·Wlam r·√(HkIntegrand α 4 F r θ)`   (`r > 0`, `θ ∈ Iθ`),

which, after Cauchy–Schwarz in `θ` (constant `1`, measure `π/2`), upgrades to the *slice*
bound

`∫_θ |K θ · F r θ / r| ≤ 3·√(π/2)·Wlam r·√(H r)`,   `H r := ∫_θ HkIntegrand α 4 F r θ`.

The pointwise form also gives, for a.e. `r`, the integrability of the `θ`-slice of the density
(the majorant `3·Wlam r·√(HkIntegrand)` is integrable since `√x ≤ x + 1` on the finite measure
`Iθ`), and the slice bound gives the integrability of the marginal against the majorant
`3·√(π/2)·(Wlam r·√(H r))` (AM–GM for `Wlam·√H ≤ (Wlam² + H)/2`).  Hence
`MeasureTheory.integrable_prod_iff` applies and the density is integrable on the product.
Tonelli then converts the integral of its norm into the iterated integral, the slice bound
applies a.e., and Cauchy–Schwarz in the radial variable
(`Work.Elliptic.psi_sq_integrable_aux` for `∫Wlam² = W2`, and `∫_{(0,∞)} H = HkSq α 4 F`)
gives the stated constant.

`hslice` (a.e. strong measurability of the slices) is used exactly for the slice integrability,
`hAE` (joint a.e. strong measurability) for `integrable_prod_iff` and for the marginal.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.GalBasis.cc (Wlam W2 Sw Gaz K_mul_h_div_s_eq Wlam_nonneg
  abs_K_mul_Sw_le_three abs_Gaz_le_sqrt_HkIntegrand BK)

namespace Work.FTS.StrongEps.E5Aux3

set_option maxHeartbeats 1000000

/-! ## Elementary angular facts -/

/-- `∫_{Iθ} 1 = π/2`. -/
private lemma integral_one_Iθ : (∫ θ in Work.Spaces.Iθ, (1 : ℝ)) = π / 2 := by
  rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, Work.Spaces.Iθ]
  simp only [Measure.real, Real.volume_Icc, sub_zero]
  exact ENNReal.toReal_ofReal (by positivity)

/-- On the angular interval the square root of the `ℋ⁴`-integrand is integrable: on the
finite-measure set `Iθ` the elementary bound `√x ≤ x + 1` reduces this to the integrability
of `HkIntegrand`. -/
private lemma integrableOn_sqrt_HkIntegrand {α s : ℝ} {F : ℝ → ℝ → ℝ}
    (hint : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 F s θ) Work.Spaces.Iθ) :
    IntegrableOn (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ)) Work.Spaces.Iθ := by
  have hcone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const (C := (1 : ℝ)) (s := Work.Spaces.Iθ)
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hsum := hint.add hcone
  refine Integrable.mono' hsum ?_ ?_
  · exact Real.continuous_sqrt.comp_aestronglyMeasurable hint.aestronglyMeasurable
  · filter_upwards with θ
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Pi.add_apply]
    have hnn : 0 ≤ Work.Spaces.HkIntegrand α 4 F s θ :=
      Work.Spaces.HkIntegrand_nonneg α 4 F s θ
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith⟩

/-! ## The pointwise bound and the slice bound -/

/-- **Pointwise domination of the angular density.**  For `r > 0` and `θ ∈ Iθ`,
`|K θ · F r θ / r| ≤ 3·Wlam r·√(HkIntegrand α 4 F r θ)`. -/
private lemma abs_K_mul_F_div_le_sqrt {α : ℝ} {F : ℝ → ℝ → ℝ} {s θ : ℝ} (hs : 0 < s)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.K θ * F s θ / s|
      ≤ 3 * Wlam s * Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ) := by
  rw [K_mul_h_div_s_eq F hs θ hθ, abs_mul, abs_of_nonneg (Wlam_nonneg hs.le)]
  have h1 : |Work.Spaces.K θ * Sw θ * Gaz F s θ|
      ≤ 3 * Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ) := by
    rw [abs_mul]
    exact mul_le_mul (abs_K_mul_Sw_le_three hθ) (abs_Gaz_le_sqrt_HkIntegrand α F s θ)
      (abs_nonneg _) (by norm_num)
  calc Wlam s * |Work.Spaces.K θ * Sw θ * Gaz F s θ|
      ≤ Wlam s * (3 * Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ)) :=
        mul_le_mul_of_nonneg_left h1 (Wlam_nonneg hs.le)
    _ = 3 * Wlam s * Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ) := by ring

/-- **The slice bound.**  For `r > 0`, the integral over `θ ∈ Iθ` of the absolute value of the
angular density is dominated by `3·√(π/2)·Wlam r·√(H r)`, with `H r := ∫_θ HkIntegrand`. -/
private lemma slice_abs_le {α : ℝ} {F : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 4 F) {s : ℝ}
    (hs : 0 < s) :
    (∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ * F s θ / s|)
      ≤ 3 * Real.sqrt (π / 2) * (Wlam s
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 F s θ)) := by
  have hint : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 F s θ) Work.Spaces.Iθ :=
    hmem.1 s (Set.mem_Ici.mpr hs.le)
  have hsqrt_int : IntegrableOn (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ))
      Work.Spaces.Iθ := integrableOn_sqrt_HkIntegrand hint
  -- the pointwise domination
  have hmaj_int : IntegrableOn
      (fun θ => 3 * Wlam s * Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ)) Work.Spaces.Iθ :=
    hsqrt_int.const_mul _
  have hstep1 : (∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ * F s θ / s|)
      ≤ ∫ θ in Work.Spaces.Iθ,
          3 * Wlam s * Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ) := by
    refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ => abs_nonneg _)
      hmaj_int ?_
    exact (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
      (Eventually.of_forall fun θ hθ => abs_K_mul_F_div_le_sqrt (α := α) hs hθ)
  have hstep2 : (∫ θ in Work.Spaces.Iθ,
        3 * Wlam s * Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ))
      = 3 * Wlam s
        * ∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ) :=
    MeasureTheory.integral_const_mul _ _
  -- Cauchy–Schwarz in `θ` with the constant function `1`
  have hHnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 F s θ :=
    integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 F s θ
  have hcs : (∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ))
      ≤ Real.sqrt (π / 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 F s θ) := by
    have hu : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict Work.Spaces.Iθ) := by
      refine (MeasureTheory.memLp_two_iff_integrable_sq
        (f := fun _ : ℝ => (1 : ℝ)) aestronglyMeasurable_const).mpr ?_
      simpa using (MeasureTheory.integrableOn_const (C := (1 : ℝ)) (s := Work.Spaces.Iθ)
        (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    have hv : MemLp (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ)) 2
        (volume.restrict Work.Spaces.Iθ) := by
      refine (MeasureTheory.memLp_two_iff_integrable_sq
        hsqrt_int.aestronglyMeasurable).mpr ?_
      exact hint.congr (Eventually.of_forall fun θ =>
        (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α 4 F s θ)).symm)
    have h := Work.Spaces.cs_integral hu hv
    simp only [one_mul] at h
    have h1 : (∫ θ in Work.Spaces.Iθ, (1 : ℝ) ^ 2) = π / 2 := by
      simpa using integral_one_Iθ
    have h2 : (∫ θ in Work.Spaces.Iθ,
        Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 F s θ :=
      integral_congr_ae (Eventually.of_forall fun θ =>
        Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α 4 F s θ))
    rw [h1, h2] at h
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ) :=
      integral_nonneg fun θ => Real.sqrt_nonneg _
    have hstep := Real.sqrt_le_sqrt h
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnn,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ π / 2)] at hstep
    exact hstep
  calc (∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ * F s θ / s|)
      ≤ ∫ θ in Work.Spaces.Iθ,
          3 * Wlam s * Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ) := hstep1
    _ = 3 * Wlam s
          * ∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ) := hstep2
    _ ≤ 3 * Wlam s * (Real.sqrt (π / 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 F s θ)) :=
        mul_le_mul_of_nonneg_left hcs (mul_nonneg (by norm_num) (Wlam_nonneg hs.le))
    _ = 3 * Real.sqrt (π / 2) * (Wlam s
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 F s θ)) := by ring

/-- **AM–GM in the radial variable.**  `Wlam·√H` is integrable on `(0,∞)` when `H` is,
because `Wlam·√H ≤ Wlam² + H` and `Wlam²` is integrable (`Work.Elliptic.psi_sq_integrable_aux`). -/
private lemma integrableOn_wlam_sqrt {H : ℝ → ℝ} (hHnn : ∀ s, 0 ≤ H s)
    (hH : IntegrableOn H (Set.Ioi 0)) :
    IntegrableOn (fun s => Wlam s * Real.sqrt (H s)) (Set.Ioi 0) := by
  have hA_aesm : AEStronglyMeasurable (fun s => Real.sqrt (H s))
      (volume.restrict (Set.Ioi 0)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hH.aestronglyMeasurable
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
  have hA2_int : IntegrableOn (fun s => Real.sqrt (H s) ^ 2) (Set.Ioi 0) :=
    hH.congr (Eventually.of_forall fun s => (Real.sq_sqrt (hHnn s)).symm)
  refine (hWlam2_int.add hA2_int).mono' (hWlam_aesm.mul hA_aesm) ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
  have h1 : 0 ≤ Wlam s := Wlam_nonneg hs.le
  have h2 : 0 ≤ Real.sqrt (H s) := Real.sqrt_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 h2), Pi.add_apply]
  nlinarith [sq_nonneg (Wlam s - Real.sqrt (H s))]

/-! ## The theorem -/

theorem integrable_angleDens_of_hkMem {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 4 F)
    (hAE : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * F p.1 p.2 / p.1)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hslice : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.K θ * F r θ / r)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.Integrable
        (fun p : ℝ × ℝ => Work.Spaces.K p.2 * F p.1 p.2 / p.1)
        ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      (∫ p : ℝ × ℝ, ‖Work.Spaces.K p.2 * F p.1 p.2 / p.1‖
        ∂((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        ≤ 3 * Real.sqrt (π / 2) * Real.sqrt Work.FTS.GalBasis.cc.W2
          * Work.Spaces.HkNorm α 4 F := by
  set f : ℝ × ℝ → ℝ := fun p => Work.Spaces.K p.2 * F p.1 p.2 / p.1 with hf
  set H : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 F s θ with hH
  have hHnn : ∀ s, 0 ≤ H s :=
    fun s => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 F s θ
  have hH_int : IntegrableOn H (Set.Ioi 0) := hmem.2.mono_set Set.Ioi_subset_Ici_self
  -- the majorant `3√(π/2)·(Wlam·√H)` is integrable
  have hg_int : Integrable (fun s => 3 * Real.sqrt (π / 2) * (Wlam s * Real.sqrt (H s)))
      (volume.restrict (Set.Ioi 0)) :=
    (integrableOn_wlam_sqrt hHnn hH_int).const_mul (3 * Real.sqrt (π / 2))
  -- the a.e. slice bound
  have hslice_bd : ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)),
      (∫ θ, ‖f (s, θ)‖ ∂(volume.restrict Work.Spaces.Iθ))
        ≤ 3 * Real.sqrt (π / 2) * (Wlam s * Real.sqrt (H s)) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun s hs => ?_
    have h1 : (∫ θ, ‖f (s, θ)‖ ∂(volume.restrict Work.Spaces.Iθ))
        = ∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ * F s θ / s| := by
      refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
      simp only [hf, Real.norm_eq_abs]
    rw [h1]
    exact slice_abs_le hmem hs
  have hslice_bd_norm : ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)),
      ‖∫ θ, ‖f (s, θ)‖ ∂(volume.restrict Work.Spaces.Iθ)‖
        ≤ 3 * Real.sqrt (π / 2) * (Wlam s * Real.sqrt (H s)) :=
    hslice_bd.mono fun s h => by
      rwa [Real.norm_of_nonneg (integral_nonneg fun θ => norm_nonneg _)]
  -- a.e. integrability of the slices
  have hslice_int : ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)),
      Integrable (fun θ => f (s, θ)) (volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [hslice, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs hsI
    have hint : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 F s θ) Work.Spaces.Iθ :=
      hmem.1 s (Set.mem_Ici.mpr hsI.le)
    refine Integrable.mono'
      ((integrableOn_sqrt_HkIntegrand hint).const_mul (3 * Wlam s)) hs ?_
    exact (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
      (Eventually.of_forall fun θ hθ => by
        simpa only [hf, Real.norm_eq_abs] using abs_K_mul_F_div_le_sqrt (α := α) hsI hθ)
  -- integrability of the marginal
  have hmarg_aesm : AEStronglyMeasurable
      (fun s => ∫ θ, ‖f (s, θ)‖ ∂(volume.restrict Work.Spaces.Iθ))
      (volume.restrict (Set.Ioi 0)) := (hAE.norm).integral_prod_right'
  have hmarg_int : Integrable (fun s => ∫ θ, ‖f (s, θ)‖ ∂(volume.restrict Work.Spaces.Iθ))
      (volume.restrict (Set.Ioi 0)) :=
    Integrable.mono' hg_int hmarg_aesm hslice_bd_norm
  -- integrability of the density on the product
  have hInt : Integrable f
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ)) :=
    (MeasureTheory.integrable_prod_iff hAE).mpr ⟨hslice_int, hmarg_int⟩
  refine ⟨hInt, ?_⟩
  -- `∫_{(0,∞)} H = HkSq α 4 F`
  have hHsq : (∫ s in Set.Ioi 0, H s) = Work.Spaces.HkSq α 4 F := by
    rw [MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici' (MeasureTheory.measure_singleton (0 : ℝ)))]
    rfl
  have hsqrtH : Real.sqrt (∫ s in Set.Ioi 0, H s) = Work.Spaces.HkNorm α 4 F := by
    rw [hHsq, Work.Spaces.HkNorm]
  have hconst : (0 : ℝ) ≤ 3 * Real.sqrt (π / 2) := by
    have hp := Real.pi_pos
    positivity
  rw [MeasureTheory.integral_prod (fun p : ℝ × ℝ => ‖f p‖) hInt.norm]
  calc ∫ s, ∫ θ, ‖f (s, θ)‖ ∂(volume.restrict Work.Spaces.Iθ)
        ∂(volume.restrict (Set.Ioi 0))
      ≤ ∫ s, 3 * Real.sqrt (π / 2) * (Wlam s * Real.sqrt (H s))
          ∂(volume.restrict (Set.Ioi 0)) :=
        integral_mono_ae hmarg_int hg_int hslice_bd
    _ = 3 * Real.sqrt (π / 2)
          * ∫ s, Wlam s * Real.sqrt (H s) ∂(volume.restrict (Set.Ioi 0)) := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ 3 * Real.sqrt (π / 2) * (Real.sqrt W2 * Real.sqrt (∫ s in Set.Ioi 0, H s)) :=
        mul_le_mul_of_nonneg_left (WlamSqrtMarginal hHnn hH_int) hconst
    _ = 3 * Real.sqrt (π / 2) * (Real.sqrt W2 * Work.Spaces.HkNorm α 4 F) := by rw [hsqrtH]
    _ = 3 * Real.sqrt (π / 2) * Real.sqrt W2 * Work.Spaces.HkNorm α 4 F := by ring

end Work.FTS.StrongEps.E5Aux3
