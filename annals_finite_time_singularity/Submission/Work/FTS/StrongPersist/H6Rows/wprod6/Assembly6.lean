/-
# `WProd6/Assembly6` — the measure-theoretic assembly of the `𝒲^{6,∞}`-priced product rule

The level-six shift of `Work.FTS.OpenPkg.wprod_field_winf`: from the pointwise majorant
(`prod_majorant_winf6`) and the three slot lemmas (the pure `D_z`-slots, the mean-term bound for
the radial `g`-slots, and the mixed slots) build the `ℋ⁶`-membership of `f·g` and the
`α^{-1/2}`-priced bound

`|f·g|_{ℋ⁶} ≤ C α^{-1/2} |f|_{𝒲^{6,∞}} |g|_{ℋ⁶}`.

The three slot lemmas are taken as hypotheses here so that the assembly can be checked
independently; `Submission/Work/FTS/StrongPersist/H6Rows/wprod6.lean` instantiates them.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Majorant6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Gmaj6
import Submission.Work.FTS.VocabO
import Submission.Work.Spaces.aesm_HkIntegrand_quad
import Submission.Work.Spaces.ProductRuleInW

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.WProd6

open Work.Spaces
open Work.FTS.EllipticEst (SmoothOpen)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- `√(x⁻¹) = x^(-1/2)` for `x > 0`. -/
theorem sqrt_inv_eq_rpow_neg_half6 {x : ℝ} (hx : 0 < x) :
    Real.sqrt x⁻¹ = x ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul hx.le]
  congr 1
  ring

/-- **The measure-theoretic assembly of the `𝒲^{6,∞}`-priced product rule**, from the three
slot lemmas. -/
theorem wprod6_of_slots
    (hZ : ∃ Cz : ℝ, 0 < Cz ∧
      ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
        Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 6 f →
        Work.FTS.EllipticEst.SmoothOpen g →
        ∀ i : ℕ, i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ Cz * (Work.Spaces.WlInf α 6 f) ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ)
    (hMe : ∃ CB : ℝ, 0 < CB ∧
      ∀ (α : ℝ) (g : ℝ → ℝ → ℝ) (d : ℕ), 0 < α → α ≤ 1 →
        Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g → d ≤ 5 →
        ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
          ≤ CB * ((Work.Spaces.w z) ^ 2
                * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
              + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z))
    (hMx : ∀ CB : ℝ, ∃ Cm : ℝ, 0 < Cm ∧
      ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
        Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 6 f →
        Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
        (∀ d : ℕ, d ≤ 5 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
            ≤ CB * ((Work.Spaces.w z) ^ 2
                  * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
                + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z)) →
        ∀ I J : ℕ, 1 ≤ I → I + J ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ Cm * (Work.Spaces.WlInf α 6 f) ^ 2
              * GmajW6 α g z θ) :
    ∃ Ci α₂ : ℝ, 0 < Ci ∧ 0 < α₂ ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Work.FTS.Galerkin.Fn,
        Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 6 f →
        Work.FTS.VocabO.HQo α 6 g →
        Work.Spaces.HkMem α 6 (fun z θ => f z θ * g z θ) ∧
        Work.Spaces.HkNorm α 6 (fun z θ => f z θ * g z θ)
          ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 6 f
              * Work.Spaces.HkNorm α 6 g := by
  obtain ⟨Cz, hCz0, hzslot⟩ := hZ
  obtain ⟨CB, hCB0, hCmean⟩ := hMe
  obtain ⟨Cm, hCm0, hmslot⟩ := hMx CB
  refine ⟨Real.sqrt (42701 * (7 * Cz + 49 * Cm)) + 1, 1, by positivity, by norm_num, ?_⟩
  intro α hαIoc f g hf hfm hg
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  obtain ⟨hgsm, hgm⟩ := hg
  set K : ℝ := 7 * Cz + 49 * Cm with hKdef
  set Kg : ℝ := 1 + 700 * (1 + 6 * (gam α - 1)⁻¹) with hKgdef
  have hKpos : 0 < K := by rw [hKdef]; linarith
  have hKgpos : 0 < Kg := by
    rw [hKgdef]
    have h1 : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
    have h2 : 0 ≤ (gam α - 1)⁻¹ := inv_nonneg.mpr h1.le
    linarith
  have hWnn : 0 ≤ WlInf α 6 f := WlInf_nonneg α 6 f hfm
  have hfgsm : SmoothOpen (fun z θ => f z θ * g z θ) := hf.mul hgsm
  -- the pointwise majorant, with the two slot lemmas instantiated
  have hmajor : ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ
        ≤ K * (WlInf α 6 f) ^ 2 * GmajW6 α g z θ := by
    have h := prod_majorant_winf6 hα hα1 hf hfm hgsm hgm hCz0 hCm0
      (fun i hi z θ hz hθ1 hθ2 => hzslot α f g hα hα1 hf hfm hgsm i hi z θ hz hθ1 hθ2)
      (fun I J hI hIJ z θ hz hθ1 hθ2 =>
        hmslot α f g hα hα1 hf hfm hgsm hgm
          (fun d hd z' θ' hz' hθ1' hθ2' => hCmean α g d hα hα1 hgsm hgm hd z' θ' hz' hθ1' hθ2')
          I J hI hIJ z θ hz hθ1 hθ2)
    intro z hz θ hθ
    rw [hKdef]
    exact h z hz θ hθ
  -- integrability of the angular slices of the product's integrand
  have hslice : ∀ z ∈ Iz, IntegrableOn (fun θ => HkIntegrand α 6
      (fun z θ => f z θ * g z θ) z θ) Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hzz | hzpos
    · have hz0 : z = 0 := hzz.symm
      subst hz0
      have hzero : (fun θ => HkIntegrand α 6 (fun z θ => f z θ * g z θ) 0 θ)
          = fun _ : ℝ => (0 : ℝ) :=
        funext fun θ => HkIntegrand_zero_z α 6 _ θ
      rw [hzero]
      exact integrableOn_zero
    · refine Integrable.mono'
        ((GmajW6_integrableOn_theta hα hα1 hgm hz).const_mul (K
          * (WlInf α 6 f) ^ 2)) ?_ ?_
      · exact aesm_slice_of_continuousOn_Qd _
          (hfgsm.continuousOn_HkIntegrand α 6) hzpos
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
        rw [Real.norm_of_nonneg (HkIntegrand_nonneg α 6 _ z θ)]
        exact hmajor z hz θ hθ
  -- the angular integral of the majorant at every radius
  have hinner : ∀ z ∈ Iz,
      (∫ θ in Iθ, HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
        ≤ K * (WlInf α 6 f) ^ 2 * (Kg * HgInt6 α g z) := by
    intro z hz
    have hint : IntegrableOn (fun θ => (K * (WlInf α 6 f) ^ 2)
        * GmajW6 α g z θ) Iθ :=
      (GmajW6_integrableOn_theta hα hα1 hgm hz).const_mul _
    have h1 : (∫ θ in Iθ, HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
        ≤ ∫ θ in Iθ, (K * (WlInf α 6 f) ^ 2) * GmajW6 α g z θ :=
      integral_mono_of_nonneg
        (Eventually.of_forall fun θ => HkIntegrand_nonneg α 6 _ z θ) hint
        (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hmajor z hz θ hθ))
    rw [MeasureTheory.integral_const_mul] at h1
    have h2 : (∫ θ in Iθ, GmajW6 α g z θ) ≤ Kg * HgInt6 α g z := by
      simpa only [hKgdef] using GmajW6_theta_integral_le (α := α) (g := g) hα hα1 hgm hz
    calc (∫ θ in Iθ, HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
        ≤ (K * (WlInf α 6 f) ^ 2) * (∫ θ in Iθ, GmajW6 α g z θ) := h1
      _ ≤ (K * (WlInf α 6 f) ^ 2) * (Kg * HgInt6 α g z) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hKpos.le (sq_nonneg _))
  -- the dominating function of the `z`-integral
  have hbdd : ∀ z ∈ Iz,
      (∫ θ in Iθ, HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
        ≤ (K * (WlInf α 6 f) ^ 2 * Kg) * HgInt6 α g z := by
    intro z hz
    have h1 := hinner z hz
    calc (∫ θ in Iθ, HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
        ≤ K * (WlInf α 6 f) ^ 2 * (Kg * HgInt6 α g z) := h1
      _ = (K * (WlInf α 6 f) ^ 2 * Kg) * HgInt6 α g z := by ring
  have hdom : IntegrableOn (fun z => (K * (WlInf α 6 f) ^ 2 * Kg)
      * HgInt6 α g z) Iz :=
    hgm.2.const_mul (K * (WlInf α 6 f) ^ 2 * Kg)
  -- a.e. strong measurability of the `z`-slice integral
  have haesm : AEStronglyMeasurable (fun z => ∫ θ in Iθ,
      HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
      (volume.restrict Iz) := by
    have h := (aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => HkIntegrand α 6 (fun z θ => f z θ * g z θ) p.1 p.2)
      (hfgsm.continuousOn_HkIntegrand α 6)).integral_prod_right'
    have hfun : (fun z => ∫ θ, HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ
          ∂(volume.restrict Iθ))
        = (fun z => ∫ θ in Iθ,
            HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ) := rfl
    rw [← hfun]
    exact h
  have hzg : IntegrableOn (fun z => ∫ θ in Iθ,
      HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ) Iz := by
    refine Integrable.mono' hdom haesm ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ =>
      HkIntegrand_nonneg α 6 _ z θ)]
    exact hbdd z hz
  refine ⟨⟨hslice, hzg⟩, ?_⟩
  have hSq : HkSq α 6 (fun z θ => f z θ * g z θ)
      ≤ (K * (WlInf α 6 f) ^ 2 * Kg) * HkSq α 6 g := by
    have h1 : HkSq α 6 (fun z θ => f z θ * g z θ)
        ≤ ∫ z in Iz, (K * (WlInf α 6 f) ^ 2 * Kg) * HgInt6 α g z := by
      rw [HkSq]
      exact setIntegral_mono_of_nonneg
        (fun z _ => integral_nonneg fun θ => HkIntegrand_nonneg α 6 _ z θ)
        (fun z hz => hbdd z hz) hdom
    refine le_trans h1 ?_
    rw [MeasureTheory.integral_const_mul, HgInt6_z_integral]
  -- the passage to the `ℋ⁶`-norm
  have hXn : HkNorm α 6 (fun z θ => f z θ * g z θ)
      ≤ Real.sqrt (K * Kg) * WlInf α 6 f * HkNorm α 6 g := by
    have h1 : HkNorm α 6 (fun z θ => f z θ * g z θ)
        ≤ Real.sqrt ((K * Kg) * (WlInf α 6 f) ^ 2 * HkSq α 6 g) := by
      rw [show HkNorm α 6 (fun z θ => f z θ * g z θ)
            = Real.sqrt (HkSq α 6 (fun z θ => f z θ * g z θ)) from rfl]
      refine Real.sqrt_le_sqrt ?_
      calc HkSq α 6 (fun z θ => f z θ * g z θ)
          ≤ (K * (WlInf α 6 f) ^ 2 * Kg) * HkSq α 6 g := hSq
        _ = (K * Kg) * (WlInf α 6 f) ^ 2 * HkSq α 6 g := by ring
    refine le_trans h1 (le_of_eq ?_)
    rw [show HkNorm α 6 g = Real.sqrt (HkSq α 6 g) from rfl,
      Real.sqrt_mul (show (0 : ℝ) ≤ (K * Kg) * (WlInf α 6 f) ^ 2 by positivity),
      Real.sqrt_mul (show (0 : ℝ) ≤ K * Kg by positivity),
      Real.sqrt_sq hWnn]
  refine le_trans hXn ?_
  -- `√(K Kg) ≤ √(42701 K) α^{-1/2}`
  have hKg_le : Kg ≤ 42701 * α⁻¹ := by
    have h1 : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
    have hginv : (gam α - 1)⁻¹ = 10 / α := by
      rw [gam_sub_one, inv_div]
    have hαinv : (1 : ℝ) ≤ α⁻¹ := by rw [one_le_inv₀ hα]; exact hα1
    rw [hKgdef, hginv, div_eq_mul_inv]
    ring_nf
    nlinarith [hαinv]
  have hsqrt : Real.sqrt (K * Kg) ≤ Real.sqrt (42701 * K) * α ^ (-(1 / 2 : ℝ)) := by
    have h1 : K * Kg ≤ 42701 * K * α⁻¹ := by
      calc K * Kg ≤ K * (42701 * α⁻¹) := mul_le_mul_of_nonneg_left hKg_le hKpos.le
        _ = 42701 * K * α⁻¹ := by ring
    refine le_trans (Real.sqrt_le_sqrt h1) ?_
    rw [show (42701 : ℝ) * K * α⁻¹ = (42701 * K) * α⁻¹ from by ring,
      Real.sqrt_mul (show (0 : ℝ) ≤ 42701 * K by positivity),
      sqrt_inv_eq_rpow_neg_half6 hα]
  have hmain : Real.sqrt (K * Kg) * WlInf α 6 f * HkNorm α 6 g
      ≤ Real.sqrt (42701 * K) * α ^ (-(1 / 2 : ℝ)) * WlInf α 6 f
        * HkNorm α 6 g := by
    calc Real.sqrt (K * Kg) * WlInf α 6 f * HkNorm α 6 g
        = Real.sqrt (K * Kg) * (WlInf α 6 f * HkNorm α 6 g) := by ring
      _ ≤ (Real.sqrt (42701 * K) * α ^ (-(1 / 2 : ℝ)))
            * (WlInf α 6 f * HkNorm α 6 g) :=
          mul_le_mul_of_nonneg_right hsqrt (mul_nonneg hWnn (Real.sqrt_nonneg _))
      _ = Real.sqrt (42701 * K) * α ^ (-(1 / 2 : ℝ)) * WlInf α 6 f
            * HkNorm α 6 g := by ring
  calc Real.sqrt (K * Kg) * WlInf α 6 f * HkNorm α 6 g
      ≤ Real.sqrt (42701 * K) * α ^ (-(1 / 2 : ℝ)) * WlInf α 6 f
          * HkNorm α 6 g := hmain
    _ = Real.sqrt (42701 * (7 * Cz + 49 * Cm)) * α ^ (-(1 / 2 : ℝ))
          * WlInf α 6 f * HkNorm α 6 g := by rw [hKdef]
    _ ≤ (Real.sqrt (42701 * (7 * Cz + 49 * Cm)) + 1) * α ^ (-(1 / 2 : ℝ))
          * WlInf α 6 f * HkNorm α 6 g := by
        have h1 : (0 : ℝ) ≤ Real.sqrt (42701 * (7 * Cz + 49 * Cm)) := Real.sqrt_nonneg _
        have h2 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
        have h3 : (0 : ℝ) ≤ WlInf α 6 f := hWnn
        have h4 : (0 : ℝ) ≤ HkNorm α 6 g := Real.sqrt_nonneg _
        nlinarith [mul_nonneg (mul_nonneg h2 h3) h4,
          mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4]

end Work.FTS.StrongPersist.H6Rows.WProd6
