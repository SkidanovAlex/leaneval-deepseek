import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.H5.LevelShift
import Submission.Work.FTS.StrongEps.H5.WProd5.Gmaj5
import Submission.Work.FTS.StrongEps.H5.WProd5.zslot_le_winf5
import Submission.Work.FTS.StrongEps.H5.WProd5.dzIter_w_mean_le5
import Submission.Work.FTS.StrongEps.H5.WProd5.mslot_le_winf5
import Submission.Work.FTS.StrongEps.H5.WProd5.prod_majorant_winf5
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

namespace Work.FTS.StrongEps.H5

open Work.Spaces
open Work.FTS.EllipticEst (SmoothOpen)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- `√(x⁻¹) = x^(-1/2)` for `x > 0`. -/
theorem sqrt_inv_eq_rpow_neg_half5 {x : ℝ} (hx : 0 < x) :
    Real.sqrt x⁻¹ = x ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul hx.le]
  congr 1
  ring

/-- **The level-`5` `𝒲^{5,∞}`-priced product rule** — the literal level-`5` analogue of the
proved `Work.FTS.OpenPkg.wprod_field_winf` (the same statement with `4 → 5` and `Xn → HkNorm α 5`).

*Statement.*  There is a universal `C > 0` such that for every `α ∈ (0,1]`, every `f` smooth on
the open quadrant with `WlInfMem α 5 f` and every `g` of class `HQo α 5`,

`HkMem α 5 (f·g) ∧ HkNorm α 5 (f·g) ≤ C α^{-1/2} |f|_{𝒲^{5,∞}} |g|_{ℋ⁵}`.

*Why the pointwise version against `HkIntegrand α 5 g` is FALSE and the integrated statement is the
right one.*  If all the `θ`-derivatives of a mixed product slot `mixed j i (f·g)` sit on `f`, the
`g`-side carries the weight `Wt = w sin(2θ)^{-γ/2}` (`γ = 1 + α/10`) whereas the matching `g`-slot
of `HkIntegrand α 5 g` is a *pure* slot with weight `w sin(2θ)^{-η/2}` (`η = 99/100`), and
`sin^{-γ/2} > sin^{-η/2}`: the residual `sin(2θ)^{3α/10 - 1/100}` blows up for `α < 1/30`.  This is
exactly why the level-4 proof compares against the *majorant* `WProdWin.GmajW` (with its
`(γ-1)^{-1}` mean-term block and the angular factor `TW = (α+sin2θ)²sin(2θ)^{2α/5-γ}`) and then
*integrates* in `θ`.

*Route.*  Re-run `Submission/Work/FTS/OpenPkg/wprod_field_winf.lean` and
`Submission/Work/FTS/OpenPkg/WProdWin/` (`zslot_le_winf`, `dzIter_w_mean_le`, `mslot_le_winf`,
`Basic`) with `4 → 5`: the pure `D_z`-slots of `f·g` up to order `5` and the mixed slots with
`i + j ≤ 5`, using `WlInf α 5 f` and `HkIntegrand α 5 g`.  Note `WProdWin/dzIter_w_mean_le` is
*not* reusable verbatim (it is stated for `d ≤ 3` with `HkMem α 4 g`; at level `5` one needs
`d ≤ 4` and `HkMem α 5 g`, the same `sob_theta_mean` argument).  `WlInf_z_bound` /
`WlInf_mixed_bound` (`Spaces/WlInf_terms.lean`) give the slot bounds of `f` (note
`|DzIter b f| ≤ (Σ_k |scoef b k|) · WlInf α 5 f` from `Spaces.DzIter_eq_sum_scoef` and
`z^k ≤ (1+z)^k`), `ProdOpen.leibniz_open_Dz` / `leibniz_open_mixed` the Leibniz expansions, and
`Nonlinear.N4Fields.HkSq_le_of_integrand_le` + `LocData.HkMem_of_majorant` (continuity from
`Cert.smoothOpen_mul_bsl`) the integration and the membership.

*Consumer.*  The star coefficients `((z+1)/z)ℛ(Φ̃_*)`, `((z+1)/z)U(Φ̃_*)/sin 2θ`,
`((z+1)/z)V(Φ̃_*)` carry `𝒲^{6,∞}`-bounds (`StrongPersist.StarPkg6`), whence
`WlInf α 5 R_s ≤ WlInf α 6 R_s ≤ Cs·α`; with this rule the pieces of `N α (F_tot+…)` that carry a
star coefficient are priced at level `5` **without any derivative data of `f`**, which is what
makes the level-`5` `N`-block provable. -/
theorem wprod_field_winf5 :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f g : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 5 f →
      Work.FTS.VocabO.HQo α 5 g →
      Work.Spaces.HkMem α 5 (fun z θ => f z θ * g z θ) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => f z θ * g z θ)
        ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 5 f * Work.Spaces.HkNorm α 5 g := by
  obtain ⟨Cz, hCz0, hzslot⟩ := WProd5.zslot_le_winf5
  obtain ⟨CB, _hCB0, hCmean⟩ := WProd5.dzIter_w_mean_le5
  obtain ⟨Cm, hCm0, hmslot⟩ := WProd5.mslot_le_winf5 CB
  refine ⟨Real.sqrt (35701 * (6 * Cz + 36 * Cm)) + 1, by positivity, ?_⟩
  intro α hα hα1 f g hf hfm hg
  obtain ⟨hgsm, hgm⟩ := hg
  set K : ℝ := 6 * Cz + 36 * Cm with hKdef
  set Kg : ℝ := 1 + 700 * (1 + 5 * (gam α - 1)⁻¹) with hKgdef
  have hKpos : 0 < K := by rw [hKdef]; linarith
  have hKgpos : 0 < Kg := by
    rw [hKgdef]
    have h1 : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
    have h2 : 0 ≤ (gam α - 1)⁻¹ := inv_nonneg.mpr h1.le
    linarith
  have hWnn : 0 ≤ WlInf α 5 f := WlInf_nonneg α 5 f hfm
  have hfgsm : SmoothOpen (fun z θ => f z θ * g z θ) := hf.mul hgsm
  -- the pointwise majorant, with the two slot lemmas instantiated
  have hmajor : ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      HkIntegrand α 5 (fun z θ => f z θ * g z θ) z θ
        ≤ K * (WlInf α 5 f) ^ 2 * WProd5.GmajW5 α g z θ := by
    have h := WProd5.prod_majorant_winf5 hα hα1 hf hfm hgsm hgm hCz0 hCm0
      (fun i hi z θ hz hθ1 hθ2 => hzslot α f g hα hα1 hf hfm hgsm i hi z θ hz hθ1 hθ2)
      (fun I J hI hIJ z θ hz hθ1 hθ2 =>
        hmslot α f g hα hα1 hf hfm hgsm hgm
          (fun d hd z' θ' hz' hθ1' hθ2' =>
            hCmean α g d hα hα1 hgsm hgm hd z' θ' hz' hθ1' hθ2')
          I J hI hIJ z θ hz hθ1 hθ2)
    intro z hz θ hθ
    rw [hKdef]
    exact h z hz θ hθ
  -- integrability of the angular slices of the product's integrand
  have hslice : ∀ z ∈ Iz, IntegrableOn (fun θ => HkIntegrand α 5
      (fun z θ => f z θ * g z θ) z θ) Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hzz | hzpos
    · have hz0 : z = 0 := hzz.symm
      subst hz0
      have hzero : (fun θ => HkIntegrand α 5 (fun z θ => f z θ * g z θ) 0 θ)
          = fun _ : ℝ => (0 : ℝ) :=
        funext fun θ => HkIntegrand_zero_z α 5 _ θ
      rw [hzero]
      exact integrableOn_zero
    · refine Integrable.mono'
        ((WProd5.GmajW5_integrableOn_theta hα hα1 hgm hz).const_mul (K
          * (WlInf α 5 f) ^ 2)) ?_ ?_
      · exact aesm_slice_of_continuousOn_Qd _
          (hfgsm.continuousOn_HkIntegrand α 5) hzpos
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
        rw [Real.norm_of_nonneg (HkIntegrand_nonneg α 5 _ z θ)]
        exact hmajor z hz θ hθ
  -- the angular integral of the majorant at every radius
  have hinner : ∀ z ∈ Iz,
      (∫ θ in Iθ, HkIntegrand α 5 (fun z θ => f z θ * g z θ) z θ)
        ≤ K * (WlInf α 5 f) ^ 2 * (Kg * WProd5.HgInt5 α g z) := by
    intro z hz
    have hint : IntegrableOn (fun θ => (K * (WlInf α 5 f) ^ 2)
        * WProd5.GmajW5 α g z θ) Iθ :=
      (WProd5.GmajW5_integrableOn_theta hα hα1 hgm hz).const_mul _
    have h1 : (∫ θ in Iθ, HkIntegrand α 5 (fun z θ => f z θ * g z θ) z θ)
        ≤ ∫ θ in Iθ, (K * (WlInf α 5 f) ^ 2) * WProd5.GmajW5 α g z θ :=
      integral_mono_of_nonneg
        (Eventually.of_forall fun θ => HkIntegrand_nonneg α 5 _ z θ) hint
        (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hmajor z hz θ hθ))
    rw [MeasureTheory.integral_const_mul] at h1
    have h2 : (∫ θ in Iθ, WProd5.GmajW5 α g z θ) ≤ Kg * WProd5.HgInt5 α g z := by
      simpa only [hKgdef] using WProd5.GmajW5_theta_integral_le (α := α) (g := g) hα hα1 hgm hz
    calc (∫ θ in Iθ, HkIntegrand α 5 (fun z θ => f z θ * g z θ) z θ)
        ≤ (K * (WlInf α 5 f) ^ 2) * (∫ θ in Iθ, WProd5.GmajW5 α g z θ) := h1
      _ ≤ (K * (WlInf α 5 f) ^ 2) * (Kg * WProd5.HgInt5 α g z) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hKpos.le (sq_nonneg _))
  -- the dominating function of the `z`-integral
  have hbdd : ∀ z ∈ Iz,
      (∫ θ in Iθ, HkIntegrand α 5 (fun z θ => f z θ * g z θ) z θ)
        ≤ (K * (WlInf α 5 f) ^ 2 * Kg) * WProd5.HgInt5 α g z := by
    intro z hz
    have h1 := hinner z hz
    calc (∫ θ in Iθ, HkIntegrand α 5 (fun z θ => f z θ * g z θ) z θ)
        ≤ K * (WlInf α 5 f) ^ 2 * (Kg * WProd5.HgInt5 α g z) := h1
      _ = (K * (WlInf α 5 f) ^ 2 * Kg) * WProd5.HgInt5 α g z := by ring
  have hdom : IntegrableOn (fun z => (K * (WlInf α 5 f) ^ 2 * Kg)
      * WProd5.HgInt5 α g z) Iz :=
    hgm.2.const_mul (K * (WlInf α 5 f) ^ 2 * Kg)
  -- a.e. strong measurability of the `z`-slice integral
  have haesm : AEStronglyMeasurable (fun z => ∫ θ in Iθ,
      HkIntegrand α 5 (fun z θ => f z θ * g z θ) z θ)
      (volume.restrict Iz) := by
    have h := (aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => HkIntegrand α 5 (fun z θ => f z θ * g z θ) p.1 p.2)
      (hfgsm.continuousOn_HkIntegrand α 5)).integral_prod_right'
    have hfun : (fun z => ∫ θ, HkIntegrand α 5 (fun z θ => f z θ * g z θ) z θ
          ∂(volume.restrict Iθ))
        = (fun z => ∫ θ in Iθ,
            HkIntegrand α 5 (fun z θ => f z θ * g z θ) z θ) := rfl
    rw [← hfun]
    exact h
  have hzg : IntegrableOn (fun z => ∫ θ in Iθ,
      HkIntegrand α 5 (fun z θ => f z θ * g z θ) z θ) Iz := by
    refine Integrable.mono' hdom haesm ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ =>
      HkIntegrand_nonneg α 5 _ z θ)]
    exact hbdd z hz
  refine ⟨⟨hslice, hzg⟩, ?_⟩
  have hSq : HkSq α 5 (fun z θ => f z θ * g z θ)
      ≤ (K * (WlInf α 5 f) ^ 2 * Kg) * HkSq α 5 g := by
    have h1 : HkSq α 5 (fun z θ => f z θ * g z θ)
        ≤ ∫ z in Iz, (K * (WlInf α 5 f) ^ 2 * Kg) * WProd5.HgInt5 α g z := by
      rw [HkSq]
      exact setIntegral_mono_of_nonneg
        (fun z _ => integral_nonneg fun θ => HkIntegrand_nonneg α 5 _ z θ)
        (fun z hz => hbdd z hz) hdom
    refine le_trans h1 ?_
    rw [MeasureTheory.integral_const_mul, WProd5.HgInt5_z_integral]
  -- the passage to the `ℋ⁵`-norm
  have hXn : HkNorm α 5 (fun z θ => f z θ * g z θ)
      ≤ Real.sqrt (K * Kg) * WlInf α 5 f * HkNorm α 5 g := by
    have h1 : HkNorm α 5 (fun z θ => f z θ * g z θ)
        ≤ Real.sqrt ((K * Kg) * (WlInf α 5 f) ^ 2 * HkSq α 5 g) := by
      rw [show HkNorm α 5 (fun z θ => f z θ * g z θ)
            = Real.sqrt (HkSq α 5 (fun z θ => f z θ * g z θ)) from rfl]
      refine Real.sqrt_le_sqrt ?_
      calc HkSq α 5 (fun z θ => f z θ * g z θ)
          ≤ (K * (WlInf α 5 f) ^ 2 * Kg) * HkSq α 5 g := hSq
        _ = (K * Kg) * (WlInf α 5 f) ^ 2 * HkSq α 5 g := by ring
    refine le_trans h1 (le_of_eq ?_)
    rw [show HkNorm α 5 g = Real.sqrt (HkSq α 5 g) from rfl,
      Real.sqrt_mul (show (0 : ℝ) ≤ (K * Kg) * (WlInf α 5 f) ^ 2 by positivity),
      Real.sqrt_mul (show (0 : ℝ) ≤ K * Kg by positivity),
      Real.sqrt_sq hWnn]
  refine le_trans hXn ?_
  -- `√(K Kg) ≤ √(35701 K) α^{-1/2}`
  have hKg_le : Kg ≤ 35701 * α⁻¹ := by
    have h1 : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
    have hginv : (gam α - 1)⁻¹ = 10 / α := by
      rw [gam_sub_one, inv_div]
    have hαinv : (1 : ℝ) ≤ α⁻¹ := by rw [one_le_inv₀ hα]; exact hα1
    rw [hKgdef, hginv, div_eq_mul_inv]
    ring_nf
    nlinarith [hαinv]
  have hsqrt : Real.sqrt (K * Kg) ≤ Real.sqrt (35701 * K) * α ^ (-(1 / 2 : ℝ)) := by
    have h1 : K * Kg ≤ 35701 * K * α⁻¹ := by
      calc K * Kg ≤ K * (35701 * α⁻¹) := mul_le_mul_of_nonneg_left hKg_le hKpos.le
        _ = 35701 * K * α⁻¹ := by ring
    refine le_trans (Real.sqrt_le_sqrt h1) ?_
    rw [show (35701 : ℝ) * K * α⁻¹ = (35701 * K) * α⁻¹ from by ring,
      Real.sqrt_mul (show (0 : ℝ) ≤ 35701 * K by positivity),
      sqrt_inv_eq_rpow_neg_half5 hα]
  have hmain : Real.sqrt (K * Kg) * WlInf α 5 f * HkNorm α 5 g
      ≤ Real.sqrt (35701 * K) * α ^ (-(1 / 2 : ℝ)) * WlInf α 5 f
        * HkNorm α 5 g := by
    calc Real.sqrt (K * Kg) * WlInf α 5 f * HkNorm α 5 g
        = Real.sqrt (K * Kg) * (WlInf α 5 f * HkNorm α 5 g) := by ring
      _ ≤ (Real.sqrt (35701 * K) * α ^ (-(1 / 2 : ℝ)))
            * (WlInf α 5 f * HkNorm α 5 g) :=
          mul_le_mul_of_nonneg_right hsqrt (mul_nonneg hWnn (Real.sqrt_nonneg _))
      _ = Real.sqrt (35701 * K) * α ^ (-(1 / 2 : ℝ)) * WlInf α 5 f
            * HkNorm α 5 g := by ring
  calc Real.sqrt (K * Kg) * WlInf α 5 f * HkNorm α 5 g
      ≤ Real.sqrt (35701 * K) * α ^ (-(1 / 2 : ℝ)) * WlInf α 5 f
          * HkNorm α 5 g := hmain
    _ = Real.sqrt (35701 * (6 * Cz + 36 * Cm)) * α ^ (-(1 / 2 : ℝ))
          * WlInf α 5 f * HkNorm α 5 g := by rw [hKdef]
    _ ≤ (Real.sqrt (35701 * (6 * Cz + 36 * Cm)) + 1) * α ^ (-(1 / 2 : ℝ))
          * WlInf α 5 f * HkNorm α 5 g := by
        have h1 : (0 : ℝ) ≤ Real.sqrt (35701 * (6 * Cz + 36 * Cm)) := Real.sqrt_nonneg _
        have h2 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
        have h3 : (0 : ℝ) ≤ WlInf α 5 f := hWnn
        have h4 : (0 : ℝ) ≤ HkNorm α 5 g := Real.sqrt_nonneg _
        nlinarith [mul_nonneg (mul_nonneg h2 h3) h4,
          mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4]

end Work.FTS.StrongEps.H5
