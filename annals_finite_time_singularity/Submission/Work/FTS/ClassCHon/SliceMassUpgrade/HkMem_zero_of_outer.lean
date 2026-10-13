/-
Copyright: work module for the Elgindi finite-time singularity project.

# `HkMem_zero_of_outer` — every-`z` level-`0` honesty from the *outer* bounds one `D_z`-order up

The elliptic node `EllNode7` needs the **every-`z`** honesty `Work.Spaces.HkMem α 0 (slot)` of
the second-order slots of the solution, whereas the workspace's elliptic estimates produce
*integrated* (`∫⁻`) bounds.  This file supplies the transfer, using the `SliceMassUpgrade`
machinery (the fundamental theorem of calculus on a slice + AM–GM + the radial comparison
`(z₁²)⁻¹ ∫σ(∂_zF)² ≤ ∫σ(z∂_zF)²/z²`):

  > `HkMem α 0 F`  ⟸  the *outer* `∫⁻`-bounds of `HkIntegrand α 0 F`
  >                    and of `HkIntegrand α 0 (z ∂_z F)`, plus measurability and smoothness.

The mathematical content is the identification of the level-`0` integrand

  `HkIntegrand α 0 F z θ = w z² · (σ θ · F z θ²)`,   `σ = sin(2θ)^{-η}`,  (`θ ∈ Iθ`)

which turns the given outer bounds into the two outer bounds of the *`σ`-form* consumed by
`sliceMass_lintegral_lt_top_of_outer` (`w z ≥ 1` on `z > 0` supplies the comparison), whose
conclusion is the finiteness of the `σ`-weighted slice mass at **every** `z > 0`.  Multiplying
back by the finite constant `w z²` gives the finiteness of the `HkIntegrand`-slice mass at every
`z > 0`, hence — via `lintegral_ofReal_ne_top_iff_integrable` and the given slice
measurabilities — the honest slice integrability at every `z ∈ Iz` (the point `z = 0` being
trivial because `w 0 = 0`).  The outer conjunct is `HkMemAe_of_lintegral` plus
`(0,∞) =ᵐ [0,∞)`.

The *joint* measurability of the `σ`-weighted square of `∂_zF`, which the slice-mass upgrade
needs for its Tonelli swap, is derived here from `SmoothOpen F` (continuity on the open quadrant)
rather than from the slicewise measurabilities; consequently the `D_z`-slice measurability
hypotheses `hslmeas1`, `hmeas1` and the constant bound `hC₁` of the statement are *not* used by
this proof (only their `F`-counterparts and `hfin1` are).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.ClassCHon.SliceMassUpgrade
import Submission.Work.FTS.ClassC.HonestCut.HkMemAe_of_lintegral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

namespace Work.FTS.ClassCHon.SliceMassUpgrade

set_option autoImplicit false

local notation "Iz" => Work.Spaces.Iz
local notation "Iθ" => Work.Spaces.Iθ
local notation "HkInt" => Work.Spaces.HkIntegrand
local notation "sEta" => Work.FTS.EllipticEst.sEta
local notation "sOpen" => Work.FTS.EllipticEst.SmoothOpen
local notation "QQ" => Work.FTS.EllipticEst.Q0

/-! ## The level-`0` integrand as `w²` times the `σ`-weighted square -/

/-- At level `0` the `ℋ⁰`-integrand is the single square of the weighted profile
(`Work.EllipticEst.Honest.HkIntegrand_zero_eq`, reproved here to keep the import cone small). -/
theorem slm_HkIntegrand_zero_profile (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    HkInt α 0 g z θ
      = (g z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp only [Work.Spaces.HkIntegrand, Finset.range_one]
  norm_num

/-- **The level-`0` integrand is `w z²` times the `σ`-weighted square of the value**, on `Iθ`.
This is the bridge between the `HkIntegrand`-form of the workspace's norms and the
`σ = sin(2θ)^{-η}` slice mass of the `SliceMassUpgrade` machinery. -/
theorem slm_HkIntegrand_zero_radial (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Iθ) :
    HkInt α 0 g z θ = (Work.Spaces.w z) ^ 2 * (sEta θ * (g z θ) ^ 2) := by
  rw [slm_HkIntegrand_zero_profile]
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hsq : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
      = Real.sin (2 * θ) ^ Work.Spaces.eta := by
    rcases eq_or_lt_of_le hs with h0 | hpos
    · rw [← h0, Real.zero_rpow (by norm_num [Work.Spaces.eta] : Work.Spaces.eta / 2 ≠ 0),
        Real.zero_rpow (by norm_num [Work.Spaces.eta] : Work.Spaces.eta ≠ 0)]
      norm_num
    · rw [pow_two, ← Real.rpow_add hpos]
      congr 1
      ring
  rw [mul_pow, div_pow, hsq, Work.FTS.EllipticEst.sEta, div_eq_mul_inv,
    ← Real.rpow_neg hs (Work.Spaces.eta)]
  ring

/-! ## The angular interval rewritings -/

/-- `∫⁻` over `Iθ = [0,π/2]` equals `∫⁻` over the open interval `(0,π/2)` (the two endpoints
are null). -/
theorem slm_lintegral_Iθ_eq_Ioo (f : ℝ → ℝ≥0∞) :
    (∫⁻ θ in Iθ, f θ) = ∫⁻ θ in Set.Ioo 0 (π / 2), f θ := by
  show (∫⁻ θ : ℝ, f θ ∂(volume.restrict (Set.Icc 0 (π / 2))))
      = ∫⁻ θ : ℝ, f θ ∂(volume.restrict (Set.Ioo 0 (π / 2)))
  rw [MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)).symm]

/-- **The slice-mass identity**: the `(0,π/2)`-integral of the level-`0` integrand is `w z²`
times the `σ`-weighted slice mass. -/
theorem slm_lintegral_HkIntegrand_zero (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (HkInt α 0 g z θ))
      = ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * ∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (sEta θ * (g z θ) ^ 2) := by
  rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal ((Work.Spaces.w z) ^ 2))
    (fun θ : ℝ => ENNReal.ofReal (sEta θ * (g z θ) ^ 2)) ENNReal.ofReal_ne_top]
  refine MeasureTheory.lintegral_congr_ae ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
  rw [slm_HkIntegrand_zero_radial α g ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩,
    ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z))]

/-! ## `w z ≥ 1` on the open half-line -/

/-- `w z = (1+z)²/z² ≥ 1` for `z > 0`. -/
theorem slm_one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith [hz]

/-- The square of the radial weight is at least `1` on the open half-line. -/
theorem slm_one_le_ofReal_w_sq {z : ℝ} (hz : 0 < z) :
    (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((Work.Spaces.w z) ^ 2) :=
  ENNReal.one_le_ofReal.mpr (one_le_pow₀ (slm_one_le_w hz))

/-! ## Joint a.e. measurability of the `σ`-weighted square from `SmoothOpen` -/

/-- Continuity on the open quadrant of the `σ`-weighted square of a `SmoothOpen` datum. -/
theorem slm_continuousOn_sEta_mul_sq {G : ℝ → ℝ → ℝ} (hG : sOpen G) :
    ContinuousOn (fun p : ℝ × ℝ => sEta p.2 * (G p.1 p.2) ^ 2) QQ := by
  have hsinθ : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), 0 < Real.sin (2 * θ) := by
    intro θ hθ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have hsinpos : ∀ p ∈ QQ, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact hsinθ p.2 ⟨hθ0, hθ1⟩
  have hsEtaθ : ContinuousOn (fun θ : ℝ => sEta θ) (Set.Ioo 0 (π / 2)) := by
    rw [show sEta = fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) from rfl]
    exact ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (hsinθ θ hθ)))
  have hsEta : ContinuousOn (fun p : ℝ × ℝ => sEta p.2) QQ :=
    hsEtaθ.comp continuousOn_snd (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).2)
  exact hsEta.mul ((hG.continuousOn).pow 2)

/-- **Joint a.e. measurability**: for a datum `C^∞` on the open quadrant, the `σ`-weighted
square is a.e. strongly measurable for the product of the two restricted measures. -/
theorem slm_aesm_ofReal_sEta_mul_sq {G : ℝ → ℝ → ℝ} (hG : sOpen G) :
    AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (sEta p.2 * (G p.1 p.2) ^ 2))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2)))) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => ENNReal.ofReal (sEta p.2 * (G p.1 p.2) ^ 2))
      QQ := ENNReal.continuous_ofReal.comp_continuousOn (slm_continuousOn_sEta_mul_sq hG)
  have hUm : MeasurableSet QQ := (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  have hmain : AEStronglyMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (sEta p.2 * (G p.1 p.2) ^ 2))
      ((volume.prod volume).restrict QQ) := hcont.aestronglyMeasurable hUm
  rw [show (volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2)))
      = (volume.prod volume).restrict QQ from MeasureTheory.Measure.prod_restrict _ _]
  exact hmain.aemeasurable

/-! ## The `σ`-form of an outer `HkIntegrand`-bound -/

/-- **The outer `σ`-weighted mass is finite** as soon as the outer `HkIntegrand`-bound of the
same datum is finite: the two integrands differ by the factor `w z² ≥ 1` (`z > 0`) which is
constant in `θ`, and the angular intervals `Iθ` and `(0,π/2)` differ by a null set. -/
theorem slm_sigma_mass_lt_top_of_HkIntegrand_outer (α : ℝ) (g : ℝ → ℝ → ℝ) {C : ℝ}
    (hfin : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Iθ, ENNReal.ofReal (HkInt α 0 g z θ))
      ≤ ENNReal.ofReal C) :
    (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
      ENNReal.ofReal (sEta θ * (g z θ) ^ 2)) < ⊤ := by
  refine lt_of_le_of_lt ?_ (lt_of_le_of_lt hfin ENNReal.ofReal_lt_top)
  calc (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
          ENNReal.ofReal (sEta θ * (g z θ) ^ 2))
      ≤ ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (sEta θ * (g z θ) ^ 2)) := by
        refine MeasureTheory.lintegral_mono_ae ?_
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
        exact Filter.Eventually.of_forall fun z hz =>
          le_mul_of_one_le_left' (slm_one_le_ofReal_w_sq hz)
    _ = ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
          ENNReal.ofReal (HkInt α 0 g z θ) := by
        refine MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        exact (slm_lintegral_HkIntegrand_zero α g z).symm
    _ = ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Iθ, ENNReal.ofReal (HkInt α 0 g z θ) := by
        refine MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        exact (slm_lintegral_Iθ_eq_Ioo _).symm

/-! ## The main transfer -/

theorem HkMem_zero_of_outer {α : ℝ} {F : ℝ → ℝ → ℝ} {C₀ C₁ : ℝ} (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hslmeas : ∀ z ∈ Work.Spaces.Iz, AEMeasurable (fun θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 F z θ)) (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hmeas : AEMeasurable (fun z => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 F z θ)) (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hfin0 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 F z θ)) ≤ ENNReal.ofReal C₀)
    (hslmeas1 : ∀ z ∈ Work.Spaces.Iz, AEMeasurable (fun θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (fun z θ => z * Work.Spaces.pz F z θ) z θ)) (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hmeas1 : AEMeasurable (fun z => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (fun z θ => z * Work.Spaces.pz F z θ) z θ)) (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hfin1 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (fun z θ => z * Work.Spaces.pz F z θ) z θ)) ≤ ENNReal.ofReal C₁) :
    Work.Spaces.HkMem α 0 F := by
  -- (1) the two outer bounds of the `σ`-form, from the given outer `HkIntegrand`-bounds
  have houter0 := slm_sigma_mass_lt_top_of_HkIntegrand_outer α F hfin0
  have houter1 := slm_sigma_mass_lt_top_of_HkIntegrand_outer α
    (fun z θ => z * Work.Spaces.pz F z θ) hfin1
  -- (2) the `σ`-form slice mass is finite at *every* `z > 0`
  have hMs : ∀ z ∈ Set.Ioi (0 : ℝ),
      (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (sEta θ * (F z θ) ^ 2)) < ⊤ :=
    sliceMass_lintegral_lt_top_of_outer hsm
      (slm_aesm_ofReal_sEta_mul_sq hsm.pz)
      ((slm_aesm_ofReal_sEta_mul_sq hsm).lintegral_prod_right)
      houter0 houter1
  -- (3) the slice conjunct
  have hslice : ∀ z ∈ Iz, IntegrableOn (fun θ => HkInt α 0 F z θ) Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · -- `z = 0`: the radial weight vanishes
      have hzero : (fun θ : ℝ => HkInt α 0 F z θ) = fun _ : ℝ => (0 : ℝ) := by
        funext θ
        rw [← hz0, slm_HkIntegrand_zero_profile, Work.Spaces.w]
        norm_num
      rw [hzero]
      exact integrableOn_zero
    · -- `z > 0`: finiteness of the slice mass, then honest integrability
      have hfin : (∫⁻ θ in Iθ, ENNReal.ofReal (HkInt α 0 F z θ)) < ⊤ := by
        rw [slm_lintegral_Iθ_eq_Ioo, slm_lintegral_HkIntegrand_zero α F z]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hMs z hzpos)
      refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable ?_ ?_).mp (ne_of_lt hfin)
      · refine (((hslmeas z (Set.Ioi_subset_Ici_self hzpos)).ennreal_toReal).aestronglyMeasurable).congr ?_
        exact Filter.Eventually.of_forall fun θ =>
          ENNReal.toReal_ofReal (Work.Spaces.HkIntegrand_nonneg α 0 F z θ)
      · exact Filter.Eventually.of_forall fun θ =>
          Work.Spaces.HkIntegrand_nonneg α 0 F z θ
  -- (4) the outer conjunct: a.e. integrability, upgraded from `(0,∞)` to `[0,∞)`
  refine ⟨hslice, ?_⟩
  have houter : IntegrableOn
      (fun z => ∫ θ in Iθ, HkInt α 0 F z θ) (Set.Ioi 0) :=
    (Work.FTS.ClassC.HonestCut.HkMemAe_of_lintegral hC₀ hslmeas hfin0 hmeas).2
  refine houter.congr_set_ae ?_
  rw [Work.Spaces.Iz]
  exact (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))).symm

end Work.FTS.ClassCHon.SliceMassUpgrade
