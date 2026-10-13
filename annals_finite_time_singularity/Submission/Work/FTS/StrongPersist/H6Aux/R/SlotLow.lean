import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Aux.R.Slots
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.CoercivityFix.Coer1.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Coercivity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `SlotLow`: the two zeroth-order slot estimates for the base case `base_R`

The two `L²`-pairings of the clean operator `𝓛̂ = 𝓛 − Transport` against `h` itself,

  `wip ρ_η (𝓛̂h) h`  and  `wip w² (𝓛̂h) h`   (`ρ_β = w²·sin(2θ)^{-β}`, `w² = ρ_0`),

are bounded below by `-5·|h|²_{ℋ¹}`, for `h` smooth on the open quadrant with an honest
`ℋ¹`-integral.

The proof has three ingredients, none of which needs the smoothness of `h` beyond what is
already in `HkMem`:

* **pointwise AM–GM.**  `Lhat h z θ = h + D_z h − 2h/(1+z) − 3 D_θh/(1+z)`, and on `z ≥ 0`
  (`1/(1+z) ≤ 1`) the elementary `2|ab| ≤ a² + b²` gives

    `Lhat h · h · ρ ≥ -((1/2)(D_zh)² + (3/2)(D_θh)² + 3h²)·ρ`  for every `ρ ≥ 0`;

* **slot domination.**  The bracket is at most `5·HkIntegrand α 1 h` a.e. in `θ`: each of
  `h²`, `(D_zh)²` with the weight `ρ_η`, resp. `(D_θh)²` with the weight `ρ_γ = w²·Wt²`
  (dominated by `ρ_η` since `η ≤ γ = 1 + α/10` for `α ≥ 0`) is a *single summand* of
  `HkIntegrand α 1 h`, while `w² ≤ ρ_η` because `sin(2θ)^{-η} ≥ 1` on `(0,π/2)`;

* **the exact integral comparison.**  If `f + g ≥ 0` a.e. and `g ≥ 0` is integrable then
  `∫f ≥ -∫g` *without* any integrability or measurability assumption on `f` (a
  non-integrable `f` has Bochner integral `0`).  Applied to the angular slice (with
  `g = 5·HkIntegrand`) and then to the radial variable (with `g = 5·∫_θ HkIntegrand` — the
  integrability there is exactly the second clause of `HkMem α 1 h`), this converts the
  pointwise bound into the two stated inequalities.  In particular no joint integrability
  of `𝓛̂h·h·ρ` is needed.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux.R

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! ## The general integral comparison -/

/-- **Integral lower bound from a two-sided-signed pointwise bound.**  If `f + g ≥ 0` a.e. and
`g ≥ 0` is integrable, then `∫ f ≥ -∫ g`.  Nothing is assumed about `f`: if `f` is not
integrable its Bochner integral is `0 ≥ -∫g`, and otherwise `∫(f+g) = ∫f + ∫g ≥ 0`. -/
private theorem neg_integral_le_integral {β : Type*} [MeasurableSpace β]
    {μ : MeasureTheory.Measure β} {f g : β → ℝ} (hg : MeasureTheory.Integrable g μ)
    (hgnn : ∀ᵐ a ∂μ, 0 ≤ g a) (hfg : ∀ᵐ a ∂μ, 0 ≤ f a + g a) :
    -(∫ a, g a ∂μ) ≤ ∫ a, f a ∂μ := by
  by_cases hf : MeasureTheory.Integrable f μ
  · have h0 : 0 ≤ ∫ a, f a + g a ∂μ := MeasureTheory.integral_nonneg_of_ae hfg
    rw [MeasureTheory.integral_add hf hg] at h0
    linarith
  · rw [MeasureTheory.integral_undef hf]
    have h0 : 0 ≤ ∫ a, g a ∂μ := MeasureTheory.integral_nonneg_of_ae hgnn
    linarith

/-! ## The pointwise AM–GM bound -/

/-- **The pointwise AM–GM lower bound for `𝓛̂`.**  For `z ≥ 0` and `ρ ≥ 0`,

`𝓛̂h · h · ρ ≥ -((1/2)(D_zh)² + (3/2)(D_θh)² + 3h²)·ρ`.

The decomposition of the sum `𝓛̂h·h + (1/2)(D_zh)² + (3/2)(D_θh)² + 3h²` into the three
nonnegative pieces `(1/2)(h + D_zh)²`, `(3/2)(D_θh − h/(1+z))²` and
`(1/2)(1 − 1/(1+z))(3/(1+z) + 7)h²` is what makes this exact. -/
private theorem lhat_amgm {h : Fn} {z θ ρ : ℝ} (hz : 0 ≤ z) (hρ : 0 ≤ ρ) :
    -((1 / 2) * (Work.Spaces.Dz h z θ) ^ 2 + (3 / 2) * (Work.Spaces.Dth h z θ) ^ 2
        + 3 * (h z θ) ^ 2) * ρ
      ≤ Work.FTS.CoercivityFix.Lhat h z θ * h z θ * ρ := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hL : Work.FTS.CoercivityFix.Lhat h z θ
      = h z θ + Work.Spaces.Dz h z θ - 2 * ((1 + z)⁻¹ * h z θ)
        - 3 * ((1 + z)⁻¹ * Work.Spaces.Dth h z θ) := by
    rw [Work.FTS.CoercivityFix.Lhat_eq]
    field_simp
  have hZ0 : 0 ≤ (1 + z)⁻¹ := by positivity
  have hZ1 : (1 + z)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ h1z]; linarith
  have hkey : Work.FTS.CoercivityFix.Lhat h z θ * h z θ
        + ((1 / 2) * (Work.Spaces.Dz h z θ) ^ 2 + (3 / 2) * (Work.Spaces.Dth h z θ) ^ 2
            + 3 * (h z θ) ^ 2)
      = (1 / 2) * (h z θ + Work.Spaces.Dz h z θ) ^ 2
        + (3 / 2) * (Work.Spaces.Dth h z θ - (1 + z)⁻¹ * h z θ) ^ 2
        + (1 / 2) * (1 - (1 + z)⁻¹) * (3 * (1 + z)⁻¹ + 7) * (h z θ) ^ 2 := by
    rw [hL]; ring
  have hT : 0 ≤ Work.FTS.CoercivityFix.Lhat h z θ * h z θ
        + ((1 / 2) * (Work.Spaces.Dz h z θ) ^ 2 + (3 / 2) * (Work.Spaces.Dth h z θ) ^ 2
            + 3 * (h z θ) ^ 2) := by
    rw [hkey]
    have h1 : 0 ≤ (1 / 2) * (h z θ + Work.Spaces.Dz h z θ) ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg _)
    have h2 : 0 ≤ (3 / 2) * (Work.Spaces.Dth h z θ - (1 + z)⁻¹ * h z θ) ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg _)
    have h3 : 0 ≤ (1 / 2) * (1 - (1 + z)⁻¹) * (3 * (1 + z)⁻¹ + 7) * (h z θ) ^ 2 := by
      have hA : 0 ≤ 1 - (1 + z)⁻¹ := by linarith
      have hB : 0 ≤ 3 * (1 + z)⁻¹ + 7 := by linarith
      have hC : 0 ≤ (1 / 2 : ℝ) * (1 - (1 + z)⁻¹) * (3 * (1 + z)⁻¹ + 7) :=
        mul_nonneg (mul_nonneg (by norm_num) hA) hB
      exact mul_nonneg hC (sq_nonneg _)
    linarith
  have hTρ : 0 ≤ (Work.FTS.CoercivityFix.Lhat h z θ * h z θ
        + ((1 / 2) * (Work.Spaces.Dz h z θ) ^ 2 + (3 / 2) * (Work.Spaces.Dth h z θ) ^ 2
            + 3 * (h z θ) ^ 2)) * ρ := mul_nonneg hT hρ
  nlinarith [hTρ]

/-! ## The angular weights -/

/-- `η ≤ γ = gam α` for `α ≥ 0`. -/
private theorem eta_le_gam (α : ℝ) (hα : 0 ≤ α) : Work.Spaces.eta ≤ Work.Spaces.gam α := by
  rw [Work.Spaces.gam]
  have := Work.Spaces.eta_lt_one
  linarith

/-- `sin(2θ)^{-η} ≤ sin(2θ)^{-γ}` on `Iθ`, for `α ≥ 0`. -/
private theorem sig_eta_le_sig_gam (α : ℝ) (hα : 0 ≤ α) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ
      ≤ Work.FTS.CoercivityFix.Coer1.sig (Work.Spaces.gam α) θ := by
  have hgam : Work.Spaces.gam α ≠ 0 := by
    rw [Work.Spaces.gam]; intro hc; linarith
  rcases eq_or_lt_of_le (Work.FTS.CoercivityFix.Coer1.sin_nonneg_of_mem_Iθ hθ) with h | h
  · rw [Work.FTS.CoercivityFix.Coer1.sig, Work.FTS.CoercivityFix.Coer1.sig, ← h,
      Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num : -(Work.Spaces.eta) ≠ 0),
      Real.zero_rpow (neg_ne_zero.mpr hgam)]
  · have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    rw [Work.FTS.CoercivityFix.Coer1.sig, Work.FTS.CoercivityFix.Coer1.sig]
    exact Real.rpow_le_rpow_of_exponent_ge h hs1 (by linarith [eta_le_gam α hα])

/-- `(W α)² = w²·sin(2θ)^{-γ}` on `Iθ`, for `α ≥ 0`. -/
private theorem Wt_sq_self_Iθ (α : ℝ) (hα : 0 ≤ α) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Wt α z θ) ^ 2
      = Work.Spaces.w z ^ 2 * Work.FTS.CoercivityFix.Coer1.sig (Work.Spaces.gam α) θ := by
  have hγ : Work.Spaces.gam α ≠ 0 := by
    rw [Work.Spaces.gam]; intro hc; linarith
  have hγ2 : -(Work.Spaces.gam α / 2) ≠ 0 := by intro hc; exact hγ (by linarith)
  have hγ' : -(Work.Spaces.gam α) ≠ 0 := by intro hc; exact hγ (by linarith)
  have hfun : (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2 := by
    simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
  rw [hfun]
  rcases eq_or_lt_of_le (Work.FTS.CoercivityFix.Coer1.sin_nonneg_of_mem_Iθ hθ) with h | h
  · rw [Work.FTS.CoercivityFix.Coer1.sig, ← h, Real.zero_rpow hγ2, Real.zero_rpow hγ']
    ring
  · rw [mul_pow, Work.FTS.CoercivityFix.Coer1.sig]
    rw [show ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) from by
      rw [sq, ← Real.rpow_add h]
      congr 1
      ring]

/-! ## The three `ℋ¹`-slots with the `η`-weight -/

/-- The `h²`-slot. -/
private theorem slot_eta_h (α : ℝ) {h : Fn} {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (h z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ
      ≤ Work.Spaces.HkIntegrand α 1 h z θ := by
  have hIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have he : (h z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ
      = (h z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [mul_pow, Work.FTS.CoercivityFix.Coer1.sig_div_sq_Iθ Work.Spaces.eta
      (by rw [Work.Spaces.eta]; norm_num) z θ hIθ, Work.FTS.CoercivityFix.Coer1.Rho]
  rw [he]
  exact Work.Spaces.sq_le_HkIntegrand_z α 1 h z θ 0 (by norm_num)

/-- The `D_zh`-slot. -/
private theorem slot_eta_dz (α : ℝ) {h : Fn} {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.Dz h z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ
      ≤ Work.Spaces.HkIntegrand α 1 h z θ := by
  have hIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have he : (Work.Spaces.Dz h z θ) ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ
      = (Work.Spaces.Dz h z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [mul_pow, Work.FTS.CoercivityFix.Coer1.sig_div_sq_Iθ Work.Spaces.eta
      (by rw [Work.Spaces.eta]; norm_num) z θ hIθ, Work.FTS.CoercivityFix.Coer1.Rho]
  rw [he]
  exact Work.Spaces.sq_le_HkIntegrand_z α 1 h z θ 1 (by norm_num)

/-- The `D_θh`-slot: the `γ`-weight of `ℋ¹` dominates the `η`-weight. -/
private theorem slot_eta_dth (α : ℝ) (hα : 0 ≤ α) {h : Fn} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.Dth h z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ
      ≤ Work.Spaces.HkIntegrand α 1 h z θ := by
  have hIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hsig := sig_eta_le_sig_gam α hα hIθ
  have hstep : (Work.Spaces.Dth h z θ) ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ
      ≤ (Work.Spaces.Dth h z θ) ^ 2
        * (Work.Spaces.w z ^ 2 * Work.FTS.CoercivityFix.Coer1.sig (Work.Spaces.gam α) θ) := by
    rw [Work.FTS.CoercivityFix.Coer1.Rho]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsig (sq_nonneg _)) (sq_nonneg _)
  have he : (Work.Spaces.Dth h z θ) ^ 2
        * (Work.Spaces.w z ^ 2 * Work.FTS.CoercivityFix.Coer1.sig (Work.Spaces.gam α) θ)
      = (Work.Spaces.mixed 0 1 h z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    rw [mul_pow, Wt_sq_self_Iθ α hα z θ hIθ]
    rfl
  rw [he] at hstep
  exact le_trans hstep
    (Work.Spaces.sq_le_HkIntegrand_mixed α 1 h z θ 1 0 (by norm_num) (by norm_num))

/-- **Slot domination, `η`-weight.** -/
private theorem slot_dom_eta (α : ℝ) (hα : 0 ≤ α) {h : Fn} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ((1 / 2) * (Work.Spaces.Dz h z θ) ^ 2 + (3 / 2) * (Work.Spaces.Dth h z θ) ^ 2
        + 3 * (h z θ) ^ 2) * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ
      ≤ 5 * Work.Spaces.HkIntegrand α 1 h z θ := by
  nlinarith [slot_eta_h (α := α) (h := h) (z := z) (θ := θ) hθ,
    slot_eta_dz (α := α) (h := h) (z := z) (θ := θ) hθ,
    slot_eta_dth α hα (h := h) (z := z) (θ := θ) hθ,
    Work.Spaces.HkIntegrand_nonneg α 1 h z θ]

/-- **Slot domination, plain radial weight `w²`** (which is `Rhoq 0`). -/
private theorem slot_dom_w (α : ℝ) (hα : 0 ≤ α) {h : Fn} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ((1 / 2) * (Work.Spaces.Dz h z θ) ^ 2 + (3 / 2) * (Work.Spaces.Dth h z θ) ^ 2
        + 3 * (h z θ) ^ 2) * (Work.Spaces.w z) ^ 2
      ≤ 5 * Work.Spaces.HkIntegrand α 1 h z θ := by
  have hone := Work.FTS.CoercivityFix.Coer1.one_le_sig_eta hθ
  have hρ : (Work.Spaces.w z) ^ 2 ≤ Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ := by
    rw [Work.FTS.CoercivityFix.Coer1.Rho]
    simpa using mul_le_mul_of_nonneg_left hone (sq_nonneg (Work.Spaces.w z))
  have h1 : (h z θ) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ Work.Spaces.HkIntegrand α 1 h z θ :=
    le_trans (mul_le_mul_of_nonneg_left hρ (sq_nonneg _))
      (slot_eta_h (α := α) (h := h) (z := z) (θ := θ) hθ)
  have h2 : (Work.Spaces.Dz h z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α 1 h z θ :=
    le_trans (mul_le_mul_of_nonneg_left hρ (sq_nonneg _))
      (slot_eta_dz (α := α) (h := h) (z := z) (θ := θ) hθ)
  have h3 : (Work.Spaces.Dth h z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α 1 h z θ :=
    le_trans (mul_le_mul_of_nonneg_left hρ (sq_nonneg _))
      (slot_eta_dth α hα (h := h) (z := z) (θ := θ) hθ)
  nlinarith [h1, h2, h3, Work.Spaces.HkIntegrand_nonneg α 1 h z θ]

/-! ## The general weighted form, and the target -/

/-- **The weighted form of `SlotLow`.**  For an `ℋ¹`-function `h` and any weight `ρ ≥ 0`
on `Iθ` such that the pointwise bracket is dominated by `5·HkIntegrand α 1 h` a.e.,
`wip ρ (𝓛̂h) h ≥ -5·|h|²_{ℋ¹}`. -/
private theorem slot_low_wip (α : ℝ) {h : Fn} (hm : Work.Spaces.HkMem α 1 h)
    {ρ : Fn} (hρnn : ∀ z θ, θ ∈ Work.Spaces.Iθ → 0 ≤ ρ z θ)
    (hG : ∀ z, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ((1 / 2) * (Work.Spaces.Dz h z θ) ^ 2 + (3 / 2) * (Work.Spaces.Dth h z θ) ^ 2
        + 3 * (h z θ) ^ 2) * ρ z θ ≤ 5 * Work.Spaces.HkIntegrand α 1 h z θ) :
    -(5 : ℝ) * Work.Spaces.HkSq α 1 h
      ≤ Work.Coercivity.wip ρ (Work.FTS.CoercivityFix.Lhat h) h := by
  -- the angular estimate, for every fixed `z ∈ I_z`
  have hθlv : ∀ z ∈ Work.Spaces.Iz,
      -(5 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 h z θ))
        ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.CoercivityFix.Lhat h z θ * h z θ * ρ z θ := by
    intro z hz
    have hgnn : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        0 ≤ 5 * Work.Spaces.HkIntegrand α 1 h z θ :=
      Filter.Eventually.of_forall fun θ => by
        have := Work.Spaces.HkIntegrand_nonneg α 1 h z θ
        linarith
    have hsum : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        0 ≤ Work.FTS.CoercivityFix.Lhat h z θ * h z θ * ρ z θ
          + 5 * Work.Spaces.HkIntegrand α 1 h z θ := by
      filter_upwards [hG z, MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => hρnn z θ hθ)] with θ hGθ hρθ
      have ham := lhat_amgm (h := h) (z := z) (θ := θ) (ρ := ρ z θ) hz hρθ
      linarith
    have h := neg_integral_le_integral ((hm.1 z hz).const_mul 5) hgnn hsum
    rw [MeasureTheory.integral_const_mul] at h
    linarith
  -- the radial estimate
  have hz_lv : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      0 ≤ (∫ θ in Work.Spaces.Iθ, Work.FTS.CoercivityFix.Lhat h z θ * h z θ * ρ z θ)
        + 5 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 h z θ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => by
      have := hθlv z hz
      linarith
  have hgnn₂ : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      0 ≤ 5 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 h z θ) :=
    Filter.Eventually.of_forall fun z => by
      have : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 h z θ :=
        MeasureTheory.setIntegral_nonneg measurableSet_Icc
          (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 1 h z θ)
      linarith
  have h := neg_integral_le_integral (hm.2.const_mul 5) hgnn₂ hz_lv
  rw [MeasureTheory.integral_const_mul] at h
  simp only [Work.Spaces.HkSq, Work.Coercivity.wip]
  linarith [h]

/-- `Rhoq 0` is the plain radial weight `w²`. -/
private theorem rhoq_zero : Rhoq 0 = fun z θ => (Work.Spaces.w z) ^ 2 := by
  funext z θ
  simp only [Rhoq, Work.FTS.CoercivityFix.Coer1.Rho,
    Work.FTS.CoercivityFix.Coer1.sig, neg_zero, Real.rpow_zero, mul_one]

/-- **`SlotLow`.**  The two zeroth-order pairings of the clean operator `𝓛̂` against `h` are
bounded below by `-5` times the square of the `ℋ¹`-norm of `h`. -/
theorem SlotLow (α : ℝ) (hα : 0 ≤ α) {h : ℝ → ℝ → ℝ}
    (hs : Work.FTS.EllipticEst.SmoothOpen h) (hm : Work.Spaces.HkMem α 1 h) :
    -(5 : ℝ) * Work.Spaces.HkSq α 1 h
        ≤ Work.Coercivity.wip (Work.FTS.StrongPersist.H6Aux.R.Rhoq Work.Spaces.eta)
            (Work.FTS.CoercivityFix.Lhat h) h
      ∧ -(5 : ℝ) * Work.Spaces.HkSq α 1 h
        ≤ Work.Coercivity.wip (Work.FTS.StrongPersist.H6Aux.R.Rhoq 0)
            (Work.FTS.CoercivityFix.Lhat h) h := by
  refine ⟨?_, ?_⟩
  · exact slot_low_wip α hm (ρ := Work.FTS.StrongPersist.H6Aux.R.Rhoq Work.Spaces.eta)
      (fun z θ hθ => Work.FTS.CoercivityFix.Coer1.Rho_nonneg _ z θ hθ)
      (fun z => Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo.mono
        (fun θ hθ => slot_dom_eta α hα (h := h) (z := z) (θ := θ) hθ))
  · rw [rhoq_zero]
    exact slot_low_wip α hm (ρ := fun z θ => (Work.Spaces.w z) ^ 2)
      (fun z θ _ => sq_nonneg _)
      (fun z => Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo.mono
        (fun θ hθ => slot_dom_w α hα (h := h) (z := z) (θ := θ) hθ))

end Work.FTS.StrongPersist.H6Aux.R
