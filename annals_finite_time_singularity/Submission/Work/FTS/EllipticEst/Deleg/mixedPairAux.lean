/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Deleg/mixedPairAux` — generic helpers for the `δ ↓ 0` limit of the cut-off chain

This module collects the reusable facts about `Work.Spaces.HkMem α 0 ·`, the angular weight
`sigθ θ = sin(2θ)^{-η}` and the radial weight `wt z = w(z)²` that the proof of
`Deleg.mixedPairLimit` needs:

* `hkIntegrand_zero_eq` — the `k = 0` form of the `ℋ⁰`-integrand:
  `HkIntegrand α 0 f z θ = f z θ² · wt z · sigθ θ` on `Iθ`;
* the angular slices / radial marginals of an `ℋ⁰`-honest `f` are integrable
  (`integrableOn_sig_mul_sq_of_HkMem`, `integrableOn_marginal_of_HkMem`, …);
* `wt z ≥ 1` for `z > 0`, the AM–GM bound `abs_mixed_slice_le`, and the measurability
  helpers (continuity on the open quadrant `Q0` and `AEStronglyMeasurable.integral_prod_right'`);
* the uniform bound for the transfer coefficient `deriv (χ_n w² z²)/z`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.AeColl.pairFacts
import Submission.Work.FTS.EllipticEst.AeColl.limitBoundAux.pieces2
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Deleg.i1Paper_weakMixedDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Deleg

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-! ## 1. Elementary facts about the weights -/

theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sigθ_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.AeColl.sigθ θ :=
  Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _

theorem sigθ_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Work.FTS.EllipticEst.AeColl.sigθ θ :=
  Real.rpow_pos_of_pos (sin_two_pos_of_mem_Ioo hθ) _

theorem wt_nonneg (z : ℝ) : 0 ≤ Work.FTS.EllipticEst.AeColl.wt z := sq_nonneg _

theorem one_le_w_of_pos {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith [hz]

theorem one_le_wt_of_pos {z : ℝ} (hz : 0 < z) : 1 ≤ Work.FTS.EllipticEst.AeColl.wt z := by
  have hw := one_le_w_of_pos hz
  have h0 : (0 : ℝ) ≤ Work.Spaces.w z := le_trans zero_le_one hw
  rw [Work.FTS.EllipticEst.AeColl.wt]
  nlinarith [hw, h0]

theorem wt_ne_zero_of_pos {z : ℝ} (hz : 0 < z) : Work.FTS.EllipticEst.AeColl.wt z ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_wt_of_pos hz))

theorem mem_Iz_of_nonneg {z : ℝ} (hz : 0 ≤ z) : z ∈ Work.Spaces.Iz := by
  rw [Work.Spaces.Iz]
  exact Set.mem_Ici.mpr hz

theorem mem_Iz_of_pos {z : ℝ} (hz : 0 < z) : z ∈ Work.Spaces.Iz :=
  mem_Iz_of_nonneg (le_of_lt hz)

/-! ## 2. The `k = 0` form of the `ℋ⁰`-integrand -/

theorem hkIntegrand_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
        * Work.FTS.EllipticEst.AeColl.sigθ θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have h1 : (∑ i ∈ Finset.range (0 + 1), (Work.Spaces.DzIter i f z θ *
      (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      = (f z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by simp
  have h2 : (∑ i ∈ Finset.range (0 + 1), ∑ j ∈ Finset.range (0 + 1),
      if 1 ≤ i ∧ i + j ≤ 0
      then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) = 0 := by simp
  rw [Work.Spaces.HkIntegrand, h1, h2, add_zero]
  by_cases hs0 : Real.sin (2 * θ) = 0
  · have hpow : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) = 0 := by
      rw [hs0]; exact Real.zero_rpow (by norm_num [Work.Spaces.eta])
    have hsig0 : Work.FTS.EllipticEst.AeColl.sigθ θ = 0 := by
      rw [Work.FTS.EllipticEst.AeColl.sigθ, hs0]
      exact Real.zero_rpow (by norm_num [Work.Spaces.eta])
    rw [hsig0, hpow, div_zero]
    ring
  · have hpos : 0 < Real.sin (2 * θ) := lt_of_le_of_ne hs (Ne.symm hs0)
    have hsin : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
        = Real.sin (2 * θ) ^ Work.Spaces.eta := by
      rw [sq, ← Real.rpow_add hpos]; norm_num
    have hsig : Work.FTS.EllipticEst.AeColl.sigθ θ
        = (Real.sin (2 * θ) ^ Work.Spaces.eta)⁻¹ := by
      rw [Work.FTS.EllipticEst.AeColl.sigθ, Real.rpow_neg (le_of_lt hpos)]
    rw [hsig, Work.FTS.EllipticEst.AeColl.wt, mul_pow, div_pow, hsin]
    ring

/-! ## 3. Slices and marginals of an `ℋ⁰`-honest function -/

/-- The angular slice of `f z · ²`, weighted by `wt z · sigθ`, is integrable on `Iθ`. -/
theorem integrableOn_sig_sq_wt_of_HkMem (α : ℝ) {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 0 f)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    Integrable (fun θ => f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
      * Work.FTS.EllipticEst.AeColl.sigθ θ) (volume.restrict Work.Spaces.Iθ) :=
  (hmem.1 z hz).congr (ae_restrict_of_forall_mem measurableSet_Icc
    (fun θ hθ => hkIntegrand_zero_eq α f hθ))

/-- The angular slice of `f z · ²`, weighted only by `sigθ`, is integrable on `(0, π/2)`. -/
theorem integrableOn_sig_mul_sq_of_HkMem (α : ℝ) {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 0 f)
    {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have h2 : Integrable (fun θ => f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
      * Work.FTS.EllipticEst.AeColl.sigθ θ) (volume.restrict Work.Spaces.Iθ) :=
    integrableOn_sig_sq_wt_of_HkMem α hmem (le_of_lt hz)
  have h3 : Integrable (fun θ => (Work.FTS.EllipticEst.AeColl.wt z)⁻¹ *
      (f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ))
      (volume.restrict Work.Spaces.Iθ) := h2.const_mul _
  have h4 : Integrable (fun θ => Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ ^ 2)
      (volume.restrict Work.Spaces.Iθ) := by
    refine h3.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ _
    have hwt := wt_ne_zero_of_pos hz
    calc (Work.FTS.EllipticEst.AeColl.wt z)⁻¹ * (f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
          * Work.FTS.EllipticEst.AeColl.sigθ θ)
        = ((Work.FTS.EllipticEst.AeColl.wt z)⁻¹ * Work.FTS.EllipticEst.AeColl.wt z)
            * (f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.sigθ θ) := by ring
      _ = f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.sigθ θ := by
          rw [inv_mul_cancel₀ hwt, one_mul]
      _ = Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ ^ 2 := by ring
  exact MeasureTheory.IntegrableOn.mono_set h4 (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)

/-- The radial marginal of `f² wt sigθ` is integrable. -/
theorem integrableOn_marginal_of_HkMem (α : ℝ) {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 0 f) :
    IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, f z θ ^ 2
        * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)
      Work.Spaces.Iz :=
  hmem.2.congr (Filter.Eventually.of_forall (fun z =>
    setIntegral_congr_fun measurableSet_Icc (fun θ hθ => hkIntegrand_zero_eq α f hθ)))

/-- The radial marginal of `f² wt sigθ`, as an integrability statement on `(0,∞)`. -/
theorem integrableOn_marginal_Ioi_of_HkMem (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 0 f) :
    IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, f z θ ^ 2
        * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)
      (Set.Ioi 0) :=
  MeasureTheory.IntegrableOn.mono_set (integrableOn_marginal_of_HkMem α hmem) Set.Ioi_subset_Ici_self

/-- **AM–GM for the mixed marginal**: the absolute mixed angular marginal of `f` and `g` is
dominated by the sum of the two diagonal marginals (which contain the radial weight `wt z`). -/
theorem abs_mixed_slice_le (α : ℝ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α 0 f) (hg : Work.Spaces.HkMem α 0 g) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ * g z θ|)
      ≤ (∫ θ in Work.Spaces.Iθ, f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
            * Work.FTS.EllipticEst.AeColl.sigθ θ)
        + (∫ θ in Work.Spaces.Iθ, g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
            * Work.FTS.EllipticEst.AeColl.sigθ θ) := by
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hfz : Integrable (fun θ => f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
      * Work.FTS.EllipticEst.AeColl.sigθ θ) (volume.restrict Work.Spaces.Iθ) :=
    integrableOn_sig_sq_wt_of_HkMem α hf (le_of_lt hz)
  have hgz : Integrable (fun θ => g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
      * Work.FTS.EllipticEst.AeColl.sigθ θ) (volume.restrict Work.Spaces.Iθ) :=
    integrableOn_sig_sq_wt_of_HkMem α hg (le_of_lt hz)
  have hfz' := MeasureTheory.IntegrableOn.mono_set hfz hsub
  have hgz' := MeasureTheory.IntegrableOn.mono_set hgz hsub
  have hstep1 : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ * g z θ|)
      ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ
            + g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
              * Work.FTS.EllipticEst.AeColl.sigθ θ) := by
    refine integral_mono_of_nonneg ?_ (hfz'.add hgz') ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ _
      exact abs_nonneg _
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hs0 := sigθ_nonneg_of_mem_Iθ (hsub hθ)
      have hw1 := one_le_wt_of_pos hz
      have h1 : |f z θ| * |g z θ| ≤ f z θ ^ 2 + g z θ ^ 2 := by
        nlinarith [sq_nonneg (|f z θ| - |g z θ|), sq_abs (f z θ), sq_abs (g z θ)]
      calc |Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ * g z θ|
          = Work.FTS.EllipticEst.AeColl.sigθ θ * (|f z θ| * |g z θ|) := by
            rw [abs_mul, abs_mul, abs_of_nonneg hs0]; ring
        _ ≤ Work.FTS.EllipticEst.AeColl.sigθ θ * (f z θ ^ 2 + g z θ ^ 2) :=
            mul_le_mul_of_nonneg_left h1 hs0
        _ ≤ Work.FTS.EllipticEst.AeColl.sigθ θ
              * (Work.FTS.EllipticEst.AeColl.wt z * (f z θ ^ 2 + g z θ ^ 2)) := by
            refine mul_le_mul_of_nonneg_left ?_ hs0
            nlinarith [hw1, sq_nonneg (f z θ), sq_nonneg (g z θ)]
        _ = f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ
              + g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
                * Work.FTS.EllipticEst.AeColl.sigθ θ := by ring
  have hstep2 : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ
            + g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
              * Work.FTS.EllipticEst.AeColl.sigθ θ))
      = (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)
        + (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
              * Work.FTS.EllipticEst.AeColl.sigθ θ) :=
    integral_add hfz' hgz'
  have hstep3a : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)
      ≤ ∫ θ in Work.Spaces.Iθ, f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
          * Work.FTS.EllipticEst.AeColl.sigθ θ := by
    refine setIntegral_mono_set hfz ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (wt_nonneg z))
        (sigθ_nonneg_of_mem_Iθ (show θ ∈ Work.Spaces.Iθ from hθ))
    · filter_upwards with θ hθ
      exact hsub hθ
  have hstep3b : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)
      ≤ ∫ θ in Work.Spaces.Iθ, g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
          * Work.FTS.EllipticEst.AeColl.sigθ θ := by
    refine setIntegral_mono_set hgz ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (wt_nonneg z))
        (sigθ_nonneg_of_mem_Iθ (show θ ∈ Work.Spaces.Iθ from hθ))
    · filter_upwards with θ hθ
      exact hsub hθ
  exact le_trans hstep1 (le_trans hstep2.le (add_le_add hstep3a hstep3b))

/-! ## 3b. Further `wt`-weighted comparisons -/

theorem wtB_nonneg (n : ℕ) : 0 ≤ Work.FTS.EllipticEst.AeColl.wtB n := by
  rw [Work.FTS.EllipticEst.AeColl.wtB]; positivity

/-- The angular slice of `σ f²` is integrable on `Iθ` (without the radial weight). -/
theorem integrableOn_sig_mul_sq_Iθ_of_HkMem (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 0 f) {z : ℝ} (hz : 0 < z) :
    Integrable (fun θ => Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ ^ 2)
      (volume.restrict Work.Spaces.Iθ) := by
  have h2 : Integrable (fun θ => f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
      * Work.FTS.EllipticEst.AeColl.sigθ θ) (volume.restrict Work.Spaces.Iθ) :=
    integrableOn_sig_sq_wt_of_HkMem α hmem (le_of_lt hz)
  have h3 : Integrable (fun θ => (Work.FTS.EllipticEst.AeColl.wt z)⁻¹ *
      (f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ))
      (volume.restrict Work.Spaces.Iθ) := h2.const_mul _
  refine h3.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with θ _
  have hwt := wt_ne_zero_of_pos hz
  calc (Work.FTS.EllipticEst.AeColl.wt z)⁻¹ * (f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
        * Work.FTS.EllipticEst.AeColl.sigθ θ)
      = ((Work.FTS.EllipticEst.AeColl.wt z)⁻¹ * Work.FTS.EllipticEst.AeColl.wt z)
          * (f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.sigθ θ) := by ring
    _ = f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.sigθ θ := by
        rw [inv_mul_cancel₀ hwt, one_mul]
    _ = Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ ^ 2 := by ring

/-- **AM–GM for the mixed marginal, in `wt`-weighted form**: multiplying the angular integral
by `wt z` puts the radial weight *inside* the integral, where it can be compared with the two
diagonal `ℋ⁰`-marginals. -/
theorem abs_mixed_slice_wt_le (α : ℝ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α 0 f) (hg : Work.Spaces.HkMem α 0 g) {z : ℝ} (hz : 0 < z) :
    Work.FTS.EllipticEst.AeColl.wt z
        * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            |Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ * g z θ|)
      ≤ (∫ θ in Work.Spaces.Iθ, f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
            * Work.FTS.EllipticEst.AeColl.sigθ θ)
        + (∫ θ in Work.Spaces.Iθ, g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
            * Work.FTS.EllipticEst.AeColl.sigθ θ) := by
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hfz : Integrable (fun θ => f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
      * Work.FTS.EllipticEst.AeColl.sigθ θ) (volume.restrict Work.Spaces.Iθ) :=
    integrableOn_sig_sq_wt_of_HkMem α hf (le_of_lt hz)
  have hgz : Integrable (fun θ => g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
      * Work.FTS.EllipticEst.AeColl.sigθ θ) (volume.restrict Work.Spaces.Iθ) :=
    integrableOn_sig_sq_wt_of_HkMem α hg (le_of_lt hz)
  have hfz' := MeasureTheory.IntegrableOn.mono_set hfz hsub
  have hgz' := MeasureTheory.IntegrableOn.mono_set hgz hsub
  have hstep1 : Work.FTS.EllipticEst.AeColl.wt z
        * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            |Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ * g z θ|)
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.AeColl.wt z
          * |Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ * g z θ| := by
    rw [MeasureTheory.integral_const_mul]
  have hstep2 : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.AeColl.wt z
          * |Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ * g z θ|)
      ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ
            + g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
              * Work.FTS.EllipticEst.AeColl.sigθ θ) := by
    refine integral_mono_of_nonneg ?_ (hfz'.add hgz') ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ _
      exact mul_nonneg (wt_nonneg z) (abs_nonneg _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hs0 := sigθ_nonneg_of_mem_Iθ (hsub hθ)
      have hwt0 := wt_nonneg z
      have h1 : |f z θ| * |g z θ| ≤ f z θ ^ 2 + g z θ ^ 2 := by
        nlinarith [sq_nonneg (|f z θ| - |g z θ|), sq_abs (f z θ), sq_abs (g z θ)]
      calc Work.FTS.EllipticEst.AeColl.wt z
            * |Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ * g z θ|
          = (Work.FTS.EllipticEst.AeColl.sigθ θ * (|f z θ| * |g z θ|))
              * Work.FTS.EllipticEst.AeColl.wt z := by
            rw [abs_mul, abs_mul, abs_of_nonneg hs0]; ring
        _ ≤ (Work.FTS.EllipticEst.AeColl.sigθ θ * (f z θ ^ 2 + g z θ ^ 2))
              * Work.FTS.EllipticEst.AeColl.wt z :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hs0) hwt0
        _ = f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ
              + g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
                * Work.FTS.EllipticEst.AeColl.sigθ θ := by ring
  have hstep3 : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ
            + g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
              * Work.FTS.EllipticEst.AeColl.sigθ θ))
      = (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)
        + (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
              * Work.FTS.EllipticEst.AeColl.sigθ θ) :=
    integral_add hfz' hgz'
  have hstep4a : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)
      ≤ ∫ θ in Work.Spaces.Iθ, f z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
          * Work.FTS.EllipticEst.AeColl.sigθ θ := by
    refine setIntegral_mono_set hfz ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (wt_nonneg z))
        (sigθ_nonneg_of_mem_Iθ (show θ ∈ Work.Spaces.Iθ from hθ))
    · filter_upwards with θ hθ
      exact hsub hθ
  have hstep4b : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)
      ≤ ∫ θ in Work.Spaces.Iθ, g z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
          * Work.FTS.EllipticEst.AeColl.sigθ θ := by
    refine setIntegral_mono_set hgz ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (wt_nonneg z))
        (sigθ_nonneg_of_mem_Iθ (show θ ∈ Work.Spaces.Iθ from hθ))
    · filter_upwards with θ hθ
      exact hsub hθ
  exact le_trans hstep1.le
    (le_trans hstep2 (le_trans hstep3.le (add_le_add hstep4a hstep4b)))

/-! ## 4. Measurability -/

/-- Continuity on the open quadrant gives a.e. strong measurability for the product of the two
restricted measures. -/
theorem aesm_prod_of_continuousOn_Q0 {g : ℝ × ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    AEStronglyMeasurable g ((volume.restrict (Set.Ioi (0 : ℝ))).prod
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))) := by
  have hUm : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  have hmain : AEStronglyMeasurable g
      ((volume.prod volume).restrict
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hg.aestronglyMeasurable hUm
  rw [Measure.prod_restrict]
  exact hmain

/-- The absolute value of an a.e. strongly measurable real function is a.e. strongly
measurable (`|f| = max f (-f)`). -/
theorem aesm_abs {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X} {f : X → ℝ}
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun x => |f x|) μ := by
  have h2 : AEStronglyMeasurable (fun x => max (f x) (-1 * f x)) μ :=
    hf.sup (hf.const_mul (-1))
  refine h2.congr (Filter.Eventually.of_forall (fun x => ?_))
  show max (f x) (-1 * f x) = |f x|
  rw [abs_eq_max_neg]
  congr 1
  ring

/-- The radial marginal of a jointly measurable function is a.e. strongly measurable. -/
theorem aesm_marginal {G : ℝ → ℝ → ℝ}
    (hjoint : AEStronglyMeasurable (fun p : ℝ × ℝ => G p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))) :
    AEStronglyMeasurable (fun z => ∫ θ, G z θ
      ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
  hjoint.integral_prod_right'

/-- The weight `cut n · · wt ·` is a.e. strongly measurable on `(0,∞)`. -/
theorem aesm_cut_mul_wt (n : ℕ) :
    AEStronglyMeasurable (fun z => Work.FTS.EllipticEst.cut n z
      * Work.FTS.EllipticEst.AeColl.wt z) (volume.restrict (Set.Ioi (0 : ℝ))) :=
  ((((Work.FTS.EllipticEst.cut_contDiff n).continuous.continuousOn).mul
      Work.FTS.EllipticEst.AeColl.continuousOn_wt).aestronglyMeasurable measurableSet_Ioi)

/-- The squared radial weight `wt ·` is measurable. -/
theorem measurable_wt : Measurable Work.FTS.EllipticEst.AeColl.wt := by
  have h' : Work.FTS.EllipticEst.AeColl.wt = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
    funext z; simp only [Work.FTS.EllipticEst.AeColl.wt, Work.Spaces.w]
  rw [h']
  exact (((measurable_const.add measurable_id).pow_const 2).div
    (measurable_id.pow_const 2)).pow_const 2

/-- The transfer coefficient `deriv (χ_n w² z²)/z` is a.e. strongly measurable on `(0,∞)`. -/
theorem aesm_trtr_coef (n : ℕ) :
    AEStronglyMeasurable
      (fun z => deriv (fun z' => Work.FTS.EllipticEst.cut n z'
        * Work.FTS.EllipticEst.AeColl.wt z' * z' ^ 2) z / z)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hcut : Measurable (deriv (Work.FTS.EllipticEst.cut n)) :=
    ((Work.FTS.EllipticEst.cut_contDiff n).continuous_deriv (by norm_num)).measurable
  have hcwf : Measurable Work.FTS.EllipticEst.AeColl.cwf := by
    have h2 : Work.FTS.EllipticEst.AeColl.cwf = fun z : ℝ => 2 * (z - 1) / (1 + z) := by
      funext z; rfl
    rw [h2]
    exact ((measurable_const.mul (measurable_id.sub measurable_const))).div
      (measurable_const.add measurable_id)
  have hcfun : Measurable (Work.FTS.EllipticEst.AeColl.cfun n) := by
    have h : Work.FTS.EllipticEst.AeColl.cfun n
        = fun z : ℝ => deriv (Work.FTS.EllipticEst.cut n) z * z
            + Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.cwf z := by
      funext z; rfl
    rw [h]
    exact (hcut.mul measurable_id).add
      (((Work.FTS.EllipticEst.cut_contDiff n).continuous.measurable).mul hcwf)
  refine ((hcfun.mul measurable_wt).aestronglyMeasurable).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  exact (Work.FTS.EllipticEst.AeColl.deriv_cut_wt_zsq hz).symm

/-! ## 5. The uniform bound for the transfer coefficient -/

/-- The transfer coefficient is dominated by the radial weight: there is `C > 0` with
`|deriv (χ_n w² z²) z / z| ≤ C · wt z` for every `z > 0`. -/
theorem trtr_coef_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 0 < z →
      |deriv (fun z' => Work.FTS.EllipticEst.cut n z' * Work.FTS.EllipticEst.AeColl.wt z'
        * z' ^ 2) z / z| ≤ C * Work.FTS.EllipticEst.AeColl.wt z := by
  obtain ⟨K, hKpos, hKbd, -, -⟩ := Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
  refine ⟨K + 2, by linarith, fun z hz => ?_⟩
  rw [Work.FTS.EllipticEst.AeColl.deriv_cut_wt_zsq hz, abs_mul,
    abs_of_nonneg (wt_nonneg z)]
  exact mul_le_mul_of_nonneg_right
    (Work.FTS.EllipticEst.AeColl.abs_cfun_le (hKbd n) (le_of_lt hz)) (wt_nonneg z)


end

end Work.FTS.EllipticEst.Deleg
