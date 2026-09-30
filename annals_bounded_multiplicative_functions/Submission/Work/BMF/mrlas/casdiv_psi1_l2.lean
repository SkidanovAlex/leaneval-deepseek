import Mathlib
import Submission.Work.BMF.halasz_series_aux
import Submission.Work.BMF.Psi1_L2_defs
import Submission.Work.BMF.Psi1_L2_local_mass
import Submission.Work.BMF.Psi1_L2_total_mass
import Submission.Work.BMF.Psi1_L2_psi_rewrite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-
The L² window bound for `Ψ₁` on the line `Re s = 1 + α`.

`Ψ₁ f s = -∑_p f p · log p · p^{-s}` (see `Submission.Work.BMF.halasz_series_aux`).  We show that
for every `1`-bounded `f` there is a constant `C > 0` with

`∫_τ∈[c,c+1] ‖Ψ₁ f (1+α+iτ)‖² dτ ≤ C/α`   for all `0 < α ≤ 1`, `c ∈ ℝ`.

The bound is *not* trivial: the pointwise size of `Ψ₁` on the line is only `O(1/α)`, which would
give `O(1/α²)`.  We instead use the oscillatory nature of the sum over the *logarithms* of the
primes: localising the integral with the Gaussian window `PhiLoc` and using the exact Fourier pair
`PhiLoc ↔ pairK` (`pairK θ = exp (-θ²)`), the unit-window mean square is dominated by the pair sum

`∑_{p,q} ‖b_p‖ ‖b_q‖ pairK (log p - log q)`,

which splits into a *diagonal* contribution `∑_p ‖b_p‖² = O(1)` and an *off-diagonal* contribution
estimated through the local mass bound `∑_q (log q)/q^{1+α} pairK (log p - log q) ≤ C p^{-α}`
(`Work.BMF.Psi1_L2_local_mass`, via Chebyshev's estimate in log-dyadic blocks) together with
`∑_p (log p)/p^{1+α} ≤ C/α` (`Work.BMF.Psi1_L2_total_mass`).

Everything here is sorry-free.
-/

namespace Work.BMF.mrlas

open MeasureTheory Real Filter
open scoped BigOperators Topology

noncomputable section

/-- The localiser against an oscillation: `∫ τ, PhiLoc (τ - c) * exp (-I τ θ) = exp (-I c θ) * pairK θ`. -/
lemma casdiv_l2_PhiLoc_fourier_shift (θ c : ℝ) :
    ∫ τ : ℝ, ((PhiLoc (τ - c) : ℂ) * Complex.exp (-(τ * θ) * Complex.I))
      = Complex.exp (-(c * θ) * Complex.I) * (pairK θ : ℂ) := by
  have hshift : (∫ τ : ℝ, ((PhiLoc (τ - c) : ℂ) * Complex.exp (-((τ - c) * θ) * Complex.I)))
      = ∫ s : ℝ, ((PhiLoc s : ℂ) * Complex.exp (-(s * θ) * Complex.I)) := by
    have h := integral_add_right_eq_self (μ := volume)
      (fun s : ℝ => (PhiLoc s : ℂ) * Complex.exp (-(s * θ) * Complex.I)) (-c)
    simpa [sub_eq_add_neg] using h
  have hpt : ∀ τ : ℝ, (PhiLoc (τ - c) : ℂ) * Complex.exp (-(τ * θ) * Complex.I)
      = ((PhiLoc (τ - c) : ℂ) * Complex.exp (-((τ - c) * θ) * Complex.I))
        * Complex.exp (-(c * θ) * Complex.I) := by
    intro τ
    have harg : -(↑τ * ↑θ) * Complex.I
        = -((↑τ - ↑c) * ↑θ) * Complex.I + -(↑c * ↑θ) * Complex.I := by
      push_cast; ring
    rw [harg, Complex.exp_add, mul_assoc]
  rw [funext hpt, MeasureTheory.integral_mul_const, hshift, PhiLoc_fourier]
  ring

/-- **The finite-sum mean square bound.**  For any finite set of "frequencies" `u` with coefficients
`b`, the mean square of `Σ b n exp (-I τ u n)` over a unit interval is bounded by the (φ-localised)
pair sum, the constant being `1 / phiDelta`. -/
lemma casdiv_l2_finite_osc_L2_le (S : Finset ℕ) (b : ℕ → ℂ) (u : ℕ → ℝ) (c : ℝ) :
    ∫ τ in c..(c+1), ‖∑ n ∈ S, b n * Complex.exp (-(τ * u n) * Complex.I)‖ ^ 2
      ≤ (1 / phiDelta) * ∑ p ∈ S, ∑ q ∈ S, ‖b p‖ * ‖b q‖ * pairK (u p - u q) := by
  set F : ℝ → ℂ := fun τ => ∑ n ∈ S, b n * Complex.exp (-(τ * u n) * Complex.I) with hF
  have hcc : c ≤ c + 1 := by linarith
  have hδ : (0:ℝ) < phiDelta := phiDelta_pos
  have hFcont : Continuous F := by
    rw [hF]
    refine continuous_finsetSum _ fun n _ => ?_
    exact continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))
  have hFnorm : ∀ τ : ℝ, ‖F τ‖ ≤ ∑ n ∈ S, ‖b n‖ := by
    intro τ
    rw [hF]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [norm_mul, Complex.norm_exp]
    simp
  have hInt : ∀ p q : ℕ, Integrable (fun τ : ℝ => (b p * (starRingEnd ℂ) (b q)) *
      ((PhiLoc (τ - c) : ℂ) * Complex.exp (-(τ * (u p - u q)) * Complex.I))) := by
    intro p q
    have hbase : Integrable (fun τ : ℝ => (PhiLoc (τ - c) : ℂ) *
        Complex.exp (-(τ * (u p - u q)) * Complex.I)) := by
      have h1 := Integrable.bdd_mul (c := 1) (PhiLoc_integrableC.comp_sub_right c)
        (by fun_prop :
          AEStronglyMeasurable (fun τ : ℝ => Complex.exp (-(τ * (u p - u q)) * Complex.I)) volume)
        (by
          filter_upwards with τ
          rw [Complex.norm_exp]
          simp)
      exact h1.congr (Filter.Eventually.of_forall (fun τ => mul_comm _ _))
    exact hbase.const_mul _
  have hpt : ∀ τ : ℝ, (PhiLoc (τ - c) : ℂ) * (F τ * (starRingEnd ℂ) (F τ))
      = ∑ p ∈ S, ∑ q ∈ S, (b p * (starRingEnd ℂ) (b q)) *
          ((PhiLoc (τ - c) : ℂ) * Complex.exp (-(τ * (u p - u q)) * Complex.I)) := by
    intro τ
    have hconj : (starRingEnd ℂ) (F τ)
        = ∑ n ∈ S, (starRingEnd ℂ) (b n) * Complex.exp ((τ * u n) * Complex.I) := by
      rw [hF, map_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [map_mul]
      congr 1
      rw [← Complex.exp_conj]
      congr 1
      simp
    rw [hF, hconj, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have h1 : (b p * Complex.exp (-(↑τ * ↑(u p)) * Complex.I))
        * ((starRingEnd ℂ) (b q) * Complex.exp (↑τ * ↑(u q) * Complex.I))
        = (b p * (starRingEnd ℂ) (b q)) *
          (Complex.exp (-(↑τ * ↑(u p)) * Complex.I) * Complex.exp (↑τ * ↑(u q) * Complex.I)) := by
      ring
    have harg : -(↑τ * ↑(u p)) * Complex.I + ↑τ * ↑(u q) * Complex.I
        = -(↑τ * (↑(u p) - ↑(u q))) * Complex.I := by ring
    rw [h1, ← Complex.exp_add, harg]
    ring
  have hFint : Integrable (fun τ : ℝ => (PhiLoc (τ - c) : ℂ) * (F τ * (starRingEnd ℂ) (F τ))) := by
    refine Integrable.mono' (g := fun τ : ℝ => (∑ n ∈ S, ‖b n‖) ^ 2 * PhiLoc (τ - c)) ?_ ?_ ?_
    · exact (PhiLoc_integrable.comp_sub_right c).const_mul _
    · exact ((Complex.continuous_ofReal.comp (PhiLoc_continuous.comp
          (continuous_id.sub continuous_const))).mul
        (hFcont.mul (Complex.continuous_conj.comp hFcont))).aestronglyMeasurable
    · filter_upwards with τ
      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
        Real.norm_of_nonneg (PhiLoc_nonneg _)]
      have h1 : ‖F τ‖ ^ 2 ≤ (∑ n ∈ S, ‖b n‖) ^ 2 := by
        have := hFnorm τ
        nlinarith [norm_nonneg (F τ), Finset.sum_nonneg (s := S) (fun n _ => norm_nonneg (b n))]
      nlinarith [PhiLoc_nonneg (τ - c)]
  have hwhole : ∫ τ : ℝ, PhiLoc (τ - c) * ‖F τ‖ ^ 2
      = (∑ p ∈ S, ∑ q ∈ S, (b p * (starRingEnd ℂ) (b q)) *
          (Complex.exp (-(c * (u p - u q)) * Complex.I) * (pairK (u p - u q) : ℂ))).re := by
    have hcomm : (∫ τ : ℝ, Complex.reCLM ((PhiLoc (τ - c) : ℂ) * (F τ * (starRingEnd ℂ) (F τ))))
        = (∫ τ : ℝ, (PhiLoc (τ - c) : ℂ) * (F τ * (starRingEnd ℂ) (F τ))).re := by
      rw [ContinuousLinearMap.integral_comp_comm Complex.reCLM hFint]
      simp only [Complex.reCLM_apply]
    have hA : ∫ τ : ℝ, PhiLoc (τ - c) * ‖F τ‖ ^ 2
        = (∫ τ : ℝ, (PhiLoc (τ - c) : ℂ) * (F τ * (starRingEnd ℂ) (F τ))).re := by
      rw [← hcomm]
      apply integral_congr_ae
      filter_upwards with τ
      simp only [Complex.reCLM_apply]
      simp only [Complex.mul_conj, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.normSq_eq_norm_sq]
      ring
    rw [hA]
    congr 1
    rw [funext hpt]
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [MeasureTheory.integral_finsetSum]
      · refine Finset.sum_congr rfl fun q _ => ?_
        rw [MeasureTheory.integral_const_mul]
        have hcast : ((↑(u p) - ↑(u q) : ℂ)) = ((u p - u q : ℝ) : ℂ) := by push_cast; ring
        rw [hcast, casdiv_l2_PhiLoc_fourier_shift]
      · intro q _; exact hInt p q
    · intro p _; exact integrable_finsetSum _ (fun q _ => hInt p q)
  have hbound : (∑ p ∈ S, ∑ q ∈ S, (b p * (starRingEnd ℂ) (b q)) *
        (Complex.exp (-(c * (u p - u q)) * Complex.I) * (pairK (u p - u q) : ℂ))).re
      ≤ ∑ p ∈ S, ∑ q ∈ S, ‖b p‖ * ‖b q‖ * pairK (u p - u q) := by
    refine (Complex.re_le_norm _).trans ?_
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    have hExpNorm : ‖Complex.exp (-(↑c * (↑(u p) - ↑(u q))) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    rw [norm_mul, norm_mul, Complex.norm_mul, Complex.norm_conj, hExpNorm, Complex.norm_real,
      Real.norm_of_nonneg (pairK_nonneg _), one_mul]
  have hstep1 : ∫ τ in c..(c+1), ‖F τ‖ ^ 2
      ≤ (1 / phiDelta) * ∫ τ in c..(c+1), PhiLoc (τ - c) * ‖F τ‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hcc
    · exact (hFcont.norm.pow 2).intervalIntegrable _ _
    · exact (continuous_const.mul ((PhiLoc_continuous.comp (continuous_id.sub continuous_const)).mul
        (hFcont.norm.pow 2))).intervalIntegrable _ _
    · intro τ hτ
      have h1 : phiDelta ≤ PhiLoc (τ - c) :=
        phiDelta_le_PhiLoc ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      have h2 : (1:ℝ) ≤ (1 / phiDelta) * PhiLoc (τ - c) := by
        rw [show (1 / phiDelta) * PhiLoc (τ - c) = PhiLoc (τ - c) / phiDelta by ring]
        rw [le_div_iff₀ hδ]
        simpa using h1
      calc ‖F τ‖ ^ 2 = 1 * ‖F τ‖ ^ 2 := by ring
        _ ≤ ((1 / phiDelta) * PhiLoc (τ - c)) * ‖F τ‖ ^ 2 :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = (1 / phiDelta) * (PhiLoc (τ - c) * ‖F τ‖ ^ 2) := by ring
  have hstep2 : ∫ τ in c..(c+1), PhiLoc (τ - c) * ‖F τ‖ ^ 2
      ≤ ∫ τ : ℝ, PhiLoc (τ - c) * ‖F τ‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hcc]
    refine setIntegral_le_integral ?_ ?_
    · have h1 : Integrable (fun τ : ℝ => ‖F τ‖ ^ 2 * PhiLoc (τ - c)) :=
        Integrable.bdd_mul (c := (∑ n ∈ S, ‖b n‖) ^ 2)
          (PhiLoc_integrable.comp_sub_right c)
          (by fun_prop : AEStronglyMeasurable (fun τ : ℝ => ‖F τ‖ ^ 2) volume)
          (by
            filter_upwards with τ
            rw [Real.norm_of_nonneg (by positivity)]
            have := hFnorm τ
            nlinarith [norm_nonneg (F τ), Finset.sum_nonneg (s := S) (fun n _ => norm_nonneg (b n))])
      exact h1.congr (Filter.Eventually.of_forall (fun τ => by ring))
    · filter_upwards with τ
      exact mul_nonneg (PhiLoc_nonneg _) (by positivity)
  calc ∫ τ in c..(c+1), ‖F τ‖ ^ 2
      ≤ (1 / phiDelta) * ∫ τ in c..(c+1), PhiLoc (τ - c) * ‖F τ‖ ^ 2 := hstep1
    _ ≤ (1 / phiDelta) * ∫ τ : ℝ, PhiLoc (τ - c) * ‖F τ‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hstep2 (by positivity)
    _ = (1 / phiDelta) * (∑ p ∈ S, ∑ q ∈ S, (b p * (starRingEnd ℂ) (b q)) *
          (Complex.exp (-(c * (u p - u q)) * Complex.I) * (pairK (u p - u q) : ℂ))).re := by
        rw [hwhole]
    _ ≤ (1 / phiDelta) * ∑ p ∈ S, ∑ q ∈ S, ‖b p‖ * ‖b q‖ * pairK (u p - u q) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)

/-- The norm of the coefficient of a prime `n` in `Ψ₁`. -/
lemma casdiv_l2_coeff_norm_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (α : ℝ) {n : ℕ} (hn : n.Prime) :
    ‖-((f n * (Real.log n : ℂ)) * (((n : ℝ) ^ (-(1 + α)) : ℝ) : ℂ))‖
      ≤ Real.log n / (n : ℝ) ^ (1 + α) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by
    have : 0 < n := hn.pos
    exact_mod_cast this
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by
    have : 1 ≤ n := hn.one_le
    exact_mod_cast this
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hmain : ‖-((f n * (Real.log n : ℂ)) * (((n : ℝ) ^ (-(1 + α)) : ℝ) : ℂ))‖
      = ‖f n‖ * Real.log n * (n : ℝ) ^ (-(1 + α)) := by
    simp only [norm_neg, norm_mul, Complex.norm_real]
    rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg (Real.rpow_nonneg hnpos.le _)]
  rw [hmain, Real.rpow_neg hnpos.le, div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc ‖f n‖ * Real.log n ≤ 1 * Real.log n := mul_le_mul_of_nonneg_right (hf n) hlog
    _ = Real.log n := one_mul _

/-- Summability of the weights `log n / n^{1+α}` (over all `n`). -/
lemma casdiv_l2_summable_log_div_rpow (α : ℝ) (hα : 0 < α) :
    Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ (1 + α)) := by
  have hα2 : (0:ℝ) < α / 2 := by linarith
  have hα1 : (1:ℝ) + α ≠ 0 := by linarith
  have hα2' : (1:ℝ) + α / 2 ≠ 0 := by linarith
  have hnonneg : ∀ n : ℕ, 0 ≤ Real.log n / (n : ℝ) ^ (1 + α) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      rw [Nat.cast_zero, Real.log_zero, Real.zero_rpow hα1, div_zero]
    · have hn1 : (1:ℝ) ≤ (n:ℝ) := by
        have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        exact_mod_cast this
      exact div_nonneg (Real.log_nonneg hn1) (by positivity)
  refine Summable.of_nonneg_of_le hnonneg (fun n => ?_)
    (Summable.mul_left (2 / α)
      ((Real.summable_nat_rpow_inv (p := 1 + α / 2)).mpr (by linarith)))
  by_cases hn : n = 0
  · subst hn
    rw [Nat.cast_zero, Real.log_zero, Real.zero_rpow hα1, div_zero, Real.zero_rpow hα2',
      inv_zero, mul_zero]
  · have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hlog := Real.log_le_rpow_div hn0.le hα2
    have hkey : ((n:ℝ) ^ (α/2) / (α/2)) / (n : ℝ) ^ (1 + α)
        = (2 / α) * ((n : ℝ) ^ (1 + α / 2))⁻¹ := by
      have h1 : (n:ℝ)^(1+α) = (n:ℝ)^(α/2) * (n:ℝ)^(1+α/2) := by
        rw [← Real.rpow_add hn0]; congr 1; ring
      rw [h1]
      field_simp
    calc Real.log n / (n : ℝ) ^ (1 + α)
        ≤ ((n:ℝ) ^ (α/2) / (α/2)) / (n : ℝ) ^ (1 + α) :=
          div_le_div_of_nonneg_right hlog (by positivity)
      _ = (2 / α) * ((n : ℝ) ^ (1 + α / 2))⁻¹ := hkey

/-- Nonnegativity of the weight `log n / n^{1+α}`. -/
lemma casdiv_l2_log_div_rpow_nonneg (α : ℝ) (hα : 0 < α) (n : ℕ) :
    0 ≤ Real.log n / (n : ℝ) ^ (1 + α) := by
  by_cases hn : n = 0
  · subst hn
    rw [Nat.cast_zero, Real.log_zero, Real.zero_rpow (by linarith : (1:ℝ) + α ≠ 0), div_zero]
  · have hn1 : (1:ℝ) ≤ (n:ℝ) := by
      have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      exact_mod_cast this
    exact div_nonneg (Real.log_nonneg hn1) (by positivity)

/-- The double sum of the pair kernel over primes is at most `C₁ * C₂ / α`. -/
lemma casdiv_l2_prime_double_sum_le (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁)
    (hloc : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ p : ℕ, p.Prime →
      (∑' q : ℕ, (if q.Prime then
        Real.log q / (q : ℝ) ^ (1 + α) * pairK (Real.log p - Real.log q) else 0))
        ≤ C₁ * (p : ℝ) ^ (-α))
    (htot : ∀ (β : ℝ), 0 < β → β ≤ 2 →
      (∑' p : ℕ, (if p.Prime then Real.log p / (p : ℝ) ^ (1 + β) else 0)) ≤ C₂ / β)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (S T : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hT : ∀ q ∈ T, q.Prime) :
    ∑ p ∈ S, ∑ q ∈ T, (Real.log p / (p : ℝ) ^ (1 + α)) * (Real.log q / (q : ℝ) ^ (1 + α))
        * pairK (Real.log p - Real.log q) ≤ C₁ * C₂ / α := by
  have hsumm_w : Summable (fun n : ℕ => if n.Prime then Real.log n / (n:ℝ)^(1+α) else 0) := by
    have h1 : ∀ n : ℕ, 0 ≤ (if n.Prime then Real.log n / (n:ℝ)^(1+α) else 0) := by
      intro n
      by_cases hn : n.Prime
      · rw [if_pos hn]; exact casdiv_l2_log_div_rpow_nonneg α hα0 n
      · rw [if_neg hn]
    have h2 : ∀ n : ℕ, (if n.Prime then Real.log n / (n:ℝ)^(1+α) else 0)
        ≤ Real.log n / (n:ℝ)^(1+α) := by
      intro n
      by_cases hn : n.Prime
      · rw [if_pos hn]
      · rw [if_neg hn]; exact casdiv_l2_log_div_rpow_nonneg α hα0 n
    exact Summable.of_nonneg_of_le h1 h2 (casdiv_l2_summable_log_div_rpow α hα0)
  have hsumm_pk : ∀ p : ℕ, Summable (fun q : ℕ =>
      if q.Prime then Real.log q / (q:ℝ)^(1+α) * pairK (Real.log p - Real.log q) else 0) := by
    intro p
    have h1 : ∀ q : ℕ, 0 ≤ (if q.Prime then
        Real.log q / (q:ℝ)^(1+α) * pairK (Real.log p - Real.log q) else 0) := by
      intro q
      by_cases hq : q.Prime
      · rw [if_pos hq]
        exact mul_nonneg (casdiv_l2_log_div_rpow_nonneg α hα0 q) (pairK_nonneg _)
      · rw [if_neg hq]
    have h2 : ∀ q : ℕ, (if q.Prime then
        Real.log q / (q:ℝ)^(1+α) * pairK (Real.log p - Real.log q) else 0)
        ≤ (if q.Prime then Real.log q / (q:ℝ)^(1+α) else 0) := by
      intro q
      by_cases hq : q.Prime
      · rw [if_pos hq, if_pos hq]
        exact mul_le_of_le_one_right (casdiv_l2_log_div_rpow_nonneg α hα0 q) (pairK_le_one _)
      · rw [if_neg hq, if_neg hq]
    exact Summable.of_nonneg_of_le h1 h2 hsumm_w
  have hinner : ∀ p ∈ S, ∑ q ∈ T, (Real.log q / (q:ℝ)^(1+α)) * pairK (Real.log p - Real.log q)
      ≤ C₁ * (p:ℝ)^(-α) := by
    intro p hp
    have h1 : ∑ q ∈ T, (Real.log q / (q:ℝ)^(1+α)) * pairK (Real.log p - Real.log q)
        ≤ ∑' q : ℕ, (if q.Prime then
            Real.log q / (q:ℝ)^(1+α) * pairK (Real.log p - Real.log q) else 0) := by
      calc ∑ q ∈ T, (Real.log q / (q:ℝ)^(1+α)) * pairK (Real.log p - Real.log q)
          ≤ ∑ q ∈ T, (if q.Prime then
              Real.log q / (q:ℝ)^(1+α) * pairK (Real.log p - Real.log q) else 0) := by
            refine Finset.sum_le_sum fun q hq => ?_
            rw [if_pos (hT q hq)]
        _ ≤ ∑' q : ℕ, (if q.Prime then
              Real.log q / (q:ℝ)^(1+α) * pairK (Real.log p - Real.log q) else 0) := by
            refine Summable.sum_le_tsum _ (fun q hq => ?_) (hsumm_pk p)
            by_cases hq' : q.Prime
            · rw [if_pos hq']
              exact mul_nonneg (casdiv_l2_log_div_rpow_nonneg α hα0 q) (pairK_nonneg _)
            · rw [if_neg hq']
    exact h1.trans (hloc α hα0 hα1 p (hS p hp))
  have hlast : ∑ p ∈ S, (Real.log p / (p:ℝ)^(1+α)) * (p:ℝ)^(-α) ≤ C₂ / α := by
    have hstep : ∑ p ∈ S, (Real.log p / (p:ℝ)^(1+α)) * (p:ℝ)^(-α)
        ≤ ∑ p ∈ S, Real.log p / (p:ℝ)^(1+α) := by
      refine Finset.sum_le_sum fun p hp => ?_
      have hpp : (1:ℝ) ≤ (p:ℝ) := by
        have : 1 ≤ p := (hS p hp).one_le
        exact_mod_cast this
      have hpw : 0 ≤ Real.log p / (p:ℝ) ^ (1 + α) := casdiv_l2_log_div_rpow_nonneg α hα0 p
      have hpm : (p:ℝ)^(-α) ≤ 1 := by
        rw [Real.rpow_neg (by linarith : (0:ℝ) ≤ (p:ℝ))]
        refine inv_le_one_of_one_le₀ ?_
        calc (1:ℝ) = (1:ℝ) ^ α := (Real.one_rpow α).symm
          _ ≤ (p:ℝ) ^ α := Real.rpow_le_rpow (by norm_num) hpp hα0.le
      calc (Real.log p / (p:ℝ) ^ (1 + α)) * (p:ℝ)^(-α)
          ≤ (Real.log p / (p:ℝ) ^ (1 + α)) * 1 := mul_le_mul_of_nonneg_left hpm hpw
        _ = Real.log p / (p:ℝ) ^ (1 + α) := mul_one _
    have hstep2 : ∑ p ∈ S, Real.log p / (p:ℝ)^(1+α)
        ≤ ∑' p : ℕ, (if p.Prime then Real.log p / (p:ℝ)^(1+α) else 0) := by
      calc ∑ p ∈ S, Real.log p / (p:ℝ)^(1+α)
          ≤ ∑ p ∈ S, (if p.Prime then Real.log p / (p:ℝ)^(1+α) else 0) := by
            refine Finset.sum_le_sum fun p hp => ?_
            rw [if_pos (hS p hp)]
        _ ≤ ∑' p : ℕ, (if p.Prime then Real.log p / (p:ℝ)^(1+α) else 0) := by
            refine Summable.sum_le_tsum _ (fun p hp => ?_) hsumm_w
            by_cases hp' : p.Prime
            · rw [if_pos hp']
              exact casdiv_l2_log_div_rpow_nonneg α hα0 p
            · rw [if_neg hp']
    exact (hstep.trans hstep2).trans (htot α hα0 (by linarith))
  calc ∑ p ∈ S, ∑ q ∈ T, (Real.log p / (p : ℝ) ^ (1 + α)) * (Real.log q / (q : ℝ) ^ (1 + α))
        * pairK (Real.log p - Real.log q)
      = ∑ p ∈ S, (Real.log p / (p:ℝ)^(1+α)) *
          ∑ q ∈ T, (Real.log q / (q:ℝ)^(1+α)) * pairK (Real.log p - Real.log q) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun q hq => by ring
    _ ≤ ∑ p ∈ S, (Real.log p / (p:ℝ)^(1+α)) * (C₁ * (p:ℝ)^(-α)) := by
        refine Finset.sum_le_sum fun p hp => ?_
        exact mul_le_mul_of_nonneg_left (hinner p hp) (casdiv_l2_log_div_rpow_nonneg α hα0 p)
    _ = C₁ * ∑ p ∈ S, (Real.log p / (p:ℝ)^(1+α)) * (p:ℝ)^(-α) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun p hp => by ring
    _ ≤ C₁ * (C₂ / α) := mul_le_mul_of_nonneg_left hlast hC₁
    _ = C₁ * C₂ / α := by ring

/-- The oscillation has unit modulus. -/
lemma casdiv_l2_norm_exp_neg_mul_I (τ x : ℝ) : ‖Complex.exp (-(τ * x) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  have h2 : (-(↑τ * ↑x) * Complex.I).re = 0 := by simp
  rw [h2, Real.exp_zero]

/-- Reindexing the partial sums of a series supported on the primes. -/
lemma casdiv_l2_tendsto_sum_primesBelow (h : ℕ → ℂ) (h0 : ∀ n, ¬ n.Prime → h n = 0) (hs : Summable h) :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Nat.primesBelow N, h n) Filter.atTop (𝓝 (∑' n, h n)) := by
  have h1 : ∀ N : ℕ, ∑ n ∈ Nat.primesBelow N, h n = ∑ n ∈ Finset.range N, h n := by
    intro N
    rw [Nat.primesBelow_eq_filter_range, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : n.Prime
    · rw [if_pos hn]
    · rw [if_neg hn, h0 n hn]
  rw [funext h1]
  exact hs.hasSum.tendsto_sum_nat

/-- The L² window bound for `Ψ₁` on the line `Re s = 1+α`: for a `1`-bounded `f`, every unit
window integral of `‖Ψ₁ f (1+α+iτ)‖²` is at most `C/α` for `0 < α ≤ 1`.

This is the statement of `Submission.Work.BMF.mrlas.Psi1_L2_bound`, proved here as a *fresh*
self-contained module: the proof adapts the one in `Submission.Work.BMF.Psi1_L2_bound`
(whose hypotheses `Work.BMF.Psi1_L2_local_mass` and `Work.BMF.Psi1_L2_total_mass` are
sorry-free), so that no `sorry` is used anywhere in the dependency cone. -/
theorem casdiv_psi1_l2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) →
      ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ c : ℝ,
        (∫ τ in c..(c+1), ‖Work.BMF.Psi1 f ((((1+α : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)
          ≤ C / α := by
  obtain ⟨C₁, hC₁pos, hloc⟩ := Work.BMF.Psi1_L2_local_mass
  obtain ⟨C₂, hC₂pos, htot⟩ := Work.BMF.Psi1_L2_total_mass
  refine ⟨(1 / phiDelta) * (C₁ * C₂), ?_, ?_⟩
  · exact mul_pos (div_pos one_pos phiDelta_pos) (mul_pos hC₁pos hC₂pos)
  · intro f hf α hα0 hα1 c
    set b : ℕ → ℂ := fun n => if n.Prime then
        -((f n * (Real.log n : ℂ)) * (((n : ℝ) ^ (-(1 + α)) : ℝ) : ℂ)) else 0 with hb
    set g : ℕ → ℝ → ℂ := fun n τ => b n * Complex.exp (-(τ * Real.log n) * Complex.I) with hg
    have hb0 : ∀ n, ¬ n.Prime → b n = 0 := by
      intro n hn; rw [hb]; simp [hn]
    have hbnorm : ∀ n, ‖b n‖ ≤ if n.Prime then Real.log n / (n:ℝ)^(1+α) else 0 := by
      intro n
      by_cases hn : n.Prime
      · rw [hb]; simp only [if_pos hn]
        exact casdiv_l2_coeff_norm_le f hf α hn
      · rw [hb]; simp only [if_neg hn, norm_zero, le_refl]
    have hsumm_w : Summable (fun n : ℕ => if n.Prime then Real.log n / (n:ℝ)^(1+α) else 0) := by
      have h1 : ∀ n : ℕ, 0 ≤ (if n.Prime then Real.log n / (n:ℝ)^(1+α) else 0) := by
        intro n
        by_cases hn : n.Prime
        · rw [if_pos hn]; exact casdiv_l2_log_div_rpow_nonneg α hα0 n
        · rw [if_neg hn]
      have h2 : ∀ n : ℕ, (if n.Prime then Real.log n / (n:ℝ)^(1+α) else 0)
          ≤ Real.log n / (n:ℝ)^(1+α) := by
        intro n
        by_cases hn : n.Prime
        · rw [if_pos hn]
        · rw [if_neg hn]; exact casdiv_l2_log_div_rpow_nonneg α hα0 n
      exact Summable.of_nonneg_of_le h1 h2 (casdiv_l2_summable_log_div_rpow α hα0)
    have hsumm_b : Summable (fun n => ‖b n‖) :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbnorm hsumm_w
    have hboundN : ∀ N : ℕ, ∫ τ in c..(c+1), ‖∑ n ∈ Nat.primesBelow N, g n τ‖ ^ 2
        ≤ (1 / phiDelta) * (C₁ * C₂) / α := by
      intro N
      have h1 := casdiv_l2_finite_osc_L2_le (Nat.primesBelow N) b (fun n => Real.log n) c
      have h2 : ∑ p ∈ Nat.primesBelow N, ∑ q ∈ Nat.primesBelow N,
          ‖b p‖ * ‖b q‖ * pairK (Real.log p - Real.log q)
          ≤ ∑ p ∈ Nat.primesBelow N, ∑ q ∈ Nat.primesBelow N,
            (Real.log p / (p:ℝ)^(1+α)) * (Real.log q / (q:ℝ)^(1+α))
              * pairK (Real.log p - Real.log q) := by
        refine Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => ?_
        have hpw : ‖b p‖ ≤ Real.log p / (p:ℝ)^(1+α) := by
          have h := hbnorm p
          rwa [if_pos (Nat.mem_primesBelow.mp hp).2] at h
        have hqw : ‖b q‖ ≤ Real.log q / (q:ℝ)^(1+α) := by
          have h := hbnorm q
          rwa [if_pos (Nat.mem_primesBelow.mp hq).2] at h
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hpw hqw (norm_nonneg _) (casdiv_l2_log_div_rpow_nonneg α hα0 p)) (pairK_nonneg _)
      have h3 := casdiv_l2_prime_double_sum_le C₁ C₂ hC₁pos.le hloc htot hα0 hα1 (Nat.primesBelow N)
        (Nat.primesBelow N) (fun p hp => (Nat.mem_primesBelow.mp hp).2)
        (fun q hq => (Nat.mem_primesBelow.mp hq).2)
      calc ∫ τ in c..(c+1), ‖∑ n ∈ Nat.primesBelow N, g n τ‖ ^ 2
          = ∫ τ in c..(c+1),
              ‖∑ n ∈ Nat.primesBelow N, b n * Complex.exp (-(τ * Real.log n) * Complex.I)‖ ^ 2 := by
            simp only [hg]
        _ ≤ (1 / phiDelta) * ∑ p ∈ Nat.primesBelow N, ∑ q ∈ Nat.primesBelow N,
              ‖b p‖ * ‖b q‖ * pairK (Real.log p - Real.log q) := h1
        _ ≤ (1 / phiDelta) * (C₁ * C₂ / α) := by
            refine mul_le_mul_of_nonneg_left ?_ (by have := phiDelta_pos; positivity)
            exact h2.trans h3
        _ = (1 / phiDelta) * (C₁ * C₂) / α := by ring
    have hconv : ∀ τ : ℝ, Filter.Tendsto (fun N : ℕ => ‖∑ n ∈ Nat.primesBelow N, g n τ‖ ^ 2)
        Filter.atTop
        (𝓝 (‖Work.BMF.Psi1 f ((((1+α : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)) := by
      intro τ
      have hψ : Work.BMF.Psi1 f ((((1+α : ℝ)) : ℂ) + (τ : ℂ) * Complex.I) = ∑' n, g n τ := by
        rw [Psi1_L2_psi_rewrite f α τ]
        refine tsum_congr fun n => ?_
        by_cases hn : n.Prime
        · simp only [hg, hb, if_pos hn]
        · simp only [hg, hb, if_neg hn, zero_mul]
      have hsum : Filter.Tendsto (fun N : ℕ => ∑ n ∈ Nat.primesBelow N, g n τ) Filter.atTop
          (𝓝 (∑' n, g n τ)) := by
        refine casdiv_l2_tendsto_sum_primesBelow _ (fun n hn => ?_) ?_
        · simp only [hg, hb, if_neg hn, zero_mul]
        · refine Summable.of_norm ?_
          have hnorm : (fun n => ‖g n τ‖) = fun n => ‖b n‖ := by
            funext n
            simp only [hg, norm_mul, casdiv_l2_norm_exp_neg_mul_I (τ) (Real.log n), mul_one, le_refl]
          rw [hnorm]; exact hsumm_b
      rw [hψ]
      exact (hsum.norm.pow 2)
    have hmeasc : ∀ N : ℕ,
        AEStronglyMeasurable (fun τ : ℝ => ‖∑ n ∈ Nat.primesBelow N, g n τ‖ ^ 2)
          (volume.restrict (Set.Ioc c (c+1))) := by
      intro N
      have hcont : Continuous fun τ : ℝ => ‖∑ n ∈ Nat.primesBelow N, g n τ‖ ^ 2 :=
        (((continuous_finsetSum _ fun n hn => by
          rw [hg]
          exact continuous_const.mul (Complex.continuous_exp.comp (by fun_prop)))).norm).pow 2
      exact hcont.aestronglyMeasurable
    have hbdd : ∀ N : ℕ, ∀ᵐ τ ∂(volume.restrict (Set.Ioc c (c+1))),
        ‖‖∑ n ∈ Nat.primesBelow N, g n τ‖ ^ 2‖ ≤ (∑' n, ‖b n‖) ^ 2 := by
      intro N
      filter_upwards with τ
      rw [Real.norm_of_nonneg (by positivity)]
      have h1 : ‖∑ n ∈ Nat.primesBelow N, g n τ‖ ≤ ∑' n, ‖b n‖ := by
        refine ((norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)).trans
          (Summable.sum_le_tsum _ (fun n hn => norm_nonneg _) hsumm_b)
        simp only [hg, norm_mul, casdiv_l2_norm_exp_neg_mul_I (τ) (Real.log n), mul_one, le_refl]
      nlinarith [norm_nonneg (∑ n ∈ Nat.primesBelow N, g n τ), h1]
    have hint : Integrable (fun _ : ℝ => (∑' n, ‖b n‖) ^ 2)
        (volume.restrict (Set.Ioc c (c+1))) :=
      integrableOn_const (s := Set.Ioc c (c+1)) (μ := volume) (C := (∑' n, ‖b n‖) ^ 2)
        measure_Ioc_lt_top.ne (by simp)
    have hDCT := MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := volume.restrict (Set.Ioc c (c+1)))
      (F := fun N τ => ‖∑ n ∈ Nat.primesBelow N, g n τ‖ ^ 2)
      (f := fun τ => ‖Work.BMF.Psi1 f ((((1+α : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)
      (fun _ => (∑' n, ‖b n‖) ^ 2) hmeasc hint hbdd (Filter.Eventually.of_forall hconv)
    have hfinal : (∫ τ, ‖Work.BMF.Psi1 f ((((1+α : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2
        ∂(volume.restrict (Set.Ioc c (c+1)))) ≤ (1 / phiDelta) * (C₁ * C₂) / α :=
      le_of_tendsto_of_tendsto' hDCT tendsto_const_nhds (fun N =>
        by simpa only [intervalIntegral.integral_of_le (by linarith : c ≤ c + 1)]
          using hboundN N)
    rw [intervalIntegral.integral_of_le (by linarith : c ≤ c + 1)]
    exact hfinal

end

end Work.BMF.mrlas

