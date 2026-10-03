import Mathlib
import Submission.Work.KMTAreas.A7.randSymbG_aux
import Submission.Work.KMTAreas.A7.diffSymbol_contDiff_deriv
import Submission.Work.Analysis.CzShift.Main
import Submission.Work.Analysis.CzShift.exists_isCZSeed_of_fourierInv
import Submission.Work.BourgainPlan.Maximal.main_narrow_taoSetS
import Submission.Work.BourgainPlan.Maximal.mikhlinConvolutionLp

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open Finset Polynomial
open scoped BigOperators

noncomputable section

/-! ## Elementary estimates used by `Work.KMTAreas.A7.randSymbG_mikhlin`

This module collects the analytic ingredients of the Mikhlin bound for the randomised `g`-side
symbol: elementary estimates for the character `ee`, the first two derivatives of a modulated bump,
Abel summation with bounded partial sums, and the pointwise bounds for a single modulated bump.
They are separated from the main file to keep each module's elaboration small.
-/
/-- The character `ee` has unit modulus. -/
lemma rSG_norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  have h : ee x = Complex.exp (Complex.I * (((2 * Real.pi * x : ℝ)) : ℂ)) := by
    rw [ee]; congr 1; push_cast; ring
  rw [h, Complex.norm_exp_I_mul_ofReal]

/-- `‖e(x) - 1‖ ≤ 2π|x|`. -/
lemma rSG_norm_ee_sub_one_le (x : ℝ) : ‖ee x - 1‖ ≤ 2 * Real.pi * |x| := by
  have h : ee x = Complex.exp (Complex.I * (((2 * Real.pi * x : ℝ)) : ℂ)) := by
    rw [ee]; congr 1; push_cast; ring
  rw [h, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul]
  have hsin : |Real.sin ((2 * Real.pi * x) / 2)| ≤ Real.pi * |x| := by
    have h1 : |Real.sin (Real.pi * x)| ≤ |Real.pi * x| := Real.abs_sin_le_abs
    rw [show (2 * Real.pi * x) / 2 = Real.pi * x by ring]
    rwa [abs_mul, abs_of_pos Real.pi_pos] at h1
  calc |(2 : ℝ)| * |Real.sin ((2 * Real.pi * x) / 2)|
      = 2 * |Real.sin ((2 * Real.pi * x) / 2)| := by norm_num
    _ ≤ 2 * (Real.pi * |x|) := by linarith
    _ = 2 * Real.pi * |x| := by ring

/-- `‖e(x) - e(y)‖ ≤ 2π|x - y|`. -/
lemma rSG_norm_ee_sub_le (x y : ℝ) : ‖ee x - ee y‖ ≤ 2 * Real.pi * |x - y| := by
  have h1 : ee x - ee y = ee y * (ee (x - y) - 1) := by
    have : ee x = ee y * ee (x - y) := by
      rw [ee, ee, ee, ← Complex.exp_add]; congr 1; push_cast; ring
    rw [this]; ring
  rw [h1, norm_mul, rSG_norm_ee, one_mul]
  exact rSG_norm_ee_sub_one_le (x - y)

/-- The derivative of `x ↦ e(c x)`. -/
lemma rSG_hasDerivAt_ee_comp (c ξ : ℝ) :
    HasDerivAt (fun x : ℝ => ee (c * x)) ((2 * Real.pi * Complex.I * (c : ℂ)) * ee (c * ξ)) ξ := by
  have h := hasDerivAt_expLin c ξ
  simpa [ee] using h

/-- `‖2πi·a‖ = 2π|a|`. -/
lemma rSG_norm_two_pi_I_mul (a : ℝ) :
    ‖(2 * Real.pi * Complex.I * (a : ℂ))‖ = 2 * Real.pi * |a| := by
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [show (2 * Real.pi * Complex.I * (a : ℂ)) = (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (a : ℂ)
    by ring]
  rw [norm_mul, norm_mul, norm_mul, h2, hpi, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
  ring

/-! ## Derivatives of a modulated bump `x ↦ g (σ x) * e (c x)` -/

/-- **First and second derivative of a modulated bump.**  If `g` is differentiable on `ℝ` with
`deriv g` differentiable on `ℝ`, then `x ↦ g (σ x) e (c x)` has the expected first and second
derivatives. -/
lemma rSG_deriv_modulatedBump_p {g : ℝ → ℂ} (hgd : ∀ u : ℝ, HasDerivAt g (deriv g u) u)
    (hgd2 : ∀ u : ℝ, HasDerivAt (deriv g) (iteratedDeriv 2 g u) u) (σ c : ℝ) :
    (∀ ξ : ℝ, HasDerivAt (fun x : ℝ => g (σ * x) * ee (c * x))
        ((σ * deriv g (σ * ξ) + (2 * Real.pi * Complex.I * (c : ℂ)) * g (σ * ξ)) * ee (c * ξ)) ξ) ∧
    (∀ ξ : ℝ, HasDerivAt
        (fun x : ℝ => (σ * deriv g (σ * x) + (2 * Real.pi * Complex.I * (c : ℂ)) * g (σ * x))
          * ee (c * x))
        ((σ^2 * iteratedDeriv 2 g (σ * ξ)
          + 2 * (2 * Real.pi * Complex.I * (c : ℂ)) * (σ * deriv g (σ * ξ))
          + (2 * Real.pi * Complex.I * (c : ℂ))^2 * g (σ * ξ)) * ee (c * ξ)) ξ) ∧
    (∀ ξ : ℝ, deriv (fun x : ℝ => g (σ * x) * ee (c * x)) ξ
        = (σ * deriv g (σ * ξ) + (2 * Real.pi * Complex.I * (c : ℂ)) * g (σ * ξ)) * ee (c * ξ)) ∧
    (∀ ξ : ℝ, iteratedDeriv 2 (fun x : ℝ => g (σ * x) * ee (c * x)) ξ =
        ((σ^2 * iteratedDeriv 2 g (σ * ξ)
          + 2 * (2 * Real.pi * Complex.I * (c : ℂ)) * (σ * deriv g (σ * ξ))
          + (2 * Real.pi * Complex.I * (c : ℂ))^2 * g (σ * ξ)) * ee (c * ξ))) := by
  have h1st : ∀ ξ : ℝ, HasDerivAt (fun x : ℝ => g (σ * x) * ee (c * x))
      ((σ * deriv g (σ * ξ) + (2 * Real.pi * Complex.I * (c : ℂ)) * g (σ * ξ)) * ee (c * ξ)) ξ := by
    intro ξ
    have hA : HasDerivAt (fun x : ℝ => g (σ * x)) (σ * deriv g (σ * ξ)) ξ :=
      hasDerivAt_eta_comp hgd σ ξ
    have hB := rSG_hasDerivAt_ee_comp c ξ
    have hmul := hA.mul hB
    have he : (σ * deriv g (σ * ξ)) * ee (c * ξ)
        + g (σ * ξ) * ((2 * Real.pi * Complex.I * (c : ℂ)) * ee (c * ξ))
        = (σ * deriv g (σ * ξ) + (2 * Real.pi * Complex.I * (c : ℂ)) * g (σ * ξ)) * ee (c * ξ) := by
      ring
    rwa [he] at hmul
  have h2nd : ∀ ξ : ℝ, HasDerivAt
      (fun x : ℝ => (σ * deriv g (σ * x) + (2 * Real.pi * Complex.I * (c : ℂ)) * g (σ * x))
        * ee (c * x))
      ((σ^2 * iteratedDeriv 2 g (σ * ξ)
        + 2 * (2 * Real.pi * Complex.I * (c : ℂ)) * (σ * deriv g (σ * ξ))
        + (2 * Real.pi * Complex.I * (c : ℂ))^2 * g (σ * ξ)) * ee (c * ξ)) ξ := by
    intro ξ
    have hA' : HasDerivAt (fun y : ℝ => σ * deriv g (σ * y))
        (σ * (σ * iteratedDeriv 2 g (σ * ξ))) ξ :=
      hasDerivAt_derivEta_comp hgd2 σ ξ
    have hB' : HasDerivAt (fun y : ℝ => (2 * Real.pi * Complex.I * (c : ℂ)) * g (σ * y))
        ((2 * Real.pi * Complex.I * (c : ℂ)) * (σ * deriv g (σ * ξ))) ξ :=
      (hasDerivAt_eta_comp hgd σ ξ).const_mul _
    have hsum : HasDerivAt
        (fun y : ℝ => σ * deriv g (σ * y) + (2 * Real.pi * Complex.I * (c : ℂ)) * g (σ * y))
        (σ * (σ * iteratedDeriv 2 g (σ * ξ))
          + (2 * Real.pi * Complex.I * (c : ℂ)) * (σ * deriv g (σ * ξ))) ξ :=
      hA'.add hB'
    have hprod := hsum.mul (rSG_hasDerivAt_ee_comp c ξ)
    have he : (σ * (σ * iteratedDeriv 2 g (σ * ξ))
          + (2 * Real.pi * Complex.I * (c : ℂ)) * (σ * deriv g (σ * ξ))) * ee (c * ξ)
        + (σ * deriv g (σ * ξ) + (2 * Real.pi * Complex.I * (c : ℂ)) * g (σ * ξ))
          * ((2 * Real.pi * Complex.I * (c : ℂ)) * ee (c * ξ))
        = ((σ^2 * iteratedDeriv 2 g (σ * ξ)
          + 2 * (2 * Real.pi * Complex.I * (c : ℂ)) * (σ * deriv g (σ * ξ))
          + (2 * Real.pi * Complex.I * (c : ℂ))^2 * g (σ * ξ)) * ee (c * ξ)) := by
      ring
    rwa [he] at hprod
  refine ⟨h1st, h2nd, fun ξ => (h1st ξ).deriv, ?_⟩
  intro ξ
  have hfun : deriv (fun x : ℝ => g (σ * x) * ee (c * x))
      = fun x : ℝ => (σ * deriv g (σ * x) + (2 * Real.pi * Complex.I * (c : ℂ)) * g (σ * x))
        * ee (c * x) := funext fun x => (h1st x).deriv
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hfun]
  exact (h2nd ξ).deriv

/-! ## Abel summation with bounded partial sums -/

/-- **Abel summation with a bounded partial-sum hypothesis.**  If all the partial sums
`∑_{m ≤ v} c m` are bounded by `4`, then `∑_{i ≤ N} c i * z i` is bounded by `4‖z N‖` plus
`4` times the total variation `∑_{i<N}‖z (i+1) - z i‖`. -/
lemma rSG_abel_sum_bound (N : ℕ) (c z : ℕ → ℂ)
    (hc : ∀ v : ℕ, ‖∑ m ∈ Finset.range (v + 1), c m‖ ≤ 4) :
    ‖∑ i ∈ Finset.range (N + 1), c i * z i‖
      ≤ 4 * ‖z N‖ + 4 * ∑ i ∈ Finset.range N, ‖z (i + 1) - z i‖ := by
  have h := Finset.sum_range_by_parts (f := fun i : ℕ => z i) (g := c) (n := N + 1)
  simp only [Nat.add_sub_cancel, smul_eq_mul] at h
  have hcomm : ∑ i ∈ Finset.range (N + 1), c i * z i
      = ∑ i ∈ Finset.range (N + 1), z i * c i :=
    Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have h1 : ‖z N * (∑ i ∈ Finset.range (N + 1), c i)‖ ≤ 4 * ‖z N‖ := by
    rw [norm_mul]
    calc ‖z N‖ * ‖∑ i ∈ Finset.range (N + 1), c i‖ ≤ ‖z N‖ * 4 :=
          mul_le_mul_of_nonneg_left (hc N) (norm_nonneg _)
      _ = 4 * ‖z N‖ := by ring
  have h2 : ‖∑ i ∈ Finset.range N, (z (i + 1) - z i) * (∑ j ∈ Finset.range (i + 1), c j)‖
      ≤ 4 * ∑ i ∈ Finset.range N, ‖z (i + 1) - z i‖ := by
    calc ‖∑ i ∈ Finset.range N, (z (i + 1) - z i) * (∑ j ∈ Finset.range (i + 1), c j)‖
        ≤ ∑ i ∈ Finset.range N, ‖(z (i + 1) - z i) * (∑ j ∈ Finset.range (i + 1), c j)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range N, ‖z (i + 1) - z i‖ * 4 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hc i) (norm_nonneg _)
      _ = 4 * ∑ i ∈ Finset.range N, ‖z (i + 1) - z i‖ := by
          rw [← Finset.sum_mul]; ring
  have hsub : ‖z N * (∑ i ∈ Finset.range (N + 1), c i)
      - ∑ i ∈ Finset.range N, (z (i + 1) - z i) * (∑ j ∈ Finset.range (i + 1), c j)‖
      ≤ 4 * ‖z N‖ + 4 * ∑ i ∈ Finset.range N, ‖z (i + 1) - z i‖ :=
    (norm_sub_le _ _).trans (add_le_add h1 h2)
  rw [hcomm, h]
  exact hsub

/-! ## Pointwise bounds for one modulated bump -/

/-- **Pointwise bounds for a single modulated bump** `x ↦ g (σx) e (λx)` and its first two
derivatives, in terms of the sup bounds `M0, M1, M2` for `g`, the product `σ|ξ| ≤ 1` and the
phase bound `|ξ||λ| ≤ K2 (σ|ξ|)`. -/
lemma rSG_bump_bounds {g : ℝ → ℂ} (M0 M1 M2 σ lam ξ K2 : ℝ) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hM2 : 0 ≤ M2) (hσ : 0 ≤ σ) (hK2 : 0 ≤ K2)
    (hg0 : ∀ u : ℝ, ‖g u‖ ≤ M0) (hg1 : ∀ u : ℝ, ‖deriv g u‖ ≤ M1)
    (hg2 : ∀ u : ℝ, ‖iteratedDeriv 2 g u‖ ≤ M2)
    (hlam : |ξ| * |lam| ≤ K2 * (σ * |ξ|)) (hw : σ * |ξ| ≤ 1) :
    (‖g (σ * ξ) * ee (lam * ξ)‖ ≤ M0) ∧
    (|ξ| * ‖(σ * deriv g (σ * ξ) + (2 * Real.pi * Complex.I * (lam : ℂ)) * g (σ * ξ))
        * ee (lam * ξ)‖ ≤ (M1 + 2 * Real.pi * K2 * M0) * (σ * |ξ|)) ∧
    (|ξ| ^ 2 * ‖((σ) ^ 2 * iteratedDeriv 2 g (σ * ξ)
        + 2 * (2 * Real.pi * Complex.I * (lam : ℂ)) * (σ * deriv g (σ * ξ))
        + (2 * Real.pi * Complex.I * (lam : ℂ)) ^ 2 * g (σ * ξ)) * ee (lam * ξ)‖
      ≤ (M2 + 4 * Real.pi * (K2 * M1) + 4 * Real.pi ^ 2 * (K2 ^ 2 * M0)) * (σ * |ξ|)) := by
  have hξ0 : 0 ≤ |ξ| := abs_nonneg ξ
  have ha : 0 ≤ σ * |ξ| := mul_nonneg hσ hξ0
  have hbK : |ξ| * |lam| ≤ K2 := by
    refine hlam.trans ?_
    calc K2 * (σ * |ξ|) ≤ K2 * 1 := mul_le_mul_of_nonneg_left hw hK2
      _ = K2 := mul_one K2
  have hcoef : 0 ≤ M2 + 4 * Real.pi * (K2 * M1) + 4 * Real.pi ^ 2 * (K2 ^ 2 * M0) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_mul, rSG_norm_ee, mul_one]; exact hg0 _
  · have hA : ‖σ * deriv g (σ * ξ) + (2 * Real.pi * Complex.I * (lam : ℂ)) * g (σ * ξ)‖
        ≤ σ * M1 + 2 * Real.pi * |lam| * M0 := by
      refine (norm_add_le _ _).trans ?_
      have h1 : ‖σ * deriv g (σ * ξ)‖ ≤ σ * M1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ]
        exact mul_le_mul_of_nonneg_left (hg1 _) hσ
      have h2 : ‖(2 * Real.pi * Complex.I * (lam : ℂ)) * g (σ * ξ)‖ ≤ 2 * Real.pi * |lam| * M0 := by
        rw [norm_mul, rSG_norm_two_pi_I_mul]
        have hp : 0 ≤ 2 * Real.pi * |lam| := by positivity
        exact mul_le_mul_of_nonneg_left (hg0 _) hp
      linarith
    rw [norm_mul, rSG_norm_ee, mul_one]
    calc |ξ| * ‖σ * deriv g (σ * ξ) + (2 * Real.pi * Complex.I * (lam : ℂ)) * g (σ * ξ)‖
        ≤ |ξ| * (σ * M1 + 2 * Real.pi * |lam| * M0) := mul_le_mul_of_nonneg_left hA hξ0
      _ = M1 * (σ * |ξ|) + (2 * Real.pi * M0) * (|ξ| * |lam|) := by ring
      _ ≤ M1 * (σ * |ξ|) + (2 * Real.pi * M0) * (K2 * (σ * |ξ|)) := by
          refine add_le_add le_rfl ?_
          exact mul_le_mul_of_nonneg_left hlam (by positivity)
      _ = (M1 + 2 * Real.pi * K2 * M0) * (σ * |ξ|) := by ring
  · have hB : ‖(σ) ^ 2 * iteratedDeriv 2 g (σ * ξ)
        + 2 * (2 * Real.pi * Complex.I * (lam : ℂ)) * (σ * deriv g (σ * ξ))
        + (2 * Real.pi * Complex.I * (lam : ℂ)) ^ 2 * g (σ * ξ)‖
        ≤ (σ) ^ 2 * M2 + 2 * (2 * Real.pi * |lam|) * (σ * M1) + (2 * Real.pi * |lam|) ^ 2 * M0 := by
      have h1 : ‖(σ) ^ 2 * iteratedDeriv 2 g (σ * ξ)‖ ≤ (σ) ^ 2 * M2 := by
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ]
        exact mul_le_mul_of_nonneg_left (hg2 _) (by positivity)
      have h2 : ‖2 * (2 * Real.pi * Complex.I * (lam : ℂ)) * (σ * deriv g (σ * ξ))‖
          ≤ 2 * (2 * Real.pi * |lam|) * (σ * M1) := by
        rw [norm_mul, norm_mul, rSG_norm_two_pi_I_mul]
        have h3 : ‖σ * deriv g (σ * ξ)‖ ≤ σ * M1 := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ]
          exact mul_le_mul_of_nonneg_left (hg1 _) hσ
        have h4 : ‖(2 : ℂ)‖ = 2 := by simp
        rw [h4]
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
      have h3 : ‖(2 * Real.pi * Complex.I * (lam : ℂ)) ^ 2 * g (σ * ξ)‖
          ≤ (2 * Real.pi * |lam|) ^ 2 * M0 := by
        rw [norm_mul, norm_pow, rSG_norm_two_pi_I_mul]
        exact mul_le_mul_of_nonneg_left (hg0 _) (by positivity)
      exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) h3)
    rw [norm_mul, rSG_norm_ee, mul_one]
    calc |ξ| ^ 2 * ‖(σ) ^ 2 * iteratedDeriv 2 g (σ * ξ)
          + 2 * (2 * Real.pi * Complex.I * (lam : ℂ)) * (σ * deriv g (σ * ξ))
          + (2 * Real.pi * Complex.I * (lam : ℂ)) ^ 2 * g (σ * ξ)‖
        ≤ |ξ| ^ 2 * ((σ) ^ 2 * M2 + 2 * (2 * Real.pi * |lam|) * (σ * M1)
            + (2 * Real.pi * |lam|) ^ 2 * M0) := mul_le_mul_of_nonneg_left hB (by positivity)
      _ = M2 * (σ * |ξ|) ^ 2 + 4 * Real.pi * M1 * ((|ξ| * |lam|) * (σ * |ξ|))
            + 4 * Real.pi ^ 2 * M0 * (|ξ| * |lam|) ^ 2 := by ring
      _ ≤ M2 * (σ * |ξ|) ^ 2 + 4 * Real.pi * M1 * ((K2 * (σ * |ξ|)) * (σ * |ξ|))
            + 4 * Real.pi ^ 2 * M0 * (K2 * (σ * |ξ|)) ^ 2 := by
          refine add_le_add (add_le_add le_rfl ?_) ?_
          · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right hlam ha
          · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact pow_le_pow_left₀ (mul_nonneg (abs_nonneg ξ) (abs_nonneg lam)) hlam 2
      _ ≤ (M2 + 4 * Real.pi * (K2 * M1) + 4 * Real.pi ^ 2 * (K2 ^ 2 * M0)) * (σ * |ξ|) := by
          have h1 : (σ * |ξ|) ^ 2 ≤ σ * |ξ| := by nlinarith [ha, hw]
          nlinarith [ha, hw, hM0, hM1, hM2, hK2, Real.pi_pos, h1, hcoef,
            pow_nonneg ha 2]

end

end Work.KMTAreas.A7
