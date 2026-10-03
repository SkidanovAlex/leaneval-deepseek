/-
# `Submission.Work.FIArea1.conjunct2_le` — the second conjunct of *FI* (5.22)

`Dform Pa f β ≤ Dstar Pa f β + c τ² (M^{3/4}N^{3/4} + Pz^{-1}M^{1/2}N^{3/2})(log(MN))^{516}`.

## The proof

1. *(algebra, this file)* For `IsBetaCoeff Pa φ β` the coefficient is a real-valued function
   (`exists_real_of_IsBetaCoeff`), so with `Zc w z = (Zint (cForm w z) : ℂ)` real and non-negative
   the summands of `Dform - Dstar` are real casts, and the `.re` in `Dstar` is redundant:

     `Dform - Dstar = Σ_w f(|w|²)·(Σ_{z₁,z₂} (if ¬GaussCoprime z₁ z₂ then g_{z₁}·conj g_{z₂} else 0)).re`

   (`Dform_sub_Dstar_eq`), where `g_z = β z·Zc w z`.

2. *(diagonal, delegated)* Splitting the non-coprime pairs into `z₁ = z₂` and `z₁ ≠ z₂`, the
   diagonal part is `≤ Σ_w f(|w|²)(Σ_z β_z²Z(wz)²).re`, which is the left-hand side of
   `Work.FIArea1.diagonal_le`:
   `≤ c₁τ²M^{3/4}N^{3/4}(1+log(MN))^{516} ≤ c₁2^{516}τ²M^{3/4}N^{3/4}(log(MN))^{516}` (the log
   comparison needs `MN ≥ e`; for `MN < e` the coefficient vanishes identically).

3. *(off-diagonal, delegated)* The off-diagonal part is
   `≤ τ²·Work.FIArea1.offdiagPairSum Pa φ` (`‖β z‖ ≤ τ` on the support, `f ≤ 1`), and the count is
   the delegated `Work.FIArea1.offdiag_polar_count`.

4. Combining the two pieces gives the statement with `c = c₁·2^{516} + c₂`.
-/
import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop3.Smooth
import Submission.Work.FITop3.Smooth.sm_props
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop3.Witness.exists_primary_norm
import Submission.Work.FIArea1.Basic
import Submission.Work.FIArea1.Helpers
import Submission.Work.FIArea1.count_line_squares
import Submission.Work.FIArea1.conjunct2_defs
import Submission.Work.FIArea1.offdiag_polar_count

set_option autoImplicit false

namespace Work.FIArea1

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

set_option maxHeartbeats 1000000

/-! ## 1. Elementary facts about the set-up and the coefficient -/

/-- `θ ≤ 1`: the smoothing parameter (4.15) is `< 1` because `log x > 1` and `A' > 0`. -/
lemma c2_theta_le_one (Pa : Work.FITop.Params) : Pa.θ ≤ 1 := by
  rw [Pa.hθ]
  have hx0 : (0 : ℝ) < (Pa.x : ℝ) := by
    have : (0 : ℕ) < Pa.x := by linarith [Pa.hx]
    exact_mod_cast this
  have hx1 : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) := by
    rw [Real.le_log_iff_exp_le hx0]
    have : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    linarith [Real.exp_one_lt_three]
  have hA'0 : (0 : ℝ) ≤ Pa.A' := by
    have : (0 : ℝ) < (2 : ℝ) ^ (20 : ℕ) := by positivity
    linarith [Pa.hA, Pa.hA']
  exact Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)

/-- `0 ≤ τ`. -/
lemma c2_tau_nonneg (Pa : Work.FITop.Params) : 0 ≤ Pa.τ := by
  have hx : (0 : ℝ) ≤ Real.log (Pa.x : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (by linarith [Pa.hx] : (1 : ℕ) ≤ Pa.x)
  exact le_trans (Real.rpow_nonneg hx _) Pa.hτ1

/-- **The coefficient of (4.13) is real-valued.**  `IsBetaCoeff` exhibits `β_z` as a product of
three real casts (`q·p`, the Möbius function and `γ(·;C)`), so `β` is the cast of a real function.
This is what makes the `.re` in `Dstar` redundant and the summands of `D - D*` real. -/
lemma exists_real_of_IsBetaCoeff {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (hβ : Work.FITop3.IsBetaCoeff Pa φ β) :
    ∃ b : GaussianInt → ℝ, ∀ z, β z = (b z : ℂ) := by
  obtain ⟨q, p, hq0, hq1, hqsupp, hq1', hq2', hp0, hp1, hpsupp, hp1', hp2', hβz⟩ := hβ
  refine ⟨fun z => if Work.FITop3.InPolarBox Pa φ z ∧ Work.FITop3.NoSmallPrimes Pa z ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ)
    then (q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z))
      * ((ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℤ) : ℝ)
      * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)) else 0, fun z => ?_⟩
  by_cases h : Work.FITop3.InPolarBox Pa φ z ∧ Work.FITop3.NoSmallPrimes Pa z ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ)
  · rw [hβz z]
    simp only []
    rw [if_pos h, if_pos h]
    push_cast
    ring
  · rw [hβz z]
    simp only []
    rw [if_neg h, if_neg h]
    simp

/-- **The structure of the support of `β`** (4.13): `β z ≠ 0` forces the polar box (5.14), a
squarefree norm, freedom of primes `≤ P` (5.8) and `‖β z‖ ≤ τ` (5.9). -/
lemma beta_structure {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (hβ : Work.FITop3.IsBetaCoeff Pa φ β) {z : GaussianInt} (hz : β z ≠ 0) :
    Work.FITop3.InPolarBox Pa φ z ∧ Squarefree (Work.FIPlan.gnorm z) ∧
      Work.FITop3.NoSmallPrimes Pa z ∧ ‖β z‖ ≤ Pa.τ ∧
      (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N := by
  have hcoeff := hβ
  obtain ⟨q, p, -, -, -, -, -, -, -, -, -, -, hβz⟩ := hβ
  have hcond : Work.FITop3.InPolarBox Pa φ z ∧ Work.FITop3.NoSmallPrimes Pa z ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) := by
    by_contra hc
    rw [hβz z, if_neg hc] at hz
    exact hz rfl
  have hsq := (beta_ne_zero_structure hcoeff hz).1
  refine ⟨hcond.1, hsq, hcond.2.1, ?_, ?_⟩
  · exact le_trans (norm_beta_le_divisors_card hcoeff z) hcond.2.2
  · obtain ⟨-, h1, h2, -⟩ := hcond.1
    have hθ1 := c2_theta_le_one Pa
    have hN0 : (0 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
    nlinarith

/-- A point of the box `boxN Pa` on which `β` does not vanish lies in `polarSupp`. -/
lemma mem_polarSupp_of_beta {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (hβ : Work.FITop3.IsBetaCoeff Pa φ β) {z : GaussianInt} (hzN : z ∈ Work.FITop.boxN Pa)
    (hz : β z ≠ 0) : z ∈ polarSupp Pa φ := by
  obtain ⟨hbox, hsq, hns, -, -⟩ := beta_structure hβ hz
  rw [mem_polarSupp]
  exact ⟨hzN, hbox, hsq, hns⟩

/-! ## 2. The kernel `Zc` -/

lemma Zc_eq_ofReal (w z : GaussianInt) :
    Work.FITop3.Zc w z = (((Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℕ) : ℝ) : ℂ) := by
  rw [Work.FITop3.Zc]
  norm_num

lemma Zc_star (w z : GaussianInt) : star (Work.FITop3.Zc w z) = Work.FITop3.Zc w z := by
  rw [Zc_eq_ofReal, Complex.star_def, Complex.conj_ofReal]

lemma norm_Zc (w z : GaussianInt) :
    ‖Work.FITop3.Zc w z‖ = ((Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℕ) : ℝ) := by
  rw [Zc_eq_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  positivity


/-! ## 2. The algebra of `D - D*` -/

/-- `normSq` of the inner `z`-sum, squared out. -/
lemma normSq_sum_eq (Pa : Work.FITop.Params) (w : GaussianInt) (β : GaussianInt → ℂ) :
    Complex.normSq (∑ z ∈ Work.FITop.boxN Pa, β z * Work.FITop3.Zc w z)
      = (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2)).re := by
  have hX : (∑ z ∈ Work.FITop.boxN Pa, β z * Work.FITop3.Zc w z)
        * star (∑ z ∈ Work.FITop.boxN Pa, β z * Work.FITop3.Zc w z)
      = ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) := by
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun z1 _ => ?_
    rw [Finset.mul_sum]
  have h2 : ((∑ z ∈ Work.FITop.boxN Pa, β z * Work.FITop3.Zc w z)
        * star (∑ z ∈ Work.FITop.boxN Pa, β z * Work.FITop3.Zc w z)).re
      = Complex.normSq (∑ z ∈ Work.FITop.boxN Pa, β z * Work.FITop3.Zc w z) := by
    have h := congrArg Complex.re (Complex.mul_conj
      (∑ z ∈ Work.FITop.boxN Pa, β z * Work.FITop3.Zc w z))
    simpa using h
  rw [← h2, hX]

/-- **The algebra of `D - D*`**: the `.re` in `Dstar` is redundant (all factors are real casts) and
what remains is the sum over the *non-coprime* pairs. -/
lemma Dform_sub_Dstar_eq (Pa : Work.FITop.Params) (f : ℤ → ℝ) (β : GaussianInt → ℂ) :
    Work.FITop3.Dform Pa f β - Work.FITop3.Dstar Pa f β
      = ∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w)
          * (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
              (if ¬ Work.FIPlan.GaussCoprime z1 z2 then
                (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2)
               else 0)).re := by
  rw [Work.FITop3.Dform, Work.FITop3.Dstar, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hA : (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2))
      = (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if Work.FIPlan.GaussCoprime z1 z2 then
            (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0))
        + (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if ¬ Work.FIPlan.GaussCoprime z1 z2 then
            (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z1 _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z2 _ => ?_
    by_cases h : Work.FIPlan.GaussCoprime z1 z2 <;> simp [h]
  rw [normSq_sum_eq Pa w β, hA, Complex.add_re]
  ring

/-- Splitting the non-coprime pairs into the diagonal `z₁ = z₂` and the off-diagonal `z₁ ≠ z₂`. -/
lemma noncop_split (Pa : Work.FITop.Params) (w : GaussianInt) (β : GaussianInt → ℂ) :
    (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        (if ¬ Work.FIPlan.GaussCoprime z1 z2 then
          (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0))
      = (∑ z ∈ Work.FITop.boxN Pa,
          (if ¬ Work.FIPlan.GaussCoprime z z then
            (β z * Work.FITop3.Zc w z) * star (β z * Work.FITop3.Zc w z) else 0))
        + (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
            (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
              (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)) := by
  have hdiag : (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        (if z1 = z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
          (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0))
      = ∑ z ∈ Work.FITop.boxN Pa,
          (if ¬ Work.FIPlan.GaussCoprime z z then
            (β z * Work.FITop3.Zc w z) * star (β z * Work.FITop3.Zc w z) else 0) := by
    refine Finset.sum_congr rfl fun z1 hz1 => ?_
    rw [Finset.sum_eq_single z1]
    · by_cases h : ¬ Work.FIPlan.GaussCoprime z1 z1 <;> simp [h]
    · intro z2 _ hz2
      have hne : ¬ (z1 = z2) := fun h => hz2 h.symm
      simp [hne]
    · intro h
      exact absurd hz1 h
  have hsplit : (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        (if ¬ Work.FIPlan.GaussCoprime z1 z2 then
          (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0))
      = (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if z1 = z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
            (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0))
        + (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
            (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
              (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z1 _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z2 _ => ?_
    by_cases h : ¬ Work.FIPlan.GaussCoprime z1 z2
    · by_cases h2 : z1 = z2 <;> simp [h, h2]
    · simp [h]
  rw [hsplit, hdiag]

/-! ## 3. The two pieces -/

/-- `polarSupp Pa φ ⊆ boxN Pa`. -/
lemma polarSupp_subset (Pa : Work.FITop.Params) (φ : ℝ) :
    polarSupp Pa φ ⊆ Work.FITop.boxN Pa := by
  intro z hz
  rw [polarSupp] at hz
  exact (Finset.mem_filter.mp hz).1

/-- Sums over `polarSupp` as sums over `boxN` with an indicator. -/
lemma sum_polarSupp_eq (Pa : Work.FITop.Params) (φ : ℝ) (g : GaussianInt → ℝ) :
    (∑ z ∈ Work.FITop.boxN Pa, (if z ∈ polarSupp Pa φ then g z else 0))
      = ∑ z ∈ polarSupp Pa φ, g z := by
  rw [polarSupp]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun z hz => ?_
  by_cases hp : Work.FITop3.InPolarBox Pa φ z ∧ Squarefree (Work.FIPlan.gnorm z)
      ∧ Work.FITop3.NoSmallPrimes Pa z <;> simp [Finset.mem_filter, hz, hp]

/-- If `z ∈ boxN Pa` and `β z ≠ 0` then `z ∈ polarSupp Pa φ`. -/
lemma beta_eq_zero_of_not_mem {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (hβ : Work.FITop3.IsBetaCoeff Pa φ β) {z : GaussianInt} (hzN : z ∈ Work.FITop.boxN Pa)
    (hz : z ∉ polarSupp Pa φ) : β z = 0 := by
  by_contra h
  exact hz (mem_polarSupp_of_beta hβ hzN h)

/-- `‖β z‖ ≤ τ` for every `z`. -/
lemma norm_beta_le_tau {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (hβ : Work.FITop3.IsBetaCoeff Pa φ β) (z : GaussianInt) : ‖β z‖ ≤ Pa.τ := by
  by_cases hz : β z = 0
  · rw [hz, norm_zero]
    exact c2_tau_nonneg Pa
  · exact (beta_structure hβ hz).2.2.2.1

/-- `β z * Zc w z` as a real cast. -/
lemma beta_Zc_eq {β : GaussianInt → ℂ} {b : GaussianInt → ℝ}
    (hb : ∀ z, β z = (b z : ℂ)) (w z : GaussianInt) :
    β z * Work.FITop3.Zc w z
      = ((b z * ((Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℕ) : ℝ) : ℝ) : ℂ) := by
  rw [hb z, Zc_eq_ofReal, ← Complex.ofReal_mul]

/-- `(β z)²·Z(wz)²` as a real cast. -/
lemma beta_sq_Zc_sq_eq {β : GaussianInt → ℂ}
    {b : GaussianInt → ℝ} (hb : ∀ z, β z = (b z : ℂ)) (w z : GaussianInt) :
    (β z) ^ 2 * (Work.FITop3.Zc w z) ^ 2
      = (((b z) ^ 2 * (((Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ) := by
  rw [hb z, Zc_eq_ofReal, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul]

/-- The diagonal summand is `(β z)²Z(wz)²`: both factors are real, so the conjugate is redundant. -/
lemma diag_pair_eq {β : GaussianInt → ℂ} {b : GaussianInt → ℝ}
    (hb : ∀ z, β z = (b z : ℂ)) (w z : GaussianInt) :
    (β z * Work.FITop3.Zc w z) * star (β z * Work.FITop3.Zc w z)
      = (β z) ^ 2 * (Work.FITop3.Zc w z) ^ 2 := by
  have hz : star (β z * Work.FITop3.Zc w z) = β z * Work.FITop3.Zc w z := by
    rw [beta_Zc_eq hb w z, Complex.star_def, Complex.conj_ofReal]
  rw [hz]; ring

/-- The diagonal part is bounded by the left-hand side of `diagonal_le`. -/
lemma diag_sum_re_le {Pa : Work.FITop.Params} {β : GaussianInt → ℂ}
    {b : GaussianInt → ℝ} (hb : ∀ z, β z = (b z : ℂ)) (w : GaussianInt) :
    (∑ z ∈ Work.FITop.boxN Pa,
        (if ¬ Work.FIPlan.GaussCoprime z z then
          (β z * Work.FITop3.Zc w z) * star (β z * Work.FITop3.Zc w z) else 0)).re
      ≤ (∑ z ∈ Work.FITop.boxN Pa, (β z) ^ 2 * (Work.FITop3.Zc w z) ^ 2).re := by
  rw [Complex.re_sum, Complex.re_sum]
  refine Finset.sum_le_sum fun z _ => ?_
  by_cases h : ¬ Work.FIPlan.GaussCoprime z z
  · rw [if_pos h, diag_pair_eq hb w z]
  · rw [if_neg h, beta_sq_Zc_sq_eq hb w z, Complex.ofReal_re]
    positivity

/-- The norm of the crossed term: both factors are real casts. -/
lemma norm_T_eq {β : GaussianInt → ℂ} {b : GaussianInt → ℝ}
    (hb : ∀ z, β z = (b z : ℂ)) (w z1 z2 : GaussianInt) :
    ‖(β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2)‖
      = ‖β z1‖ * ‖β z2‖
        * (((Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℕ) : ℝ)
            * ((Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℕ) : ℝ)) := by
  rw [norm_mul, norm_star, norm_mul, norm_mul, norm_Zc, norm_Zc]
  ring

/-- **The per-`w` off-diagonal estimate**: the off-diagonal part of the non-coprime pairs is
bounded by `τ²` times the corresponding sum over the support set `polarSupp`. -/
lemma offdiag_w_le {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    {b : GaussianInt → ℝ} (hb : ∀ z, β z = (b z : ℂ))
    (hβ : Work.FITop3.IsBetaCoeff Pa φ β) (w : GaussianInt) :
    ‖∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
          (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)‖
      ≤ Pa.τ ^ 2 * (∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ polarSupp Pa φ,
          (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
            ((Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℕ) : ℝ)
              * ((Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℕ) : ℝ) else 0)) := by
  set n : GaussianInt → ℝ := fun z => ((Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℕ) : ℝ) with hn
  have hn0 : ∀ z, 0 ≤ n z := fun z => by positivity
  have hτ0 : 0 ≤ Pa.τ := c2_tau_nonneg Pa
  -- (1) triangle inequality
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun z1 _ => norm_sum_le _ _) ?_
  -- (2) termwise: the norm is bounded by the indicator term over `polarSupp`
  have hterm : ∀ z1 ∈ Work.FITop.boxN Pa, ∀ z2 ∈ Work.FITop.boxN Pa,
      ‖(if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
          (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)‖
        ≤ (if z1 ∈ polarSupp Pa φ ∧ z2 ∈ polarSupp Pa φ
              ∧ z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2
            then Pa.τ ^ 2 * (n z1 * n z2) else 0) := by
    intro z1 hz1 z2 hz2
    by_cases h1 : z1 ∈ polarSupp Pa φ
    · by_cases h2 : z2 ∈ polarSupp Pa φ
      · by_cases hc : z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2
        · rw [if_pos hc, if_pos ⟨h1, h2, hc⟩, norm_T_eq hb, hn]
          have hb1 := norm_beta_le_tau hβ z1
          have hb2 := norm_beta_le_tau hβ z2
          have hnn : 0 ≤ n z1 * n z2 := mul_nonneg (hn0 z1) (hn0 z2)
          calc ‖β z1‖ * ‖β z2‖ * (n z1 * n z2)
              ≤ Pa.τ * Pa.τ * (n z1 * n z2) := by
                refine mul_le_mul_of_nonneg_right ?_ hnn
                exact mul_le_mul hb1 hb2 (norm_nonneg _) hτ0
            _ = Pa.τ ^ 2 * (n z1 * n z2) := by ring
        · rw [if_neg hc, if_neg (fun h => hc ⟨h.2.2.1, h.2.2.2⟩)]
          simp
      · have hz0 : β z2 = 0 := beta_eq_zero_of_not_mem hβ hz2 h2
        have hcond : ¬ (z1 ∈ polarSupp Pa φ ∧ z2 ∈ polarSupp Pa φ
            ∧ z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2) := by
          rintro ⟨-, h, -⟩
          exact h2 h
        rw [if_neg hcond]
        by_cases hc : z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2
        · rw [if_pos hc]
          have hzero : (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) = 0 := by
            rw [hz0]; simp
          rw [hzero, norm_zero]
        · rw [if_neg hc, norm_zero]
    · have hz0 : β z1 = 0 := beta_eq_zero_of_not_mem hβ hz1 h1
      have hcond : ¬ (z1 ∈ polarSupp Pa φ ∧ z2 ∈ polarSupp Pa φ
          ∧ z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2) := by
        rintro ⟨h, -⟩
        exact h1 h
      rw [if_neg hcond]
      by_cases hc : z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2
      · rw [if_pos hc]
        have hzero : (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) = 0 := by
          rw [hz0]; simp
        rw [hzero, norm_zero]
      · rw [if_neg hc, norm_zero]
  refine le_trans (Finset.sum_le_sum fun z1 hz1 => Finset.sum_le_sum fun z2 hz2 =>
    hterm z1 hz1 z2 hz2) ?_
  -- (3) replace the box sums by the sums over `polarSupp`
  have hinner : ∀ z1 : GaussianInt,
      (∑ z2 ∈ Work.FITop.boxN Pa,
          (if z1 ∈ polarSupp Pa φ ∧ z2 ∈ polarSupp Pa φ
              ∧ z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2
            then Pa.τ ^ 2 * (n z1 * n z2) else 0))
        = (if z1 ∈ polarSupp Pa φ then
            Pa.τ ^ 2 * (∑ z2 ∈ polarSupp Pa φ,
              (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then n z1 * n z2 else 0))
           else 0) := by
    intro z1
    by_cases h1 : z1 ∈ polarSupp Pa φ
    · rw [if_pos h1]
      have hstep : (∑ z2 ∈ Work.FITop.boxN Pa,
            (if z1 ∈ polarSupp Pa φ ∧ z2 ∈ polarSupp Pa φ
                ∧ z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2
              then Pa.τ ^ 2 * (n z1 * n z2) else 0))
          = ∑ z2 ∈ Work.FITop.boxN Pa,
              (if z2 ∈ polarSupp Pa φ then
                (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2
                  then Pa.τ ^ 2 * (n z1 * n z2) else 0) else 0) := by
        refine Finset.sum_congr rfl fun z2 _ => ?_
        simp only [h1, true_and]
        by_cases h2 : z2 ∈ polarSupp Pa φ <;>
          by_cases hp : z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 <;> simp [h2, hp]
      rw [hstep, sum_polarSupp_eq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z2 _ => ?_
      by_cases hp : z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 <;> simp [hp]
    · rw [if_neg h1]
      refine Finset.sum_eq_zero fun z2 _ => ?_
      rw [if_neg]
      tauto
  calc (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        (if z1 ∈ polarSupp Pa φ ∧ z2 ∈ polarSupp Pa φ
            ∧ z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2
          then Pa.τ ^ 2 * (n z1 * n z2) else 0))
      = ∑ z1 ∈ Work.FITop.boxN Pa,
          (if z1 ∈ polarSupp Pa φ then
            Pa.τ ^ 2 * (∑ z2 ∈ polarSupp Pa φ,
              (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then n z1 * n z2 else 0))
           else 0) := Finset.sum_congr rfl fun z1 _ => hinner z1
    _ = ∑ z1 ∈ polarSupp Pa φ,
          Pa.τ ^ 2 * (∑ z2 ∈ polarSupp Pa φ,
            (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then n z1 * n z2 else 0)) :=
        sum_polarSupp_eq Pa φ _
    _ = Pa.τ ^ 2 * (∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ polarSupp Pa φ,
          (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then n z1 * n z2 else 0)) := by
        rw [Finset.mul_sum]
    _ ≤ Pa.τ ^ 2 * (∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ polarSupp Pa φ,
          (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
            ((Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℕ) : ℝ)
              * ((Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℕ) : ℝ) else 0)) :=
        le_of_eq rfl

/-- `offdiagPairSum` with the indicator `z₁ ≠ z₂ ∧ ¬cop` in place of `z₁ = z₂ ∨ cop`. -/
lemma offdiagPairSum_eq (Pa : Work.FITop.Params) (φ : ℝ) :
    offdiagPairSum Pa φ
      = ∑ w ∈ Work.FITop.boxM Pa, ∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ polarSupp Pa φ,
          (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
            ((Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℕ) : ℝ)
              * ((Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℕ) : ℝ) else 0) := by
  rw [offdiagPairSum]
  refine Finset.sum_congr rfl fun w _ => ?_
  refine Finset.sum_congr rfl fun z1 _ => ?_
  refine Finset.sum_congr rfl fun z2 _ => ?_
  by_cases h : z1 = z2 ∨ Work.FIPlan.GaussCoprime z1 z2
  · rw [if_pos h, if_neg (by tauto)]
  · rw [if_neg h, if_pos (by tauto)]

/-- The off-diagonal part of `D - D*`, summed over `w`, is `≤ τ²·offdiagPairSum`. -/
lemma offdiag_sum_abs_le {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    {b : GaussianInt → ℝ} (hb : ∀ z, β z = (b z : ℂ))
    (hβ : Work.FITop3.IsBetaCoeff Pa φ β) (f : ℤ → ℝ) (hf : Work.FITop3.IsMajorant Pa f) :
    (∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w)
        * |(∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
            (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
              (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)).re|)
      ≤ Pa.τ ^ 2 * offdiagPairSum Pa φ := by
  have hτ0 : 0 ≤ Pa.τ := c2_tau_nonneg Pa
  have hf1 : ∀ u, f u ≤ 1 := hf.2.1
  have hS0 : ∀ w : GaussianInt, 0 ≤ (∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ polarSupp Pa φ,
      (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
        ((Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℕ) : ℝ)
          * ((Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℕ) : ℝ) else 0)) := by
    intro w
    refine Finset.sum_nonneg fun z1 _ => Finset.sum_nonneg fun z2 _ => ?_
    by_cases hc : z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2
    · rw [if_pos hc]; positivity
    · rw [if_neg hc]
  have hsum : ∀ w ∈ Work.FITop.boxM Pa,
      f (Work.FIPlan.gnorm w)
        * |(∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
            (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
              (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)).re|
      ≤ Pa.τ ^ 2 * (∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ polarSupp Pa φ,
          (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
            ((Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℕ) : ℝ)
              * ((Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℕ) : ℝ) else 0)) := by
    intro w _
    have h1 : |(∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
            (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
              (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)).re|
        ≤ ‖∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
            (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
              (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)‖ :=
      Complex.abs_re_le_norm _
    have h2 : ‖∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
            (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
              (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)‖
        ≤ Pa.τ ^ 2 * (∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ polarSupp Pa φ,
            (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
              ((Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℕ) : ℝ)
                * ((Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℕ) : ℝ) else 0)) :=
      offdiag_w_le hb hβ w
    have hbnd : 0 ≤ Pa.τ ^ 2 * (∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ polarSupp Pa φ,
          (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
            ((Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℕ) : ℝ)
              * ((Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℕ) : ℝ) else 0)) :=
      mul_nonneg (sq_nonneg _) (hS0 w)
    calc f (Work.FIPlan.gnorm w)
          * |(∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
            (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
              (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)).re|
        ≤ 1 * (Pa.τ ^ 2 * (∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ polarSupp Pa φ,
            (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
              ((Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℕ) : ℝ)
                * ((Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℕ) : ℝ) else 0))) :=
          mul_le_mul (hf1 _) (le_trans h1 h2) (abs_nonneg _) zero_le_one
      _ = Pa.τ ^ 2 * (∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ polarSupp Pa φ,
            (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
              ((Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℕ) : ℝ)
                * ((Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℕ) : ℝ) else 0)) := one_mul _
  rw [offdiagPairSum_eq Pa φ, Finset.mul_sum]
  exact Finset.sum_le_sum fun w hw => hsum w hw

/-- **`D - D*` is bounded by the diagonal left-hand side plus `τ²` times the off-diagonal
count.** -/
lemma Dform_sub_Dstar_le (Pa : Work.FITop.Params) (f : ℤ → ℝ) (φ : ℝ) (β : GaussianInt → ℂ)
    (hf : Work.FITop3.IsMajorant Pa f) (hβ : Work.FITop3.IsBetaCoeff Pa φ β)
    {b : GaussianInt → ℝ} (hb : ∀ z, β z = (b z : ℂ)) :
    Work.FITop3.Dform Pa f β - Work.FITop3.Dstar Pa f β
      ≤ (∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w) *
          (∑ z ∈ Work.FITop.boxN Pa, (β z) ^ 2 * (Work.FITop3.Zc w z) ^ 2).re)
        + Pa.τ ^ 2 * offdiagPairSum Pa φ := by
  rw [Dform_sub_Dstar_eq Pa f β]
  have hf0 : ∀ u, 0 ≤ f u := hf.1
  have hper : ∀ w : GaussianInt, f (Work.FIPlan.gnorm w)
        * (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
            (if ¬ Work.FIPlan.GaussCoprime z1 z2 then
              (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)).re
      ≤ f (Work.FIPlan.gnorm w)
          * (∑ z ∈ Work.FITop.boxN Pa, (β z) ^ 2 * (Work.FITop3.Zc w z) ^ 2).re
        + f (Work.FIPlan.gnorm w)
          * |(∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
              (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
                (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)).re| := by
    intro w
    rw [noncop_split Pa w β, Complex.add_re]
    have h1 : (∑ z ∈ Work.FITop.boxN Pa,
          (if ¬ Work.FIPlan.GaussCoprime z z then
            (β z * Work.FITop3.Zc w z) * star (β z * Work.FITop3.Zc w z) else 0)).re
        ≤ (∑ z ∈ Work.FITop.boxN Pa, (β z) ^ 2 * (Work.FITop3.Zc w z) ^ 2).re :=
      diag_sum_re_le hb w
    have h2 : (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
            (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)).re
        ≤ |(∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
            (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)).re| :=
      le_abs_self _
    have hf0' : 0 ≤ f (Work.FIPlan.gnorm w) := hf0 _
    nlinarith [h1, h2, hf0']
  calc (∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w)
        * (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
            (if ¬ Work.FIPlan.GaussCoprime z1 z2 then
              (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)).re)
      ≤ ∑ w ∈ Work.FITop.boxM Pa, (f (Work.FIPlan.gnorm w)
            * (∑ z ∈ Work.FITop.boxN Pa, (β z) ^ 2 * (Work.FITop3.Zc w z) ^ 2).re
          + f (Work.FIPlan.gnorm w)
            * |(∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
                (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
                  (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)).re|) :=
        Finset.sum_le_sum fun w _ => hper w
    _ = (∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w)
            * (∑ z ∈ Work.FITop.boxN Pa, (β z) ^ 2 * (Work.FITop3.Zc w z) ^ 2).re)
          + ∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w)
            * |(∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
                (if z1 ≠ z2 ∧ ¬ Work.FIPlan.GaussCoprime z1 z2 then
                  (β z1 * Work.FITop3.Zc w z1) * star (β z2 * Work.FITop3.Zc w z2) else 0)).re| :=
        Finset.sum_add_distrib
    _ ≤ (∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w)
            * (∑ z ∈ Work.FITop.boxN Pa, (β z) ^ 2 * (Work.FITop3.Zc w z) ^ 2).re)
          + Pa.τ ^ 2 * offdiagPairSum Pa φ :=
        add_le_add (le_refl _) (offdiag_sum_abs_le hb hβ f hf)

/-- `3` is not a sum of two squares: the only squares `≤ 3` are `0,1`, and `0,1,2 ≠ 3`. -/
lemma three_not_sum_two_squares : ¬ ∃ r s : ℤ, r ^ 2 + s ^ 2 = 3 := by
  rintro ⟨r, s, h⟩
  have h1 : r ^ 2 ≤ 3 := by nlinarith [sq_nonneg s]
  have h2 : s ^ 2 ≤ 3 := by nlinarith [sq_nonneg r]
  have hr1 : -1 ≤ r := by
    have : 4 * r ≥ -7 := by nlinarith [sq_nonneg (r + 2)]
    omega
  have hr2 : r ≤ 1 := by
    have : 4 * r ≤ 7 := by nlinarith [sq_nonneg (r - 2)]
    omega
  have hs1 : -1 ≤ s := by
    have : 4 * s ≥ -7 := by nlinarith [sq_nonneg (s + 2)]
    omega
  have hs2 : s ≤ 1 := by
    have : 4 * s ≤ 7 := by nlinarith [sq_nonneg (s - 2)]
    omega
  interval_cases r <;> interval_cases s <;> norm_num at h

/-- **The arithmetic of (5.22)**: combining the diagonal bound, the off-diagonal count and the
comparison `(1 + log(MN))^{516} ≤ 2^{516}(log(MN))^{516}` (valid when `log(MN) ≥ 1`). -/
lemma c2_arith {A B L Y X τ c₁ c₂ Dg Do : ℝ}
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hL0 : 0 ≤ L) (hτ : 0 ≤ τ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hY : Y ≤ 2 ^ (516 : ℕ) * L)
    (hDg : Dg ≤ c₁ * τ ^ 2 * A * Y)
    (hDo : Do ≤ c₂ * (A + B) * L)
    (hX : X ≤ Dg + τ ^ 2 * Do) :
    X ≤ (c₁ * 2 ^ (516 : ℕ) + c₂) * τ ^ 2 * (A + B) * L := by
  have h1 : Dg ≤ c₁ * τ ^ 2 * A * (2 ^ (516 : ℕ) * L) := by
    refine le_trans hDg ?_
    exact mul_le_mul_of_nonneg_left hY (by positivity)
  have h2 : τ ^ 2 * Do ≤ τ ^ 2 * (c₂ * (A + B) * L) :=
    mul_le_mul_of_nonneg_left hDo (by positivity)
  have h3 : c₁ * τ ^ 2 * A * (2 ^ (516 : ℕ) * L) + τ ^ 2 * (c₂ * (A + B) * L)
      ≤ (c₁ * 2 ^ (516 : ℕ) + c₂) * τ ^ 2 * (A + B) * L := by
    have h2' : 0 ≤ c₁ * 2 ^ (516 : ℕ) * τ ^ 2 * L := by positivity
    have h4 : c₁ * 2 ^ (516 : ℕ) * τ ^ 2 * L * A
        ≤ c₁ * 2 ^ (516 : ℕ) * τ ^ 2 * L * (A + B) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hB0) h2'
    nlinarith [h4]
  linarith

end

end Work.FIArea1
