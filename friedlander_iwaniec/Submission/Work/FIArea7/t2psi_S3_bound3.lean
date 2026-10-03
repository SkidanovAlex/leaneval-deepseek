import Mathlib
import Submission.Work.FIArea7.Classical172Defs
import Submission.Work.FIArea7.exists_separating_function
import Submission.Work.FIArea7.t2psi_block_glue

set_option autoImplicit false

namespace Work.FIArea7

open Finset MeasureTheory
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The integral representation of the block sum (FI Lemma 26.1) -/

/-- Master measure-theory bound: `‖∫ h·B‖ ≤ (sup ‖B‖)·∫|h|`. -/
theorem t2psi3_block_integral_bound (h : ℝ → ℝ) (Be : ℝ → ℂ) (Cb : ℝ)
    (hint : MeasureTheory.Integrable (fun t : ℝ => (h t : ℂ)))
    (hB : ∀ t, ‖Be t‖ ≤ Cb) :
    ‖∫ t : ℝ, (h t : ℂ) * Be t‖ ≤ Cb * ∫ t : ℝ, |h t| := by
  have hgi : MeasureTheory.Integrable (fun t : ℝ => Cb * |h t|) := by
    have h1 : MeasureTheory.Integrable (fun t : ℝ => |h t|) := by
      simpa [Complex.norm_real] using hint.norm
    simpa using h1.const_mul Cb
  have hle : ∀ᵐ t ∂MeasureTheory.volume, ‖(h t : ℂ) * Be t‖ ≤ Cb * |h t| := by
    filter_upwards with t
    rw [norm_mul, Complex.norm_real]
    calc |h t| * ‖Be t‖ ≤ |h t| * Cb := mul_le_mul_of_nonneg_left (hB t) (abs_nonneg _)
      _ = Cb * |h t| := by ring
  have hmain := MeasureTheory.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) hgi hle
  rwa [MeasureTheory.integral_const_mul] at hmain

/-- The block sum equals the integral of the separated bracket (via the separating function
`h`). -/
theorem t2psi3_block_integral_repr
    (h : ℝ → ℝ) (N c A Bhi : ℕ) (k : ℤ) (chi : GaussianInt → ℂ) (φ : ℕ → ℂ)
    (hA : 1 ≤ A)
    (hint : MeasureTheory.Integrable (fun t : ℝ => (h t : ℂ)))
    (hsep : ∀ kk : ℕ, 1 ≤ kk →
      (∫ t : ℝ, (h t : ℂ) * (kk : ℂ) ^ (t * Complex.I))
        = if (kk : ℝ) ≤ (N : ℝ) then 1 else 0) :
    (∑ a ∈ Finset.Icc A Bhi, (ArithmeticFunction.moebius a : ℂ) *
        ∑ n ∈ Finset.Icc 1 (N / a),
          φ n * quadEigen (grossenChar chi k) (c * (a * n)))
      = ∫ t : ℝ, (h t : ℂ) *
          (∑ a ∈ Finset.Icc A Bhi, (ArithmeticFunction.moebius a : ℂ) *
            (a : ℂ) ^ (t * Complex.I) *
            ∑ n ∈ Finset.Icc 1 (N / A),
              φ n * (n : ℂ) ^ (t * Complex.I) *
                quadEigen (grossenChar chi k) (c * (a * n))) := by
  have hstep1 : ∀ a ∈ Finset.Icc A Bhi,
      (∑ n ∈ Finset.Icc 1 (N / a), φ n * quadEigen (grossenChar chi k) (c * (a * n)))
      = ∑ n ∈ Finset.Icc 1 (N / A),
          (if a * n ≤ N then φ n * quadEigen (grossenChar chi k) (c * (a * n)) else 0) := by
    intro a ha
    have haA : A ≤ a := (Finset.mem_Icc.mp ha).1
    have hapos : 0 < a := by omega
    have hdiv : N / a ≤ N / A := Nat.div_le_div_left haA (by omega)
    have hfilt : (Finset.Icc 1 (N / A)).filter (fun n => a * n ≤ N) = Finset.Icc 1 (N / a) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, (Nat.le_div_iff_mul_le hapos).mpr (by rwa [Nat.mul_comm] at h3)⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, le_trans h2 hdiv⟩,
          by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hapos).mp h2⟩
    rw [← Finset.sum_filter, hfilt]
  have hstep2 : ∀ a ∈ Finset.Icc A Bhi,
      (∑ n ∈ Finset.Icc 1 (N / A),
          (if a * n ≤ N then φ n * quadEigen (grossenChar chi k) (c * (a * n)) else 0))
      = ∑ n ∈ Finset.Icc 1 (N / A),
          (∫ t : ℝ, (h t : ℂ) * ((a * n : ℕ) : ℂ) ^ (t * Complex.I)) *
            (φ n * quadEigen (grossenChar chi k) (c * (a * n))) := by
    intro a ha
    have hapos : 0 < a := by have := (Finset.mem_Icc.mp ha).1; omega
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have han1 : 1 ≤ a * n := by
      have : 0 < a * n := Nat.mul_pos hapos (by omega)
      omega
    rw [hsep (a * n) han1]
    by_cases hc : a * n ≤ N
    · rw [if_pos hc, if_pos (by exact_mod_cast hc), one_mul]
    · rw [if_neg hc, if_neg (by exact_mod_cast hc), zero_mul]
  have hstep3 : ∀ a ∈ Finset.Icc A Bhi,
      (∑ n ∈ Finset.Icc 1 (N / A),
          (∫ t : ℝ, (h t : ℂ) * ((a * n : ℕ) : ℂ) ^ (t * Complex.I)) *
            (φ n * quadEigen (grossenChar chi k) (c * (a * n))))
      = ∑ n ∈ Finset.Icc 1 (N / A),
          ∫ t : ℝ, (h t : ℂ) *
            (((a * n : ℕ) : ℂ) ^ (t * Complex.I) *
              (φ n * quadEigen (grossenChar chi k) (c * (a * n)))) := by
    intro a ha
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [(MeasureTheory.integral_mul_const
          (r := φ n * quadEigen (grossenChar chi k) (c * (a * n)))
          (f := fun t : ℝ => (h t : ℂ) * ((a * n : ℕ) : ℂ) ^ (t * Complex.I))).symm]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    ring
  have hstep4 : ∀ a ∈ Finset.Icc A Bhi,
      (∑ n ∈ Finset.Icc 1 (N / A),
          ∫ t : ℝ, (h t : ℂ) *
            (((a * n : ℕ) : ℂ) ^ (t * Complex.I) *
              (φ n * quadEigen (grossenChar chi k) (c * (a * n)))))
      = ∫ t : ℝ, ∑ n ∈ Finset.Icc 1 (N / A),
          (h t : ℂ) * (((a * n : ℕ) : ℂ) ^ (t * Complex.I) *
              (φ n * quadEigen (grossenChar chi k) (c * (a * n)))) := by
    intro a ha
    have hapos : 0 < a := by have := (Finset.mem_Icc.mp ha).1; omega
    refine (MeasureTheory.integral_finsetSum (Finset.Icc 1 (N / A)) (fun n hn => ?_)).symm
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have han1 : 1 ≤ a * n := by
      have : 0 < a * n := Nat.mul_pos hapos (by omega)
      omega
    have h1 := integrable_h_mul_cpow h (a * n) han1 hint
    refine (h1.mul_const (φ n * quadEigen (grossenChar chi k) (c * (a * n)))).congr ?_
    filter_upwards with t
    ring
  have hstep5 : ∀ a ∈ Finset.Icc A Bhi,
      (∫ t : ℝ, ∑ n ∈ Finset.Icc 1 (N / A),
          (h t : ℂ) * (((a * n : ℕ) : ℂ) ^ (t * Complex.I) *
              (φ n * quadEigen (grossenChar chi k) (c * (a * n)))))
      = ∫ t : ℝ, (h t : ℂ) * ∑ n ∈ Finset.Icc 1 (N / A),
          (((a * n : ℕ) : ℂ) ^ (t * Complex.I) *
              (φ n * quadEigen (grossenChar chi k) (c * (a * n)))) := by
    intro a ha
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [Finset.mul_sum]
  have key : ∀ a ∈ Finset.Icc A Bhi,
      (ArithmeticFunction.moebius a : ℂ) *
        (∑ n ∈ Finset.Icc 1 (N / a), φ n * quadEigen (grossenChar chi k) (c * (a * n)))
      = ∫ t : ℝ, (h t : ℂ) *
          ((ArithmeticFunction.moebius a : ℂ) * (a : ℂ) ^ (t * Complex.I) *
            ∑ n ∈ Finset.Icc 1 (N / A),
              (n : ℂ) ^ (t * Complex.I) *
                (φ n * quadEigen (grossenChar chi k) (c * (a * n)))) := by
    intro a ha
    rw [hstep1 a ha, hstep2 a ha, hstep3 a ha, hstep4 a ha, hstep5 a ha]
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    have hsum : (∑ n ∈ Finset.Icc 1 (N / A),
          (((a * n : ℕ) : ℂ) ^ (t * Complex.I) *
              (φ n * quadEigen (grossenChar chi k) (c * (a * n)))))
        = (a : ℂ) ^ (t * Complex.I) * ∑ n ∈ Finset.Icc 1 (N / A),
              ((n : ℂ) ^ (t * Complex.I) *
                (φ n * quadEigen (grossenChar chi k) (c * (a * n)))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [natCast_cpow_I_mul]
      ring
    rw [hsum]
    ring
  rw [Finset.sum_congr rfl key]
  rw [(MeasureTheory.integral_finsetSum (Finset.Icc A Bhi) (fun a ha => by
    have hapos : 0 < a := by have := (Finset.mem_Icc.mp ha).1; omega
    have hpt : ∀ t : ℝ, (∑ n ∈ Finset.Icc 1 (N / A),
          (h t : ℂ) * (((a * n : ℕ) : ℂ) ^ (t * Complex.I) *
            ((ArithmeticFunction.moebius a : ℂ) *
              (φ n * quadEigen (grossenChar chi k) (c * (a * n))))))
        = (h t : ℂ) * ((ArithmeticFunction.moebius a : ℂ) * (a : ℂ) ^ (t * Complex.I) *
            ∑ n ∈ Finset.Icc 1 (N / A),
              (n : ℂ) ^ (t * Complex.I) *
                (φ n * quadEigen (grossenChar chi k) (c * (a * n)))) := by
      intro t
      rw [Finset.mul_sum (Finset.Icc 1 (N / A)) (fun n => (n : ℂ) ^ (t * Complex.I) *
        (φ n * quadEigen (grossenChar chi k) (c * (a * n))))
        ((ArithmeticFunction.moebius a : ℂ) * (a : ℂ) ^ (t * Complex.I))]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [natCast_cpow_I_mul]
      ring
    refine (MeasureTheory.integrable_finsetSum (Finset.Icc 1 (N / A)) (fun n hn => ?_)).congr
      (Filter.Eventually.of_forall hpt)
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have h0 : MeasureTheory.Integrable (fun t : ℝ => (h t : ℂ) * (((a * n : ℕ) : ℂ) ^ (t * Complex.I))) :=
      integrable_h_mul_cpow h (a * n)
        (by have := Nat.mul_pos hapos (by omega : 0 < n); omega) hint
    refine (h0.mul_const ((ArithmeticFunction.moebius a : ℂ) *
      (φ n * quadEigen (grossenChar chi k) (c * (a * n))))).congr ?_
    filter_upwards with t
    ring)).symm]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hsum2 : (∑ n ∈ Finset.Icc 1 (N / A), (n : ℂ) ^ (t * Complex.I) *
        (φ n * quadEigen (grossenChar chi k) (c * (i * n))))
      = ∑ n ∈ Finset.Icc 1 (N / A), φ n * (n : ℂ) ^ (t * Complex.I) *
        quadEigen (grossenChar chi k) (c * (i * n)) := by
    refine Finset.sum_congr rfl (fun n hn => by ring)
  rw [hsum2]

/-! ## A log-free block arithmetic -/

theorem block_arith_eps (A N : ℕ) (hA : 1 ≤ A) (hN : 1 ≤ N) :
    (2 * (A:ℝ) + (N:ℝ)/(A:ℝ)) ^ ((1:ℝ)/12) * (2 * (N:ℝ)) ^ ((11:ℝ)/12)
      ≤ 4 * (((A:ℝ) ^ ((1:ℝ)/12)) * ((N:ℝ) ^ ((11:ℝ)/12))
          + (N:ℝ) * ((A:ℝ) ^ ((1:ℝ)/12))⁻¹) := by
  have hApos : (0:ℝ) < (A:ℝ) := by exact_mod_cast hA
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hlogN : (0:ℝ) < Real.log ((N:ℝ) + 2) := Real.log_pos (by linarith)
  have htwo : (2:ℝ)^((1:ℝ)/12) * (2:ℝ)^((11:ℝ)/12) = 2 := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]; norm_num
  have hNadd : (N:ℝ)^((1:ℝ)/12) * (N:ℝ)^((11:ℝ)/12) = (N:ℝ) := by
    rw [← Real.rpow_add hNpos]; norm_num
  have h2pow : (2:ℝ)^((11:ℝ)/12) ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (by norm_num : (11:ℝ)/12 ≤ 1)
    rwa [Real.rpow_one] at this
  have hsplit : (2 * (A:ℝ) + (N:ℝ)/(A:ℝ)) ^ ((1:ℝ)/12)
      ≤ (2:ℝ)^((1:ℝ)/12) * (A:ℝ)^((1:ℝ)/12)
        + (N:ℝ)^((1:ℝ)/12) * ((A:ℝ)^((1:ℝ)/12))⁻¹ := by
    calc (2 * (A:ℝ) + (N:ℝ)/(A:ℝ)) ^ ((1:ℝ)/12)
        ≤ (2 * (A:ℝ)) ^ ((1:ℝ)/12) + ((N:ℝ)/(A:ℝ)) ^ ((1:ℝ)/12) :=
          Real.rpow_add_le_add_rpow (by positivity) (by positivity) (by norm_num) (by norm_num)
      _ = (2:ℝ)^((1:ℝ)/12) * (A:ℝ)^((1:ℝ)/12)
            + (N:ℝ)^((1:ℝ)/12) * ((A:ℝ)^((1:ℝ)/12))⁻¹ := by
          rw [Real.mul_rpow (by norm_num) (le_of_lt hApos),
              Real.div_rpow (le_of_lt hNpos) (le_of_lt hApos)]
          ring
  have h2N : (2 * (N:ℝ)) ^ ((11:ℝ)/12) = (2:ℝ)^((11:ℝ)/12) * (N:ℝ)^((11:ℝ)/12) :=
    Real.mul_rpow (by norm_num) (le_of_lt hNpos)
  have hmain : (2 * (A:ℝ) + (N:ℝ)/(A:ℝ)) ^ ((1:ℝ)/12) * (2 * (N:ℝ)) ^ ((11:ℝ)/12)
      ≤ 2 * (((A:ℝ) ^ ((1:ℝ)/12)) * ((N:ℝ) ^ ((11:ℝ)/12))
              + (N:ℝ) * ((A:ℝ) ^ ((1:ℝ)/12))⁻¹) := by
    have hexpand : ((2:ℝ)^((1:ℝ)/12) * (A:ℝ)^((1:ℝ)/12)
            + (N:ℝ)^((1:ℝ)/12) * ((A:ℝ)^((1:ℝ)/12))⁻¹)
          * ((2:ℝ)^((11:ℝ)/12) * (N:ℝ)^((11:ℝ)/12))
        = 2 * ((A:ℝ)^((1:ℝ)/12) * (N:ℝ)^((11:ℝ)/12))
            + (2:ℝ)^((11:ℝ)/12) * ((N:ℝ) * ((A:ℝ)^((1:ℝ)/12))⁻¹) := by
      rw [show ((2:ℝ)^((1:ℝ)/12) * (A:ℝ)^((1:ℝ)/12)
            + (N:ℝ)^((1:ℝ)/12) * ((A:ℝ)^((1:ℝ)/12))⁻¹)
          * ((2:ℝ)^((11:ℝ)/12) * (N:ℝ)^((11:ℝ)/12))
          = ((2:ℝ)^((1:ℝ)/12) * (2:ℝ)^((11:ℝ)/12))
              * ((A:ℝ)^((1:ℝ)/12) * (N:ℝ)^((11:ℝ)/12))
            + ((2:ℝ)^((11:ℝ)/12) * ((N:ℝ)^((1:ℝ)/12) * (N:ℝ)^((11:ℝ)/12)))
              * ((A:ℝ)^((1:ℝ)/12))⁻¹ from by ring]
      rw [htwo, hNadd]
      ring
    calc (2 * (A:ℝ) + (N:ℝ)/(A:ℝ)) ^ ((1:ℝ)/12) * (2 * (N:ℝ)) ^ ((11:ℝ)/12)
        ≤ ((2:ℝ)^((1:ℝ)/12) * (A:ℝ)^((1:ℝ)/12)
            + (N:ℝ)^((1:ℝ)/12) * ((A:ℝ)^((1:ℝ)/12))⁻¹)
          * ((2:ℝ)^((11:ℝ)/12) * (N:ℝ)^((11:ℝ)/12)) := by
          rw [h2N]
          exact mul_le_mul hsplit le_rfl (by positivity) (by positivity)
      _ = 2 * ((A:ℝ)^((1:ℝ)/12) * (N:ℝ)^((11:ℝ)/12))
            + (2:ℝ)^((11:ℝ)/12) * ((N:ℝ) * ((A:ℝ)^((1:ℝ)/12))⁻¹) := hexpand
      _ ≤ 2 * (((A:ℝ) ^ ((1:ℝ)/12)) * ((N:ℝ) ^ ((11:ℝ)/12))
              + (N:ℝ) * ((A:ℝ) ^ ((1:ℝ)/12))⁻¹) := by
          have h1 : (2:ℝ)^((11:ℝ)/12) * ((N:ℝ) * ((A:ℝ)^((1:ℝ)/12))⁻¹)
              ≤ 2 * ((N:ℝ) * ((A:ℝ)^((1:ℝ)/12))⁻¹) :=
            mul_le_mul_of_nonneg_right h2pow (by positivity)
          nlinarith [h1]
  have hS : (0:ℝ) ≤ ((A:ℝ) ^ ((1:ℝ)/12)) * ((N:ℝ) ^ ((11:ℝ)/12))
              + (N:ℝ) * ((A:ℝ) ^ ((1:ℝ)/12))⁻¹ := by positivity
  linarith [hmain, hS]

/-! ## Helpers for the third Vaughan term -/

/-- `w n = ∑_{b ∣ n, b > Y} Λ b`. -/
def t2psiWd (Y n : ℕ) : ℂ :=
  ∑ b ∈ n.divisors.filter (fun b => Y < b), ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ)

lemma t2psiWd_eq (Y n : ℕ) :
    t2psiWd Y n
      = ((∑ b ∈ n.divisors.filter (fun b => Y < b),
          ArithmeticFunction.vonMangoldt b : ℝ) : ℂ) := by
  rw [t2psiWd, Complex.ofReal_sum]

lemma t2psiWd_nonneg (Y n : ℕ) :
    (0 : ℝ) ≤ ∑ b ∈ n.divisors.filter (fun b => Y < b), ArithmeticFunction.vonMangoldt b :=
  Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

lemma t2psiWd_bound (Y n : ℕ) : ‖t2psiWd Y n‖ ≤ Real.log n := by
  rw [t2psiWd_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (t2psiWd_nonneg Y n)]
  calc (∑ b ∈ n.divisors.filter (fun b => Y < b), ArithmeticFunction.vonMangoldt b)
      ≤ ∑ b ∈ n.divisors, ArithmeticFunction.vonMangoldt b :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = Real.log n := ArithmeticFunction.vonMangoldt_sum

/-- `Nat.log2` is monotone. -/
lemma nat_log2_mono {a b : ℕ} (h : a ≤ b) : a.log2 ≤ b.log2 := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; rw [Nat.log2_zero]; exact Nat.zero_le _
  · have hb : b ≠ 0 := by omega
    rw [Nat.le_log2 hb]
    have h1 : 2 ^ a.log2 ≤ a := ((Nat.log2_eq_iff (by omega : a ≠ 0)).mp rfl).1
    omega

/-- The `Nat.log2`-fibre of `Icc (Y+1) (N/Y)` is its intersection with the dyadic block
`Icc (2^j) (2^(j+1)-1)`. -/
lemma t2psi_fiber_eq (N Y j : ℕ) :
    (Finset.Icc (Y + 1) (N / Y)).filter (fun a => Nat.log2 a = j)
      = Finset.Icc (max (2 ^ j) (Y + 1)) (min (2 ^ (j + 1) - 1) (N / Y)) := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have ha : a ≠ 0 := by omega
    have h4 := (Nat.log2_eq_iff ha).mp h3
    constructor <;> omega
  · rintro ⟨h1, h2⟩
    have ha : a ≠ 0 := by omega
    exact ⟨⟨by omega, by omega⟩,
      (Nat.log2_eq_iff ha).mpr (by omega : 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))⟩

/-- The number of dyadic blocks below `M ≤ N` is at most `3 log(N+2)`. -/
lemma t2psi_log2_le (M N : ℕ) (hN : 1 ≤ N) (hMN : M ≤ N) :
    (M.log2 : ℝ) + 1 ≤ 3 * Real.log ((N : ℝ) + 2) := by
  have hkey : (M.log2 : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
    rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM
      rw [Nat.log2_zero]
      simp only [Nat.cast_zero, zero_mul]
      exact Real.log_nonneg (by exact_mod_cast hN)
    · have h1 : 2 ^ M.log2 ≤ M := ((Nat.log2_eq_iff (by omega : M ≠ 0)).mp rfl).1
      have h2 : Real.log ((2 : ℝ) ^ M.log2) ≤ Real.log (M : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast h1)
      have h3 : Real.log ((2 : ℝ) ^ M.log2) = (M.log2 : ℝ) * Real.log 2 := by
        rw [Real.log_pow]
      have h4 : Real.log (M : ℝ) ≤ Real.log (N : ℝ) :=
        Real.log_le_log (by exact_mod_cast hM) (by exact_mod_cast hMN)
      rw [h3] at h2
      linarith
  have hM2 : (M.log2 : ℝ) ≤ 2 * Real.log ((N : ℝ) + 2) := by
    have h1 : (M.log2 : ℝ) * (1 / 2) ≤ (M.log2 : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (by linarith [Real.log_two_gt_d9]) (Nat.cast_nonneg _)
    have h2 : (M.log2 : ℝ) * (1 / 2) ≤ Real.log (N : ℝ) := le_trans h1 hkey
    have h3 : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 2) :=
      Real.log_le_log (by exact_mod_cast (show 0 < N by omega)) (by linarith)
    linarith
  have hL1 : (1 : ℝ) ≤ Real.log ((N : ℝ) + 2) := by
    have h3 : (3 : ℝ) ≤ (N : ℝ) + 2 := by
      have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 3) h3, Real.log_three_gt_d9]
  linarith

/-- Real-power comparisons for one dyadic block: `Y < 2A` and `A ≤ N/Y` give
`A^{1/12}N^{11/12} ≤ N Y^{-1/12}` and `N A^{-1/12} ≤ 2^{1/12} N Y^{-1/12}`. -/
lemma t2psi_rpow_le (A N Y : ℕ) (hN : 1 ≤ N) (hY : 1 ≤ Y) (hA : Y < 2 * A)
    (hAN : A ≤ N / Y) :
    (A : ℝ) ^ ((1 : ℝ) / 12) * (N : ℝ) ^ ((11 : ℝ) / 12)
        ≤ (N : ℝ) * (Y : ℝ) ^ (-((1 : ℝ) / 12)) ∧
      (N : ℝ) * (A : ℝ) ^ (-((1 : ℝ) / 12))
        ≤ 2 ^ ((1 : ℝ) / 12) * (N : ℝ) * (Y : ℝ) ^ (-((1 : ℝ) / 12)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hYpos : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hY
  have hApos : (0 : ℝ) < (A : ℝ) := by
    have : 0 < A := by omega
    exact_mod_cast this
  constructor
  · have hAY : (A : ℝ) ≤ (N : ℝ) / (Y : ℝ) :=
      le_trans (by exact_mod_cast hAN) (Nat.cast_div_le)
    have h1 : (A : ℝ) ^ ((1 : ℝ) / 12) ≤ ((N : ℝ) / (Y : ℝ)) ^ ((1 : ℝ) / 12) :=
      Real.rpow_le_rpow (le_of_lt hApos) hAY (by norm_num)
    have h2 : ((N : ℝ) / (Y : ℝ)) ^ ((1 : ℝ) / 12)
        = (N : ℝ) ^ ((1 : ℝ) / 12) * (Y : ℝ) ^ (-((1 : ℝ) / 12)) := by
      rw [Real.div_rpow (le_of_lt hNpos) (le_of_lt hYpos), div_eq_mul_inv,
        ← Real.rpow_neg (le_of_lt hYpos) ((1 : ℝ) / 12)]
    calc (A : ℝ) ^ ((1 : ℝ) / 12) * (N : ℝ) ^ ((11 : ℝ) / 12)
        ≤ ((N : ℝ) ^ ((1 : ℝ) / 12) * (Y : ℝ) ^ (-((1 : ℝ) / 12)))
            * (N : ℝ) ^ ((11 : ℝ) / 12) := by
          rw [h2] at h1
          exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (le_of_lt hNpos) _)
      _ = ((N : ℝ) ^ ((1 : ℝ) / 12) * (N : ℝ) ^ ((11 : ℝ) / 12))
            * (Y : ℝ) ^ (-((1 : ℝ) / 12)) := by ring
      _ = (N : ℝ) ^ ((1 : ℝ) / 12 + (11 : ℝ) / 12) * (Y : ℝ) ^ (-((1 : ℝ) / 12)) := by
          rw [Real.rpow_add hNpos]
      _ = (N : ℝ) * (Y : ℝ) ^ (-((1 : ℝ) / 12)) := by
          rw [show (1 : ℝ) / 12 + 11 / 12 = 1 by norm_num, Real.rpow_one]
  · have hA2 : (Y : ℝ) / 2 ≤ (A : ℝ) := by
      have h : (Y : ℝ) < 2 * (A : ℝ) := by
        have h' : (Y : ℝ) < ((2 * A : ℕ) : ℝ) := by exact_mod_cast hA
        push_cast at h'
        linarith
      linarith
    have h1 : (A : ℝ) ^ (-((1 : ℝ) / 12)) ≤ ((Y : ℝ) / 2) ^ (-((1 : ℝ) / 12)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hA2 (by norm_num)
    have h2 : ((Y : ℝ) / 2) ^ (-((1 : ℝ) / 12))
        = 2 ^ ((1 : ℝ) / 12) * (Y : ℝ) ^ (-((1 : ℝ) / 12)) := by
      rw [Real.div_rpow (le_of_lt hYpos) (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) ((1 : ℝ) / 12), inv_inv]
      ring
    calc (N : ℝ) * (A : ℝ) ^ (-((1 : ℝ) / 12))
        ≤ (N : ℝ) * (2 ^ ((1 : ℝ) / 12) * (Y : ℝ) ^ (-((1 : ℝ) / 12))) := by
          rw [h2] at h1
          exact mul_le_mul_of_nonneg_left h1 (le_of_lt hNpos)
      _ = 2 ^ ((1 : ℝ) / 12) * (N : ℝ) * (Y : ℝ) ^ (-((1 : ℝ) / 12)) := by ring

/-! ## The pointwise bound of the separated bracket (ε-form of Prop. 23.1) -/

/-- **Pointwise bound of the separated bracket**, from the ε-form of Proposition 23.1.  The bracket
is `L·(L(Bhi,N/A) − L(A−1,N/A))` (prefix difference of the rectangular bilinear form) with the
bounded coefficients `α_m = μ(m)m^{it}`, `β_n = (φ n / L) n^{it}`. -/
theorem t2psi_block_bracket_le_eps (h31 : Work.FIArea7.Prop231) (ε : ℝ) (hε : 0 < ε) :
    ∃ K B : ℝ, 0 < K ∧ 0 < B ∧
      ∀ (N c A Bhi : ℕ) (k : ℤ) (chi : GaussianInt → ℂ) (φ : ℕ → ℂ) (L t : ℝ),
        1 ≤ N → 1 ≤ c → 1 ≤ A → A ≤ Bhi → Bhi ≤ 2 * A - 1 →
        (∀ z, ‖chi z‖ ≤ 1) →
        (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2) →
        0 < L → (∀ n : ℕ, ‖φ n‖ ≤ L) →
        ‖∑ a ∈ Finset.Icc A Bhi, (ArithmeticFunction.moebius a : ℂ) *
            (a : ℂ) ^ (t * Complex.I) *
            ∑ n ∈ Finset.Icc 1 (N / A),
              φ n * (n : ℂ) ^ (t * Complex.I) *
                quadEigen (grossenChar chi k) (c * (a * n))‖
          ≤ K * ((c.divisors.card : ℕ) : ℝ) * L *
              (((A : ℝ) ^ ((1:ℝ)/12)) * ((N : ℝ) ^ ((11:ℝ)/12))
                + (N : ℝ) * ((A : ℝ) ^ (-(1:ℝ)/12)))
              * ((2 * (N : ℝ) + (c : ℝ) + 2) ^ ε)
              * (Real.log ((N : ℝ) + 2)) ^ B := by
  obtain ⟨C31, hC31, h31b⟩ := h31 ε hε
  refine ⟨8 * C31, 1, by positivity, one_pos, ?_⟩
  intro N c A Bhi k chi φ L t hN hc hA hAB hBhi2 hchi hchimul hL hφ
  set M : ℕ := N / A with hMdef
  set τ : ℝ := ((c.divisors.card : ℕ) : ℝ) with hτdef
  have hApos : (0:ℝ) < (A:ℝ) := by exact_mod_cast hA
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hτnn : (0:ℝ) ≤ τ := by rw [hτdef]; positivity
  have hBhiA : Bhi ≤ 2 * A := by omega
  have hAm1A : A - 1 ≤ 2 * A := by omega
  have hMle : (M:ℝ) ≤ (N:ℝ)/(A:ℝ) := by
    rw [le_div_iff₀ hApos]
    have hmul : A * (N / A) ≤ N := Nat.mul_div_le N A
    have hcast : ((A * (N / A) : ℕ) : ℝ) ≤ (N:ℝ) := by exact_mod_cast hmul
    rw [Nat.cast_mul] at hcast
    rw [← hMdef] at hcast
    nlinarith [hcast, mul_comm (M:ℝ) (A:ℝ)]
  rw [show (A:ℝ)^(-(1:ℝ)/12) = ((A:ℝ)^((1:ℝ)/12))⁻¹ from by
      rw [show (-(1:ℝ)/12) = -((1:ℝ)/12) by norm_num, Real.rpow_neg (le_of_lt hApos)]]
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · have hIc : Finset.Icc 1 (0:ℕ) = (∅ : Finset ℕ) := by
      exact Finset.Icc_eq_empty_of_lt (by norm_num : (0:ℕ) < 1)
    have hb : (∑ a ∈ Finset.Icc A Bhi, (ArithmeticFunction.moebius a : ℂ) *
        (a : ℂ) ^ (t * Complex.I) *
        ∑ n ∈ Finset.Icc 1 M, φ n * (n : ℂ) ^ (t * Complex.I) *
            quadEigen (grossenChar chi k) (c * (a * n))) = 0 := by
      rw [hM0, hIc]; simp
    rw [hb, norm_zero]
    have hSqnn : (0:ℝ) ≤ ((A:ℝ)^((1:ℝ)/12)) * ((N:ℝ)^((11:ℝ)/12))
        + (N:ℝ) * ((A:ℝ)^((1:ℝ)/12))⁻¹ := by positivity
    have hepsnn : (0:ℝ) ≤ (2 * (N:ℝ) + (c:ℝ) + 2)^ε := Real.rpow_nonneg (by positivity) ε
    have hlognn : (0:ℝ) ≤ (Real.log ((N:ℝ) + 2))^(1:ℝ) := by
      rw [Real.rpow_one]; exact Real.log_nonneg (by linarith)
    positivity
  · have hα : ∀ (M' : ℕ) (m : ℕ), m ∈ Finset.Icc 1 M' →
        ‖(ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (t * Complex.I)‖ ≤ 1 := by
      intro M' m hm
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      calc ‖(ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (t * Complex.I)‖
          = ‖(ArithmeticFunction.moebius m : ℂ)‖ * ‖(m : ℂ) ^ (t * Complex.I)‖ := norm_mul _ _
        _ ≤ 1 * 1 := mul_le_mul (norm_moebius_cast_le_one m)
              (le_of_eq (norm_natCast_cpow_I m hm1 t)) (norm_nonneg _) (by norm_num)
        _ = 1 := by ring
    have hβ : ∀ (M' : ℕ) (n : ℕ), n ∈ Finset.Icc 1 M' →
        ‖(φ n * (n : ℂ) ^ (t * Complex.I)) / (L : ℂ)‖ ≤ 1 := by
      intro M' n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hLn : ‖(L:ℂ)‖ = L := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
      calc ‖(φ n * (n : ℂ) ^ (t * Complex.I)) / (L : ℂ)‖
          = ‖φ n * (n : ℂ) ^ (t * Complex.I)‖ / ‖(L:ℂ)‖ := norm_div _ _
        _ = ‖φ n‖ * ‖(n : ℂ) ^ (t * Complex.I)‖ / L := by rw [norm_mul, hLn]
        _ = ‖φ n‖ / L := by rw [norm_natCast_cpow_I n hn1 t, mul_one]
        _ ≤ 1 := by rw [div_le_one hL]; exact hφ n
    have hLB : ∀ M' : ℕ, ‖LBilin M' M c (grossenChar chi k)
          (fun m => (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (t * Complex.I))
          (fun n => (φ n * (n : ℂ) ^ (t * Complex.I)) / (L : ℂ))‖
        ≤ C31 * τ * (((M' + M : ℕ) : ℝ))^((1:ℝ)/12) * (((M' * M : ℕ) : ℝ))^((11:ℝ)/12)
            * ((((M' * M : ℕ) : ℝ)) + (c:ℝ) + 2)^ε := by
      intro M'
      rcases Nat.eq_zero_or_pos M' with h0 | hpos
      · subst h0
        have hIc : Finset.Icc 1 (0:ℕ) = (∅ : Finset ℕ) := by
          exact Finset.Icc_eq_empty_of_lt (by norm_num : (0:ℕ) < 1)
        have hz : LBilin 0 M c (grossenChar chi k)
            (fun m => (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (t * Complex.I))
            (fun n => (φ n * (n : ℂ) ^ (t * Complex.I)) / (L : ℂ)) = 0 := by
          simp [LBilin, hIc]
        rw [hz, norm_zero]
        simp only [Nat.zero_add, Nat.zero_mul, Nat.cast_zero,
          Real.zero_rpow (by norm_num : ((11:ℝ)/12) ≠ 0), mul_zero, zero_mul]
        positivity
      · simpa only [hτdef, Nat.cast_add, Nat.cast_mul] using (h31b M' M c 1 k chi
          (fun m => (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (t * Complex.I))
          (fun n => (φ n * (n : ℂ) ^ (t * Complex.I)) / (L : ℂ))
          hc hpos hMpos (le_refl 1) hchi hchimul (hα M') (hβ M)).1
    have hrel1 : L * LBilin Bhi M c (grossenChar chi k)
          (fun m => (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (t * Complex.I))
          (fun n => (φ n * (n : ℂ) ^ (t * Complex.I)) / (L : ℂ))
        = ∑ m ∈ Finset.Icc 1 Bhi, (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (t * Complex.I) *
            ∑ n ∈ Finset.Icc 1 M, φ n * (n : ℂ) ^ (t * Complex.I) *
              quadEigen (grossenChar chi k) (c * (m * n)) := by
      have hLc : (L:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hL
      rw [LBilin]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [Nat.mul_assoc]
      field_simp
    have hrel2 : L * LBilin (A - 1) M c (grossenChar chi k)
          (fun m => (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (t * Complex.I))
          (fun n => (φ n * (n : ℂ) ^ (t * Complex.I)) / (L : ℂ))
        = ∑ m ∈ Finset.Icc 1 (A - 1), (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (t * Complex.I) *
            ∑ n ∈ Finset.Icc 1 M, φ n * (n : ℂ) ^ (t * Complex.I) *
              quadEigen (grossenChar chi k) (c * (m * n)) := by
      have hLc : (L:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hL
      rw [LBilin]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [Nat.mul_assoc]
      field_simp
    have hsplit : (∑ m ∈ Finset.Icc A Bhi, (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (t * Complex.I) *
            ∑ n ∈ Finset.Icc 1 M, φ n * (n : ℂ) ^ (t * Complex.I) *
              quadEigen (grossenChar chi k) (c * (m * n)))
        = (∑ m ∈ Finset.Icc 1 Bhi, (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (t * Complex.I) *
            ∑ n ∈ Finset.Icc 1 M, φ n * (n : ℂ) ^ (t * Complex.I) *
              quadEigen (grossenChar chi k) (c * (m * n)))
          - (∑ m ∈ Finset.Icc 1 (A - 1), (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (t * Complex.I) *
            ∑ n ∈ Finset.Icc 1 M, φ n * (n : ℂ) ^ (t * Complex.I) *
              quadEigen (grossenChar chi k) (c * (m * n))) := by
      have hset : Finset.Icc A Bhi = (Finset.Icc 1 Bhi) \ (Finset.Icc 1 (A - 1)) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_sdiff]
        omega
      have hsub : Finset.Icc 1 (A - 1) ⊆ Finset.Icc 1 Bhi := by
        intro x hx
        simp only [Finset.mem_Icc] at hx ⊢
        omega
      have h := Finset.sum_sdiff (f := fun a => (ArithmeticFunction.moebius a : ℂ) *
          (a : ℂ) ^ (t * Complex.I) *
          ∑ n ∈ Finset.Icc 1 M, φ n * (n : ℂ) ^ (t * Complex.I) *
              quadEigen (grossenChar chi k) (c * (a * n))) hsub
      rw [hset]
      exact eq_sub_iff_add_eq.mpr h
    have hshape : ∀ M' : ℕ, M' ≤ 2 * A →
        (((M' + M : ℕ) : ℝ))^((1:ℝ)/12) * (((M' * M : ℕ) : ℝ))^((11:ℝ)/12)
          * ((((M' * M : ℕ) : ℝ)) + (c:ℝ) + 2)^ε
        ≤ 4 * (((A:ℝ) ^ ((1:ℝ)/12)) * ((N:ℝ) ^ ((11:ℝ)/12))
              + (N:ℝ) * ((A:ℝ) ^ ((1:ℝ)/12))⁻¹) * ((2*(N:ℝ) + (c:ℝ) + 2))^ε := by
      intro M' hM'
      have hM'le : (M':ℝ) ≤ 2 * (A:ℝ) := by
        have h2 : ((M':ℕ):ℝ) ≤ ((2*A:ℕ):ℝ) := by exact_mod_cast hM'
        rwa [Nat.cast_mul, Nat.cast_ofNat] at h2
      have hsum : ((M' + M : ℕ):ℝ) ≤ 2 * (A:ℝ) + (N:ℝ)/(A:ℝ) := by
        rw [Nat.cast_add]; linarith
      have hprod : ((M' * M : ℕ):ℝ) ≤ 2 * (N:ℝ) := by
        rw [Nat.cast_mul]
        have h := mul_le_mul hM'le hMle (by positivity) (by positivity)
        have h2 : (2*(A:ℝ)) * ((N:ℝ)/(A:ℝ)) = 2*(N:ℝ) := by field_simp
        linarith [h, h2.le, h2.ge]
      have heps : ((((M' * M : ℕ) : ℝ)) + (c:ℝ) + 2)^ε ≤ ((2*(N:ℝ) + (c:ℝ) + 2))^ε :=
        Real.rpow_le_rpow (by positivity) (by linarith [hprod]) hε.le
      have h1 : (((M' + M : ℕ) : ℝ))^((1:ℝ)/12) ≤ (2*(A:ℝ) + (N:ℝ)/(A:ℝ))^((1:ℝ)/12) :=
        Real.rpow_le_rpow (by positivity) hsum (by norm_num)
      have h2 : (((M' * M : ℕ) : ℝ))^((11:ℝ)/12) ≤ (2*(N:ℝ))^((11:ℝ)/12) :=
        Real.rpow_le_rpow (by positivity) hprod (by norm_num)
      have hb1 : (0:ℝ) ≤ (((M' * M : ℕ) : ℝ))^((11:ℝ)/12) := Real.rpow_nonneg (by positivity) _
      have hb1' : (0:ℝ) ≤ (2*(N:ℝ))^((11:ℝ)/12) := Real.rpow_nonneg (by positivity) _
      have ha' : (0:ℝ) ≤ (2*(A:ℝ) + (N:ℝ)/(A:ℝ))^((1:ℝ)/12) := Real.rpow_nonneg (by positivity) _
      have hc1 : (0:ℝ) ≤ ((((M' * M : ℕ) : ℝ)) + (c:ℝ) + 2)^ε := Real.rpow_nonneg (by positivity) ε
      have hc1' : (0:ℝ) ≤ ((2*(N:ℝ) + (c:ℝ) + 2))^ε := Real.rpow_nonneg (by positivity) ε
      calc (((M' + M : ℕ) : ℝ))^((1:ℝ)/12) * (((M' * M : ℕ) : ℝ))^((11:ℝ)/12)
            * ((((M' * M : ℕ) : ℝ)) + (c:ℝ) + 2)^ε
          ≤ (2*(A:ℝ) + (N:ℝ)/(A:ℝ))^((1:ℝ)/12) * (2*(N:ℝ))^((11:ℝ)/12)
            * ((2*(N:ℝ) + (c:ℝ) + 2))^ε :=
            mul_le_mul (mul_le_mul h1 h2 hb1 ha') heps hc1 (mul_nonneg ha' hb1')
        _ ≤ 4 * (((A:ℝ) ^ ((1:ℝ)/12)) * ((N:ℝ) ^ ((11:ℝ)/12))
              + (N:ℝ) * ((A:ℝ) ^ ((1:ℝ)/12))⁻¹) * ((2*(N:ℝ) + (c:ℝ) + 2))^ε :=
            mul_le_mul_of_nonneg_right (block_arith_eps A N hA hN) hc1'
    have hX : ∀ M' : ℕ, M' ≤ 2 * A →
          ‖LBilin M' M c (grossenChar chi k)
            (fun m => (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (t * Complex.I))
            (fun n => (φ n * (n : ℂ) ^ (t * Complex.I)) / (L : ℂ))‖
          ≤ C31 * τ * (4 * (((A:ℝ) ^ ((1:ℝ)/12)) * ((N:ℝ) ^ ((11:ℝ)/12))
              + (N:ℝ) * ((A:ℝ) ^ ((1:ℝ)/12))⁻¹) * ((2*(N:ℝ) + (c:ℝ) + 2))^ε) := by
      intro M' hM'
      calc ‖LBilin M' M c (grossenChar chi k)
            (fun m => (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (t * Complex.I))
            (fun n => (φ n * (n : ℂ) ^ (t * Complex.I)) / (L : ℂ))‖
          ≤ C31 * τ * ((((M' + M : ℕ) : ℝ))^((1:ℝ)/12) * (((M' * M : ℕ) : ℝ))^((11:ℝ)/12)
              * ((((M' * M : ℕ) : ℝ)) + (c:ℝ) + 2)^ε) := by
            simpa only [mul_assoc] using hLB M'
        _ ≤ C31 * τ * (4 * (((A:ℝ) ^ ((1:ℝ)/12)) * ((N:ℝ) ^ ((11:ℝ)/12))
              + (N:ℝ) * ((A:ℝ) ^ ((1:ℝ)/12))⁻¹) * ((2*(N:ℝ) + (c:ℝ) + 2))^ε) :=
            mul_le_mul_of_nonneg_left (hshape M' hM') (mul_nonneg (le_of_lt hC31) hτnn)
    have hlogN1 : (1:ℝ) ≤ Real.log ((N:ℝ) + 2) := by
      have h3 : (3:ℝ) ≤ (N:ℝ) + 2 := by linarith
      linarith [Real.log_le_log (by norm_num : (0:ℝ) < 3) h3, Real.log_three_gt_d9]
    have hnorm : ‖∑ a ∈ Finset.Icc A Bhi, (ArithmeticFunction.moebius a : ℂ) *
          (a : ℂ) ^ (t * Complex.I) *
          ∑ n ∈ Finset.Icc 1 M, φ n * (n : ℂ) ^ (t * Complex.I) *
            quadEigen (grossenChar chi k) (c * (a * n))‖
        ≤ 8 * C31 * τ * L *
            (((A:ℝ) ^ ((1:ℝ)/12)) * ((N:ℝ) ^ ((11:ℝ)/12))
              + (N:ℝ) * ((A:ℝ) ^ ((1:ℝ)/12))⁻¹) * ((2*(N:ℝ) + (c:ℝ) + 2))^ε := by
      have hcombine : (∑ a ∈ Finset.Icc A Bhi, (ArithmeticFunction.moebius a : ℂ) *
            (a : ℂ) ^ (t * Complex.I) *
            ∑ n ∈ Finset.Icc 1 M, φ n * (n : ℂ) ^ (t * Complex.I) *
              quadEigen (grossenChar chi k) (c * (a * n)))
          = L * (LBilin Bhi M c (grossenChar chi k)
              (fun m => (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (t * Complex.I))
              (fun n => (φ n * (n : ℂ) ^ (t * Complex.I)) / (L : ℂ))
            - LBilin (A - 1) M c (grossenChar chi k)
              (fun m => (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (t * Complex.I))
              (fun n => (φ n * (n : ℂ) ^ (t * Complex.I)) / (L : ℂ))) := by
        rw [hsplit, ← hrel1, ← hrel2]
        ring
      rw [hcombine]
      calc ‖L * (LBilin Bhi M c (grossenChar chi k)
              (fun m => (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (t * Complex.I))
              (fun n => (φ n * (n : ℂ) ^ (t * Complex.I)) / (L : ℂ))
            - LBilin (A - 1) M c (grossenChar chi k)
              (fun m => (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (t * Complex.I))
              (fun n => (φ n * (n : ℂ) ^ (t * Complex.I)) / (L : ℂ)))‖
          ≤ L * (C31 * τ * (4 * (((A:ℝ) ^ ((1:ℝ)/12)) * ((N:ℝ) ^ ((11:ℝ)/12))
              + (N:ℝ) * ((A:ℝ) ^ ((1:ℝ)/12))⁻¹) * ((2*(N:ℝ) + (c:ℝ) + 2))^ε)
            + C31 * τ * (4 * (((A:ℝ) ^ ((1:ℝ)/12)) * ((N:ℝ) ^ ((11:ℝ)/12))
              + (N:ℝ) * ((A:ℝ) ^ ((1:ℝ)/12))⁻¹) * ((2*(N:ℝ) + (c:ℝ) + 2))^ε)) := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hL)
            exact le_trans (norm_sub_le _ _) (add_le_add (hX Bhi hBhiA) (hX (A - 1) hAm1A))
        _ = 8 * C31 * τ * L *
            (((A:ℝ) ^ ((1:ℝ)/12)) * ((N:ℝ) ^ ((11:ℝ)/12))
              + (N:ℝ) * ((A:ℝ) ^ ((1:ℝ)/12))⁻¹) * ((2*(N:ℝ) + (c:ℝ) + 2))^ε := by ring
    calc ‖∑ a ∈ Finset.Icc A Bhi, (ArithmeticFunction.moebius a : ℂ) *
          (a : ℂ) ^ (t * Complex.I) *
          ∑ n ∈ Finset.Icc 1 M, φ n * (n : ℂ) ^ (t * Complex.I) *
            quadEigen (grossenChar chi k) (c * (a * n))‖
        ≤ 8 * C31 * τ * L *
            (((A:ℝ) ^ ((1:ℝ)/12)) * ((N:ℝ) ^ ((11:ℝ)/12))
              + (N:ℝ) * ((A:ℝ) ^ ((1:ℝ)/12))⁻¹) * ((2*(N:ℝ) + (c:ℝ) + 2))^ε := hnorm
      _ ≤ 8 * C31 * τ * L *
            (((A:ℝ) ^ ((1:ℝ)/12)) * ((N:ℝ) ^ ((11:ℝ)/12))
              + (N:ℝ) * ((A:ℝ) ^ ((1:ℝ)/12))⁻¹) * ((2*(N:ℝ) + (c:ℝ) + 2))^ε
            * (Real.log ((N:ℝ) + 2))^(1:ℝ) := by
          have h1 : (1:ℝ) ≤ (Real.log ((N:ℝ) + 2))^(1:ℝ) := by
            rw [Real.rpow_one]; exact hlogN1
          exact le_mul_of_one_le_right (by positivity) h1

/-! ## The dyadic block bound (ε-form) -/

/-- **Main block bound, ε-form**: the dyadic block `[A, Bhi]` of the bilinear form is bounded by
`τ(c)·L·(A^{1/12}N^{11/12} + N A^{-1/12})·(2N+c+2)^ε·(log(N+2))^B`. -/
theorem t2psi_block_bilinear_gen_eps (h31 : Work.FIArea7.Prop231) (ε : ℝ) (hε : 0 < ε) :
    ∃ K B : ℝ, 0 < K ∧ 0 < B ∧
      ∀ (N c A Bhi : ℕ) (k : ℤ) (chi : GaussianInt → ℂ) (h : ℝ → ℝ)
        (φ : ℕ → ℂ) (L : ℝ),
        1 ≤ N → 1 ≤ c → 1 ≤ A → A ≤ Bhi → Bhi ≤ 2 * A - 1 →
        (∀ z, ‖chi z‖ ≤ 1) →
        (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2) →
        0 < L → (∀ n : ℕ, ‖φ n‖ ≤ L) →
        MeasureTheory.Integrable (fun t : ℝ => (h t : ℂ)) →
        (∫ t : ℝ, |h t|) < Real.log (6 * (N : ℝ)) →
        (∀ kk : ℕ, 1 ≤ kk → (∫ t : ℝ, (h t : ℂ) * (kk : ℂ) ^ (t * Complex.I))
            = if (kk : ℝ) ≤ (N : ℝ) then 1 else 0) →
        ‖∑ a ∈ Finset.Icc A Bhi, (ArithmeticFunction.moebius a : ℂ) *
            ∑ n ∈ Finset.Icc 1 (N / a),
              φ n * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (a * n))‖
          ≤ K * ((c.divisors.card : ℕ) : ℝ) * L *
              (((A : ℝ) ^ ((1:ℝ)/12)) * ((N : ℝ) ^ ((11:ℝ)/12))
                + (N : ℝ) * ((A : ℝ) ^ (-(1:ℝ)/12)))
              * ((2 * (N : ℝ) + (c : ℝ) + 2) ^ ε)
              * (Real.log ((N : ℝ) + 2)) ^ B := by
  obtain ⟨K', B', hK', hB', hBle⟩ := t2psi_block_bracket_le_eps h31 ε hε
  refine ⟨3 * K', B' + 1, by positivity, by linarith, ?_⟩
  intro N c A Bhi k chi h φ L hN hc hA hAB hBhi2 hchi hchimul hL hφ hint hint1 hsep
  rw [t2psi3_block_integral_repr h N c A Bhi k chi φ hA hint hsep]
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hlogN : (0:ℝ) < Real.log ((N:ℝ) + 2) := Real.log_pos (by linarith)
  set Sq : ℝ := ((A:ℝ) ^ ((1:ℝ)/12)) * ((N:ℝ) ^ ((11:ℝ)/12))
      + (N:ℝ) * ((A:ℝ) ^ (-(1:ℝ)/12)) with hSqdef
  have hSqnn : (0:ℝ) ≤ Sq := by rw [hSqdef]; positivity
  have hepsnn : (0:ℝ) ≤ (2 * (N:ℝ) + (c:ℝ) + 2)^ε := Real.rpow_nonneg (by positivity) ε
  have hlognn : (0:ℝ) ≤ (Real.log ((N:ℝ) + 2))^B' := Real.rpow_nonneg (le_of_lt hlogN) B'
  have hn : (0:ℝ) ≤ K' * ((c.divisors.card : ℕ) : ℝ) * L * Sq
      * (2 * (N:ℝ) + (c:ℝ) + 2)^ε * (Real.log ((N:ℝ) + 2))^B' := by
    have h1 : (0:ℝ) ≤ ((c.divisors.card : ℕ) : ℝ) := by positivity
    positivity
  have hb : ∀ t : ℝ, ‖∑ a ∈ Finset.Icc A Bhi, (ArithmeticFunction.moebius a : ℂ) *
        (a : ℂ) ^ (t * Complex.I) *
        ∑ n ∈ Finset.Icc 1 (N / A), φ n * (n : ℂ) ^ (t * Complex.I) *
          quadEigen (grossenChar chi k) (c * (a * n))‖
      ≤ K' * ((c.divisors.card : ℕ) : ℝ) * L * Sq
          * (2 * (N:ℝ) + (c:ℝ) + 2)^ε * (Real.log ((N:ℝ) + 2))^B' :=
    fun t => hBle N c A Bhi k chi φ L t hN hc hA hAB hBhi2 hchi hchimul hL hφ
  have h6N : Real.log (6 * (N:ℝ)) ≤ 3 * Real.log ((N:ℝ) + 2) := by
    have hN2 : (3:ℝ) ≤ (N:ℝ) + 2 := by
      have : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
      linarith
    have hsq : (6:ℝ) ≤ ((N:ℝ) + 2)^2 := by nlinarith [hN2]
    have hle : 6 * (N:ℝ) ≤ ((N:ℝ) + 2)^3 := by nlinarith [hsq, hNpos]
    calc Real.log (6 * (N:ℝ)) ≤ Real.log (((N:ℝ) + 2)^3) := Real.log_le_log (by positivity) hle
      _ = 3 * Real.log ((N:ℝ) + 2) := by rw [Real.log_pow]; norm_num
  have hrpow : (Real.log ((N:ℝ) + 2))^(B' + 1)
      = (Real.log ((N:ℝ) + 2))^B' * Real.log ((N:ℝ) + 2) := by
    rw [Real.rpow_add hlogN, Real.rpow_one]
  calc ‖∫ t : ℝ, (h t : ℂ) *
        (∑ a ∈ Finset.Icc A Bhi, (ArithmeticFunction.moebius a : ℂ) *
          (a : ℂ) ^ (t * Complex.I) *
          ∑ n ∈ Finset.Icc 1 (N / A), φ n * (n : ℂ) ^ (t * Complex.I) *
            quadEigen (grossenChar chi k) (c * (a * n)))‖
      ≤ (K' * ((c.divisors.card : ℕ) : ℝ) * L * Sq
          * (2 * (N:ℝ) + (c:ℝ) + 2)^ε * (Real.log ((N:ℝ) + 2))^B')
          * ∫ t : ℝ, |h t| := t2psi3_block_integral_bound _ _ _ hint hb
    _ ≤ (K' * ((c.divisors.card : ℕ) : ℝ) * L * Sq
          * (2 * (N:ℝ) + (c:ℝ) + 2)^ε * (Real.log ((N:ℝ) + 2))^B')
          * Real.log (6 * (N:ℝ)) := mul_le_mul_of_nonneg_left (le_of_lt hint1) hn
    _ ≤ (K' * ((c.divisors.card : ℕ) : ℝ) * L * Sq
          * (2 * (N:ℝ) + (c:ℝ) + 2)^ε * (Real.log ((N:ℝ) + 2))^B')
          * (3 * Real.log ((N:ℝ) + 2)) := mul_le_mul_of_nonneg_left h6N hn
    _ = 3 * K' * ((c.divisors.card : ℕ) : ℝ) * L * Sq
          * (2 * (N:ℝ) + (c:ℝ) + 2)^ε * (Real.log ((N:ℝ) + 2))^(B' + 1) := by
        rw [hrpow]; ring

/-! ## The bound on the third Vaughan term -/

/-- **The third Vaughan term `S₃`** with the sharp exponent `75/76 + 1/20000`. -/
theorem t2psi_S3_bound3 (h31 : Work.FIArea7.Prop231) :
    ∃ K B : ℝ, 0 < K ∧ 0 < B ∧
      ∀ (N c Y : ℕ) (k : ℤ) (chi : GaussianInt → ℂ),
        1 ≤ N → 1 ≤ c → 1 ≤ Y → (c : ℝ) ≤ (N : ℝ) →
        (N : ℝ) ^ ((3:ℝ)/19) < (Y : ℝ) →
        (∀ z, ‖chi z‖ ≤ 1) →
        (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2) →
        ‖∑ a ∈ Finset.Icc (Y + 1) (N / Y), (ArithmeticFunction.moebius a : ℂ) *
            ∑ n ∈ Finset.Icc 1 (N / a),
              (∑ b ∈ n.divisors.filter (fun b => Y < b),
                  ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ)) *
                Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (a * n))‖
          ≤ K * (c : ℝ) * (N : ℝ) ^ ((75:ℝ)/76 + 1/20000)
              * (Real.log ((N : ℝ) + 2)) ^ B := by
  obtain ⟨Kb, Bb, hKb, hBb, hblock⟩ := t2psi_block_bilinear_gen_eps h31 (1/20000) (by norm_num)
  refine ⟨9 * 5 ^ ((1:ℝ)/20000) * Kb, Bb + 2, by positivity, by linarith, ?_⟩
  intro N c Y k chi hN hc hY hcN hY3 hchi hchimul
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hYpos : (0:ℝ) < (Y:ℝ) := by exact_mod_cast hY
  obtain ⟨h, hhL1, hsep⟩ := exists_separating_function (N : ℝ) (by exact_mod_cast hN)
  have hInt : Integrable (fun t : ℝ => (h t : ℂ)) := by
    refine Integrable.of_integral_ne_zero ?_
    have h1 := hsep 1 le_rfl
    rw [if_pos (by exact_mod_cast hN)] at h1
    have h2 : (∫ t : ℝ, (h t : ℂ) * ((1 : ℕ) : ℂ) ^ (t * Complex.I)) = ∫ t : ℝ, (h t : ℂ) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp [Complex.one_cpow]
    rw [h2] at h1
    rw [h1]
    norm_num
  set L : ℝ := Real.log ((N : ℝ) + 2) with hLdef
  have hLge1 : 1 ≤ L := by
    rw [hLdef]
    have h3 : (3 : ℝ) ≤ (N : ℝ) + 2 := by linarith
    linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 3) h3, Real.log_three_gt_d9]
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hLge1
  have hφb : ∀ n : ℕ, ‖(if n ≤ N then t2psiWd Y n else 0)‖ ≤ L := by
    intro n
    by_cases hn : n ≤ N
    · rw [if_pos hn]
      have h1 : ‖t2psiWd Y n‖ ≤ Real.log n := t2psiWd_bound Y n
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · rw [hn0] at h1 ⊢
        rw [show Real.log ((0 : ℕ) : ℝ) = 0 by simp] at h1
        rw [hLdef]
        have h3 : (0 : ℝ) ≤ Real.log ((N : ℝ) + 2) :=
          Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N])
        linarith
      · have h2 : Real.log (n : ℝ) ≤ Real.log (N : ℝ) :=
          Real.log_le_log (by exact_mod_cast hnpos) (by exact_mod_cast hn)
        have h3 : Real.log (N : ℝ) ≤ L := by
          rw [hLdef]
          exact Real.log_le_log (by exact_mod_cast (show 0 < N by omega)) (by linarith)
        linarith
    · rw [if_neg hn]
      simp only [norm_zero]
      linarith
  have hg : ∀ a ∈ Finset.Icc (Y + 1) (N / Y),
      Nat.log2 a ∈ Finset.range ((N / Y).log2 + 1) := by
    intro a ha
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (nat_log2_mono (Finset.mem_Icc.mp ha).2)
  have key : ∀ j ∈ Finset.range ((N / Y).log2 + 1),
      ‖∑ a ∈ (Finset.Icc (Y + 1) (N / Y)).filter (fun a => Nat.log2 a = j),
          (ArithmeticFunction.moebius a : ℂ) *
            ∑ n ∈ Finset.Icc 1 (N / a),
              t2psiWd Y n * quadEigen (grossenChar chi k) (c * (a * n))‖
        ≤ 3 * 5 ^ ((1:ℝ)/20000) * Kb * ((c.divisors.card : ℕ) : ℝ) * L
            * ((N:ℝ) ^ ((1:ℝ) + 1/20000) * (Y:ℝ) ^ (-((1:ℝ)/12))) * L ^ Bb := by
    intro j hj
    set Aj : ℕ := max (2 ^ j) (Y + 1) with hAjdef
    set Bj : ℕ := min (2 ^ (j + 1) - 1) (N / Y) with hBjdef
    have hfib : (Finset.Icc (Y + 1) (N / Y)).filter (fun a => Nat.log2 a = j)
        = Finset.Icc Aj Bj := by
      rw [t2psi_fiber_eq, ← hAjdef, ← hBjdef]
    rw [hfib]
    have hAj1 : 1 ≤ Aj := by rw [hAjdef]; omega
    have hAjY : Y < 2 * Aj := by rw [hAjdef]; omega
    have hBjle : Bj ≤ 2 * Aj - 1 := by
      have h1 : Bj ≤ 2 ^ (j + 1) - 1 := by rw [hBjdef]; exact min_le_left _ _
      have h2 : 2 ^ j ≤ Aj := by rw [hAjdef]; exact le_max_left _ _
      have h3 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
      omega
    by_cases hle : Aj ≤ Bj
    · have hAjN : Aj ≤ N / Y := le_trans hle (by rw [hBjdef]; exact min_le_right _ _)
      have hbl := hblock N c Aj Bj k chi h (fun n : ℕ => if n ≤ N then t2psiWd Y n else 0) L
        hN hc hAj1 hle hBjle hchi hchimul hLpos hφb hInt hhL1 hsep
      rw [← hLdef] at hbl
      rw [show (-(1:ℝ)/12) = (-((1:ℝ)/12)) by norm_num] at hbl
      have hsum_eq : (∑ a ∈ Finset.Icc Aj Bj, (ArithmeticFunction.moebius a : ℂ) *
            ∑ n ∈ Finset.Icc 1 (N / a),
              t2psiWd Y n * quadEigen (grossenChar chi k) (c * (a * n)))
          = ∑ a ∈ Finset.Icc Aj Bj, (ArithmeticFunction.moebius a : ℂ) *
            ∑ n ∈ Finset.Icc 1 (N / a),
              (if n ≤ N then t2psiWd Y n else 0) *
                quadEigen (grossenChar chi k) (c * (a * n)) := by
        refine Finset.sum_congr rfl (fun a ha => ?_)
        congr 1
        refine Finset.sum_congr rfl (fun n hn => ?_)
        have h1 : n ≤ N / a := (Finset.mem_Icc.mp hn).2
        have ha1 : 1 ≤ a := by have := (Finset.mem_Icc.mp ha).1; omega
        rw [if_pos (by have := Nat.div_le_self N a; omega : n ≤ N)]
      rw [← hsum_eq] at hbl
      have hrp := t2psi_rpow_le Aj N Y hN hY hAjY hAjN
      have h2 : (2 : ℝ) ^ ((1 : ℝ) / 12) ≤ 2 := by
        have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (1 : ℝ) / 12 ≤ 1)
        simpa using hh
      have hYnn : (0 : ℝ) ≤ (N : ℝ) * (Y : ℝ) ^ (-((1 : ℝ) / 12)) := by positivity
      have hX : (Aj : ℝ) ^ ((1 : ℝ) / 12) * (N : ℝ) ^ ((11 : ℝ) / 12)
            + (N : ℝ) * (Aj : ℝ) ^ (-((1 : ℝ) / 12))
          ≤ 3 * (N : ℝ) * (Y : ℝ) ^ (-((1 : ℝ) / 12)) := by
        have h22 : (N : ℝ) * (Aj : ℝ) ^ (-((1 : ℝ) / 12))
            ≤ 2 ^ ((1 : ℝ) / 12) * ((N : ℝ) * (Y : ℝ) ^ (-((1 : ℝ) / 12))) := by
          refine le_trans hrp.2 (le_of_eq ?_)
          ring
        calc (Aj : ℝ) ^ ((1 : ℝ) / 12) * (N : ℝ) ^ ((11 : ℝ) / 12)
              + (N : ℝ) * (Aj : ℝ) ^ (-((1 : ℝ) / 12))
            ≤ (N : ℝ) * (Y : ℝ) ^ (-((1 : ℝ) / 12))
              + 2 ^ ((1 : ℝ) / 12) * ((N : ℝ) * (Y : ℝ) ^ (-((1 : ℝ) / 12))) := by
              linarith [hrp.1, h22]
          _ = (1 + 2 ^ ((1 : ℝ) / 12)) * ((N : ℝ) * (Y : ℝ) ^ (-((1 : ℝ) / 12))) := by ring
          _ ≤ 3 * ((N : ℝ) * (Y : ℝ) ^ (-((1 : ℝ) / 12))) := by
              apply mul_le_mul_of_nonneg_right _ hYnn
              linarith
          _ = 3 * (N : ℝ) * (Y : ℝ) ^ (-((1 : ℝ) / 12)) := by ring
      have hstep1 : ‖∑ a ∈ Finset.Icc Aj Bj, (ArithmeticFunction.moebius a : ℂ) *
            ∑ n ∈ Finset.Icc 1 (N / a),
              t2psiWd Y n * quadEigen (grossenChar chi k) (c * (a * n))‖
          ≤ Kb * ((c.divisors.card : ℕ) : ℝ) * L
              * (3 * (N:ℝ) * (Y:ℝ) ^ (-((1:ℝ)/12)))
              * (2 * (N:ℝ) + (c:ℝ) + 2) ^ ((1:ℝ)/20000) * L ^ Bb := by
        calc ‖∑ a ∈ Finset.Icc Aj Bj, (ArithmeticFunction.moebius a : ℂ) *
              ∑ n ∈ Finset.Icc 1 (N / a),
                t2psiWd Y n * quadEigen (grossenChar chi k) (c * (a * n))‖
            ≤ Kb * ((c.divisors.card : ℕ) : ℝ) * L
                * ((Aj:ℝ) ^ ((1:ℝ)/12) * (N:ℝ) ^ ((11:ℝ)/12)
                   + (N:ℝ) * (Aj:ℝ) ^ (-((1:ℝ)/12)))
                * (2 * (N:ℝ) + (c:ℝ) + 2) ^ ((1:ℝ)/20000) * L ^ Bb := hbl
          _ ≤ Kb * ((c.divisors.card : ℕ) : ℝ) * L
                * (3 * (N:ℝ) * (Y:ℝ) ^ (-((1:ℝ)/12)))
                * (2 * (N:ℝ) + (c:ℝ) + 2) ^ ((1:ℝ)/20000) * L ^ Bb := by
              refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (le_of_lt hLpos) Bb)
              refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) ((1:ℝ)/20000))
              exact mul_le_mul_of_nonneg_left hX (by positivity)
      have hstep2 : Kb * ((c.divisors.card : ℕ) : ℝ) * L
              * (3 * (N:ℝ) * (Y:ℝ) ^ (-((1:ℝ)/12)))
              * (2 * (N:ℝ) + (c:ℝ) + 2) ^ ((1:ℝ)/20000) * L ^ Bb
          ≤ 3 * 5 ^ ((1:ℝ)/20000) * Kb * ((c.divisors.card : ℕ) : ℝ) * L
              * ((N:ℝ) ^ ((1:ℝ) + 1/20000) * (Y:ℝ) ^ (-((1:ℝ)/12))) * L ^ Bb := by
        have h5N : (5 * (N:ℝ)) ^ ((1:ℝ)/20000)
            = 5 ^ ((1:ℝ)/20000) * (N:ℝ) ^ ((1:ℝ)/20000) :=
          Real.mul_rpow (by norm_num) (Nat.cast_nonneg N)
        have hε5 : (2 * (N:ℝ) + (c:ℝ) + 2) ^ ((1:ℝ)/20000)
            ≤ 5 ^ ((1:ℝ)/20000) * (N:ℝ) ^ ((1:ℝ)/20000) := by
          rw [← h5N]
          exact Real.rpow_le_rpow (by positivity) (by nlinarith [hcN, hN1]) (by norm_num)
        have hNε : (N:ℝ) ^ ((1:ℝ) + 1/20000) = (N:ℝ) * (N:ℝ) ^ ((1:ℝ)/20000) := by
          rw [Real.rpow_add hNpos, Real.rpow_one]
        calc Kb * ((c.divisors.card : ℕ) : ℝ) * L
                * (3 * (N:ℝ) * (Y:ℝ) ^ (-((1:ℝ)/12)))
                * (2 * (N:ℝ) + (c:ℝ) + 2) ^ ((1:ℝ)/20000) * L ^ Bb
              ≤ Kb * ((c.divisors.card : ℕ) : ℝ) * L
                * (3 * (N:ℝ) * (Y:ℝ) ^ (-((1:ℝ)/12)))
                * (5 ^ ((1:ℝ)/20000) * (N:ℝ) ^ ((1:ℝ)/20000)) * L ^ Bb := by
                refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (le_of_lt hLpos) Bb)
                exact mul_le_mul_of_nonneg_left hε5 (by positivity)
          _ = 3 * 5 ^ ((1:ℝ)/20000) * Kb * ((c.divisors.card : ℕ) : ℝ) * L
                * ((N:ℝ) ^ ((1:ℝ) + 1/20000) * (Y:ℝ) ^ (-((1:ℝ)/12))) * L ^ Bb := by
                rw [hNε]; ring
      exact le_trans hstep1 hstep2
    · have hempty : Finset.Icc Aj Bj = ∅ := Finset.Icc_eq_empty_iff.mpr hle
      rw [hempty]
      simp only [Finset.sum_empty, norm_zero]
      have hLnn : (0:ℝ) ≤ L := le_of_lt hLpos
      have hYnn2 : (0:ℝ) ≤ (Y:ℝ) ^ (-((1:ℝ)/12)) := Real.rpow_nonneg (le_of_lt hYpos) _
      have hNεnn : (0:ℝ) ≤ (N:ℝ) ^ ((1:ℝ) + 1/20000) := Real.rpow_nonneg (Nat.cast_nonneg N) _
      have hLbnn : (0:ℝ) ≤ L ^ Bb := Real.rpow_nonneg hLnn Bb
      positivity
  have hτ : ((c.divisors.card : ℕ) : ℝ) ≤ (c : ℝ) := by
    have hsub : c.divisors ⊆ Finset.Icc 1 c := fun d hd =>
      Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.divisor_le hd⟩
    have hcard : c.divisors.card ≤ (Finset.Icc 1 c).card := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard
    have h2 : ((c.divisors.card : ℕ) : ℝ) ≤ ((c + 1 - 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    simpa using h2
  have hJle : (((N / Y).log2 + 1 : ℕ) : ℝ) ≤ 3 * L := by
    have h := t2psi_log2_le (N / Y) N hN (Nat.div_le_self N Y)
    rw [hLdef]
    push_cast
    linarith
  have hYN : (Y:ℝ) ^ (-((1:ℝ)/12)) ≤ (N:ℝ) ^ (-((1:ℝ)/76)) := by
    have h1 : (N:ℝ) ^ ((1:ℝ)/76) ≤ (Y:ℝ) ^ ((1:ℝ)/12) := by
      have h2 : (N:ℝ) ^ ((1:ℝ)/76) = ((N:ℝ) ^ ((3:ℝ)/19)) ^ ((1:ℝ)/12) := by
        rw [← Real.rpow_mul (Nat.cast_nonneg N)]
        congr 1
        norm_num
      rw [h2]
      exact Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg N) _) (le_of_lt hY3) (by norm_num)
    rw [Real.rpow_neg (le_of_lt hYpos), Real.rpow_neg (le_of_lt hNpos)]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos hYpos _) (Real.rpow_pos_of_pos hNpos _)).mpr h1
  have hNpow : (N:ℝ) ^ ((1:ℝ) + 1/20000) * (N:ℝ) ^ (-((1:ℝ)/76))
      = (N:ℝ) ^ ((75:ℝ)/76 + 1/20000) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    norm_num
  have hNY : (N:ℝ) ^ ((1:ℝ) + 1/20000) * (Y:ℝ) ^ (-((1:ℝ)/12))
      ≤ (N:ℝ) ^ ((75:ℝ)/76 + 1/20000) :=
    le_trans (mul_le_mul_of_nonneg_left hYN (Real.rpow_nonneg (Nat.cast_nonneg N) _)) hNpow.le
  have hnorm : ‖∑ a ∈ Finset.Icc (Y + 1) (N / Y), (ArithmeticFunction.moebius a : ℂ) *
        ∑ n ∈ Finset.Icc 1 (N / a),
          (∑ b ∈ n.divisors.filter (fun b => Y < b),
              ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ)) *
            quadEigen (grossenChar chi k) (c * (a * n))‖
      ≤ 9 * 5 ^ ((1:ℝ)/20000) * Kb * (c : ℝ) * (N : ℝ) ^ ((75:ℝ)/76 + 1/20000)
          * L ^ (Bb + 2) := by
    change ‖∑ a ∈ Finset.Icc (Y + 1) (N / Y), (ArithmeticFunction.moebius a : ℂ) *
        ∑ n ∈ Finset.Icc 1 (N / a),
          t2psiWd Y n * quadEigen (grossenChar chi k) (c * (a * n))‖
      ≤ 9 * 5 ^ ((1:ℝ)/20000) * Kb * (c : ℝ) * (N : ℝ) ^ ((75:ℝ)/76 + 1/20000)
          * L ^ (Bb + 2)
    calc ‖∑ a ∈ Finset.Icc (Y + 1) (N / Y), (ArithmeticFunction.moebius a : ℂ) *
            ∑ n ∈ Finset.Icc 1 (N / a),
              t2psiWd Y n * quadEigen (grossenChar chi k) (c * (a * n))‖
        = ‖∑ j ∈ Finset.range ((N / Y).log2 + 1),
            ∑ a ∈ (Finset.Icc (Y + 1) (N / Y)).filter (fun a => Nat.log2 a = j),
              (ArithmeticFunction.moebius a : ℂ) *
                ∑ n ∈ Finset.Icc 1 (N / a),
                  t2psiWd Y n * quadEigen (grossenChar chi k) (c * (a * n))‖ := by
          rw [← Finset.sum_fiberwise_of_maps_to hg]
      _ ≤ ∑ j ∈ Finset.range ((N / Y).log2 + 1),
            ‖∑ a ∈ (Finset.Icc (Y + 1) (N / Y)).filter (fun a => Nat.log2 a = j),
              (ArithmeticFunction.moebius a : ℂ) *
                ∑ n ∈ Finset.Icc 1 (N / a),
                  t2psiWd Y n * quadEigen (grossenChar chi k) (c * (a * n))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range ((N / Y).log2 + 1),
            3 * 5 ^ ((1:ℝ)/20000) * Kb * ((c.divisors.card : ℕ) : ℝ) * L
              * ((N:ℝ) ^ ((1:ℝ) + 1/20000) * (Y:ℝ) ^ (-((1:ℝ)/12))) * L ^ Bb :=
          Finset.sum_le_sum key
      _ = (((N / Y).log2 + 1 : ℕ) : ℝ)
            * (3 * 5 ^ ((1:ℝ)/20000) * Kb * ((c.divisors.card : ℕ) : ℝ) * L
              * ((N:ℝ) ^ ((1:ℝ) + 1/20000) * (Y:ℝ) ^ (-((1:ℝ)/12))) * L ^ Bb) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (3 * L) * (3 * 5 ^ ((1:ℝ)/20000) * Kb * ((c.divisors.card : ℕ) : ℝ) * L
              * ((N:ℝ) ^ ((1:ℝ) + 1/20000) * (Y:ℝ) ^ (-((1:ℝ)/12))) * L ^ Bb) := by
          apply mul_le_mul_of_nonneg_right hJle
          positivity
      _ ≤ (3 * L) * (3 * 5 ^ ((1:ℝ)/20000) * Kb * ((c.divisors.card : ℕ) : ℝ) * L
              * ((N:ℝ) ^ ((75:ℝ)/76 + 1/20000)) * L ^ Bb) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (le_of_lt hLpos) Bb)
          exact mul_le_mul_of_nonneg_left hNY (by positivity)
      _ = 9 * 5 ^ ((1:ℝ)/20000) * Kb * ((c.divisors.card : ℕ) : ℝ)
            * (N:ℝ) ^ ((75:ℝ)/76 + 1/20000) * L ^ (Bb + 2) := by
          rw [Real.rpow_add hLpos, Real.rpow_two]
          ring
      _ ≤ 9 * 5 ^ ((1:ℝ)/20000) * Kb * (c : ℝ) * (N:ℝ) ^ ((75:ℝ)/76 + 1/20000)
            * L ^ (Bb + 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (le_of_lt hLpos) (Bb+2))
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg N) _)
          exact mul_le_mul_of_nonneg_left hτ (by positivity)
  exact hnorm

end

end Work.FIArea7
