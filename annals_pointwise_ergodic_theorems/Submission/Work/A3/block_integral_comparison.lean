import Mathlib
import Submission.Commons.Analysis.ExponentialSums.monic_poly_major_arc_approx_coeff

namespace Work.A3

open MeasureTheory intervalIntegral

open scoped BigOperators

/-- Arithmetic of the residue-block length `P = (N-r)/q + 1`: for `r ≤ N` the block
`r, r+q, …, r+(P-1)q` stays inside `[0, N+q]` (the largest term is `< r + P q ≤ N + q`). -/
private lemma block_P_le (N q r : ℕ) (_hq : 1 ≤ q) (hrN : r ≤ N) :
    ((N - r) / q + 1) * q + r ≤ N + q := by
  have h1 : (N - r) / q * q ≤ N - r := Nat.div_mul_le_self _ _
  have h2 : ((N - r) / q + 1) * q = (N - r) / q * q + q := by rw [add_mul, one_mul]
  omega

/-- Arithmetic of the residue-block length `P = (N-r)/q + 1`: for `r < q ≤ N` the block
reaches past `N`, i.e. `r + (P-1)q ≥ N - q` and hence `P q + q ≥ N`. -/
private lemma block_P_ge (N q r : ℕ) (hq : 1 ≤ q) (hr : r < q) (hrN : r ≤ N) :
    N ≤ ((N - r) / q + 1) * q + q := by
  have hdec : (N - r) / q * q + (N - r) % q = N - r := by
    have h := Nat.div_add_mod (N - r) q
    rw [Nat.mul_comm q ((N - r) / q)] at h
    exact h
  have hmod : (N - r) % q < q := Nat.mod_lt _ (by omega)
  have h2 : ((N - r) / q + 1) * q = (N - r) / q * q + q := by rw [add_mul, one_mul]
  omega

/-- Comparison of one residue block `∑_{p<P} φ(r + p*q)` of a Lipschitz modulus-`1` function with the oscillatory integral `∫_0^{N/q} φ(q*t) dt`.  The number of terms is `P = (N-r)/q + 1`, comparable to `N/q` (for `r ≤ N` it satisfies `P*q + r ≤ N+q` and `N ≤ P*q + q`, so `Commons.Analysis.ExponentialSums.phase_block_bound` applies directly; for `r > N` the block is the single term `φ r` and the bound is immediate), so the Riemann-sum error is `2 L (N+q) + 1`.  Import `Submission.Commons.Analysis.ExponentialSums.monic_poly_major_arc_approx_coeff` for `phase_block_bound`. -/
lemma block_integral_comparison (N q : ℕ) (hq : 1 ≤ q) (hN : 1 ≤ N)
    (φ : ℝ → ℂ) (L : ℝ) (hL : 0 ≤ L) (hφ : Continuous φ)
    (hlip : ∀ x ∈ Set.Icc (0:ℝ) ((N:ℝ)+(q:ℝ)), ∀ y ∈ Set.Icc (0:ℝ) ((N:ℝ)+(q:ℝ)),
      ‖φ x - φ y‖ ≤ L * |x - y|)
    (hnorm : ∀ x ∈ Set.Icc (0:ℝ) ((N:ℝ)+(q:ℝ)), ‖φ x‖ ≤ 1)
    (r : ℕ) (hr : r < q) :
    ‖(∑ p ∈ Finset.range ((N - r) / q + 1), φ ((r + p * q : ℕ) : ℝ))
        - ∫ t in (0:ℝ)..((N:ℝ)/(q:ℝ)), φ ((q:ℝ) * t)‖
      ≤ 2 * L * ((N:ℝ) + (q:ℝ)) + 1 := by
  rcases lt_or_ge N r with hrN | hrN
  · -- ### Case `N < r`: then `r > N` and the block `(N-r)/q + 1 = 1` is the single term `φ r`.
    -- Since `r < q ≤ N + q`, the value `φ r` is within `L * r * (N/q) + (1 - N/q)` of the
    -- integral, which is at most `2 L (N+q) + 1`.
    have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hNnn : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
    have hqnn : (0:ℝ) ≤ (q:ℝ) := Nat.cast_nonneg q
    have hrnn : (0:ℝ) ≤ (r:ℝ) := Nat.cast_nonneg r
    have hNr : N - r = 0 := Nat.sub_eq_zero_of_le (le_of_lt hrN)
    have hP1 : (N - r) / q + 1 = 1 := by rw [hNr]; simp
    have hsum : (∑ p ∈ Finset.range ((N - r) / q + 1), φ ((r + p * q : ℕ) : ℝ)) = φ (r:ℝ) := by
      rw [hP1, Finset.sum_range_one]
      simp
    rw [hsum]
    set c : ℝ := (N:ℝ)/(q:ℝ) with hcdef
    have hc0 : 0 ≤ c := by rw [hcdef]; positivity
    have hNq : N ≤ q := le_of_lt (lt_trans hrN hr)
    have hc1 : c ≤ 1 := by
      rw [hcdef, div_le_one hq0]
      exact_mod_cast hNq
    have hrmem : (r:ℝ) ∈ Set.Icc (0:ℝ) ((N:ℝ)+(q:ℝ)) := by
      refine ⟨hrnn, ?_⟩
      have h1 : (r:ℝ) < (q:ℝ) := by exact_mod_cast hr
      linarith
    have hφr : ‖φ (r:ℝ)‖ ≤ 1 := hnorm _ hrmem
    have hInt : IntervalIntegrable (fun t : ℝ => φ ((q:ℝ)*t)) volume (0:ℝ) c :=
      ((hφ.comp (by continuity)).continuousOn).intervalIntegrable_of_Icc hc0
    have hqc : (q:ℝ)*c = (N:ℝ) := by rw [hcdef]; field_simp
    -- `∫_0^c φ(qt) - φ r = ∫_0^c (φ(qt) - φ r) + (c-1) φ r`
    have hdecomp : (∫ t in (0:ℝ)..c, φ ((q:ℝ)*t)) - φ (r:ℝ)
        = (∫ t in (0:ℝ)..c, (φ ((q:ℝ)*t) - φ (r:ℝ))) + ((c - 1 : ℝ) : ℂ) * φ (r:ℝ) := by
      rw [intervalIntegral.integral_sub hInt intervalIntegrable_const, intervalIntegral.integral_const,
        Complex.real_smul]
      push_cast
      ring
    rw [norm_sub_rev, hdecomp]
    refine le_trans (norm_add_le _ _) ?_
    -- the Lipschitz part, estimated against the constant `φ r`
    have hA : ‖∫ t in (0:ℝ)..c, (φ ((q:ℝ)*t) - φ (r:ℝ))‖ ≤ L * (N:ℝ) := by
      have hbd : ∀ t ∈ Set.uIoc (0:ℝ) c, ‖φ ((q:ℝ)*t) - φ (r:ℝ)‖ ≤ L * (r:ℝ) := by
        intro t ht
        rw [Set.uIoc_of_le hc0] at ht
        have ht0 : 0 < t := ht.1
        have htle : t ≤ c := ht.2
        have hqt : (q:ℝ)*t ∈ Set.Icc (0:ℝ) ((N:ℝ)+(q:ℝ)) := by
          refine ⟨by positivity, ?_⟩
          have hmul : (q:ℝ)*t ≤ (q:ℝ)*c := mul_le_mul_of_nonneg_left htle (le_of_lt hq0)
          linarith [hmul, hqc]
        have hdist : |(q:ℝ)*t - (r:ℝ)| ≤ (r:ℝ) := by
          have hmul : (q:ℝ)*t ≤ (q:ℝ)*c := mul_le_mul_of_nonneg_left htle (le_of_lt hq0)
          have h3 : (N:ℝ) < (r:ℝ) := by exact_mod_cast hrN
          have hle : (q:ℝ)*t ≤ (r:ℝ) := by linarith [hmul, hqc]
          rw [abs_of_nonpos (by linarith : (q:ℝ)*t - (r:ℝ) ≤ 0)]
          linarith [mul_pos hq0 ht0]
        calc ‖φ ((q:ℝ)*t) - φ (r:ℝ)‖ ≤ L * |(q:ℝ)*t - (r:ℝ)| := hlip _ hqt _ hrmem
          _ ≤ L * (r:ℝ) := mul_le_mul_of_nonneg_left hdist hL
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun t : ℝ => φ ((q:ℝ)*t) - φ (r:ℝ)) (a := (0:ℝ)) (b := c) (C := L * (r:ℝ)) hbd
      refine le_trans h ?_
      rw [sub_zero, abs_of_nonneg hc0]
      have hr_le_q : (r:ℝ) ≤ (q:ℝ) := by exact_mod_cast le_of_lt hr
      have hrc : (r:ℝ) * c ≤ (N:ℝ) := by
        calc (r:ℝ)*c ≤ (q:ℝ)*c := mul_le_mul_of_nonneg_right hr_le_q hc0
          _ = (N:ℝ) := hqc
      rw [show L * (r:ℝ) * c = L * ((r:ℝ)*c) by ring]
      exact mul_le_mul_of_nonneg_left hrc hL
    -- the correction term `(c-1) φ r`, of modulus at most `1` because `c ≤ 1` and `‖φ r‖ ≤ 1`
    have hB : ‖((c - 1 : ℝ) : ℂ) * φ (r:ℝ)‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_real]
      have h1 : ‖(c - 1 : ℝ)‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonpos (by linarith), neg_sub]
        linarith
      calc ‖(c-1:ℝ)‖ * ‖φ (r:ℝ)‖ ≤ 1 * 1 :=
            mul_le_mul h1 hφr (norm_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have hLN : L * (N:ℝ) + 1 ≤ 2 * L * ((N:ℝ) + (q:ℝ)) + 1 := by
      nlinarith [hL, hNnn, hqnn, mul_nonneg hL hNnn, mul_nonneg hL hqnn]
    linarith [hA, hB, hLN]
  · -- ### Case `r ≤ N`: the block has `P = (N-r)/q + 1` terms with `P q + r ≤ N + q` and
    -- `N ≤ P q + q`, so the Riemann-sum comparison `phase_block_bound` applies verbatim.
    have hP_le_nat : ((N - r) / q + 1) * q + r ≤ N + q := block_P_le N q r hq hrN
    have hP_ge_nat : N ≤ ((N - r) / q + 1) * q + q := block_P_ge N q r hq hr hrN
    have hP_le : (((N - r) / q + 1 : ℕ) : ℝ) * (q:ℝ) + (r:ℝ) ≤ (N:ℝ) + (q:ℝ) := by
      exact_mod_cast hP_le_nat
    have hP_ge : (N:ℝ) ≤ (((N - r) / q + 1 : ℕ) : ℝ) * (q:ℝ) + (q:ℝ) := by
      exact_mod_cast hP_ge_nat
    have hmain := Commons.Analysis.ExponentialSums.phase_block_bound N q r ((N - r) / q + 1)
      φ L hL hφ hlip hnorm hq hN hr hP_le hP_ge
    -- `r + p*q = p*q + r`
    have hsum : (∑ p ∈ Finset.range ((N - r) / q + 1), φ ((r + p * q : ℕ) : ℝ))
        = ∑ p ∈ Finset.range ((N - r) / q + 1), φ (((p*q+r:ℕ)):ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      congr 1
      exact_mod_cast Nat.add_comm r (p * q)
    rw [hsum]
    exact hmain

end Work.A3
