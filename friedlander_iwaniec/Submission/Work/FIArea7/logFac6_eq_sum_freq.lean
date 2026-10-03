import Mathlib
import Submission.Work.FIArea7.LogFacFourier
import Submission.Work.FITop4.Defs6

/-!
# The frequency (Fourier) form of the `logFac6` expansion

`Work.FITop4.logFac6 z₁ z₂ = log(8|z₁z₂|/|Δ|)` is the round-6 normalisation of the *FI* (7.10)
main-term weight, with classical expansion

  `logFac6 z₁ z₂ = 2log2 + log4 + Σ_{n≥1} cos(2nt)/n`,  `t = arg z₂ − arg z₁`.

Here we record the *symmetric* (Kronecker) form of the same truncated expansion: summing over the
even, non-zero integers `k` with `|k| ≤ 2K` and using the unit complex numbers
`u₁ = z₁/|z₁|`, `u₂ = z₂/|z₂|`,

  `logFac6 z₁ z₂ = 2log2 + log4 + Σ_{k} (1/|k|)·u₁ᵏ·conj(u₂ᵏ) + O(1/(K|sin t|))`.

The point is that the summand is a genuine *product* `(z₁/|z₁|)ᵏ·(z̄₂/|z₂|)ᵏ`, which is the shape the
§16 character expansion consumes; the pairing `k ↔ −k` shows the whole sum is real with real part
`Σ_{n≤K} cos(2nt)/n`, i.e. the frequency expansion of `Work.FIArea7.logFac_eq_sum_cos`.
-/

namespace Work.FIArea7

open Finset
open Work.FIArea7.LogFacArg
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary helpers -/

lemma fi_norm_ofReal (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  rw [← Real.sqrt_sq_eq_abs, eq_comm, ← Real.sqrt_sq (norm_nonneg _)]
  congr 1
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
  ring

/-- `logFac6 = logFac + log 4`, `logFac = log(2|z₁z₂|/|Δ|)`. -/
lemma fi_logFac6_eq_logFac_add_log4 (z1 z2 : GaussianInt) (h : Work.FIPlan.Delta z1 z2 ≠ 0) :
    Work.FITop4.logFac6 z1 z2 = Work.FITop3.logFac z1 z2 + Real.log 4 := by
  have hz1 : z1 ≠ 0 := by rintro rfl; simp [Work.FIPlan.Delta] at h
  have hz2 : z2 ≠ 0 := by rintro rfl; simp [Work.FIPlan.Delta] at h
  have hprod : z1 * z2 ≠ 0 := mul_ne_zero hz1 hz2
  have hs : 0 < Real.sqrt ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) := by
    rw [Real.sqrt_pos]
    exact_mod_cast gnorm_pos_of_ne_zero hprod
  have hD : 0 < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by
    rw [Work.FIPlan.absDelta]
    exact_mod_cast Int.natAbs_pos.mpr h
  rw [Work.FITop4.logFac6, Work.FITop3.logFac]
  have hsplit : 8 * Real.sqrt ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)
        / (Work.FIPlan.absDelta z1 z2 : ℝ)
      = 4 * (2 * Real.sqrt ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)
        / (Work.FIPlan.absDelta z1 z2 : ℝ)) := by
    field_simp
    norm_num
  rw [hsplit, Real.log_mul (by norm_num) (by positivity)]
  ring

/-! ## Reindexing an even, symmetric sum over `Icc` -/

/-- Splitting off the two extreme even indices `±2(K+1)` from the filtered `Icc`. -/
lemma fi_Icc_filter_even_succ (K : ℕ) :
    (Finset.Icc (-(2*((K+1:ℕ):ℤ))) (2*((K+1:ℕ):ℤ))).filter (fun k => k ≠ 0 ∧ Even k)
    = insert (2*((K+1:ℕ):ℤ))
        (insert (-(2*((K+1:ℕ):ℤ)))
          ((Finset.Icc (-(2*(K:ℤ))) (2*(K:ℤ))).filter (fun k => k ≠ 0 ∧ Even k))) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hne, hev⟩
    rcases eq_or_ne k (2*((K+1:ℕ):ℤ)) with h | h
    · exact Or.inl h
    rcases eq_or_ne k (-(2*((K+1:ℕ):ℤ))) with h2 | h2
    · exact Or.inr (Or.inl h2)
    refine Or.inr (Or.inr ⟨⟨?_, ?_⟩, hne, hev⟩)
    · have hgt : -(2*((K+1:ℕ):ℤ)) < k := lt_of_le_of_ne hlo (Ne.symm h2)
      rcases hev with ⟨m, hm⟩
      push_cast at hgt ⊢
      omega
    · have hlt : k < 2*((K+1:ℕ):ℤ) := lt_of_le_of_ne hhi h
      rcases hev with ⟨m, hm⟩
      push_cast at hlt ⊢
      omega
  · rintro (rfl | rfl | ⟨⟨hlo2, hhi2⟩, hne, hev⟩)
    · exact ⟨⟨by push_cast; omega, by push_cast; omega⟩, by push_cast; omega,
        ⟨((K+1:ℕ):ℤ), by ring⟩⟩
    · exact ⟨⟨by push_cast; omega, by push_cast; omega⟩, by push_cast; omega,
        ⟨-((K+1:ℕ):ℤ), by ring⟩⟩
    · exact ⟨⟨by push_cast at hlo2 hhi2 ⊢; omega, by push_cast at hlo2 hhi2 ⊢; omega⟩, hne, hev⟩

/-- Reindex a sum over the even, non-zero integers of `[-2K, 2K]` by their halves. -/
lemma fi_sum_Icc_filter_even (h : ℤ → ℂ) (K : ℕ) :
    ∑ k ∈ (Finset.Icc (-(2*(K:ℤ))) (2*(K:ℤ))).filter (fun k => k ≠ 0 ∧ Even k), h k
      = ∑ n ∈ Finset.Icc 1 K, (h (2*(n:ℤ)) + h (-(2*(n:ℤ)))) := by
  induction K with
  | zero => simp [Finset.sum_filter]
  | succ K ih =>
    rw [fi_Icc_filter_even_succ K]
    rw [Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc]
          push_cast
          omega),
        Finset.sum_insert (by
          simp only [Finset.mem_filter, Finset.mem_Icc]
          push_cast
          omega)]
    rw [ih]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1)]
    push_cast
    ring

/-! ## The unit complex numbers `z/|z|` -/

/-- `(z₁/|z₁|)ᵏ·conj((z₂/|z₂|)ᵏ) = Pᵏ` with `P = z₁z̄₂/(|z₁||z₂|)`. -/
lemma fi_u_pow_star_eq (Z1 Z2 : ℂ) (k : ℤ) :
    (Z1 / ((‖Z1‖:ℝ):ℂ))^k * star ((Z2 / ((‖Z2‖:ℝ):ℂ))^k)
      = ((Z1 * star Z2) / (((‖Z1‖ * ‖Z2‖):ℝ):ℂ))^k := by
  have hstar : star ((Z2 / ((‖Z2‖:ℝ):ℂ))^k) = (star Z2 / ((‖Z2‖:ℝ):ℂ))^k := by
    rw [Complex.star_def, map_zpow₀]
    congr 1
    rw [map_div₀ (starRingEnd ℂ), Complex.conj_ofReal]
  rw [hstar, ← mul_zpow]
  congr 1
  rw [div_mul_div_comm, Complex.ofReal_mul]

/-- `Pᵏ = cos(k(arg z₁ − arg z₂)) + sin(k(arg z₁ − arg z₂))·I`. -/
lemma fi_P_zpow_form (Z1 Z2 : ℂ) (h1 : Z1 ≠ 0) (h2 : Z2 ≠ 0) (k : ℤ) :
    (((Z1 * star Z2) / (((‖Z1‖ * ‖Z2‖):ℝ):ℂ))^k)
      = ((Real.cos ((k:ℝ) * (Z1.arg - Z2.arg)) : ℝ):ℂ)
        + ((Real.sin ((k:ℝ) * (Z1.arg - Z2.arg)) : ℝ):ℂ) * Complex.I := by
  have hP : (Z1 * star Z2) / (((‖Z1‖ * ‖Z2‖):ℝ):ℂ)
      = Complex.exp (((Z1.arg - Z2.arg : ℝ) : ℂ) * Complex.I) := by
    have e1 : Z1 / ((‖Z1‖:ℝ):ℂ) = Complex.exp (((Z1.arg:ℝ):ℂ) * Complex.I) :=
      (exp_arg_mul_I Z1 h1).symm
    have e2 : star Z2 / ((‖Z2‖:ℝ):ℂ) = Complex.exp (-(((Z2.arg:ℝ):ℂ) * Complex.I)) :=
      (exp_neg_arg_mul_I Z2 h2).symm
    rw [show (Z1 * star Z2) / (((‖Z1‖ * ‖Z2‖):ℝ):ℂ)
          = (Z1 / ((‖Z1‖:ℝ):ℂ)) * (star Z2 / ((‖Z2‖:ℝ):ℂ)) from by
          rw [div_mul_div_comm, Complex.ofReal_mul]]
    rw [e1, e2, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hP, ← Complex.exp_int_mul]
  have harg : ((k:ℂ) * (((Z1.arg - Z2.arg : ℝ):ℂ) * Complex.I))
      = ((((k:ℝ) * (Z1.arg - Z2.arg) : ℝ)):ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

/-- `Pᵏ + P^{−k} = 2cos(k(arg z₂ − arg z₁))` for unit complex numbers. -/
lemma fi_P_add_P_neg (Z1 Z2 : ℂ) (h1 : Z1 ≠ 0) (h2 : Z2 ≠ 0) (k : ℤ) :
    (((Z1 * star Z2) / (((‖Z1‖ * ‖Z2‖):ℝ):ℂ))^k
      + ((Z1 * star Z2) / (((‖Z1‖ * ‖Z2‖):ℝ):ℂ))^(-k))
      = ((2 * Real.cos ((k:ℝ) * (Z2.arg - Z1.arg)) : ℝ):ℂ) := by
  rw [fi_P_zpow_form Z1 Z2 h1 h2 k, fi_P_zpow_form Z1 Z2 h1 h2 (-k)]
  have hk : (((-k:ℤ):ℝ) * (Z1.arg - Z2.arg)) = -((k:ℝ)*(Z1.arg - Z2.arg)) := by
    push_cast; ring
  rw [hk, Real.cos_neg, Real.sin_neg]
  have hcos : Real.cos ((k:ℝ)*(Z1.arg - Z2.arg)) = Real.cos ((k:ℝ)*(Z2.arg - Z1.arg)) := by
    rw [show (k:ℝ)*(Z1.arg - Z2.arg) = -((k:ℝ)*(Z2.arg - Z1.arg)) from by ring, Real.cos_neg]
  rw [hcos]
  push_cast
  ring

/-- The paired summand: `(1/|2n|)u₁^{2n}conj(u₂^{2n}) + (1/|−2n|)u₁^{−2n}conj(u₂^{−2n})`
equals the real number `cos(2n·t)/n`, `t = arg z₂ − arg z₁`. -/
lemma fi_pair_term (Z1 Z2 : ℂ) (h1 : Z1 ≠ 0) (h2 : Z2 ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    (1 / (|((2*(n:ℤ)) : ℤ)| : ℝ) : ℂ) * ((Z1/((‖Z1‖:ℝ):ℂ))^(2*(n:ℤ))
        * star ((Z2/((‖Z2‖:ℝ):ℂ))^(2*(n:ℤ))))
    + (1 / (|((-(2*(n:ℤ))) : ℤ)| : ℝ) : ℂ) * ((Z1/((‖Z1‖:ℝ):ℂ))^(-(2*(n:ℤ)))
        * star ((Z2/((‖Z2‖:ℝ):ℂ))^(-(2*(n:ℤ)))))
    = ((Real.cos (2*(n:ℝ)*(Z2.arg - Z1.arg))/(n:ℝ) : ℝ):ℂ) := by
  rw [fi_u_pow_star_eq Z1 Z2 (2*(n:ℤ)), fi_u_pow_star_eq Z1 Z2 (-(2*(n:ℤ)))]
  have h2n : (|((2*(n:ℤ)) : ℤ)| : ℝ) = 2*(n:ℝ) := by
    rw [abs_of_nonneg (by positivity)]; push_cast; ring
  have hm2n : (|((-(2*(n:ℤ))) : ℤ)| : ℝ) = 2*(n:ℝ) := by
    rw [show (((-(2*(n:ℤ))) : ℤ) : ℝ) = -(((2*(n:ℤ)) : ℤ) : ℝ) by push_cast; ring, abs_neg]
    rw [abs_of_nonneg (by positivity)]; push_cast; ring
  rw [h2n, hm2n]
  rw [← mul_add, fi_P_add_P_neg Z1 Z2 h1 h2 (2*(n:ℤ))]
  rw [show (((2*(n:ℤ):ℤ):ℝ)) = 2*(n:ℝ) from by push_cast; ring]
  rw [← Complex.ofReal_one, ← Complex.ofReal_div, ← Complex.ofReal_mul, Complex.ofReal_inj]
  have hn' : (n:ℝ) ≠ 0 := by positivity
  field_simp

/-! ## The target -/

theorem logFac6_eq_sum_freq (z1 z2 : GaussianInt) (K : ℕ) (hK : 1 ≤ K)
    (h : Work.FIPlan.Delta z1 z2 ≠ 0) :
    ‖(((Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ)
      - ((2 * Real.log 2 + Real.log 4 : ℝ) : ℂ)
      - ∑ k ∈ (Finset.Icc (-(2 * (K : ℤ))) (2 * (K : ℤ))).filter
            (fun k => k ≠ 0 ∧ Even k),
          (1 / (|k| : ℝ) : ℂ) *
            ((GaussianInt.toComplex z1 / ((‖GaussianInt.toComplex z1‖ : ℝ) : ℂ)) ^ k
             * star ((GaussianInt.toComplex z2 / ((‖GaussianInt.toComplex z2‖ : ℝ) : ℂ)) ^ k)))‖
    ≤ 4 / ((K : ℝ) * |Real.sin (Complex.arg z2.toComplex - Complex.arg z1.toComplex)|) := by
  have hz1 : z1 ≠ 0 := by rintro rfl; simp [Work.FIPlan.Delta] at h
  have hz2 : z2 ≠ 0 := by rintro rfl; simp [Work.FIPlan.Delta] at h
  have hZ1 : z1.toComplex ≠ 0 := toComplex_ne_zero_of_gnorm_pos (gnorm_pos_of_ne_zero hz1)
  have hZ2 : z2.toComplex ≠ 0 := toComplex_ne_zero_of_gnorm_pos (gnorm_pos_of_ne_zero hz2)
  have hsum : (∑ k ∈ (Finset.Icc (-(2 * (K : ℤ))) (2 * (K : ℤ))).filter
            (fun k => k ≠ 0 ∧ Even k),
          (1 / (|k| : ℝ) : ℂ) *
            ((z1.toComplex / ((‖z1.toComplex‖ : ℝ) : ℂ)) ^ k
             * star ((z2.toComplex / ((‖z2.toComplex‖ : ℝ) : ℂ)) ^ k)))
      = ((∑ n ∈ Finset.Icc 1 K,
            Real.cos (2 * (n:ℝ) * (z2.toComplex.arg - z1.toComplex.arg)) / (n : ℝ) : ℝ) : ℂ) := by
    rw [fi_sum_Icc_filter_even (fun k => (1 / (|k|:ℝ) : ℂ) *
          ((z1.toComplex / ((‖z1.toComplex‖:ℝ):ℂ))^k
            * star ((z2.toComplex / ((‖z2.toComplex‖:ℝ):ℂ))^k))) K]
    rw [Finset.sum_congr rfl (fun n hn =>
          fi_pair_term z1.toComplex z2.toComplex hZ1 hZ2 n (Finset.mem_Icc.mp hn).1)]
    rw [← Complex.ofReal_sum]
  rw [hsum]
  have hrewrite : ((Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ)
        - ((2 * Real.log 2 + Real.log 4 : ℝ) : ℂ)
        - ((∑ n ∈ Finset.Icc 1 K,
            Real.cos (2 * (n:ℝ) * (z2.toComplex.arg - z1.toComplex.arg)) / (n : ℝ) : ℝ) : ℂ)
      = ((Work.FITop3.logFac z1 z2 - 2 * Real.log 2
            - (∑ n ∈ Finset.Icc 1 K,
                Real.cos (2 * (n:ℝ) * (z2.toComplex.arg - z1.toComplex.arg)) / (n : ℝ)) : ℝ) : ℂ) := by
    rw [fi_logFac6_eq_logFac_add_log4 z1 z2 h]
    push_cast
    ring
  rw [hrewrite, fi_norm_ofReal]
  rw [show Work.FITop3.logFac z1 z2 - 2 * Real.log 2
        - ∑ n ∈ Finset.Icc 1 K,
            Real.cos (2 * (n:ℝ) * (z2.toComplex.arg - z1.toComplex.arg)) / (n : ℝ)
      = Work.FITop3.logFac z1 z2 - (2 * Real.log 2
        + ∑ n ∈ Finset.Icc 1 K,
            Real.cos (2 * (n:ℝ) * (z2.toComplex.arg - z1.toComplex.arg)) / (n : ℝ)) from by ring]
  exact logFac_eq_sum_cos z1 z2 K hK h

end

end Work.FIArea7
