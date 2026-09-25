import Mathlib
import Submission.Commons.Analysis.ExponentialSums.pure_power_major_arc_approx
import Submission.Commons.Analysis.ExponentialSums.hua_bound
import Submission.Commons.Analysis.Oscillatory.vt_oscillatory_integral

namespace Commons.Analysis.ExponentialSums

open MeasureTheory
open scoped BigOperators ComplexConjugate

noncomputable section

/-- The normalised pure `d`-th power oscillatory integral `∫_0^1 e^{i a s^d} ds`. -/
def powOsc (d : ℕ) (a : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..1, Complex.exp (Complex.I * ((a * s ^ d : ℝ) : ℂ))

/-- Trivial bound: the integrand has modulus one, so the integral is bounded by the length
of the interval. -/
lemma powOsc_triv (d : ℕ) (a : ℝ) : ‖powOsc d a‖ ≤ 1 := by
  rw [powOsc]
  have hle : ∀ x ∈ Set.uIoc (0:ℝ) 1,
      ‖Complex.exp (Complex.I * ((a * x ^ d : ℝ) : ℂ))‖ ≤ (1:ℝ) := by
    intro x hx
    have hcomm : Complex.I * ((a * x ^ d : ℝ) : ℂ) = ((a * x ^ d : ℝ) : ℂ) * Complex.I :=
      mul_comm _ _
    rw [hcomm, Complex.norm_exp_ofReal_mul_I]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hle
  simpa using h

/-- Conjugation symmetry of the pure `d`-th power oscillatory integral: `v(-a) = conj (v a)`. -/
lemma powOsc_neg (d : ℕ) (a : ℝ) : powOsc d (-a) = conj (powOsc d a) := by
  rw [powOsc, powOsc, ← intervalIntegral.intervalIntegral_conj]
  apply intervalIntegral.integral_congr
  intro s hs
  simp only []
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- The modulus of the pure `d`-th power oscillatory integral depends only on `|a|`. -/
lemma powOsc_norm_eq (d : ℕ) (a : ℝ) : ‖powOsc d a‖ = ‖powOsc d (-|a|)‖ := by
  rcases lt_or_ge a 0 with ha | ha
  · rw [abs_of_neg ha, neg_neg]
  · rw [abs_of_nonneg ha, powOsc_neg d a, Complex.norm_conj]

/-- Uniform van der Corput bound for the pure `d`-th power oscillatory integral
`∫_0^1 e^{i a s^d} ds`, in the normalised form `‖·‖ ≤ C / (1 + |a|^{1/d})`.  The `1 +` in the
denominator is the trivial bound `‖∫‖ ≤ 1` in the regime `|a|^{1/d} ≤ 1`. -/
theorem powOsc_bound (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, ‖powOsc d a‖ ≤ C / (1 + |a| ^ (1 / (d : ℝ))) := by
  obtain ⟨C1, hC1pos, hvt⟩ :=
    Commons.Analysis.Oscillatory.vt_oscillatory_integral d hd
  refine ⟨max (2 * C1) 2, lt_max_of_lt_left (by positivity), ?_⟩
  intro a
  have hden : (0:ℝ) < 1 + |a| ^ (1 / (d : ℝ)) := by
    have h := Real.rpow_nonneg (abs_nonneg a) (1 / (d : ℝ))
    linarith
  by_cases hs : |a| ^ (1 / (d : ℝ)) ≤ 1
  · calc ‖powOsc d a‖ ≤ 1 := powOsc_triv d a
      _ ≤ max (2 * C1) 2 / (1 + |a| ^ (1 / (d : ℝ))) := by
          rw [le_div_iff₀ hden, one_mul]
          have h2 : (2:ℝ) ≤ max (2 * C1) 2 := le_max_right _ _
          linarith
  · have hs' : 1 < |a| ^ (1 / (d : ℝ)) := lt_of_not_ge hs
    have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
    have hcne : (1:ℝ) / (d:ℝ) ≠ 0 := by
      rw [one_div]; exact inv_ne_zero (ne_of_gt hd0)
    have hpos : 0 < |a| := by
      rcases eq_or_lt_of_le (abs_nonneg a) with h | h
      · rw [← h] at hs'
        rw [Real.zero_rpow hcne] at hs'
        norm_num at hs'
      · exact h
    have hvtb : ‖powOsc d (-|a|)‖ ≤ C1 / |a| ^ (1 / (d : ℝ)) := by
      have h := (hvt 1 |a| (by norm_num) hpos).1
      have hcong : (∫ s in (0:ℝ)..1,
            Complex.exp (((-(|a| * 1 ^ d * s ^ d) : ℝ) : ℂ) * Complex.I)) = powOsc d (-|a|) := by
        rw [powOsc]
        apply intervalIntegral.integral_congr
        intro s hs''
        simp only [one_pow, mul_one]
        congr 1
        push_cast
        ring
      rw [hcong] at h
      rw [one_mul] at h
      exact h
    have hle1 : 1 + |a| ^ (1 / (d : ℝ)) ≤ 2 * |a| ^ (1 / (d : ℝ)) := by
      linarith
    have hstep1 : C1 / |a| ^ (1 / (d : ℝ))
        ≤ 2 * C1 / (1 + |a| ^ (1 / (d : ℝ))) := by
      rw [div_le_div_iff₀ (by linarith) hden]
      nlinarith [hC1pos, hle1]
    have hstep2 : 2 * C1 / (1 + |a| ^ (1 / (d : ℝ)))
        ≤ max (2 * C1) 2 / (1 + |a| ^ (1 / (d : ℝ))) :=
      div_le_div_of_nonneg_right (le_max_left _ _) hden.le
    calc ‖powOsc d a‖ = ‖powOsc d (-|a|)‖ := powOsc_norm_eq d a
      _ ≤ C1 / |a| ^ (1 / (d : ℝ)) := hvtb
      _ ≤ 2 * C1 / (1 + |a| ^ (1 / (d : ℝ))) := hstep1
      _ ≤ max (2 * C1) 2 / (1 + |a| ^ (1 / (d : ℝ))) := hstep2

/-- Uniform bound on the oscillatory "pseudo-projection"
`v_N(β) = ∫_0^1 e(β N^d s^d) ds`: `‖v_N(β)‖ ≤ C / (1 + N |β|^{1/d})`. -/
theorem pure_power_pseudo_projection_bound (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (β : ℝ), 1 ≤ N →
      ‖∫ s in (0 : ℝ)..1,
          Complex.exp (2 * Real.pi * Complex.I * ((β * (N : ℝ) ^ d * s ^ d : ℝ) : ℂ))‖
        ≤ C / (1 + (N : ℝ) * |β| ^ (1 / (d : ℝ))) := by
  obtain ⟨C, hCpos, hC⟩ := powOsc_bound d hd
  refine ⟨C, hCpos, ?_⟩
  intro N β hN
  have hNN : (0:ℝ) ≤ (N:ℝ) := by positivity
  set a : ℝ := 2 * Real.pi * β * (N:ℝ)^d with ha
  have hcong : (∫ s in (0:ℝ)..1,
        Complex.exp (2 * Real.pi * Complex.I * ((β * (N:ℝ)^d * s^d : ℝ) : ℂ)))
      = powOsc d a := by
    rw [powOsc, ha]
    apply intervalIntegral.integral_congr
    intro s hs
    simp only []
    congr 1
    push_cast
    ring
  rw [hcong]
  refine le_trans (hC a) ?_
  have habs : |a| = 2 * Real.pi * |β| * (N:ℝ)^d := by
    rw [ha, abs_mul, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 2*Real.pi), abs_of_nonneg (pow_nonneg hNN d)]
  have hNd_nn : (0:ℝ) ≤ (N:ℝ)^d := pow_nonneg hNN d
  have h2piB_nn : (0:ℝ) ≤ 2*Real.pi*|β| := by positivity
  have hsqrt_a : |a| ^ (1/(d:ℝ)) = (2*Real.pi*|β|) ^ (1/(d:ℝ)) * (N:ℝ) := by
    rw [habs, Real.mul_rpow h2piB_nn hNd_nn]
    have hNd : ((N:ℝ)^d) ^ (1/(d:ℝ)) = (N:ℝ) := by
      rw [← Real.rpow_natCast (N:ℝ) d, ← Real.rpow_mul hNN]
      have hdne : (d:ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
      have hdr : (d:ℝ) * (1/(d:ℝ)) = 1 := by field_simp
      rw [hdr, Real.rpow_one]
    rw [hNd]
  have hge : |β| ^ (1/(d:ℝ)) ≤ (2*Real.pi*|β|) ^ (1/(d:ℝ)) := by
    rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ 2*Real.pi) (abs_nonneg β)]
    have h1 : (1:ℝ) ≤ (2*Real.pi) ^ (1/(d:ℝ)) :=
      Real.one_le_rpow (by linarith [Real.pi_gt_three]) (by positivity)
    have h2 : (0:ℝ) ≤ |β| ^ (1/(d:ℝ)) := Real.rpow_nonneg (abs_nonneg β) _
    nlinarith [h1, h2]
  have hden2 : (0:ℝ) < 1 + (N:ℝ) * |β| ^ (1 / (d : ℝ)) := by
    have h1 : (0:ℝ) ≤ |β| ^ (1/(d:ℝ)) := Real.rpow_nonneg (abs_nonneg β) _
    nlinarith
  have hkey : (N:ℝ) * |β| ^ (1/(d:ℝ)) ≤ |a| ^ (1/(d:ℝ)) := by
    rw [hsqrt_a, mul_comm (N:ℝ) (|β| ^ (1/(d:ℝ)))]
    exact mul_le_mul_of_nonneg_right hge hNN
  apply div_le_div_of_nonneg_left hCpos.le hden2
  linarith [hkey]

/-- **Major-arc multiplier bound for the pure `d`-th powers.**  For `α = a/q + β` with
`gcd a q = 1`, `q ≥ 1`, `1 ≤ N`, and any `ε > 0`,

`‖N⁻¹ ∑_{n<N} e(α n^d)‖ ≤ C ( q^{ε − 1/2^{d−1}}/(1 + N |β|^{1/d}) + |β| q (N+q)^d / N + q/N )`.

The main term is the product of Hua's bound for the complete `d`-th power sum
`‖q⁻¹ ∑_{r<q} e(a r^d/q)‖ ≤ C q^{−1/2^{d−1}+ε}` (Commons.Analysis.ExponentialSums.hua_bound)
with the pseudo-projection bound `‖∫_0^1 e(β N^d s^d) ds‖ ≤ C/(1 + N|β|^{1/d})` (van der
Corput; Commons.Analysis.Oscillatory.vt_oscillatory_integral with `d`, plus the trivial bound
`‖·‖ ≤ 1` in the regime `N|β|^{1/d} ≤ 1` and the conjugation symmetry for `β < 0`); the
remaining terms are the error of the major-arc approximation
(Commons.Analysis.ExponentialSums.pure_power_major_arc_approx). -/
theorem pure_power_major_arc_multiplier (d : ℕ) (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N q : ℕ) (a : ℤ) (β : ℝ), 1 ≤ q → 1 ≤ N →
      Int.gcd a (q : ℤ) = 1 →
      ‖(N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
            Complex.exp (2 * Real.pi * Complex.I *
              ((((a : ℝ) / (q : ℝ) + β) * (n : ℝ) ^ d : ℝ) : ℂ))‖
        ≤ C * (Real.rpow (q : ℝ) (ε - 1 / (2:ℝ)^(d-1))
                / (1 + (N : ℝ) * Real.rpow |β| (1 / (d : ℝ)))
              + |β| * (q : ℝ) * ((N : ℝ) + (q : ℝ))^d / (N : ℝ)
              + (q : ℝ) / (N : ℝ)) := by
  obtain ⟨C1, hC1pos, happrox⟩ := pure_power_major_arc_approx d hd
  obtain ⟨C2, hC2pos, hhua⟩ := hua_bound d (by omega) hε
  obtain ⟨C3, hC3pos, hpp⟩ := pure_power_pseudo_projection_bound d hd
  have hC23pos : 0 < C2 * C3 := mul_pos hC2pos hC3pos
  refine ⟨C1 + C2 * C3 + 1, by linarith, ?_⟩
  intro N q a β hq hN hgcd
  change ‖(N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
            Complex.exp (2 * Real.pi * Complex.I *
              ((((a : ℝ) / (q : ℝ) + β) * (n : ℝ) ^ d : ℝ) : ℂ))‖
        ≤ (C1 + C2 * C3 + 1) * ((q : ℝ) ^ (ε - 1 / (2:ℝ)^(d-1))
                / (1 + (N : ℝ) * |β| ^ (1 / (d : ℝ)))
              + |β| * (q : ℝ) * ((N : ℝ) + (q : ℝ))^d / (N : ℝ)
              + (q : ℝ) / (N : ℝ))
  have hqpos : 0 < q := by omega
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hqR : (0:ℝ) ≤ (q:ℝ) := by positivity
  set S : ℂ := ∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I *
      ((((a : ℝ) / (q : ℝ) + β) * (n : ℝ) ^ d : ℝ) : ℂ)) with hS
  set G : ℂ := ∑ r ∈ Finset.range q, Complex.exp (2 * Real.pi * Complex.I *
      (((a : ℝ) / (q : ℝ) * (r : ℝ) ^ d : ℝ) : ℂ)) with hG
  set v : ℂ := ∫ s in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I *
      ((β * (N : ℝ) ^ d * s ^ d : ℝ) : ℂ)) with hv
  set M : ℝ := (q : ℝ) ^ (ε - 1 / (2:ℝ)^(d-1))
      / (1 + (N : ℝ) * |β| ^ (1 / (d : ℝ))) with hM
  set E1 : ℝ := |β| * (q : ℝ) * ((N : ℝ) + (q : ℝ))^d / (N : ℝ) with hE1
  set E2 : ℝ := (q : ℝ) / (N : ℝ) with hE2
  have hA' := happrox N q a β hq hN
  rw [← hS, ← hG, ← hv] at hA'
  have hG' : ‖(q : ℂ)⁻¹ * G‖ ≤ C2 * (q : ℝ) ^ (ε - 1 / (2:ℝ)^(d-1)) := by
    have hcong : G = ∑ r ∈ Finset.range q,
        Complex.exp (↑(2 * Real.pi * a * (r : ℝ) ^ d / q) * Complex.I) := by
      rw [hG]
      apply Finset.sum_congr rfl
      intro r hr
      congr 1
      push_cast
      ring
    rw [hcong]
    have h := hhua q a hqpos hgcd
    have hexp : -(1 / (2:ℝ)^(d-1)) + ε = ε - 1 / (2:ℝ)^(d-1) := by ring
    rwa [hexp] at h
  have hpp' := hpp N β hN
  rw [← hv] at hpp'
  have hpart2 : ‖(q : ℂ)⁻¹ * G * v‖ ≤ C2 * C3 * M := by
    rw [hM, norm_mul]
    have h1 : 0 ≤ C2 * (q : ℝ) ^ (ε - 1 / (2:ℝ)^(d-1)) :=
      mul_nonneg hC2pos.le (Real.rpow_nonneg hqR _)
    calc ‖(q : ℂ)⁻¹ * G‖ * ‖v‖
        ≤ (C2 * (q : ℝ) ^ (ε - 1/(2:ℝ)^(d-1)))
            * (C3 / (1 + (N:ℝ) * |β| ^ (1/(d:ℝ)))) :=
          mul_le_mul hG' hpp' (norm_nonneg _) h1
      _ = C2 * C3 * ((q : ℝ) ^ (ε - 1/(2:ℝ)^(d-1))
            / (1 + (N:ℝ) * |β| ^ (1/(d:ℝ)))) := by ring
  have hsplit : ‖(N : ℂ)⁻¹ * S‖
      ≤ ‖(N : ℂ)⁻¹ * S - (q : ℂ)⁻¹ * G * v‖ + ‖(q : ℂ)⁻¹ * G * v‖ := by
    have h : (N : ℂ)⁻¹ * S = ((N : ℂ)⁻¹ * S - (q : ℂ)⁻¹ * G * v) + (q : ℂ)⁻¹ * G * v := by
      ring
    calc ‖(N : ℂ)⁻¹ * S‖
        = ‖((N:ℂ)⁻¹*S - (q:ℂ)⁻¹*G*v) + (q:ℂ)⁻¹*G*v‖ := congrArg norm h
      _ ≤ _ := norm_add_le _ _
  have hpart1 : ‖(N : ℂ)⁻¹ * S - (q : ℂ)⁻¹ * G * v‖ ≤ C1 * (E1 + E2) := by
    rw [hE1, hE2]
    exact hA'
  have hMnn : 0 ≤ M := by
    rw [hM]
    have hnum : (0:ℝ) ≤ (q : ℝ) ^ (ε - 1 / (2:ℝ)^(d-1)) := Real.rpow_nonneg hqR _
    have hden : (0:ℝ) < 1 + (N:ℝ) * |β| ^ (1/(d:ℝ)) := by
      have h1 : (0:ℝ) ≤ |β| ^ (1/(d:ℝ)) := Real.rpow_nonneg (abs_nonneg β) _
      nlinarith
    exact div_nonneg hnum hden.le
  have hE1nn : 0 ≤ E1 := by rw [hE1]; positivity
  have hE2nn : 0 ≤ E2 := by rw [hE2]; positivity
  calc ‖(N : ℂ)⁻¹ * S‖
      ≤ ‖(N : ℂ)⁻¹ * S - (q : ℂ)⁻¹ * G * v‖ + ‖(q : ℂ)⁻¹ * G * v‖ := hsplit
    _ ≤ C1 * (E1 + E2) + C2 * C3 * M := add_le_add hpart1 hpart2
    _ ≤ (C1 + C2 * C3 + 1) * (M + E1 + E2) := by
        have hC1le : C1 ≤ C1 + C2 * C3 + 1 := by linarith [hC2pos, hC3pos]
        have hC23le : C2 * C3 ≤ C1 + C2 * C3 + 1 := by linarith [hC1pos]
        have hA1 : C1 * (E1 + E2) ≤ (C1 + C2*C3 + 1) * (E1 + E2) :=
          mul_le_mul_of_nonneg_right hC1le (by linarith [hE1nn, hE2nn])
        have hA2 : C2 * C3 * M ≤ (C1 + C2*C3 + 1) * M :=
          mul_le_mul_of_nonneg_right hC23le hMnn
        nlinarith [hA1, hA2]

end

end Commons.Analysis.ExponentialSums
