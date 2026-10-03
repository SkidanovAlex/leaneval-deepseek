import Mathlib
import Submission.Work.FIArea6Road.PhifacAnalyticBound

open scoped BigOperators

namespace Work.FIArea6Road

noncomputable section

/-- **The Euler product `Φ = M·L` is bounded by an *absolute* constant on `re s ≥ 3/4`.**
`Φ(s) = ∏_p((1 - λ(p)p^{-s})/(1 - λ(p)p^{-s} + (λ(p)²-λ(p²))p^{-2s}))`, the absolutely convergent
Euler product whose analyticity and boundedness on `re s > 1/2` is
`Work.FIArea6Road.PhifacAnalyticBound`; here only the *uniformity* of the constant is added: it must
not depend on `χ` or `m`.

(From the proof of `PhifacAnalyticBound`: `‖Φ(s)‖ ≤ ∏_p(1 + (4/(1-2^{-3/4})²)p^{-3/2})` for
`re s ≥ 3/4` — an absolutely summable majorant independent of `χ` and `m`.) -/
theorem PhifacBoundUniform :
    ∃ K : ℝ, 0 < K ∧ ∀ (chi : GaussianInt → ℂ) (m : ℤ),
      chi 1 = 1 → (∀ z w : GaussianInt, chi (z * w) = chi z * chi w) →
      (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
      ∀ s : ℂ, 3 / 4 ≤ s.re → ‖Work.FIArea6.TauPieces.Phifac chi m s‖ ≤ K := by
  -- The constant is carved out first, so that nothing below refers to `chi` or `m`.
  set δ : ℝ := 1 - (2:ℝ)^(-(3/4:ℝ)) with hδ
  set S0 : ℝ := ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(3/2:ℝ)) with hS0def
  have hδpos : 0 < δ := by
    rw [hδ]
    have h : (2:ℝ)^(-(3/4:ℝ)) < 1 := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) (by norm_num))
    linarith
  have hpow34 : (2:ℝ)^(-(3/4:ℝ)) = 1 - δ := by rw [hδ]; ring
  refine ⟨Real.exp ((4 / δ^2) * S0), Real.exp_pos _, ?_⟩
  intro chi m hchi1 hchimul hchibd s hs
  have hPhifac : Work.FIArea6.TauPieces.Phifac chi m s
      = ∏' p : Nat.Primes, (1 + ufac chi m p s) := by
    rw [Work.FIArea6.TauPieces.Phifac_eq_tprod_PhiLocal]
    exact tprod_congr (fun p => by simp only [ufac]; ring)
  rw [hPhifac]
  have hu_bound : ∀ p : Nat.Primes, ‖ufac chi m p s‖
      ≤ (4 / δ^2) * ((p : ℕ) : ℝ) ^ (-(3/2:ℝ)) := by
    intro p
    have hp1 : (1:ℝ) ≤ (p : ℕ) := by exact_mod_cast (p.2).one_le
    have hp2 : (2:ℝ) ≤ (p : ℕ) := by exact_mod_cast (p.2).two_le
    have hppos : (0:ℝ) < (p : ℕ) := by linarith
    have hnorm : ‖((p : ℕ) : ℂ) ^ (-s)‖ = ((p : ℕ) : ℝ) ^ (-s.re) := by
      rw [Complex.norm_natCast_cpow_of_pos (by exact (p.2).pos), Complex.neg_re]
    have hTle : ((p : ℕ) : ℝ) ^ (-s.re) ≤ (2:ℝ)^(-(3/4:ℝ)) :=
      (Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)).trans
        (Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num))
    have hz : ‖((p : ℕ) : ℂ) ^ (-s)‖ < 1 := by
      rw [hnorm]
      rw [hpow34] at hTle
      linarith [hδpos]
    have hLFB := (LocalFactorBound chi m (p : ℕ) p.2 hchi1 hchimul hchibd hz).2
    have hu : ‖ufac chi m p s‖
        ≤ 4 * (((p : ℕ) : ℝ) ^ (-s.re))^2 / (1 - ((p : ℕ) : ℝ) ^ (-s.re))^2 := by
      simpa only [ufac, Work.FIArea6.TauPieces.PhiLocal, Work.FIArea6.TauPieces.localL,
        hnorm] using hLFB
    have hTnn : (0:ℝ) ≤ ((p : ℕ) : ℝ) ^ (-s.re) := Real.rpow_nonneg (by positivity) _
    have hT2 : (((p : ℕ) : ℝ) ^ (-s.re))^2 ≤ ((p : ℕ) : ℝ) ^ (-(3/2:ℝ)) := by
      have h1 : (((p : ℕ) : ℝ) ^ (-s.re))^2 ≤ (((p : ℕ) : ℝ) ^ (-(3/4:ℝ)))^2 :=
        pow_le_pow_left₀ hTnn (Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)) 2
      have h2 : (((p : ℕ) : ℝ) ^ (-(3/4:ℝ)))^2 = ((p : ℕ) : ℝ) ^ (-(3/2:ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (p : ℕ))]
        congr 1
        ring
      rwa [h2] at h1
    have hden : δ^2 ≤ (1 - ((p : ℕ) : ℝ) ^ (-s.re))^2 := by
      have h1 : δ ≤ 1 - ((p : ℕ) : ℝ) ^ (-s.re) := by
        rw [hpow34] at hTle
        linarith
      exact pow_le_pow_left₀ (le_of_lt hδpos) h1 2
    have hnumc : (0:ℝ) ≤ 4 * ((p : ℕ) : ℝ) ^ (-(3/2:ℝ)) := by positivity
    calc ‖ufac chi m p s‖
        ≤ 4 * (((p : ℕ) : ℝ) ^ (-s.re))^2 / (1 - ((p : ℕ) : ℝ) ^ (-s.re))^2 := hu
      _ ≤ 4 * ((p : ℕ) : ℝ) ^ (-(3/2:ℝ)) / δ^2 :=
          div_le_div₀ hnumc (by linarith [hT2]) (pow_pos hδpos 2) hden
      _ = (4 / δ^2) * ((p : ℕ) : ℝ) ^ (-(3/2:ℝ)) := by ring
  have hsumu : Summable (fun p : Nat.Primes => ‖ufac chi m p s‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) hu_bound
      ((summable_primes_rpow_neg (show (1:ℝ) < 3/2 by norm_num)).mul_left (4 / δ^2))
  have htsum : (∑' p : Nat.Primes, ‖ufac chi m p s‖) ≤ (4 / δ^2) * S0 := by
    have h := Summable.tsum_le_tsum hu_bound hsumu
      ((summable_primes_rpow_neg (show (1:ℝ) < 3/2 by norm_num)).mul_left (4 / δ^2))
    rw [tsum_mul_left] at h
    rw [hS0def]
    exact h
  have hm : Multipliable (fun p : Nat.Primes => 1 + ufac chi m p s) :=
    multipliable_one_add_of_summable hsumu
  rw [hm.norm_tprod]
  exact hasProd_le_of_prod_le hm.norm.hasProd (fun S => by
    calc ∏ p ∈ S, ‖1 + ufac chi m p s‖
        ≤ ∏ p ∈ S, (1 + ‖ufac chi m p s‖) :=
          Finset.prod_le_prod₀ (fun p _ => norm_nonneg _)
            (fun p _ => by simpa using norm_add_le (1:ℂ) (ufac chi m p s))
      _ ≤ Real.exp (∑ p ∈ S, ‖ufac chi m p s‖) :=
          Real.prod_one_add_le_exp_sum S (fun p => norm_nonneg _)
      _ ≤ Real.exp (∑' p : Nat.Primes, ‖ufac chi m p s‖) :=
          Real.exp_le_exp.mpr (Summable.sum_le_tsum S (fun p _ => norm_nonneg _) hsumu)
      _ ≤ Real.exp ((4 / δ^2) * S0) := Real.exp_le_exp.mpr htsum)

end

end Work.FIArea6Road
