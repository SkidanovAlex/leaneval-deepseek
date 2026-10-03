/-
# Auxiliaries for Work.FIArea7.WUniOmega6Pull6CharLow_le

The low part (the b <= X half) of the (17.10) main term is estimated by applying the
per-character bound of FI Proposition 17.2 to each of its terms.  The normalising factor
1/Phi(4be) of the section 16 expansion cancels the number of characters, but the weight J(chi)
of the expansion has to be summed over all characters: the trivial bound norm J(chi) <= 4be
(Work.FIArea7.norm_ratWeight_charSum_le) would overshoot the target X^3 by a whole power of X.
The sharp input is the L1-L2 pair

    sum_chi norm J(chi) <= |G| * sqrt Q,

proved by Cauchy-Schwarz against the exact Plancherel identity
sum_chi norm J(chi)^2 = |G| * sum_p norm (ratWeight Q e p)^2 <= |G| * Q.

This file collects

* sum_char_mul_star_self   - Plancherel for the character table of a finite abelian group;
* sum_norm_addChar_mul_star_le - the abstract L1-bound for the Fourier transform;
* sum_norm_uniJChar_le     - its instantiation to the omega-weights J(chi) = uniJChar Q e chi;
* norm_inv_card_mul_sum_chi_le - the normalised chi-sum of the section 16 expansion;
* sum_inv_abs_evenFreq_le  - the harmonic weight of the frequency set evenFreq K.
-/
import Mathlib
import Submission.Work.FIArea7.omega_orthogonality
import Submission.Work.FIArea7.sum_addChar_mul_star
import Submission.Work.FIArea7.UniCharTerm6
import Submission.Work.FIArea7.norm_ratWeight_charSum_le
import Submission.Work.FIArea7.UniMollify6

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Plancherel for the character table of a finite abelian group -/

lemma mul_conj_eq_ofReal_normSq (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [show star z = (starRingEnd ℂ) z from rfl, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Plancherel for the character table of a finite abelian group.  The chi-sum of the squared
modulus of the Fourier transform of a is |G| times the L2-mass of a. -/
theorem sum_char_mul_star_self (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G]
    (a : G → ℂ) :
    ∑ χ : AddChar (Additive G) ℂ,
        (∑ p, a p * χ (Additive.ofMul p)) * star (∑ p, a p * χ (Additive.ofMul p))
      = (Fintype.card G : ℂ) * ∑ p, a p * star (a p) := by
  classical
  have hexp : ∀ χ : AddChar (Additive G) ℂ,
      (∑ p, a p * χ (Additive.ofMul p)) * star (∑ p, a p * χ (Additive.ofMul p))
        = ∑ p, ∑ q, (a p * star (a q)) *
            (χ (Additive.ofMul p) * star (χ (Additive.ofMul q))) := by
    intro χ
    rw [star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [star_mul]
    ring
  simp_rw [hexp]
  rw [sum3_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hinner : ∀ q : G,
      (∑ χ : AddChar (Additive G) ℂ,
          (a p * star (a q)) * (χ (Additive.ofMul p) * star (χ (Additive.ofMul q))))
        = (a p * star (a q)) * (if p = q then (Fintype.card G : ℂ) else 0) := by
    intro q
    rw [← Finset.mul_sum, sum_addChar_mul_star p q]
  simp_rw [hinner]
  have hsingle : (∑ q, (a p * star (a q)) * (if p = q then (Fintype.card G : ℂ) else 0))
      = (a p * star (a p)) * (Fintype.card G : ℂ) := by
    rw [Finset.sum_eq_single p]
    · simp
    · intro q _ hq
      rw [if_neg (Ne.symm hq), mul_zero]
    · intro hp
      exact absurd (Finset.mem_univ p) hp
  rw [hsingle, mul_comm]

/-- The L1-bound for the Fourier transform of a : G → ℂ on a finite abelian group:
Cauchy-Schwarz against Plancherel gives sum_chi norm(ahat(chi)) <= |G| * sqrt(sum_p norm(a p)^2). -/
theorem sum_norm_addChar_mul_star_le {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (a : G → ℂ) :
    ∑ χ : AddChar (Additive G) ℂ, ‖∑ p, a p * χ (Additive.ofMul p)‖
      ≤ (Fintype.card G : ℝ) * Real.sqrt (∑ p, ‖a p‖ ^ 2) := by
  classical
  have hcard : (Fintype.card (AddChar (Additive G) ℂ) : ℝ) = (Fintype.card G : ℝ) := by simp
  have hplan : ∑ χ : AddChar (Additive G) ℂ, ‖∑ p, a p * χ (Additive.ofMul p)‖ ^ 2
      = (Fintype.card G : ℝ) * ∑ p, ‖a p‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum]
    have hpt : ∀ χ : AddChar (Additive G) ℂ,
        ((‖∑ p, a p * χ (Additive.ofMul p)‖ ^ 2 : ℝ) : ℂ)
          = (∑ p, a p * χ (Additive.ofMul p)) * star (∑ p, a p * χ (Additive.ofMul p)) := by
      intro χ
      rw [mul_conj_eq_ofReal_normSq]
    simp_rw [hpt]
    rw [sum_char_mul_star_self]
    rw [Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_sum]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [mul_conj_eq_ofReal_normSq]
  have hcs : (∑ χ : AddChar (Additive G) ℂ, ‖∑ p, a p * χ (Additive.ofMul p)‖) ^ 2
      ≤ (Fintype.card G : ℝ) * ((Fintype.card G : ℝ) * ∑ p, ‖a p‖ ^ 2) := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (AddChar (Additive G) ℂ)))
      (f := fun χ : AddChar (Additive G) ℂ => ‖∑ p, a p * χ (Additive.ofMul p)‖)
    simp only [Finset.card_univ] at h
    rw [hcard, hplan] at h
    exact h
  have hnonneg : (0 : ℝ) ≤ ∑ p, ‖a p‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hA0 : (0 : ℝ) ≤ ∑ χ : AddChar (Additive G) ℂ, ‖∑ p, a p * χ (Additive.ofMul p)‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hB0 : (0 : ℝ) ≤ (Fintype.card G : ℝ) * Real.sqrt (∑ p, ‖a p‖ ^ 2) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have h3 : (∑ χ : AddChar (Additive G) ℂ, ‖∑ p, a p * χ (Additive.ofMul p)‖) ^ 2
      ≤ ((Fintype.card G : ℝ) * Real.sqrt (∑ p, ‖a p‖ ^ 2)) ^ 2 := by
    have hsq : ((Fintype.card G : ℝ) * Real.sqrt (∑ p, ‖a p‖ ^ 2)) ^ 2
        = (Fintype.card G : ℝ) * ((Fintype.card G : ℝ) * ∑ p, ‖a p‖ ^ 2) := by
      rw [mul_pow, Real.sq_sqrt hnonneg]; ring
    rw [hsq]; exact hcs
  have h4 := Real.sqrt_le_sqrt h3
  rwa [Real.sqrt_sq hA0, Real.sqrt_sq hB0] at h4

/-! ## 2. The L1-bound on the omega-weights J(chi) = uniJChar Q e chi -/

/-- The L1-bound on the omega-weights of the section 16 expansion.  Summing norm (J(chi)) over
all characters chi of the Gaussian unit group (Z[i]/Q)^* costs only |G| * sqrt Q, where
G = GaussUnit Q; the trivial bound (from norm (ratWeight Q e p) <= 1 and at most Q rational
classes, Work.FIArea7.norm_ratWeight_charSum_le) would only give |G| * Q. -/
theorem sum_norm_uniJChar_le (Q e : ℕ) [NeZero Q] :
    ∑ χ : AddChar (Additive (GaussUnit Q)) ℂ, ‖uniJChar Q e χ‖
      ≤ (Fintype.card (GaussUnit Q) : ℝ) * Real.sqrt Q := by
  have hsquares : ∑ p : GaussUnit Q, ‖ratWeight Q e p‖ ^ 2 ≤ (Q : ℝ) := by
    have h1 : ∑ p : GaussUnit Q, ‖ratWeight Q e p‖ ^ 2
        = ∑ p ∈ Finset.univ.filter (fun p : GaussUnit Q => p.1.2 = 0),
            ‖ratWeight Q e p‖ ^ 2 := by
      rw [← Finset.sum_subset (Finset.subset_univ _)]
      intro p _ hp
      have h2 : p.1.2 ≠ 0 := by
        intro h0
        exact hp (Finset.mem_filter.mpr ⟨Finset.mem_univ p, h0⟩)
      rw [ratWeight, if_neg h2]
      simp
    rw [h1]
    calc ∑ p ∈ Finset.univ.filter (fun p : GaussUnit Q => p.1.2 = 0), ‖ratWeight Q e p‖ ^ 2
        ≤ ∑ _p ∈ Finset.univ.filter (fun p : GaussUnit Q => p.1.2 = 0), (1 : ℝ) := by
          refine Finset.sum_le_sum (fun p _ => ?_)
          have h3 := norm_ratWeight_le_one Q e p
          have h4 := norm_nonneg (ratWeight Q e p)
          nlinarith
      _ = ((Finset.univ.filter (fun p : GaussUnit Q => p.1.2 = 0)).card : ℝ) := by simp
      _ ≤ (Q : ℝ) := by exact_mod_cast card_ratWeight_support_le Q
  calc ∑ χ : AddChar (Additive (GaussUnit Q)) ℂ, ‖uniJChar Q e χ‖
      = ∑ χ : AddChar (Additive (GaussUnit Q)) ℂ,
          ‖∑ p, ratWeight Q e p * χ (Additive.ofMul p)‖ := rfl
    _ ≤ (Fintype.card (GaussUnit Q) : ℝ)
          * Real.sqrt (∑ p, ‖ratWeight Q e p‖ ^ 2) := sum_norm_addChar_mul_star_le _
    _ ≤ (Fintype.card (GaussUnit Q) : ℝ) * Real.sqrt Q := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact Real.sqrt_le_sqrt hsquares

/-! ## 3. The normalised chi-sum of the section 16 expansion -/

/-- The normalised character sum of (16.11).  If every character sum S(chi) is bounded by B and
the omega-weights satisfy sum_chi norm (J chi) <= |G| * A, then the normalised chi-sum of the
expansion is bounded by A * B^2. -/
theorem norm_inv_card_mul_sum_chi_le {G : Type*} [CommGroup G] [Fintype G]
    (J S : AddChar (Additive G) ℂ → ℂ) {A B : ℝ} (hB : 0 ≤ B)
    (hJ : ∑ χ : AddChar (Additive G) ℂ, ‖J χ‖ ≤ (Fintype.card G : ℝ) * A)
    (hS : ∀ χ : AddChar (Additive G) ℂ, ‖S χ‖ ≤ B) :
    ‖(1 / (Fintype.card G : ℂ)) * ∑ χ : AddChar (Additive G) ℂ, J χ * S χ * star (S χ)‖
      ≤ A * B ^ 2 := by
  have hterm : ∀ χ : AddChar (Additive G) ℂ, ‖J χ * S χ * star (S χ)‖ ≤ ‖J χ‖ * B ^ 2 := by
    intro χ
    have h1 := hS χ
    have h2 : ‖S χ‖ * ‖S χ‖ ≤ B * B := mul_le_mul h1 h1 (norm_nonneg _) hB
    rw [norm_mul, norm_mul, norm_star]
    calc ‖J χ‖ * ‖S χ‖ * ‖S χ‖ = ‖J χ‖ * (‖S χ‖ * ‖S χ‖) := by ring
      _ ≤ ‖J χ‖ * (B * B) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = ‖J χ‖ * B ^ 2 := by ring
  have hsum : ‖∑ χ : AddChar (Additive G) ℂ, J χ * S χ * star (S χ)‖
      ≤ ((Fintype.card G : ℝ) * A) * B ^ 2 := by
    calc ‖∑ χ : AddChar (Additive G) ℂ, J χ * S χ * star (S χ)‖
        ≤ ∑ χ : AddChar (Additive G) ℂ, ‖J χ * S χ * star (S χ)‖ := norm_sum_le _ _
      _ ≤ ∑ χ : AddChar (Additive G) ℂ, ‖J χ‖ * B ^ 2 := Finset.sum_le_sum (fun χ _ => hterm χ)
      _ = (∑ χ : AddChar (Additive G) ℂ, ‖J χ‖) * B ^ 2 := by rw [Finset.sum_mul]
      _ ≤ ((Fintype.card G : ℝ) * A) * B ^ 2 := mul_le_mul_of_nonneg_right hJ (by positivity)
  have hnorm : ‖(1 / (Fintype.card G : ℂ))‖ = 1 / (Fintype.card G : ℝ) := by
    rw [one_div, norm_inv, Complex.norm_natCast, one_div]
  rw [norm_mul, hnorm]
  calc 1 / (Fintype.card G : ℝ) * ‖∑ χ : AddChar (Additive G) ℂ, J χ * S χ * star (S χ)‖
      ≤ 1 / (Fintype.card G : ℝ) * (((Fintype.card G : ℝ) * A) * B ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = A * B ^ 2 := by field_simp

/-! ## 4. The harmonic weight of the frequency set -/

/-- The harmonic weight of the even frequency set.  evenFreq K is the set of nonzero even
integers of modulus at most 2K; re-indexing k ↦ |k| (each value occurring at most twice),
sum_{k in evenFreq K} 1/|k| = sum_{1 <= j <= K} 1/j <= 1 + log K <= 2 * log(2K+2) + 2. -/
theorem sum_inv_abs_evenFreq_le (K : ℕ) :
    ∑ k ∈ evenFreq K, (1 / ((|k| : ℤ) : ℝ)) ≤ 2 * Real.log (2 * (K : ℝ) + 2) + 2 := by
  rw [evenFreq]
  have hmem : ∀ k ∈ (Finset.Icc (-(2 * (K : ℤ))) (2 * (K : ℤ))).filter
      (fun k => k ≠ 0 ∧ Even k),
      -(2 * (K : ℤ)) ≤ k ∧ k ≤ 2 * (K : ℤ) ∧ k ≠ 0 ∧ Even k := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    exact ⟨hk.1.1, hk.1.2, hk.2.1, hk.2.2⟩
  have hmaps : ∀ k ∈ (Finset.Icc (-(2 * (K : ℤ))) (2 * (K : ℤ))).filter
      (fun k => k ≠ 0 ∧ Even k), k.natAbs ∈ Finset.Icc 1 (2 * K) := by
    intro k hk
    obtain ⟨hk1, hk2, hk0, hev⟩ := hmem k hk
    rw [Finset.mem_Icc]
    constructor
    · have h3 : ((1 : ℤ)) ≤ (k.natAbs : ℤ) := by
        rw [Int.natCast_natAbs]
        by_cases h : 0 ≤ k
        · exact le_trans (by omega : (1 : ℤ) ≤ k) (le_abs_self k)
        · exact le_trans (by omega : (1 : ℤ) ≤ -k) (neg_le_abs k)
      exact_mod_cast h3
    · have h3 : (k.natAbs : ℤ) ≤ 2 * (K : ℤ) := by
        rw [Int.natCast_natAbs, abs_le]
        exact ⟨by omega, by omega⟩
      exact_mod_cast h3
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun k : ℤ => (1 / ((|k| : ℤ) : ℝ)))]
  have hfib : ∀ j ∈ Finset.Icc 1 (2 * K),
      ∑ k ∈ ((Finset.Icc (-(2 * (K : ℤ))) (2 * (K : ℤ))).filter
          (fun k => k ≠ 0 ∧ Even k)).filter (fun k => k.natAbs = j),
        (1 / ((|k| : ℤ) : ℝ)) ≤ 2 * (1 / (j : ℝ)) := by
    intro j hj
    have hterm : ∀ k ∈ ((Finset.Icc (-(2 * (K : ℤ))) (2 * (K : ℤ))).filter
        (fun k => k ≠ 0 ∧ Even k)).filter (fun k => k.natAbs = j),
        (1 / ((|k| : ℤ) : ℝ)) = 1 / (j : ℝ) := by
      intro k hk
      rw [Finset.mem_filter] at hk
      have hk1 : k.natAbs = j := hk.2
      have hkj : ((|k| : ℤ) : ℝ) = (j : ℝ) := by
        rw [← Int.natCast_natAbs, hk1]; simp
      rw [hkj]
    have hcard : (((Finset.Icc (-(2 * (K : ℤ))) (2 * (K : ℤ))).filter
        (fun k => k ≠ 0 ∧ Even k)).filter (fun k => k.natAbs = j)).card ≤ 2 := by
      have hsub : ((Finset.Icc (-(2 * (K : ℤ))) (2 * (K : ℤ))).filter
          (fun k => k ≠ 0 ∧ Even k)).filter (fun k => k.natAbs = j)
            ⊆ ({(j : ℤ), -(j : ℤ)} : Finset ℤ) := by
        intro k hk
        rw [Finset.mem_filter] at hk
        have hk1 : k.natAbs = j := hk.2
        have h4 : k.natAbs = ((j : ℤ)).natAbs := by rw [Int.natAbs_natCast]; exact hk1
        rcases (Int.natAbs_eq_natAbs_iff.mp h4) with h | h
        · rw [h]; simp
        · rw [h]; simp
      calc _ ≤ ({(j : ℤ), -(j : ℤ)} : Finset ℤ).card := Finset.card_le_card hsub
        _ ≤ 2 := by
            have hc := Finset.card_insert_le (j : ℤ) ({-(j : ℤ)} : Finset ℤ)
            rw [Finset.card_singleton] at hc
            simpa using hc
    calc ∑ k ∈ ((Finset.Icc (-(2 * (K : ℤ))) (2 * (K : ℤ))).filter
            (fun k => k ≠ 0 ∧ Even k)).filter (fun k => k.natAbs = j),
            (1 / ((|k| : ℤ) : ℝ))
        = ∑ k ∈ ((Finset.Icc (-(2 * (K : ℤ))) (2 * (K : ℤ))).filter
            (fun k => k ≠ 0 ∧ Even k)).filter (fun k => k.natAbs = j), (1 / (j : ℝ)) :=
          Finset.sum_congr rfl hterm
      _ = ((((Finset.Icc (-(2 * (K : ℤ))) (2 * (K : ℤ))).filter
            (fun k => k ≠ 0 ∧ Even k)).filter (fun k => k.natAbs = j)).card : ℝ)
            * (1 / (j : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * (1 / (j : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hcard
  refine le_trans (Finset.sum_le_sum hfib) ?_
  have hharm : ∑ j ∈ Finset.Icc 1 (2 * K), (1 : ℝ) / (j : ℝ) ≤ 1 + Real.log (2 * K : ℝ) := by
    have hcast : ((harmonic (2 * K) : ℚ) : ℝ) = ∑ j ∈ Finset.Icc 1 (2 * K), (1 : ℝ) / (j : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      ring
    calc ∑ j ∈ Finset.Icc 1 (2 * K), (1 : ℝ) / (j : ℝ) = ((harmonic (2 * K) : ℚ) : ℝ) :=
          hcast.symm
      _ ≤ 1 + Real.log (2 * K) := by
          have hh := harmonic_le_one_add_log (2 * K)
          push_cast at hh
          exact hh
  calc ∑ j ∈ Finset.Icc 1 (2 * K), 2 * (1 / (j : ℝ))
      = 2 * ∑ j ∈ Finset.Icc 1 (2 * K), (1 / (j : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ 2 * (1 + Real.log (2 * K : ℝ)) := mul_le_mul_of_nonneg_left hharm (by norm_num)
    _ ≤ 2 * Real.log (2 * (K : ℝ) + 2) + 2 := by
        have h2 : (2 * (K : ℝ)) ≤ 2 * (K : ℝ) + 2 := by linarith
        have hlog : Real.log (2 * K : ℝ) ≤ Real.log (2 * (K : ℝ) + 2) := by
          rcases eq_or_lt_of_le (show (0 : ℝ) ≤ 2 * (K : ℝ) by positivity) with h | h
          · rw [← h, Real.log_zero]; positivity
          · exact Real.log_le_log h h2
        linarith

end

end Work.FIArea7
