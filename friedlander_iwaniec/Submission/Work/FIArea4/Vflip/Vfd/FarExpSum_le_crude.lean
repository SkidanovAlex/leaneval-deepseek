import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.FarSepDefs
import Submission.Work.FIArea4.Vflip.Vfd.card_congr_crude

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# The crude bound for the far exponential sum of a `(m,c,Q)`-piece

This file proves `FarExpSum_le_crude`: the far exponential sum `farExpSum D R S a b α m c 0 1 u t`
(the piece with flipped modulus `q' = 1`) is bounded crudely by the energy of the reduced
coefficient array `redA c α` on the reduced box `Rred c R × S`, with the *crude* constant
`4·Rred·S/m + 2·min(Rred,S)` of the counting lemma `card_congr_crude`.

The proof is elementary: take absolute values (every phase has modulus one and every
Jacobi–Möbius factor has modulus at most one), apply AM–GM
`|α_p||α_q| ≤ (|α_p|²+|α_q|²)/2`, and bound the number of partners `q` of a fixed `p` under the
congruence `m | p₁q₂ - q₁p₂` by `card_congr_crude`.
-/

/-! ## Auxiliary objects -/

/-- The reduced box `[1,2Rr] × [1,2S]` of the `c`-group. -/
abbrev farRedBox (Rr S : ℕ) : Finset (ℕ × ℕ) :=
  Finset.Icc 1 (2 * Rr) ×ˢ Finset.Icc 1 (2 * S)

/-- The congruence `m | p₁q₂ - q₁p₂` between two reduced points. -/
abbrev farPairCongr (m : ℕ) (p q : ℕ × ℕ) : Prop :=
  (m : ℤ) ∣ (p.1 : ℤ) * (q.2 : ℤ) - (q.1 : ℤ) * (p.2 : ℤ)

lemma farPairCongr_comm (m : ℕ) (p q : ℕ × ℕ) :
    farPairCongr m p q ↔ farPairCongr m q p := by
  unfold farPairCongr
  have h : (q.1 : ℤ) * (p.2 : ℤ) - (p.1 : ℤ) * (q.2 : ℤ)
      = -((p.1 : ℤ) * (q.2 : ℤ) - (q.1 : ℤ) * (p.2 : ℤ)) := by ring
  rw [h]
  exact (dvd_neg (α := ℤ)).symm

/-! ## Elementary norm bounds -/

lemma norm_jacobiSym_cast_le_one (z : ℤ) (b : ℕ) : ‖(((jacobiSym z b : ℤ)) : ℂ)‖ ≤ 1 := by
  rcases jacobiSym.trichotomy z b with h | h | h <;> rw [h] <;> norm_num

lemma norm_moebius_cast_le_one (m : ℕ) : ‖(((ArithmeticFunction.moebius m : ℤ)) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := m)

lemma norm_exp_two_pi_I_mul (x : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have : (2 * Real.pi * Complex.I * (x : ℂ)).re = 0 := by simp [Complex.mul_re]
  rw [this, Real.exp_zero]

lemma norm_exp_two_pi_I_mul_prod (u x : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * ((u : ℂ) * (x : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  have hh : (2 * Real.pi * Complex.I * ((u : ℂ) * (x : ℂ))).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hh, Real.exp_zero]

lemma norm_cpow_I_mul_le_one {y : ℝ} (hy : 0 ≤ y) (t : ℝ) :
    ‖((y : ℂ)) ^ (Complex.I * (t : ℂ))‖ ≤ 1 := by
  have h := Complex.norm_cpow_le (y : ℂ) (Complex.I * (t : ℂ))
  have hre : (Complex.I * (t : ℂ)).re = 0 := by simp [Complex.mul_re]
  rw [hre, Real.rpow_zero] at h
  have harg : (y : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg hy
  rw [harg] at h
  simp only [zero_mul, Real.exp_zero, div_one] at h
  exact h

lemma amgm_normSq (x y : ℂ) :
    ‖x‖ * ‖y‖ ≤ (Complex.normSq x + Complex.normSq y) / 2 := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- The `farCoef` of an index has modulus at most `‖α (cρ₁) s₁‖·‖α (cρ₂) s₂‖`. -/
lemma norm_farCoef_le (m c : ℕ) (α : ℕ → ℕ → ℂ) (i : FarIx) :
    ‖farCoef m c α i‖ ≤ ‖α (c * i.1.2.1) i.1.2.2‖ * ‖α (c * i.2.1) i.2.2‖ := by
  unfold farCoef
  simp only [norm_mul, norm_star]
  have hA : ‖(((ArithmeticFunction.moebius m : ℤ)) : ℂ)‖ ≤ 1 := norm_moebius_cast_le_one m
  have hB : ‖(((jacobiSym (i.1.2.2 : ℤ) i.1.2.1 * jacobiSym (i.2.2 : ℤ) i.2.1 : ℤ)) : ℂ)‖ ≤ 1 := by
    rw [Int.cast_mul, norm_mul]
    exact mul_le_one₀ (norm_jacobiSym_cast_le_one _ _) (norm_nonneg _)
      (norm_jacobiSym_cast_le_one _ _)
  have hC : ‖(((jacobiSym (i.1.2.1 : ℤ) (Work.FIPlan.oddPart i.1.1) *
      jacobiSym (i.2.1 : ℤ) (Work.FIPlan.oddPart i.1.1) : ℤ)) : ℂ)‖ ≤ 1 := by
    rw [Int.cast_mul, norm_mul]
    exact mul_le_one₀ (norm_jacobiSym_cast_le_one _ _) (norm_nonneg _)
      (norm_jacobiSym_cast_le_one _ _)
  have h1 : ‖(((ArithmeticFunction.moebius m : ℤ)) : ℂ)‖ *
      ‖(((jacobiSym (i.1.2.2 : ℤ) i.1.2.1 * jacobiSym (i.2.2 : ℤ) i.2.1 : ℤ)) : ℂ)‖ ≤ 1 := by
    have := mul_le_mul hA hB (norm_nonneg _) zero_le_one
    simpa using this
  calc ‖(((ArithmeticFunction.moebius m : ℤ)) : ℂ)‖ *
        ‖(((jacobiSym (i.1.2.2 : ℤ) i.1.2.1 * jacobiSym (i.2.2 : ℤ) i.2.1 : ℤ)) : ℂ)‖ *
          (‖α (c * i.1.2.1) i.1.2.2‖ * ‖α (c * i.2.1) i.2.2‖) *
        ‖(((jacobiSym (i.1.2.1 : ℤ) (Work.FIPlan.oddPart i.1.1) *
            jacobiSym (i.2.1 : ℤ) (Work.FIPlan.oddPart i.1.1) : ℤ)) : ℂ)‖
      ≤ 1 * (‖α (c * i.1.2.1) i.1.2.2‖ * ‖α (c * i.2.1) i.2.2‖) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right h1 (by positivity)) hC (norm_nonneg _) (by positivity)
    _ = ‖α (c * i.1.2.1) i.1.2.2‖ * ‖α (c * i.2.1) i.2.2‖ := by ring

/-- `iAbs c i = |ρ₁ s₂ - ρ₂ s₁|` when the reduced moduli are coprime. -/
lemma iAbs_eq_natAbs {c : ℕ} (hc : 0 < c) {i : FarIx}
    (hcop : Nat.Coprime i.1.2.1 i.2.1) :
    iAbs c i
      = ((i.1.2.1 : ℤ) * (i.2.2 : ℤ) - (i.2.1 : ℤ) * (i.1.2.2 : ℤ)).natAbs := by
  unfold iAbs
  have hC : pairC (c * i.1.2.1) (c * i.2.1) = c := by
    rw [pairC, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
  have hR1 : pairR (c * i.1.2.1) (c * i.2.1) = i.1.2.1 := by
    rw [pairR, hC, Nat.mul_div_cancel_left _ hc]
  have hR2 : pairR (c * i.2.1) (c * i.1.2.1) = i.2.1 := by
    rw [pairR, pairC, Nat.gcd_comm (c * i.2.1) (c * i.1.2.1), Nat.gcd_mul_left,
      hcop.gcd_eq_one, mul_one, Nat.mul_div_cancel_left _ hc]
  rw [pairAbs, hR1, hR2]

/-- Coprimality of a reduced point follows from the support hypothesis `(cρ, 2s) = 1`. -/
lemma coprime_reduced_of_support {α : ℕ → ℕ → ℂ} {c : ℕ}
    (hcop : ∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) (p : ℕ × ℕ)
    (h : α (c * p.1) p.2 ≠ 0) : Nat.Coprime p.1 p.2 :=
  Nat.Coprime.coprime_dvd_right (dvd_mul_left p.2 2)
    (Nat.Coprime.coprime_dvd_left (dvd_mul_left p.1 c) (hcop (c * p.1) p.2 h))

/-! ## The counting-to-energy step -/

/-- **The crude bound for a doubly-indexed far sum.**  If every `p` of the reduced box with
`α (c p₁) p₂ ≠ 0` has `(p₁,p₂) = 1` and every congruence class has size at most `K` (the counting
lemma `card_congr_crude`), then the double sum of `‖α_p‖‖α_q‖` over the congruence
`m | p₁q₂ - q₁p₂` is bounded by `K·p14L2 Rr S (redA c α)`. -/
lemma far_reduced_sum_bound (Rr S m c : ℕ) (hm : 1 ≤ m) (α : ℕ → ℕ → ℂ)
    (hcnt : ∀ a b : ℕ, Nat.Coprime a b →
      ((((farRedBox Rr S).filter
        (fun p : ℕ × ℕ => (m : ℤ) ∣ (a : ℤ) * (p.2 : ℤ) - (p.1 : ℤ) * (b : ℤ))).card : ℝ)
        ≤ 4 * (Rr : ℝ) * (S : ℝ) / (m : ℝ) + 2 * min (Rr : ℝ) (S : ℝ)))
    (hcopf : ∀ p ∈ farRedBox Rr S,
      Complex.normSq (α (c * p.1) p.2) ≠ 0 → Nat.Coprime p.1 p.2) :
    (∑ x ∈ (farRedBox Rr S ×ˢ farRedBox Rr S).filter
        (fun x : (ℕ × ℕ) × (ℕ × ℕ) => farPairCongr m x.1 x.2),
        ‖α (c * x.1.1) x.1.2‖ * ‖α (c * x.2.1) x.2.2‖)
      ≤ (4 * (Rr : ℝ) * (S : ℝ) / (m : ℝ) + 2 * min (Rr : ℝ) (S : ℝ))
          * p14L2 Rr S (redA c α) := by
  set KK : ℝ := 4 * (Rr : ℝ) * (S : ℝ) / (m : ℝ) + 2 * min (Rr : ℝ) (S : ℝ) with hKK
  have hcard : ∀ a b : ℕ, Nat.Coprime a b →
      (((farRedBox Rr S).filter
        (fun p : ℕ × ℕ => (m : ℤ) ∣ (a : ℤ) * (p.2 : ℤ) - (p.1 : ℤ) * (b : ℤ))).card : ℝ) ≤ KK := by
    intro a b hab
    rw [hKK]
    exact hcnt a b hab
  -- Step 1: the sum over the filtered product as a double sum.
  have hstep1 : (∑ x ∈ (farRedBox Rr S ×ˢ farRedBox Rr S).filter
        (fun x : (ℕ × ℕ) × (ℕ × ℕ) => farPairCongr m x.1 x.2),
        ‖α (c * x.1.1) x.1.2‖ * ‖α (c * x.2.1) x.2.2‖)
      = ∑ p ∈ farRedBox Rr S, ∑ q ∈ farRedBox Rr S,
          (if farPairCongr m p q then ‖α (c * p.1) p.2‖ * ‖α (c * q.1) q.2‖ else 0) := by
    rw [Finset.sum_filter, Finset.sum_product]
  -- Step 2: AM-GM pointwise.
  have hstep2 : (∑ p ∈ farRedBox Rr S, ∑ q ∈ farRedBox Rr S,
          (if farPairCongr m p q then ‖α (c * p.1) p.2‖ * ‖α (c * q.1) q.2‖ else 0))
      ≤ ∑ p ∈ farRedBox Rr S, ∑ q ∈ farRedBox Rr S,
          ((if farPairCongr m p q then Complex.normSq (α (c * p.1) p.2) / 2 else 0)
            + (if farPairCongr m p q then Complex.normSq (α (c * q.1) q.2) / 2 else 0)) := by
    refine Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun q _ => ?_))
    by_cases h : farPairCongr m p q
    · rw [if_pos h, if_pos h, if_pos h]
      have hg := amgm_normSq (α (c * p.1) p.2) (α (c * q.1) q.2)
      linarith
    · rw [if_neg h, if_neg h, if_neg h]; norm_num
  -- Step 3: separate the two halves.
  have hstep3 : (∑ p ∈ farRedBox Rr S, ∑ q ∈ farRedBox Rr S,
          ((if farPairCongr m p q then Complex.normSq (α (c * p.1) p.2) / 2 else 0)
            + (if farPairCongr m p q then Complex.normSq (α (c * q.1) q.2) / 2 else 0)))
      = (∑ p ∈ farRedBox Rr S, ∑ q ∈ farRedBox Rr S,
            (if farPairCongr m p q then Complex.normSq (α (c * p.1) p.2) / 2 else 0))
        + (∑ p ∈ farRedBox Rr S, ∑ q ∈ farRedBox Rr S,
            (if farPairCongr m p q then Complex.normSq (α (c * q.1) q.2) / 2 else 0)) := by
    simp only [Finset.sum_add_distrib]
  -- First half.
  have hA1 : ∀ p ∈ farRedBox Rr S,
      (∑ q ∈ farRedBox Rr S,
        (if farPairCongr m p q then Complex.normSq (α (c * p.1) p.2) / 2 else 0))
      ≤ KK * (Complex.normSq (α (c * p.1) p.2) / 2) := by
    intro p hp
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    by_cases h0 : Complex.normSq (α (c * p.1) p.2) = 0
    · rw [h0]; simp
    · have hcp : Nat.Coprime p.1 p.2 := hcopf p hp h0
      refine mul_le_mul_of_nonneg_right ?_
        (div_nonneg (Complex.normSq_nonneg _) (by norm_num))
      exact hcard p.1 p.2 hcp
  have hAp : (∑ p ∈ farRedBox Rr S, ∑ q ∈ farRedBox Rr S,
        (if farPairCongr m p q then Complex.normSq (α (c * p.1) p.2) / 2 else 0))
      ≤ KK * (∑ p ∈ farRedBox Rr S, Complex.normSq (α (c * p.1) p.2)) / 2 := by
    calc ∑ p ∈ farRedBox Rr S, ∑ q ∈ farRedBox Rr S,
            (if farPairCongr m p q then Complex.normSq (α (c * p.1) p.2) / 2 else 0)
        ≤ ∑ p ∈ farRedBox Rr S, KK * (Complex.normSq (α (c * p.1) p.2) / 2) :=
          Finset.sum_le_sum hA1
      _ = KK * (∑ p ∈ farRedBox Rr S, Complex.normSq (α (c * p.1) p.2) / 2) := by
          rw [Finset.mul_sum]
      _ = KK * ((∑ p ∈ farRedBox Rr S, Complex.normSq (α (c * p.1) p.2)) / 2) := by
          rw [Finset.sum_div]
      _ = KK * (∑ p ∈ farRedBox Rr S, Complex.normSq (α (c * p.1) p.2)) / 2 := by ring
  -- Second half.
  have hB1 : ∀ q ∈ farRedBox Rr S,
      (∑ p ∈ farRedBox Rr S,
        (if farPairCongr m p q then Complex.normSq (α (c * q.1) q.2) / 2 else 0))
      ≤ KK * (Complex.normSq (α (c * q.1) q.2) / 2) := by
    intro q hq
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hfilteq : (farRedBox Rr S).filter (fun p => farPairCongr m p q)
        = (farRedBox Rr S).filter
            (fun r : ℕ × ℕ => (m : ℤ) ∣ (q.1 : ℤ) * (r.2 : ℤ) - (r.1 : ℤ) * (q.2 : ℤ)) := by
      refine Finset.filter_congr (fun r _ => ?_)
      exact farPairCongr_comm m r q
    rw [hfilteq]
    by_cases h0 : Complex.normSq (α (c * q.1) q.2) = 0
    · rw [h0]; simp
    · have hcq : Nat.Coprime q.1 q.2 := hcopf q hq h0
      exact mul_le_mul_of_nonneg_right (hcard q.1 q.2 hcq)
        (div_nonneg (Complex.normSq_nonneg _) (by norm_num))
  have hBq : (∑ p ∈ farRedBox Rr S, ∑ q ∈ farRedBox Rr S,
        (if farPairCongr m p q then Complex.normSq (α (c * q.1) q.2) / 2 else 0))
      ≤ KK * (∑ p ∈ farRedBox Rr S, Complex.normSq (α (c * p.1) p.2)) / 2 := by
    rw [Finset.sum_comm]
    calc ∑ q ∈ farRedBox Rr S, ∑ p ∈ farRedBox Rr S,
            (if farPairCongr m p q then Complex.normSq (α (c * q.1) q.2) / 2 else 0)
        ≤ ∑ q ∈ farRedBox Rr S, KK * (Complex.normSq (α (c * q.1) q.2) / 2) :=
          Finset.sum_le_sum hB1
      _ = KK * (∑ q ∈ farRedBox Rr S, Complex.normSq (α (c * q.1) q.2) / 2) := by
          rw [Finset.mul_sum]
      _ = KK * ((∑ q ∈ farRedBox Rr S, Complex.normSq (α (c * q.1) q.2)) / 2) := by
          rw [Finset.sum_div]
      _ = KK * (∑ q ∈ farRedBox Rr S, Complex.normSq (α (c * q.1) q.2)) / 2 := by ring
  -- Assemble.
  have hL2 : (∑ p ∈ farRedBox Rr S, Complex.normSq (α (c * p.1) p.2))
      = p14L2 Rr S (redA c α) := by
    rw [p14L2, farRedBox, Finset.sum_product]
    rfl
  calc (∑ x ∈ (farRedBox Rr S ×ˢ farRedBox Rr S).filter
        (fun x : (ℕ × ℕ) × (ℕ × ℕ) => farPairCongr m x.1 x.2),
        ‖α (c * x.1.1) x.1.2‖ * ‖α (c * x.2.1) x.2.2‖)
      = ∑ p ∈ farRedBox Rr S, ∑ q ∈ farRedBox Rr S,
          (if farPairCongr m p q then ‖α (c * p.1) p.2‖ * ‖α (c * q.1) q.2‖ else 0) := hstep1
    _ ≤ ∑ p ∈ farRedBox Rr S, ∑ q ∈ farRedBox Rr S,
          ((if farPairCongr m p q then Complex.normSq (α (c * p.1) p.2) / 2 else 0)
            + (if farPairCongr m p q then Complex.normSq (α (c * q.1) q.2) / 2 else 0)) := hstep2
    _ = (∑ p ∈ farRedBox Rr S, ∑ q ∈ farRedBox Rr S,
            (if farPairCongr m p q then Complex.normSq (α (c * p.1) p.2) / 2 else 0))
        + (∑ p ∈ farRedBox Rr S, ∑ q ∈ farRedBox Rr S,
            (if farPairCongr m p q then Complex.normSq (α (c * q.1) q.2) / 2 else 0)) := hstep3
    _ ≤ KK * (∑ p ∈ farRedBox Rr S, Complex.normSq (α (c * p.1) p.2)) / 2
        + KK * (∑ p ∈ farRedBox Rr S, Complex.normSq (α (c * p.1) p.2)) / 2 :=
          add_le_add hAp hBq
    _ = KK * (∑ p ∈ farRedBox Rr S, Complex.normSq (α (c * p.1) p.2)) := by ring
    _ = KK * p14L2 Rr S (redA c α) := by rw [hL2]

lemma ySep_nonneg (c D : ℕ) (i : FarIx) : 0 ≤ ySep c D i := by
  unfold ySep
  positivity

/-! ## The main theorem -/

/-- **The crude bound for the far exponential sum** of a `(m,c,Q)`-piece with `Q = (0,1]`:
away from the sharp large-sieve input, the far exponential sum of modulus `m` and reduced box
`Rred c R × S` is bounded by `(4·Rred·S/m + 2·min(Rred,S))` times the energy `p14L2` of the reduced
coefficient array. -/
theorem FarExpSum_le_crude {D R S : ℕ} (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b : ℝ) (α : ℕ → ℕ → ℂ) (m c : ℕ) (u t : ℝ),
        1 ≤ c → 1 ≤ m →
        (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
        (∀ r s, α r s ≠ 0 → R < r ∧ r ≤ 2 * R ∧ S < s ∧ s ≤ 2 * S) →
        ‖Work.FIArea4.Vflip.Vfd.farExpSum D R S a b α m c 0 1 u t‖
          ≤ C * (4 * ((Work.FIArea4.Vflip.Vfd.Rred c R : ℝ)) * S / m
                  + 2 * min ((Work.FIArea4.Vflip.Vfd.Rred c R : ℝ)) S)
              * Work.FIArea4.p14L2 (Work.FIArea4.Vflip.Vfd.Rred c R) S
                  (Work.FIArea4.Vflip.Vfd.redA c α) := by
  refine ⟨1, one_pos, ?_⟩
  intro a b α m c u t hc hm hsupp hbox
  -- coprimality of a reduced point follows from the support hypothesis
  have hcopf : ∀ p ∈ farRedBox (Rred c R) S,
      Complex.normSq (α (c * p.1) p.2) ≠ 0 → Nat.Coprime p.1 p.2 := by
    intro p hp h0
    exact coprime_reduced_of_support hsupp p (fun hz => h0 (by rw [hz, Complex.normSq_zero]))
  -- Step A: take absolute values inside the sum.
  have hnorm : ‖farExpSum D R S a b α m c 0 1 u t‖
      ≤ ∑ i ∈ farSet D R S a b m c 0 1,
          ‖α (c * i.1.2.1) i.1.2.2‖ * ‖α (c * i.2.1) i.2.2‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun i _ => ?_))
    calc ‖farCoef m c α i * Complex.exp (2 * Real.pi * Complex.I * (u * xOrig c i)) *
          ((ySep c D i : ℝ) : ℂ) ^ (Complex.I * (t : ℂ))‖
        = ‖farCoef m c α i‖ * ‖Complex.exp (2 * Real.pi * Complex.I * (u * xOrig c i))‖ *
            ‖((ySep c D i : ℝ) : ℂ) ^ (Complex.I * (t : ℂ))‖ := by rw [norm_mul, norm_mul]
      _ = ‖farCoef m c α i‖ * 1 * ‖((ySep c D i : ℝ) : ℂ) ^ (Complex.I * (t : ℂ))‖ := by
            rw [norm_exp_two_pi_I_mul_prod]
      _ ≤ ‖farCoef m c α i‖ * 1 * 1 := by
            gcongr
            exact norm_cpow_I_mul_le_one (ySep_nonneg c D i) t
      _ = ‖farCoef m c α i‖ := by ring
      _ ≤ ‖α (c * i.1.2.1) i.1.2.2‖ * ‖α (c * i.2.1) i.2.2‖ := norm_farCoef_le m c α i
  -- Step B: the image of `farSet` under the projection lands in the reduced box and preserves
  -- the congruence.
  have hproj : ∀ x ∈ (farSet D R S a b m c 0 1).image (fun i : FarIx => (i.1.2, i.2)),
      x ∈ (farRedBox (Rred c R) S ×ˢ farRedBox (Rred c R) S).filter
        (fun x : (ℕ × ℕ) × (ℕ × ℕ) => farPairCongr m x.1 x.2) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    obtain ⟨hq0, hq1le, _, _, _, _, _, hfc⟩ := mem_farSet.mp hi
    obtain ⟨hcpos, hcopr, ha1, ha2, hb1, hb2, hsa1, hsa2, hsb1, hsb2, hmdvd, hmq⟩ := hfc
    have hq1 : i.1.1 = 1 := by omega
    -- bounds on the reduced coordinates
    have hρ1ge : 1 ≤ i.1.2.1 := by
      have hpos : 0 < i.1.2.1 := Nat.pos_of_mul_pos_left
        (lt_of_lt_of_le (by omega : 0 < R) (le_of_lt ha1))
      omega
    have hρ1le : i.1.2.1 ≤ 2 * Rred c R := by
      have h : i.1.2.1 ≤ Rred c R := by
        rw [Rred]
        exact (Nat.le_div_iff_mul_le hcpos).mpr (by simpa [Nat.mul_comm] using ha2)
      omega
    have hρ2ge : 1 ≤ i.2.1 := by
      have hpos : 0 < i.2.1 := Nat.pos_of_mul_pos_left
        (lt_of_lt_of_le (by omega : 0 < R) (le_of_lt hb1))
      omega
    have hρ2le : i.2.1 ≤ 2 * Rred c R := by
      have h : i.2.1 ≤ Rred c R := by
        rw [Rred]
        exact (Nat.le_div_iff_mul_le hcpos).mpr (by simpa [Nat.mul_comm] using hb2)
      omega
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hρ1ge, hρ1le⟩,
          Finset.mem_Icc.mpr ⟨le_trans hS (le_of_lt hsa1), hsa2⟩⟩
      · exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hρ2ge, hρ2le⟩,
          Finset.mem_Icc.mpr ⟨le_trans hS (le_of_lt hsb1), hsb2⟩⟩
    · -- the congruence
      have hdvd : m ∣ iAbs c i := by rwa [hq1, mul_one] at hmq
      rw [iAbs_eq_natAbs hcpos hcopr] at hdvd
      have h2 : (m : ℤ) ∣ (((i.1.2.1 : ℤ) * (i.2.2 : ℤ) - (i.2.1 : ℤ) * (i.1.2.2 : ℤ)).natAbs : ℤ) := by
        exact_mod_cast hdvd
      exact (Int.dvd_natAbs.mp h2)
  -- Step C: injectivity of the projection on `farSet`.
  have hinj : Set.InjOn (fun i : FarIx => (i.1.2, i.2)) ↑(farSet D R S a b m c 0 1) := by
    intro i hi j hj heq
    have hi1 : i.1.1 = 1 := by
      obtain ⟨hq0, hq1le, _, _, _, _, _, _⟩ := mem_farSet.mp hi; omega
    have hj1 : j.1.1 = 1 := by
      obtain ⟨hq0, hq1le, _, _, _, _, _, _⟩ := mem_farSet.mp hj; omega
    have hfst : i.1.2 = j.1.2 := congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1) heq
    have hsnd : i.2 = j.2 := congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2) heq
    refine Prod.ext ?_ hsnd
    exact Prod.ext (by rw [hi1, hj1]) hfst
  have hsumcmp : (∑ i ∈ farSet D R S a b m c 0 1,
          ‖α (c * i.1.2.1) i.1.2.2‖ * ‖α (c * i.2.1) i.2.2‖)
      ≤ ∑ x ∈ (farRedBox (Rred c R) S ×ˢ farRedBox (Rred c R) S).filter
          (fun x : (ℕ × ℕ) × (ℕ × ℕ) => farPairCongr m x.1 x.2),
          ‖α (c * x.1.1) x.1.2‖ * ‖α (c * x.2.1) x.2.2‖ := by
    calc ∑ i ∈ farSet D R S a b m c 0 1,
            ‖α (c * i.1.2.1) i.1.2.2‖ * ‖α (c * i.2.1) i.2.2‖
        = ∑ x ∈ (farSet D R S a b m c 0 1).image (fun i : FarIx => (i.1.2, i.2)),
            ‖α (c * x.1.1) x.1.2‖ * ‖α (c * x.2.1) x.2.2‖ := by
          rw [Finset.sum_image hinj]
      _ ≤ ∑ x ∈ (farRedBox (Rred c R) S ×ˢ farRedBox (Rred c R) S).filter
            (fun x : (ℕ × ℕ) × (ℕ × ℕ) => farPairCongr m x.1 x.2),
            ‖α (c * x.1.1) x.1.2‖ * ‖α (c * x.2.1) x.2.2‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg hproj (fun x _ _ => by positivity)
  -- Step D: the counting-to-energy lemma.
  have hbound := far_reduced_sum_bound (Rred c R) S m c hm α
    (fun a' b' hab => card_congr_crude (Rred c R) S m a' b' hm hab) hcopf
  rw [one_mul]
  exact le_trans (le_trans hnorm hsumcmp) hbound


end

end Work.FIArea4.Vflip.Vfd
