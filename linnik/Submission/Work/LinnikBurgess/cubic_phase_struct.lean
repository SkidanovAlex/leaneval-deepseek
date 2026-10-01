import Mathlib
import Submission.Work.LinnikBurgess.cubic_phase_defs

/-!
# Structural lemmas for the reduced cubic phase

The stationary-phase reduction of the cubic Weyl sum produces, at a stationary point `c`,
the reduced phase `shiftPhase p β γ δ R c` (see `cubicPhase_rootSum`).  This module records
the three structural facts about it that drive the induction of
`Work.LinnikBurgess.cubic_phase_prime_pow`:

* if the quadratic coefficient `quadCoeff γ δ c` is a `p`-unit, the reduced phase is a
  *quadratic* phase in the sense of `IsQuad`, so the quadratic bound applies
  (`shiftPhase_isQuad`);
* otherwise the reduced phase splits as `a X + p · shiftPhaseLinear` (`shiftPhase_linear_form`);
* in the fully degenerate case `p ∣ a` and `p ∣ quadCoeff`, the reduced phase is `p` times a
  genuine cubic phase (`shiftPhase_factor`, `shiftPhaseLevel_isCubicShape`).
-/

namespace Work.LinnikBurgess

open Polynomial

/-- Splitting off the `X²` and `X³` terms of `resPoly`. -/
theorem resPoly_expand (p : ℕ) (R : Polynomial ℤ) (c : ℕ) :
    resPoly p R c
      = Polynomial.C ((Polynomial.hasseDeriv 2 R).eval (c : ℤ)) * Polynomial.X ^ 2
        + Polynomial.C ((Polynomial.hasseDeriv 3 R).eval (c : ℤ) * (p : ℤ)) * Polynomial.X ^ 3
        + Polynomial.C ((p : ℤ) ^ 2) * resPolyHi p R c := by
  by_cases hN : 3 ≤ R.natDegree
  · rw [resPoly, show R.natDegree - 1 = 2 + (R.natDegree - 3) by omega, Finset.sum_range_add]
    rw [show (∑ x ∈ Finset.range 2,
        Polynomial.C ((Polynomial.hasseDeriv (x + 2) R).eval (c : ℤ) * (p : ℤ) ^ x)
          * Polynomial.X ^ (x + 2))
      = Polynomial.C ((Polynomial.hasseDeriv 2 R).eval (c : ℤ)) * Polynomial.X ^ 2
        + Polynomial.C ((Polynomial.hasseDeriv 3 R).eval (c : ℤ) * (p : ℤ)) * Polynomial.X ^ 3 by
      rw [Finset.sum_range_succ, Finset.sum_range_one]; norm_num]
    congr 1
    rw [resPolyHi, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    have h1 : 2 + n + 2 = n + 4 := by omega
    have h2 : (p : ℤ) ^ (2 + n) = (p : ℤ) ^ 2 * (p : ℤ) ^ n := by rw [pow_add]
    rw [h1, h2]
    simp only [Polynomial.C_mul, Polynomial.C_pow]
    ring
  · have hN2 : R.natDegree ≤ 2 := by omega
    interval_cases h : R.natDegree
    · have h2 : Polynomial.hasseDeriv 2 R = 0 :=
        Polynomial.hasseDeriv_eq_zero_of_lt_natDegree (n := 2) R (by omega)
      have h3 : Polynomial.hasseDeriv 3 R = 0 :=
        Polynomial.hasseDeriv_eq_zero_of_lt_natDegree (n := 3) R (by omega)
      rw [resPoly, h, resPolyHi, h, h2, h3]
      simp
    · have h2 : Polynomial.hasseDeriv 2 R = 0 :=
        Polynomial.hasseDeriv_eq_zero_of_lt_natDegree (n := 2) R (by omega)
      have h3 : Polynomial.hasseDeriv 3 R = 0 :=
        Polynomial.hasseDeriv_eq_zero_of_lt_natDegree (n := 3) R (by omega)
      rw [resPoly, h, resPolyHi, h, h2, h3]
      simp
    · have h3 : Polynomial.hasseDeriv 3 R = 0 :=
        Polynomial.hasseDeriv_eq_zero_of_lt_natDegree (n := 3) R (by omega)
      rw [resPoly, h, resPolyHi, h, h3]
      simp

/-- If the quadratic coefficient is a `p`-unit, the reduced phase is a quadratic phase. -/
theorem shiftPhase_isQuad (p : ℕ) (β γ δ : ℤ) (R : Polynomial ℤ) (c : ℕ)
    (hs : ¬ (p : ℤ) ∣ quadCoeff γ δ c) :
    Commons.NumberTheory.GaussSum.IsQuad p (shiftPhase p β γ δ R c) := by
  refine ⟨linCoeff β γ δ c / (p : ℤ) + (Polynomial.derivative R).eval (c : ℤ), -(quadCoeff γ δ c),
    Polynomial.C δ * Polynomial.X ^ 3 + resPoly p R c, ?_, ?_⟩
  · rwa [dvd_neg]
  · rw [shiftPhase]
    simp only [Polynomial.C_mul, Polynomial.C_neg, Polynomial.C_pow]
    ring

/-- When the quadratic coefficient is divisible by `p`, the reduced phase is `a X + p · Φ`. -/
theorem shiftPhase_linear_form (p : ℕ) (hp : (p : ℤ) ≠ 0) (β γ δ : ℤ) (R : Polynomial ℤ) (c : ℕ)
    (hd : (p : ℤ) ∣ quadCoeff γ δ c) :
    shiftPhase p β γ δ R c
      = Polynomial.C (linCoeff β γ δ c / (p : ℤ) + (Polynomial.derivative R).eval (c : ℤ))
          * Polynomial.X
        + Polynomial.C (p : ℤ) * shiftPhaseLinear p γ δ R c := by
  obtain ⟨m, hm⟩ := hd
  rw [shiftPhase, shiftPhaseLinear, hm, Int.mul_ediv_cancel_left _ hp]
  simp only [Polynomial.C_mul, Polynomial.C_neg, Polynomial.C_pow]
  ring

/-- In the doubly degenerate case the reduced phase is `p` times the level-one phase. -/
theorem shiftPhase_factor (p : ℕ) (hp : (p : ℤ) ≠ 0) (β γ δ : ℤ) (R : Polynomial ℤ) (c : ℕ)
    (hd : (p : ℤ) ∣ quadCoeff γ δ c)
    (ha : (p : ℤ) ∣ linCoeff β γ δ c / (p : ℤ) + (Polynomial.derivative R).eval (c : ℤ)) :
    shiftPhase p β γ δ R c = Polynomial.C (p : ℤ) * shiftPhaseLevel p β γ δ R c := by
  obtain ⟨m, hm⟩ := hd
  obtain ⟨k, hk⟩ := ha
  rw [shiftPhase, shiftPhaseLevel, hm, hk, Int.mul_ediv_cancel_left _ hp,
    Int.mul_ediv_cancel_left _ hp]
  simp only [Polynomial.C_mul, Polynomial.C_neg, Polynomial.C_pow]
  ring

/-- The level-one phase of the doubly degenerate case is again a genuine cubic phase. -/
theorem shiftPhaseLevel_isCubicShape (p : ℕ) (β γ δ : ℤ) (R : Polynomial ℤ) (c : ℕ)
    (hδ : ¬ (p : ℤ) ∣ δ) :
    IsCubicShape p (shiftPhaseLevel p β γ δ R c) := by
  refine ⟨(linCoeff β γ δ c / (p : ℤ) + (Polynomial.derivative R).eval (c : ℤ)) / (p : ℤ),
    quadCoeff γ δ c / (p : ℤ) + (Polynomial.hasseDeriv 2 R).eval (c : ℤ),
    δ + (p : ℤ) * (Polynomial.hasseDeriv 3 R).eval (c : ℤ),
    Polynomial.C (p : ℤ) * resPolyHi p R c, ?_, ?_⟩
  · intro hcon
    refine hδ ?_
    have h2 : (p : ℤ) ∣ (δ + (p : ℤ) * (Polynomial.hasseDeriv 3 R).eval (c : ℤ))
        - (p : ℤ) * (Polynomial.hasseDeriv 3 R).eval (c : ℤ) :=
      dvd_sub hcon (dvd_mul_right _ _)
    rwa [add_sub_cancel_right] at h2
  · rw [CubicPhase, shiftPhaseLevel, resPoly_expand]
    simp only [Polynomial.C_mul, Polynomial.C_add, Polynomial.C_pow]
    ring

/-- A linear phase whose `p`-adic level is one vanishes: for `c₀` a `p`-unit,
`Tsum (p^M) (c₀ X + p Φ) = 0`. -/
lemma Tsum_linear_vanishes_aux (p M : ℕ) [Fact p.Prime] (hM : 1 ≤ M) (c₀ : ℤ)
    (hc : ¬ (p : ℤ) ∣ c₀) (Φ : Polynomial ℤ) :
    Commons.NumberTheory.GaussSum.Tsum (p ^ M)
      (Polynomial.C c₀ * Polynomial.X + Polynomial.C (p : ℤ) * Φ) = 0 := by
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).pos.ne'
  set H : Polynomial ℤ := Polynomial.C c₀ * Polynomial.X + Polynomial.C (p : ℤ) * Φ with hH
  have hev : ∀ z : ℤ, Polynomial.eval z H = c₀ * z + (p : ℤ) * Polynomial.eval z Φ := by
    intro z
    rw [hH]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [Commons.NumberTheory.GaussSum.Tsum]
  rw [show Finset.range (p ^ M) = Finset.range (p ^ (M - 1) * p) by
    congr 1
    conv_lhs => rw [show M = M - 1 + 1 by omega]
    rw [pow_succ]]
  rw [Commons.Algebra.BigOperators.sum_range_mul_eq
    (fun j => Commons.NumberTheory.GaussSum.E (p ^ M) (Polynomial.eval (j : ℤ) H))
    (p ^ (M - 1)) p]
  apply Finset.sum_eq_zero
  intro a ha
  have hfact : ∀ b : ℕ, Commons.NumberTheory.GaussSum.E (p ^ M)
        (Polynomial.eval ((a + p ^ (M - 1) * b : ℕ) : ℤ) H)
      = Commons.NumberTheory.GaussSum.E (p ^ M) (Polynomial.eval (a : ℤ) H)
        * Commons.NumberTheory.GaussSum.E p (c₀ * (b : ℤ)) := by
    intro b
    have hZ : (((a + p ^ (M - 1) * b : ℕ)) : ℤ) = (a : ℤ) + (p : ℤ) ^ (M - 1) * (b : ℤ) := by
      push_cast; ring
    have hdvd : (p : ℤ) ^ M ∣ Polynomial.eval ((a : ℤ) + (p : ℤ) ^ (M - 1) * (b : ℤ)) H
        - Polynomial.eval (a : ℤ) H - c₀ * (b : ℤ) * (p : ℤ) ^ (M - 1) := by
      have hsplit : Polynomial.eval ((a : ℤ) + (p : ℤ) ^ (M - 1) * (b : ℤ)) H
          - Polynomial.eval (a : ℤ) H - c₀ * (b : ℤ) * (p : ℤ) ^ (M - 1)
          = (p : ℤ) * (Polynomial.eval ((a : ℤ) + (p : ℤ) ^ (M - 1) * (b : ℤ)) Φ
              - Polynomial.eval (a : ℤ) Φ) := by
        rw [hev, hev]; ring
      rw [hsplit]
      have hd : (p : ℤ) ^ (M - 1) ∣ Polynomial.eval ((a : ℤ) + (p : ℤ) ^ (M - 1) * (b : ℤ)) Φ
          - Polynomial.eval (a : ℤ) Φ := by
        have h := Polynomial.sub_dvd_eval_sub ((a : ℤ) + (p : ℤ) ^ (M - 1) * (b : ℤ)) (a : ℤ) Φ
        rw [add_sub_cancel_left] at h
        exact dvd_trans (dvd_mul_right ((p : ℤ) ^ (M - 1)) (b : ℤ)) h
      obtain ⟨t, ht⟩ := hd
      refine ⟨t, ?_⟩
      rw [ht]
      have hpow : (p : ℤ) ^ M = (p : ℤ) * (p : ℤ) ^ (M - 1) := by
        conv_lhs => rw [show M = M - 1 + 1 by omega]
        rw [pow_succ']
      rw [hpow]; ring
    rw [hZ]
    rw [Commons.NumberTheory.GaussSum.E_eq_of_dvd_sub (p ^ M) _
      (Polynomial.eval (a : ℤ) H + c₀ * (b : ℤ) * (p : ℤ) ^ (M - 1)) (by
        rw [show Polynomial.eval ((a : ℤ) + (p : ℤ) ^ (M - 1) * (b : ℤ)) H
              - (Polynomial.eval (a : ℤ) H + c₀ * (b : ℤ) * (p : ℤ) ^ (M - 1))
            = Polynomial.eval ((a : ℤ) + (p : ℤ) ^ (M - 1) * (b : ℤ)) H
              - Polynomial.eval (a : ℤ) H - c₀ * (b : ℤ) * (p : ℤ) ^ (M - 1) by ring]
        exact hdvd)]
    rw [Commons.NumberTheory.GaussSum.E_add,
      show c₀ * (b : ℤ) * (p : ℤ) ^ (M - 1) = (c₀ * (b : ℤ)) * (p : ℤ) ^ (M - 1) by ring,
      Commons.NumberTheory.GaussSum.E_pow_mul p M hM]
  rw [Finset.sum_congr rfl (fun b _ => hfact b)]
  have horth : ∑ b ∈ Finset.range p, Commons.NumberTheory.GaussSum.E p (c₀ * (b : ℤ)) = 0 := by
    rw [show (∑ b ∈ Finset.range p, Commons.NumberTheory.GaussSum.E p (c₀ * (b : ℤ)))
        = ∑ b ∈ Finset.range p, Commons.NumberTheory.GaussSum.E p ((b : ℤ) * c₀) by
      apply Finset.sum_congr rfl; intro b _; rw [mul_comm]]
    rw [Commons.NumberTheory.GaussSum.orth_sum, if_neg hc]
  rw [← Finset.mul_sum, horth, mul_zero]

end Work.LinnikBurgess
