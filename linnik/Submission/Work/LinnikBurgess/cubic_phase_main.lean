import Mathlib
import Submission.Work.LinnikBurgess.ddDefs
import Submission.Work.LinnikBurgess.cubic_phase_struct
import Submission.Work.LinnikBurgess.cubicPhase_rootSum
import Submission.Work.LinnikBurgess.root_card_le_two
import Submission.Work.LinnikBurgess.root_double_unique
import Submission.Work.LinnikBurgess.Tsum_C_mul
import Submission.Work.LinnikBurgess.Tsum_prime_cubic_le

namespace Work.LinnikBurgess

open Polynomial
open scoped BigOperators

/-- `Tsum 1 H = 1`. -/
lemma Tsum_one (H : Polynomial ℤ) : Commons.NumberTheory.GaussSum.Tsum 1 H = 1 := by
  rw [Commons.NumberTheory.GaussSum.Tsum, Finset.sum_range_one,
    Commons.NumberTheory.GaussSum.E_one]

/-- `Tsum (p^0) H = 1`. -/
lemma Tsum_pow_zero (p : ℕ) [NeZero p] (H : Polynomial ℤ) :
    Commons.NumberTheory.GaussSum.Tsum (p ^ 0) H = 1 := by
  show Commons.NumberTheory.GaussSum.Tsum 1 H = 1
  rw [Commons.NumberTheory.GaussSum.Tsum, Finset.sum_range_one,
    Commons.NumberTheory.GaussSum.E_one]

/-- For an odd prime `p` and a `p`-unit `δ`, the integer `3δ` is a `p`-unit as well. -/
lemma not_dvd_three_mul (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (δ : ℤ)
    (hδ : ¬ (p : ℤ) ∣ δ) : ¬ (p : ℤ) ∣ 3 * δ := by
  intro h
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_mul] at h
  rcases mul_eq_zero.mp h with h3 | hd
  · have h3' : (3 : ZMod p) = 0 := by exact_mod_cast h3
    have hdiv : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h3'
    have : p ≤ 3 := Nat.le_of_dvd (by norm_num) hdiv
    omega
  · exact hδ ((ZMod.intCast_zmod_eq_zero_iff_dvd δ p).mp hd)

/-- Norm bound for the root sum of the stationary-phase decomposition. -/
lemma rootSum_le_card_mul (p K : ℕ) [Fact p.Prime] (β γ δ : ℤ) (R : Polynomial ℤ) (B : ℝ)
    (hPerRoot : ∀ r ∈ (Finset.range p).filter (fun r => (p : ℤ) ∣ linCoeff β γ δ r),
      ‖Commons.NumberTheory.GaussSum.Tsum (p ^ (K - 2)) (shiftPhase p β γ δ R r)‖ ≤ B) :
    ‖∑ r ∈ (Finset.range p).filter (fun r => (p : ℤ) ∣ linCoeff β γ δ r),
        Commons.NumberTheory.GaussSum.E (p ^ K)
            (Polynomial.eval (r : ℤ) (CubicPhase p β γ δ R))
          * Commons.NumberTheory.GaussSum.Tsum (p ^ (K - 2)) (shiftPhase p β γ δ R r)‖
      ≤ (((Finset.range p).filter (fun r => (p : ℤ) ∣ linCoeff β γ δ r)).card : ℝ) * B := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ r ∈ (Finset.range p).filter (fun r => (p : ℤ) ∣ linCoeff β γ δ r),
        ‖Commons.NumberTheory.GaussSum.E (p ^ K)
            (Polynomial.eval (r : ℤ) (CubicPhase p β γ δ R))
          * Commons.NumberTheory.GaussSum.Tsum (p ^ (K - 2)) (shiftPhase p β γ δ R r)‖
      ≤ ∑ _r ∈ (Finset.range p).filter (fun r => (p : ℤ) ∣ linCoeff β γ δ r), B := by
        apply Finset.sum_le_sum
        intro r hr
        rw [norm_mul, Commons.NumberTheory.GaussSum.E_norm, one_mul]
        exact hPerRoot r hr
    _ = (((Finset.range p).filter (fun r => (p : ℤ) ∣ linCoeff β γ δ r)).card : ℝ) * B := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- Arithmetic for the case of a simple stationary point: two roots give `4 p^(K/2) ≤ 8 p^(2K/3)`. -/
lemma arith_simple (p : ℝ) (hp1 : 1 ≤ p) (K : ℕ) (hK : 2 ≤ K) (c : ℝ) (hc : c ≤ 2) :
    p * (c * (2 * p ^ (((K - 2 : ℕ) : ℝ) / 2))) ≤ 8 * p ^ ((2 * (K : ℝ)) / 3) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  have hcast : (((K - 2 : ℕ)) : ℝ) = (K : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hhalf : (1 : ℝ) + (((K - 2 : ℕ)) : ℝ) / 2 = (K : ℝ) / 2 := by
    rw [hcast]; ring
  have hexp : (K : ℝ) / 2 ≤ (2 * (K : ℝ)) / 3 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) K]
  have hy0 : (0 : ℝ) ≤ p ^ ((((K - 2 : ℕ)) : ℝ) / 2) := Real.rpow_nonneg hp0.le _
  calc p * (c * (2 * p ^ ((((K - 2 : ℕ)) : ℝ) / 2)))
      ≤ p * (2 * (2 * p ^ ((((K - 2 : ℕ)) : ℝ) / 2))) := by
        apply mul_le_mul_of_nonneg_left _ hp0.le
        exact mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 4 * (p ^ (1 : ℝ) * p ^ ((((K - 2 : ℕ)) : ℝ) / 2)) := by
        rw [Real.rpow_one]; ring
    _ = 4 * p ^ ((1 : ℝ) + ((((K - 2 : ℕ)) : ℝ) / 2)) := by rw [Real.rpow_add hp0]
    _ = 4 * p ^ ((K : ℝ) / 2) := by rw [hhalf]
    _ ≤ 8 * p ^ ((2 * (K : ℝ)) / 3) := by
        have h1 : (4 : ℝ) * p ^ ((K : ℝ) / 2) ≤ 8 * p ^ ((K : ℝ) / 2) := by
          nlinarith [Real.rpow_nonneg hp0.le ((K : ℝ) / 2)]
        have h2 : (8 : ℝ) * p ^ ((K : ℝ) / 2) ≤ 8 * p ^ ((2 * (K : ℝ)) / 3) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hp1 hexp) (by norm_num)
        linarith

/-- Arithmetic for the doubly degenerate case: `p · p · 8 p^(2(K-3)/3) = 8 p^(2K/3)`. -/
lemma arith_double (p : ℝ) (hp1 : 1 ≤ p) (K : ℕ) (hK : 3 ≤ K) (c : ℝ) (hc : c ≤ 1) :
    p * (c * (p * (8 * p ^ ((2 * (((K - 3 : ℕ)) : ℝ)) / 3))))
      ≤ 8 * p ^ ((2 * (K : ℝ)) / 3) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  have hcast : (((K - 3 : ℕ)) : ℝ) = (K : ℝ) - 3 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hexp : (1 : ℝ) + (1 + 2 * (((K - 3 : ℕ)) : ℝ) / 3) = (2 * (K : ℝ)) / 3 := by
    rw [hcast]; ring
  have hy0 : (0 : ℝ) ≤ 8 * p ^ ((2 * (((K - 3 : ℕ)) : ℝ)) / 3) := by positivity
  calc p * (c * (p * (8 * p ^ ((2 * (((K - 3 : ℕ)) : ℝ)) / 3))))
      ≤ p * (1 * (p * (8 * p ^ ((2 * (((K - 3 : ℕ)) : ℝ)) / 3)))) := by
        apply mul_le_mul_of_nonneg_left _ hp0.le
        exact mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 8 * (p ^ (1 : ℝ) * (p ^ (1 : ℝ) * p ^ ((2 * (((K - 3 : ℕ)) : ℝ)) / 3))) := by
        rw [Real.rpow_one]; ring
    _ = 8 * p ^ ((1 : ℝ) + (1 + 2 * (((K - 3 : ℕ)) : ℝ) / 3)) := by
        rw [Real.rpow_add hp0, Real.rpow_add hp0]
    _ = 8 * p ^ ((2 * (K : ℝ)) / 3) := by rw [hexp]

/-- Arithmetic for `K = 2`: `p · card ≤ 8 p^(4/3)`. -/
lemma arith_two (p : ℝ) (hp1 : 1 ≤ p) (c : ℝ) (hc : c ≤ 2) :
    p * (c * 1) ≤ 8 * p ^ ((4 : ℝ) / 3) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  have h1 : p ^ ((4 : ℝ) / 3) = p ^ (1 : ℝ) * p ^ ((1 : ℝ) / 3) := by
    rw [← Real.rpow_add hp0]; norm_num
  have h2 : (1 : ℝ) ≤ p ^ ((1 : ℝ) / 3) := Real.one_le_rpow hp1 (by norm_num)
  have h3 : p ≤ p ^ ((4 : ℝ) / 3) := by
    rw [h1, Real.rpow_one]
    nlinarith [Real.rpow_nonneg hp0.le ((1 : ℝ) / 3)]
  nlinarith

/-- **Cubic `p`-adic Weyl bound for explicit cubic phases**, by strong induction on `K`. -/
theorem cubic_phase_general (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∀ K : ℕ, ∀ (β γ δ : ℤ) (R : Polynomial ℤ), ¬ (p : ℤ) ∣ δ →
      ‖Commons.NumberTheory.GaussSum.Tsum (p ^ K) (CubicPhase p β γ δ R)‖
        ≤ 8 * (p : ℝ) ^ ((2 * (K : ℝ)) / 3) := by
  intro K
  induction K using Nat.strong_induction_on with
  | _ K ih =>
    intro β γ δ R hδ
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_le
    have hpne2 : p ≠ 2 := by omega
    have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).pos.ne'
    have h3δ : ¬ (p : ℤ) ∣ 3 * δ := not_dvd_three_mul p hp5 δ hδ
    rcases Nat.lt_or_ge K 3 with hlt | hge
    · interval_cases K
      · rw [Tsum_pow_zero p (CubicPhase p β γ δ R),
          show (2 * ((0 : ℕ) : ℝ)) / 3 = 0 by norm_num, Real.rpow_zero, norm_one]
        norm_num
      · have h := Tsum_prime_cubic_le p hp5 β γ δ R hδ
        simpa using h
      · rw [cubicPhase_rootSum p 2 (by norm_num) β γ δ R, norm_mul, Complex.norm_natCast]
        have hcard : ((((Finset.range p).filter
            (fun r => (p : ℤ) ∣ linCoeff β γ δ r)).card : ℕ) : ℝ) ≤ 2 := by
          exact_mod_cast root_card_le_two p β γ δ h3δ
        have hper : ∀ r ∈ (Finset.range p).filter (fun r => (p : ℤ) ∣ linCoeff β γ δ r),
            ‖Commons.NumberTheory.GaussSum.Tsum (p ^ (2 - 2)) (shiftPhase p β γ δ R r)‖ ≤ 1 := by
          intro r _
          rw [Tsum_pow_zero p (shiftPhase p β γ δ R r), norm_one]
        refine (mul_le_mul_of_nonneg_left (rootSum_le_card_mul p 2 β γ δ R 1 hper) hp0.le).trans ?_
        rw [show (2 * ((2 : ℕ) : ℝ)) / 3 = (4 : ℝ) / 3 by norm_num]
        exact arith_two (p : ℝ) hp1 _ hcard
    · rw [cubicPhase_rootSum p K (by omega) β γ δ R, norm_mul, Complex.norm_natCast]
      by_cases hcase : ∃ r ∈ (Finset.range p).filter (fun r => (p : ℤ) ∣ linCoeff β γ δ r),
          ¬ (p : ℤ) ∣ quadCoeff γ δ r
      · obtain ⟨r₀, hr₀S, hr₀⟩ := hcase
        have hAllSimple : ∀ r ∈ (Finset.range p).filter (fun r => (p : ℤ) ∣ linCoeff β γ δ r),
            ¬ (p : ℤ) ∣ quadCoeff γ δ r := by
          intro r hr hcon
          obtain ⟨hrr, hroot⟩ := Finset.mem_filter.mp hr
          have huniq := root_double_unique p β γ δ h3δ r (Finset.mem_range.mp hrr) hroot hcon
          obtain ⟨hr₀r, hr₀root⟩ := Finset.mem_filter.mp hr₀S
          have hEq : r₀ = r := huniq r₀ hr₀r hr₀root
          rw [hEq] at hr₀
          exact hr₀ hcon
        have hcard : ((((Finset.range p).filter
            (fun r => (p : ℤ) ∣ linCoeff β γ δ r)).card : ℕ) : ℝ) ≤ 2 := by
          exact_mod_cast root_card_le_two p β γ δ h3δ
        have hper : ∀ r ∈ (Finset.range p).filter (fun r => (p : ℤ) ∣ linCoeff β γ δ r),
            ‖Commons.NumberTheory.GaussSum.Tsum (p ^ (K - 2)) (shiftPhase p β γ δ R r)‖
              ≤ 2 * (p : ℝ) ^ ((((K - 2 : ℕ)) : ℝ) / 2) := by
          intro r hr
          exact Commons.NumberTheory.GaussSum.Tsum_bound p hpne2 (K - 2) _
            (shiftPhase_isQuad p β γ δ R r (hAllSimple r hr))
        refine (mul_le_mul_of_nonneg_left
          (rootSum_le_card_mul p K β γ δ R (2 * (p : ℝ) ^ ((((K - 2 : ℕ)) : ℝ) / 2)) hper)
          hp0.le).trans ?_
        exact arith_simple (p : ℝ) hp1 K (by omega) _ hcard
      · push_neg at hcase
        have hcardN : ((Finset.range p).filter
            (fun r => (p : ℤ) ∣ linCoeff β γ δ r)).card ≤ 1 := by
          rw [Finset.card_le_one]
          intro a ha b hb
          exact (root_double_unique p β γ δ h3δ a (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
            (Finset.mem_filter.mp ha).2 (hcase a ha) b (Finset.mem_filter.mp hb).1
            (Finset.mem_filter.mp hb).2).symm
        have hcard : ((((Finset.range p).filter
            (fun r => (p : ℤ) ∣ linCoeff β γ δ r)).card : ℕ) : ℝ) ≤ 1 := by
          exact_mod_cast hcardN
        have hper : ∀ r ∈ (Finset.range p).filter (fun r => (p : ℤ) ∣ linCoeff β γ δ r),
            ‖Commons.NumberTheory.GaussSum.Tsum (p ^ (K - 2)) (shiftPhase p β γ δ R r)‖
              ≤ (p : ℝ) * (8 * (p : ℝ) ^ ((2 * (((K - 3 : ℕ)) : ℝ)) / 3)) := by
          intro r hr
          have hdbl : (p : ℤ) ∣ quadCoeff γ δ r := hcase r hr
          by_cases hdiv : (p : ℤ) ∣ linCoeff β γ δ r / (p : ℤ)
              + (Polynomial.derivative R).eval (r : ℤ)
          · rw [shiftPhase_factor p hpne β γ δ R r hdbl hdiv]
            have hCM := Tsum_C_mul p (K - 2) (by omega) (shiftPhaseLevel p β γ δ R r)
            rw [show (K - 2) - 1 = K - 3 by omega] at hCM
            rw [hCM, norm_mul, Complex.norm_natCast]
            obtain ⟨β', γ', δ', R', hδ', hEq⟩ := shiftPhaseLevel_isCubicShape p β γ δ R r hδ
            rw [hEq]
            exact mul_le_mul_of_nonneg_left (ih (K - 3) (by omega) β' γ' δ' R' hδ') hp0.le
          · rw [shiftPhase_linear_form p hpne β γ δ R r hdbl,
              Tsum_linear_vanishes_aux p (K - 2) (by omega) _ hdiv _]
            simp
            positivity
        refine (mul_le_mul_of_nonneg_left
          (rootSum_le_card_mul p K β γ δ R
            ((p : ℝ) * (8 * (p : ℝ) ^ ((2 * (((K - 3 : ℕ)) : ℝ)) / 3))) hper)
          hp0.le).trans ?_
        exact arith_double (p : ℝ) hp1 K (by omega) _ hcard

end Work.LinnikBurgess
