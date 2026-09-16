import Mathlib
import Submission.Commons.NumberTheory.BombieriVinogradov.mean_value_large_range
import Submission.Commons.NumberTheory.BombieriVinogradov.mean_value_small_modulus_bound
import Submission.Commons.NumberTheory.BombieriVinogradov.mean_value_vaughan_range
open scoped BigOperators

namespace Commons.NumberTheory.BombieriVinogradov

open Finset

private theorem bmvt_four_term_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x Q : ℕ, 2 ≤ x → 1 ≤ Q →
      (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
                (Classical.decPred _) Finset.univ),
          sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖) '' Set.Icc 1 x))
      ≤ C * ((x : ℝ) + (x : ℝ) ^ (1 / 2 : ℝ) * (Q : ℝ) ^ 2
              + (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ)
              + (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ))
          * (Real.log ((x : ℝ) * (Q : ℝ) + 2)) ^ (7 / 2 : ℝ) := by
  obtain ⟨C1, hC1pos, hC1⟩ := mean_value_vaughan_range
  obtain ⟨C2, hC2pos, hC2⟩ := mean_value_large_range
  obtain ⟨C3, hC3pos, hC3⟩ := mean_value_small_modulus_bound
  refine ⟨max C1 (max C2 C3) + 1, by positivity, ?_⟩
  intro x Q hx hQ
  have hlog1 : 1 ≤ Real.log ((x : ℝ) * (Q : ℝ) + 2) := by
    have h4 : (4 : ℝ) ≤ (x : ℝ) * (Q : ℝ) + 2 := by
      have h2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
      have h1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (x : ℝ) - 2) (by linarith : (0 : ℝ) ≤ (Q : ℝ) - 1)]
    have h14 : (1 : ℝ) ≤ Real.log 4 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 4)]
      have := Real.exp_one_lt_d9; linarith
    exact le_trans h14 (Real.log_le_log (by norm_num) h4)
  have hlogpow1 : 1 ≤ (Real.log ((x : ℝ) * (Q : ℝ) + 2)) ^ (7 / 2 : ℝ) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (7 / 2 : ℝ) := (Real.one_rpow _).symm
      _ ≤ _ := Real.rpow_le_rpow (by norm_num) hlog1 (by norm_num)
  have hE0 : 0 ≤ (x : ℝ) + (x : ℝ) ^ (1 / 2 : ℝ) * (Q : ℝ) ^ 2
              + (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ)
              + (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ) := by positivity
  have hEx : (x : ℝ) ≤ (x : ℝ) + (x : ℝ) ^ (1 / 2 : ℝ) * (Q : ℝ) ^ 2
              + (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ)
              + (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ) := by
    linarith [mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg x) (1 / 2 : ℝ)) (by positivity : (0 : ℝ) ≤ (Q : ℝ) ^ 2),
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg x) (2 / 3 : ℝ)) (by positivity : (0 : ℝ) ≤ (Q : ℝ) ^ (3 / 2 : ℝ)),
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg x) (5 / 6 : ℝ)) (Nat.cast_nonneg Q)]
  set E : ℝ := (x : ℝ) + (x : ℝ) ^ (1 / 2 : ℝ) * (Q : ℝ) ^ 2
              + (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ)
              + (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ) with hE
  set L7 : ℝ := (Real.log ((x : ℝ) * (Q : ℝ) + 2)) ^ (7 / 2 : ℝ) with hL7
  have hL : (x : ℝ) ≤ E := hEx
  have hE0' : 0 ≤ E := hE0
  have hL7one : 1 ≤ L7 := hlogpow1
  have hL70 : 0 ≤ L7 := le_trans zero_le_one hL7one
  have hsmall : C3 * (x : ℝ) ≤ (max C1 (max C2 C3) + 1) * E * L7 := by
    have h1 : C3 * (x : ℝ) ≤ C3 * E := mul_le_mul_of_nonneg_left hL hC3pos.le
    have h2 : C3 * E ≤ C3 * E * L7 := by
      have h3 : 0 ≤ C3 * E * (L7 - 1) :=
        mul_nonneg (mul_nonneg hC3pos.le hE0') (by linarith)
      nlinarith [h3]
    have h3 : C3 ≤ max C1 (max C2 C3) + 1 := by
      have ha := le_max_right C1 (max C2 C3)
      have hb := le_max_right C2 C3
      linarith
    have h4 : C3 * E * L7 ≤ (max C1 (max C2 C3) + 1) * E * L7 := by
      have h5 : 0 ≤ E * L7 := mul_nonneg hE0' hL70
      nlinarith [mul_le_mul_of_nonneg_right h3 h5]
    linarith [h1, h2, h4]
  have hlarge : C2 * E * L7 ≤ (max C1 (max C2 C3) + 1) * E * L7 := by
    have h3 : C2 ≤ max C1 (max C2 C3) + 1 := by
      have ha := le_max_left C2 C3
      have hb := le_max_right C1 (max C2 C3)
      linarith
    have h5 : 0 ≤ E * L7 := mul_nonneg hE0' hL70
    nlinarith [mul_le_mul_of_nonneg_right h3 h5]
  have hmid : C1 * E * L7 ≤ (max C1 (max C2 C3) + 1) * E * L7 := by
    have h3 : C1 ≤ max C1 (max C2 C3) + 1 := by
      have ha := le_max_left C1 (max C2 C3)
      linarith
    have h5 : 0 ≤ E * L7 := mul_nonneg hE0' hL70
    nlinarith [mul_le_mul_of_nonneg_right h3 h5]
  by_cases hQ2 : Q ≤ 2
  · exact le_trans (hC3 x Q hx hQ2) hsmall
  · have hQ3 : 2 ≤ Q := by omega
    by_cases hxq : x ≤ Q ^ 2
    · exact le_trans (hC2 x Q hx hQ hxq) hlarge
    · have hxq' : Q ^ 2 ≤ x := by omega
      exact le_trans (hC1 x Q hx hQ3 hxq') hmid

open scoped BigOperators

private lemma bmvt_key4 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a^(4:ℕ) * b^(3:ℕ) ≤ a^(5:ℕ) * b^(2:ℕ) + a^(3:ℕ) * b^(4:ℕ) := by
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have h : 0 ≤ a^(3:ℕ) * b^(2:ℕ) := by positivity
  have h2 : 0 ≤ a^2 + b^2 - a*b := by nlinarith [sq_nonneg (a - b), hab]
  nlinarith [mul_nonneg h h2]

private lemma bmvt_rpow_middle_term_le (x Q : ℕ) :
    (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ)
      ≤ (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ) + (x : ℝ) ^ (1 / 2 : ℝ) * (Q : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos x with hx | hx
  · subst hx; simp
  rcases Nat.eq_zero_or_pos Q with hQ | hQ
  · subst hQ; simp
  have hxr : (0:ℝ) < x := by exact_mod_cast hx
  have hQr : (0:ℝ) < Q := by exact_mod_cast hQ
  set a : ℝ := (x:ℝ) ^ (1/6:ℝ) with ha
  set b : ℝ := (Q:ℝ) ^ (1/2:ℝ) with hb
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have e1 : (x:ℝ)^(2/3:ℝ) * (Q:ℝ)^(3/2:ℝ) = a^(4:ℕ) * b^(3:ℕ) := by
    congr 1
    · rw [ha, ← Real.rpow_mul_natCast hxr.le]; norm_num
    · rw [hb, ← Real.rpow_mul_natCast hQr.le]; norm_num
  have e2 : (x:ℝ)^(5/6:ℝ) * (Q:ℝ) = a^(5:ℕ) * b^(2:ℕ) := by
    congr 1
    · rw [ha, ← Real.rpow_mul_natCast hxr.le]; norm_num
    · rw [hb, ← Real.rpow_mul_natCast hQr.le]; norm_num
  have e3 : (x:ℝ)^(1/2:ℝ) * (Q:ℝ)^2 = a^(3:ℕ) * b^(4:ℕ) := by
    congr 1
    · rw [ha, ← Real.rpow_mul_natCast hxr.le]; norm_num
    · rw [hb, ← Real.rpow_mul_natCast hQr.le]; norm_num
  rw [e1, e2, e3]
  exact bmvt_key4 a b ha0 hb0

private lemma bmvt_log_rpow_seven_halves_le (A : ℝ) (hA : 1 ≤ A) : A ^ (7 / 2 : ℝ) ≤ A ^ (5 : ℝ) := by
  apply Real.rpow_le_rpow_of_exponent_le hA
  norm_num

private lemma bmvt_vaughan_rhs_le (x Q : ℕ) (hx : 2 ≤ x) (hQ : 1 ≤ Q) :
    ((x:ℝ) + (x:ℝ)^(1/2:ℝ)*(Q:ℝ)^2 + (x:ℝ)^(2/3:ℝ)*(Q:ℝ)^(3/2:ℝ) + (x:ℝ)^(5/6:ℝ)*(Q:ℝ))
        * (Real.log ((x:ℝ)*(Q:ℝ)+2))^(7/2:ℝ)
      ≤ 2 * ((x:ℝ) + (x:ℝ)^(5/6:ℝ)*(Q:ℝ) + (x:ℝ)^(1/2:ℝ)*(Q:ℝ)^2)
        * (Real.log ((x:ℝ)*(Q:ℝ)+2))^(5:ℕ) := by
  have hxr : (2:ℝ) ≤ x := by exact_mod_cast hx
  have hQr : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  have h4 : (4:ℝ) ≤ (x:ℝ)*(Q:ℝ)+2 := by nlinarith
  have hlog1 : 1 ≤ Real.log ((x:ℝ)*(Q:ℝ)+2) := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 4) h4
    have h1 : (1:ℝ) ≤ Real.log 4 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 4)]
      have := Real.exp_one_lt_d9; linarith
    linarith
  have hpow : (Real.log ((x:ℝ)*(Q:ℝ)+2))^(7/2:ℝ)
      ≤ (Real.log ((x:ℝ)*(Q:ℝ)+2))^(5:ℕ) := by
    rw [← Real.rpow_natCast]
    exact bmvt_log_rpow_seven_halves_le _ hlog1
  have hmid := bmvt_rpow_middle_term_le x Q
  have hpoly : (x:ℝ) + (x:ℝ)^(1/2:ℝ)*(Q:ℝ)^2 + (x:ℝ)^(2/3:ℝ)*(Q:ℝ)^(3/2:ℝ) + (x:ℝ)^(5/6:ℝ)*(Q:ℝ)
      ≤ 2 * ((x:ℝ) + (x:ℝ)^(5/6:ℝ)*(Q:ℝ) + (x:ℝ)^(1/2:ℝ)*(Q:ℝ)^2) := by linarith
  calc ((x:ℝ) + (x:ℝ)^(1/2:ℝ)*(Q:ℝ)^2 + (x:ℝ)^(2/3:ℝ)*(Q:ℝ)^(3/2:ℝ) + (x:ℝ)^(5/6:ℝ)*(Q:ℝ))
        * (Real.log ((x:ℝ)*(Q:ℝ)+2))^(7/2:ℝ)
      ≤ 2 * ((x:ℝ) + (x:ℝ)^(5/6:ℝ)*(Q:ℝ) + (x:ℝ)^(1/2:ℝ)*(Q:ℝ)^2)
        * (Real.log ((x:ℝ)*(Q:ℝ)+2))^(7/2:ℝ) := by
        apply mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ ≤ 2 * ((x:ℝ) + (x:ℝ)^(5/6:ℝ)*(Q:ℝ) + (x:ℝ)^(1/2:ℝ)*(Q:ℝ)^2)
        * (Real.log ((x:ℝ)*(Q:ℝ)+2))^(5:ℕ) := by
        apply mul_le_mul_of_nonneg_left hpow (by positivity)

/-- The Basic Mean Value Theorem of the Bombieri–Vinogradov theorem (Vaughan,
"The Bombieri-Vinogradov theorem", §1): the totient-weighted second-moment
average over primitive characters of the Dirichlet-polynomial sums
`Σ_{n ≤ y} Λ(n) χ(n)`, taken uniformly in `y ≤ x`, is

`T(x,Q) = Σ_{q ≤ Q} (q/φ(q)) Σ*_{χ mod q} sup_{y ≤ x} ‖ψ(y,χ)‖
        ≪ (x + x^{5/6} Q + x^{1/2} Q²) (log(xQ))⁵`.

Here `Σ*` runs over the primitive characters modulo `q`. -/
theorem basic_mean_value_theorem :
    ∃ C : ℝ, 0 < C ∧ ∀ x Q : ℕ, 2 ≤ x → 1 ≤ Q →
      (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
                (Classical.decPred _) Finset.univ),
          sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖) '' Set.Icc 1 x))
      ≤ C * ((x : ℝ) + (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ) + (x : ℝ) ^ (1 / 2 : ℝ) * (Q : ℝ) ^ 2)
          * (Real.log ((x : ℝ) * (Q : ℝ) + 2)) ^ 5 := by
  obtain ⟨C0, hC0, hb⟩ := bmvt_four_term_bound
  refine ⟨2 * C0, by positivity, fun x Q hx hQ => ?_⟩
  have h := hb x Q hx hQ
  have hred := bmvt_vaughan_rhs_le x Q hx hQ
  calc (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
                (Classical.decPred _) Finset.univ),
          sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖) '' Set.Icc 1 x))
      ≤ C0 * ((x : ℝ) + (x : ℝ) ^ (1 / 2 : ℝ) * (Q : ℝ) ^ 2
              + (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ)
              + (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ))
          * (Real.log ((x : ℝ) * (Q : ℝ) + 2)) ^ (7 / 2 : ℝ) := h
    _ = C0 * (((x : ℝ) + (x : ℝ) ^ (1 / 2 : ℝ) * (Q : ℝ) ^ 2
              + (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ)
              + (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ))
          * (Real.log ((x : ℝ) * (Q : ℝ) + 2)) ^ (7 / 2 : ℝ)) := by ring
    _ ≤ C0 * (2 * ((x : ℝ) + (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ) + (x : ℝ) ^ (1 / 2 : ℝ) * (Q : ℝ) ^ 2)
          * (Real.log ((x : ℝ) * (Q : ℝ) + 2)) ^ (5:ℕ)) :=
        mul_le_mul_of_nonneg_left hred hC0.le
    _ = (2 * C0) * ((x : ℝ) + (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ) + (x : ℝ) ^ (1 / 2 : ℝ) * (Q : ℝ) ^ 2)
          * (Real.log ((x : ℝ) * (Q : ℝ) + 2)) ^ 5 := by ring


end Commons.NumberTheory.BombieriVinogradov
