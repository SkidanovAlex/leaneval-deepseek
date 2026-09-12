import Mathlib
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.int_poly_natDegree_map_eq
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.int_poly_supNorm_one_le
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.int_poly_factor_supNorm_le
import Submission.Commons.Analysis.Polynomial.supNorm_mul_le
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.isCoprime_lift_pair_real
import Submission.Commons.Analysis.Polynomial.supNorm_X_sub_C_pow_le
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.lift_shift_pair_independent_real

open Polynomial
open scoped BigOperators
open Commons.NumberTheory.DiophantineApproximation.BoundedDegree

namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree

noncomputable section

private lemma natDegree_map_int_real (P : Polynomial ℤ) :
    (P.map (Int.castRingHom ℝ)).natDegree = P.natDegree :=
  int_poly_natDegree_map_eq P

private lemma map_shift_pow_mul (P : Polynomial ℤ) (m : ℕ) (lam : ℤ) :
    (((Polynomial.X - Polynomial.C (lam : ℤ)) ^ m * P).map (Int.castRingHom ℝ)) =
      (Polynomial.X - Polynomial.C (lam : ℝ)) ^ m * (P.map (Int.castRingHom ℝ)) := by
  rw [Polynomial.map_mul, Polynomial.map_pow]
  congr 1
  simp

private lemma eval_map_shift_pow_mul (xi : ℝ) (P : Polynomial ℤ) (m : ℕ) (lam : ℤ) :
    Polynomial.eval xi
        ((((Polynomial.X - Polynomial.C (lam : ℤ)) ^ m * P).map (Int.castRingHom ℝ))) =
      (xi - (lam : ℝ)) ^ m * Polynomial.eval xi (P.map (Int.castRingHom ℝ)) := by
  rw [map_shift_pow_mul]
  rw [Polynomial.eval_mul, Polynomial.eval_pow]
  simp

private lemma natDegree_shift_pow_mul_eq (P : Polynomial ℤ) (hP : P ≠ 0) (m : ℕ) (lam : ℤ) :
    (((Polynomial.X - Polynomial.C (lam : ℤ)) ^ m * P).natDegree) = m + P.natDegree := by
  rw [Polynomial.natDegree_mul (by
    exact pow_ne_zero m (by simpa using Polynomial.X_sub_C_ne_zero (lam : ℤ))) hP]
  rw [Polynomial.natDegree_pow]
  rw [Polynomial.natDegree_X_sub_C, mul_one]

private lemma map_eq_zero_iff (P : Polynomial ℤ) :
    P.map (Int.castRingHom ℝ) = 0 ↔ P = 0 := by
  constructor
  · intro h
    exact Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective (by simpa using h)
  · intro h
    simp [h]

private lemma natDegree_shift_pow (a : ℕ) (lam : ℤ) :
    (((Polynomial.X - Polynomial.C (lam : ℝ)) ^ a : Polynomial ℝ).natDegree) = a := by
  rw [Polynomial.natDegree_pow]
  rw [Polynomial.natDegree_X_sub_C, mul_one]

/-- Coefficient sup-norm of `(X - C lam)^a` is at most `2^a (1+L)^a` when `|lam| ≤ L`. -/
private lemma supNorm_shift_pow_le (a : ℕ) (lam : ℤ) (L : ℕ) (hb : |(lam : ℝ)| ≤ (L : ℝ)) :
    (((Polynomial.X - Polynomial.C (lam : ℝ)) ^ a : Polynomial ℝ).supNorm) ≤
      (2 : ℝ) ^ a * (1 + (L : ℝ)) ^ a := by
  have h1 := Commons.Analysis.Polynomial.supNorm_X_sub_C_pow_le a (lam : ℝ)
  have hb' : (1 + |(lam : ℝ)|) ≤ (1 + (L : ℝ)) := by linarith
  have hm : (1 + |(lam : ℝ)|) ^ a ≤ (1 + (L : ℝ)) ^ a := by
    exact pow_le_pow_left₀ (by positivity) hb' a
  calc
    (((Polynomial.X - Polynomial.C (lam : ℝ)) ^ a : Polynomial ℝ).supNorm) ≤
        (2 : ℝ) ^ a * (1 + |(lam : ℝ)|) ^ a := h1
    _ ≤ (2 : ℝ) ^ a * (1 + (L : ℝ)) ^ a := by
      exact mul_le_mul_of_nonneg_left hm (by positivity)

/-- supNorm of the multiplier `(X - C lam)^a` with `a ≤ n`, `|lam| ≤ L`. -/
private lemma shift_pow_supNorm_le (a n : ℕ) (lam : ℤ) (L : ℕ) (ha : a ≤ n)
    (hb : |(lam : ℝ)| ≤ (L : ℝ)) :
    (((Polynomial.X - Polynomial.C (lam : ℝ)) ^ a : Polynomial ℝ).supNorm) ≤
      (2 : ℝ) ^ n * (1 + (L : ℝ)) ^ n := by
  have h1 := supNorm_shift_pow_le a lam L hb
  have h2a : (2 : ℝ) ^ a ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) ha
  have h2b : (1 + (L : ℝ)) ^ a ≤ (1 + (L : ℝ)) ^ n := by
    have hb1 : (1 : ℝ) ≤ 1 + (L : ℝ) := by
      have hL0 : (0 : ℝ) ≤ (L : ℝ) := by positivity
      linarith
    exact pow_le_pow_right₀ hb1 ha
  calc
    (((Polynomial.X - Polynomial.C (lam : ℝ)) ^ a : Polynomial ℝ).supNorm) ≤
        (2 : ℝ) ^ a * (1 + (L : ℝ)) ^ a := h1
    _ ≤ (2 : ℝ) ^ n * (1 + (L : ℝ)) ^ a := by
      have hp : (0 : ℝ) ≤ (1 + (L : ℝ)) ^ a := by positivity
      exact mul_le_mul_of_nonneg_right h2a hp
    _ ≤ (2 : ℝ) ^ n * (1 + (L : ℝ)) ^ n := by
      have hp : (0 : ℝ) ≤ (2 : ℝ) ^ n := by positivity
      exact mul_le_mul_of_nonneg_left h2b hp

/-- Upper sup-norm bound for the shifted lift: `‖Q_i‖ ≤ U ‖P_i‖`. -/
private lemma shift_mul_supNorm_le (P0 : Polynomial ℤ) (a n : ℕ) (lam : ℤ) (L : ℕ)
    (ha : a ≤ n) (hb : |(lam : ℝ)| ≤ (L : ℝ)) :
    (((((Polynomial.X - Polynomial.C (lam : ℤ)) ^ a) * P0).map (Int.castRingHom ℝ)).supNorm) ≤
      ((n : ℝ) + 1) * (2 : ℝ) ^ n * (1 + (L : ℝ)) ^ n *
        ((P0.map (Int.castRingHom ℝ)).supNorm) := by
  rw [map_shift_pow_mul]
  let S : Polynomial ℝ := (Polynomial.X - Polynomial.C (lam : ℝ)) ^ a
  let T : Polynomial ℝ := P0.map (Int.castRingHom ℝ)
  have hnd : S.natDegree = a := by
    dsimp [S]
    exact natDegree_shift_pow a lam
  have hs : S.supNorm ≤ (2 : ℝ) ^ n * (1 + (L : ℝ)) ^ n := by
    dsimp [S]
    exact shift_pow_supNorm_le a n lam L ha hb
  have hs0 : (0 : ℝ) ≤ S.supNorm := S.supNorm_nonneg
  have ht0 : (0 : ℝ) ≤ T.supNorm := T.supNorm_nonneg
  have hnn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  calc
    (S * T).supNorm ≤ ((S.natDegree : ℝ) + 1) * S.supNorm * T.supNorm := by
      exact Commons.Analysis.Polynomial.supNorm_mul_le S T
    _ = ((a : ℝ) + 1) * S.supNorm * T.supNorm := by rw [hnd]
    _ ≤ ((n : ℝ) + 1) * S.supNorm * T.supNorm := by
      have had : (a : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ ha
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right had hs0) ht0
    _ ≤ ((n : ℝ) + 1) * ((2 : ℝ) ^ n * (1 + (L : ℝ)) ^ n) * T.supNorm := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hnn) ht0
    _ = ((n : ℝ) + 1) * (2 : ℝ) ^ n * (1 + (L : ℝ)) ^ n * T.supNorm := by
      ring

/-- Lower sup-norm bound for the shifted lift: `‖P_i‖ ≤ D ‖Q_i‖`. -/
private lemma shift_mul_supNorm_ge (P0 : Polynomial ℤ) (a n : ℕ) (lam : ℤ)
    (hP0 : P0 ≠ 0) (hdegP : P0.natDegree ≤ n) (hsum : a + P0.natDegree ≤ n) :
    ((P0.map (Int.castRingHom ℝ)).supNorm) ≤
      (2 : ℝ) ^ n * Real.sqrt ((n : ℝ) + 1) *
        (((((Polynomial.X - Polynomial.C (lam : ℤ)) ^ a) * P0).map (Int.castRingHom ℝ)).supNorm) := by
  let Q0 : Polynomial ℤ := (Polynomial.X - Polynomial.C (lam : ℤ)) ^ a * P0
  have hQ0 : Q0 ≠ 0 := by
    intro hz
    apply hP0
    have hs : (Polynomial.X - Polynomial.C (lam : ℤ)) ^ a ≠ 0 := by
      exact pow_ne_zero a (by simpa using Polynomial.X_sub_C_ne_zero (lam : ℤ))
    simpa [Q0] using (mul_eq_zero.mp hz).resolve_left hs
  have hdegQ : Q0.natDegree ≤ n := by
    have : Q0.natDegree = a + P0.natDegree := by
      dsimp [Q0]
      exact natDegree_shift_pow_mul_eq P0 hP0 a lam
    omega
  have hdiv : P0 ∣ Q0 := ⟨(Polynomial.X - Polynomial.C (lam : ℤ)) ^ a, by rw [mul_comm]⟩
  exact int_poly_factor_supNorm_le n hP0 hQ0 hdegP hdegQ hdiv

/-- Evaluation bound for the shifted lift: `|Q_i(ξ)| ≤ E |P_i(ξ)|`. -/
private lemma shift_mul_eval_le (xi : ℝ) (P0 : Polynomial ℤ) (a n : ℕ) (lam : ℤ) (L : ℕ)
    (ha : a ≤ n) (hb : |(lam : ℝ)| ≤ (L : ℝ)) :
    ‖Polynomial.eval xi
        (((((Polynomial.X - Polynomial.C (lam : ℤ)) ^ a) * P0).map (Int.castRingHom ℝ)))‖ ≤
      (1 + (L : ℝ) + |xi|) ^ n *
        ‖Polynomial.eval xi ((P0.map (Int.castRingHom ℝ)))‖ := by
  rw [eval_map_shift_pow_mul xi P0 a lam]
  rw [norm_mul]
  rw [Real.norm_eq_abs, abs_pow]
  have hb1 : |xi - (lam : ℝ)| ≤ 1 + (L : ℝ) + |xi| := by
    calc
      |xi - (lam : ℝ)| ≤ |xi| + |(lam : ℝ)| := abs_sub xi (lam : ℝ)
      _ ≤ 1 + (L : ℝ) + |xi| := by linarith
  have hpow : |xi - (lam : ℝ)| ^ a ≤ (1 + (L : ℝ) + |xi|) ^ n := by
    have hp1 : |xi - (lam : ℝ)| ^ a ≤ (1 + (L : ℝ) + |xi|) ^ a :=
      pow_le_pow_left₀ (abs_nonneg _) hb1 a
    have hp2 : (1 + (L : ℝ) + |xi|) ^ a ≤ (1 + (L : ℝ) + |xi|) ^ n := by
      have hb1 : (1 : ℝ) ≤ 1 + (L : ℝ) + |xi| := by
        have hL0 : (0 : ℝ) ≤ (L : ℝ) := by positivity
        have hx0 : (0 : ℝ) ≤ |xi| := abs_nonneg xi
        linarith
      exact pow_le_pow_right₀ hb1 ha
    exact le_trans hp1 hp2
  have hnorm : (0 : ℝ) ≤ ‖Polynomial.eval xi ((P0.map (Int.castRingHom ℝ)))‖ := by positivity
  exact mul_le_mul_of_nonneg_right hpow hnorm

theorem p51_lift_pair_uniform2 (n k : ℕ) (hn : 1 ≤ n) (hk2 : 2 ≤ k) (hkn : k ≤ n + 1) (ξ : ℝ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (P : Fin k → Polynomial ℤ),
      (∀ i : Fin k, (P i).natDegree ≤ n) →
      (∀ i : Fin k, P i ≠ 0) →
      LinearIndependent ℝ (fun i : Fin k => (P i).map (Int.castRingHom ℝ)) →
      IsCoprime ((P ⟨0, by omega⟩).map (Int.castRingHom ℝ))
        ((P ⟨1, by omega⟩).map (Int.castRingHom ℝ)) →
      ∃ Q : Fin k → Polynomial ℤ,
        (∀ i : Fin k, (Q i).natDegree ≤ n) ∧
        (Q ⟨0, by omega⟩).natDegree = n ∧
        (Q ⟨1, by omega⟩).natDegree = n ∧
        IsCoprime ((Q ⟨0, by omega⟩).map (Int.castRingHom ℝ))
          ((Q ⟨1, by omega⟩).map (Int.castRingHom ℝ)) ∧
        LinearIndependent ℝ (fun i : Fin k => (Q i).map (Int.castRingHom ℝ)) ∧
        (∀ i : Fin k, 2 ≤ i.val → Q i = P i) ∧
        (∀ i : Fin k,
          ((Q i).map (Int.castRingHom ℝ)).supNorm ≤ C * ((P i).map (Int.castRingHom ℝ)).supNorm) ∧
        (∀ i : Fin k,
          ((P i).map (Int.castRingHom ℝ)).supNorm ≤ C * ((Q i).map (Int.castRingHom ℝ)).supNorm) ∧
        (∀ i : Fin k,
          ‖Polynomial.eval ξ ((Q i).map (Int.castRingHom ℝ))‖ ≤
            C * ‖Polynomial.eval ξ ((P i).map (Int.castRingHom ℝ))‖) := by
  rcases lift_shift_pair_independent_real n k hn hk2 hkn with ⟨L, hL⟩
  let U : ℝ := ((n : ℝ) + 1) * (2 : ℝ) ^ n * (1 + (L : ℝ)) ^ n
  let D : ℝ := (2 : ℝ) ^ n * Real.sqrt ((n : ℝ) + 1)
  let E : ℝ := (1 + (L : ℝ) + |ξ|) ^ n
  let C : ℝ := U + D + E + 1
  have hU0 : 0 ≤ U := by dsimp [U]; positivity
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hCgeU : U ≤ C := by dsimp [C]; nlinarith
  have hCgeD : D ≤ C := by dsimp [C]; nlinarith
  have hCgeE : E ≤ C := by dsimp [C]; nlinarith
  have hC1 : (1 : ℝ) ≤ C := by dsimp [C]; nlinarith
  refine ⟨C, lt_of_lt_of_le zero_lt_one hC1, ?_⟩
  intro P hdeg hne hlin hcop
  let A : Fin k → Polynomial ℝ := fun i => (P i).map (Int.castRingHom ℝ)
  have hdegA : ∀ i : Fin k, (A i).natDegree ≤ n := by
    intro i
    dsimp [A]
    rw [int_poly_natDegree_map_eq]
    exact hdeg i
  have hneA : ∀ i : Fin k, A i ≠ 0 := by
    intro i
    dsimp [A]
    exact (map_eq_zero_iff (P i)).not.mpr (hne i)
  rcases hL A hdegA hneA hlin hcop with ⟨lam0, lam1, hb0, hb1, hlam, he0, he1, hLI⟩
  let P0 : Polynomial ℤ := P ⟨0, by omega⟩
  let P1 : Polynomial ℤ := P ⟨1, by omega⟩
  let a0 : ℕ := n - P0.natDegree
  let a1 : ℕ := n - P1.natDegree
  let Q0 : Polynomial ℤ := (Polynomial.X - Polynomial.C (lam0 : ℤ)) ^ a0 * P0
  let Q1 : Polynomial ℤ := (Polynomial.X - Polynomial.C (lam1 : ℤ)) ^ a1 * P1
  let Q : Fin k → Polynomial ℤ :=
    fun j => if j.val = 0 then Q0 else if j.val = 1 then Q1 else P j
  have hP0n : P0.natDegree ≤ n := by simpa [P0] using hdeg ⟨0, by omega⟩
  have hP1n : P1.natDegree ≤ n := by simpa [P1] using hdeg ⟨1, by omega⟩
  have hP0ne : P0 ≠ 0 := by simpa [P0] using hne ⟨0, by omega⟩
  have hP1ne : P1 ≠ 0 := by simpa [P1] using hne ⟨1, by omega⟩
  have hQ0deg : Q0.natDegree = n := by
    dsimp [Q0]
    rw [natDegree_shift_pow_mul_eq P0 hP0ne a0 (lam0)]
    dsimp [a0]
    omega
  have hQ1deg : Q1.natDegree = n := by
    dsimp [Q1]
    rw [natDegree_shift_pow_mul_eq P1 hP1ne a1 (lam1)]
    dsimp [a1]
    omega
  have ha0n : a0 ≤ n := by dsimp [a0]; omega
  have ha1n : a1 ≤ n := by dsimp [a1]; omega
  have hsum0 : a0 + P0.natDegree ≤ n := by dsimp [a0]; omega
  have hsum1 : a1 + P1.natDegree ≤ n := by dsimp [a1]; omega
  have hB0 : (Q0.map (Int.castRingHom ℝ)) =
      (Polynomial.X - Polynomial.C (lam0 : ℝ)) ^ a0 * A ⟨0, by omega⟩ := by
    dsimp [Q0]
    rw [map_shift_pow_mul]
  have hB1 : (Q1.map (Int.castRingHom ℝ)) =
      (Polynomial.X - Polynomial.C (lam1 : ℝ)) ^ a1 * A ⟨1, by omega⟩ := by
    dsimp [Q1]
    rw [map_shift_pow_mul]
  have ha0A : a0 = n - (A ⟨0, by omega⟩).natDegree := by
    dsimp [a0, A]
    rw [int_poly_natDegree_map_eq]
  have ha1A : a1 = n - (A ⟨1, by omega⟩).natDegree := by
    dsimp [a1, A]
    rw [int_poly_natDegree_map_eq]
  have hfun : (fun i : Fin k => (Q i).map (Int.castRingHom ℝ)) =
      (fun j : Fin k =>
        if j.val = 0 then
          (Polynomial.X - Polynomial.C (lam0 : ℝ)) ^ (n - (A ⟨0, by omega⟩).natDegree) *
            A ⟨0, by omega⟩
        else if j.val = 1 then
          (Polynomial.X - Polynomial.C (lam1 : ℝ)) ^ (n - (A ⟨1, by omega⟩).natDegree) *
            A ⟨1, by omega⟩
        else A j) := by
    funext j
    by_cases hj0 : j.val = 0
    · simp [Q, hj0, hB0, ha0A]
    · by_cases hj1 : j.val = 1
      · simp [Q, hj0, hj1, hB1, ha1A]
      · simp [Q, hj0, hj1, A]
  have hlinQ : LinearIndependent ℝ (fun i : Fin k => (Q i).map (Int.castRingHom ℝ)) := by
    exact hfun ▸ hLI
  have hcopQ : IsCoprime (Q0.map (Int.castRingHom ℝ)) (Q1.map (Int.castRingHom ℝ)) := by
    rw [hB0, hB1]
    exact Commons.NumberTheory.DiophantineApproximation.BoundedDegree.isCoprime_lift_pair_real (A ⟨0, by omega⟩) (A ⟨1, by omega⟩) hcop a0 a1
      (lam0 : ℝ) (lam1 : ℝ) he0 he1 (by exact_mod_cast hlam)
  refine ⟨Q, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi0 : i.val = 0
    · have : Q i = Q0 := by simp [Q, hi0]
      rw [this]
      exact le_of_eq hQ0deg
    · by_cases hi1 : i.val = 1
      · have : Q i = Q1 := by simp [Q, hi0, hi1]
        rw [this]
        exact le_of_eq hQ1deg
      · simpa [Q, hi0, hi1] using hdeg i
  · have : Q ⟨0, by omega⟩ = Q0 := by simp [Q]
    rw [this]
    exact hQ0deg
  · have : Q ⟨1, by omega⟩ = Q1 := by simp [Q]
    rw [this]
    exact hQ1deg
  · rw [show Q ⟨0, by omega⟩ = Q0 by simp [Q], show Q ⟨1, by omega⟩ = Q1 by simp [Q]]
    exact hcopQ
  · exact hlinQ
  · intro i hi
    have h0 : i.val ≠ 0 := by omega
    have h1 : i.val ≠ 1 := by omega
    simpa [Q, h0, h1]
  · intro i
    by_cases hi0 : i.val = 0
    · have hQi : Q i = Q0 := by simp [Q, hi0]
      have hi0e : i = ⟨0, by omega⟩ := Fin.ext hi0
      have hPi : P i = P0 := by rw [hi0e]
      rw [hQi, hPi]
      have hU0' := shift_mul_supNorm_le P0 a0 n lam0 L ha0n hb0
      have hx0 : (0 : ℝ) ≤ ((P0.map (Int.castRingHom ℝ)).supNorm) :=
        (P0.map (Int.castRingHom ℝ)).supNorm_nonneg
      calc
        ((Q0.map (Int.castRingHom ℝ)).supNorm) ≤ U * ((P0.map (Int.castRingHom ℝ)).supNorm) := by
          simpa [Q0, U] using hU0'
        _ ≤ C * ((P0.map (Int.castRingHom ℝ)).supNorm) := by
          exact mul_le_mul_of_nonneg_right hCgeU hx0
    · by_cases hi1 : i.val = 1
      · have hQi : Q i = Q1 := by simp [Q, hi0, hi1]
        have hi1e : i = ⟨1, by omega⟩ := Fin.ext hi1
        have hPi : P i = P1 := by rw [hi1e]
        rw [hQi, hPi]
        have hU1' := shift_mul_supNorm_le P1 a1 n lam1 L ha1n hb1
        have hx0 : (0 : ℝ) ≤ ((P1.map (Int.castRingHom ℝ)).supNorm) :=
          (P1.map (Int.castRingHom ℝ)).supNorm_nonneg
        calc
          ((Q1.map (Int.castRingHom ℝ)).supNorm) ≤ U * ((P1.map (Int.castRingHom ℝ)).supNorm) := by
            simpa [Q1, U] using hU1'
          _ ≤ C * ((P1.map (Int.castRingHom ℝ)).supNorm) := by
            exact mul_le_mul_of_nonneg_right hCgeU hx0
      · have hQi : Q i = P i := by simp [Q, hi0, hi1]
        rw [hQi]
        have hx : (0 : ℝ) ≤ ((P i).map (Int.castRingHom ℝ)).supNorm :=
          ((P i).map (Int.castRingHom ℝ)).supNorm_nonneg
        calc
          ((P i).map (Int.castRingHom ℝ)).supNorm ≤
              (1 : ℝ) * ((P i).map (Int.castRingHom ℝ)).supNorm := by rw [one_mul]
          _ ≤ C * ((P i).map (Int.castRingHom ℝ)).supNorm := by
            exact mul_le_mul_of_nonneg_right hC1 hx
  · intro i
    by_cases hi0 : i.val = 0
    · have hQi : Q i = Q0 := by simp [Q, hi0]
      have hi0e : i = ⟨0, by omega⟩ := Fin.ext hi0
      have hPi : P i = P0 := by rw [hi0e]
      rw [hQi, hPi]
      have hL0' := shift_mul_supNorm_ge P0 a0 n lam0 hP0ne hP0n hsum0
      have hx0 : (0 : ℝ) ≤ ((Q0.map (Int.castRingHom ℝ)).supNorm) :=
        (Q0.map (Int.castRingHom ℝ)).supNorm_nonneg
      calc
        ((P0.map (Int.castRingHom ℝ)).supNorm) ≤ D * ((Q0.map (Int.castRingHom ℝ)).supNorm) := by
          simpa [Q0, D] using hL0'
        _ ≤ C * ((Q0.map (Int.castRingHom ℝ)).supNorm) := by
          exact mul_le_mul_of_nonneg_right hCgeD hx0
    · by_cases hi1 : i.val = 1
      · have hQi : Q i = Q1 := by simp [Q, hi0, hi1]
        have hi1e : i = ⟨1, by omega⟩ := Fin.ext hi1
        have hPi : P i = P1 := by rw [hi1e]
        rw [hQi, hPi]
        have hL1' := shift_mul_supNorm_ge P1 a1 n lam1 hP1ne hP1n hsum1
        have hx0 : (0 : ℝ) ≤ ((Q1.map (Int.castRingHom ℝ)).supNorm) :=
          (Q1.map (Int.castRingHom ℝ)).supNorm_nonneg
        calc
          ((P1.map (Int.castRingHom ℝ)).supNorm) ≤ D * ((Q1.map (Int.castRingHom ℝ)).supNorm) := by
            simpa [Q1, D] using hL1'
          _ ≤ C * ((Q1.map (Int.castRingHom ℝ)).supNorm) := by
            exact mul_le_mul_of_nonneg_right hCgeD hx0
      · have hQi : Q i = P i := by simp [Q, hi0, hi1]
        rw [hQi]
        have hx : (0 : ℝ) ≤ ((P i).map (Int.castRingHom ℝ)).supNorm :=
          ((P i).map (Int.castRingHom ℝ)).supNorm_nonneg
        calc
          ((P i).map (Int.castRingHom ℝ)).supNorm ≤
              (1 : ℝ) * ((P i).map (Int.castRingHom ℝ)).supNorm := by rw [one_mul]
          _ ≤ C * ((P i).map (Int.castRingHom ℝ)).supNorm := by
            exact mul_le_mul_of_nonneg_right hC1 hx
  · intro i
    by_cases hi0 : i.val = 0
    · have hQi : Q i = Q0 := by simp [Q, hi0]
      have hi0e : i = ⟨0, by omega⟩ := Fin.ext hi0
      have hPi : P i = P0 := by rw [hi0e]
      rw [hQi, hPi]
      have hE0' := shift_mul_eval_le ξ P0 a0 n lam0 L ha0n hb0
      have hx0 : (0 : ℝ) ≤ ‖Polynomial.eval ξ ((P0.map (Int.castRingHom ℝ)))‖ := by positivity
      calc
        ‖Polynomial.eval ξ ((Q0.map (Int.castRingHom ℝ)))‖ ≤
            E * ‖Polynomial.eval ξ ((P0.map (Int.castRingHom ℝ)))‖ := by
              simpa [Q0, E] using hE0'
        _ ≤ C * ‖Polynomial.eval ξ ((P0.map (Int.castRingHom ℝ)))‖ := by
          exact mul_le_mul_of_nonneg_right hCgeE hx0
    · by_cases hi1 : i.val = 1
      · have hQi : Q i = Q1 := by simp [Q, hi0, hi1]
        have hi1e : i = ⟨1, by omega⟩ := Fin.ext hi1
        have hPi : P i = P1 := by rw [hi1e]
        rw [hQi, hPi]
        have hE1' := shift_mul_eval_le ξ P1 a1 n lam1 L ha1n hb1
        have hx0 : (0 : ℝ) ≤ ‖Polynomial.eval ξ ((P1.map (Int.castRingHom ℝ)))‖ := by positivity
        calc
          ‖Polynomial.eval ξ ((Q1.map (Int.castRingHom ℝ)))‖ ≤
              E * ‖Polynomial.eval ξ ((P1.map (Int.castRingHom ℝ)))‖ := by
                simpa [Q1, E] using hE1'
          _ ≤ C * ‖Polynomial.eval ξ ((P1.map (Int.castRingHom ℝ)))‖ := by
            exact mul_le_mul_of_nonneg_right hCgeE hx0
      · have hQi : Q i = P i := by simp [Q, hi0, hi1]
        rw [hQi]
        have hx : (0 : ℝ) ≤ ‖Polynomial.eval ξ ((P i).map (Int.castRingHom ℝ))‖ := by positivity
        calc
          ‖Polynomial.eval ξ ((P i).map (Int.castRingHom ℝ))‖ ≤
              (1 : ℝ) * ‖Polynomial.eval ξ ((P i).map (Int.castRingHom ℝ))‖ := by rw [one_mul]
          _ ≤ C * ‖Polynomial.eval ξ ((P i).map (Int.castRingHom ℝ))‖ := by
            exact mul_le_mul_of_nonneg_right hC1 hx

end
