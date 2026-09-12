import Mathlib.NumberTheory.NumberField.House
import Mathlib.RingTheory.PowerSeries.Basic
import Submission.PowersOdd

/-!
# Power polynomials of a monic integer polynomial

For a monic polynomial `P ∈ ℤ[X]` of degree `d` whose complex roots are
`α₁,…,α_d`, the *power polynomial* `P₂` (resp. `P₄`) is the monic
polynomial whose roots are the squares (fourth powers) of the roots of `P`.

Rather than working with roots, we define `P₂` purely algebraically by
`P₂(X²) = (-1)^d · P(X) · P(-X)` (the even part extraction), which is valid
over any commutative ring.
-/

noncomputable section

open Polynomial
open scoped Polynomial

namespace Submission.Powers

/-- The even part of a polynomial `F`: `(evenPart F).coeff n = F.coeff (2*n)`.
Here `F.sum` is `Polynomial.sum`, summing `f k a` over the support of `F`. -/
def evenPart {R : Type*} [CommSemiring R] (F : R[X]) : R[X] :=
  F.sum fun n a => if Even n then monomial (n / 2) a else 0

lemma evenPart_coeff {R : Type*} [CommSemiring R] (F : R[X]) (n : ℕ) :
    (evenPart F).coeff n = F.coeff (2 * n) := by
  classical
  have hsum : (evenPart F).coeff n =
      ∑ b ∈ F.support, (if Even b then (if n = b / 2 then F.coeff b else 0) else 0) := by
    unfold evenPart
    rw [Polynomial.coeff_sum, Polynomial.sum_def]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hE : Even b <;> simp [hE, Polynomial.coeff_monomial, eq_comm]
  rw [hsum]
  by_cases h : 2 * n ∈ F.support
  · rw [Finset.sum_eq_single (2 * n)]
    · simp
    · intro b hb hbne
      by_cases hE : Even b
      · have hdiv : n ≠ b / 2 := by
          intro hd
          rcases hE with ⟨k, hk⟩
          have : b = 2 * n := by omega
          exact hbne this
        simp [hE, hdiv, eq_comm]
      · simp [hE]
    · simpa using h
  · have hcoeff : F.coeff (2 * n) = 0 := by
      simpa [Polynomial.mem_support_iff] using h
    rw [Finset.sum_eq_zero]
    · simp [hcoeff]
    · intro b hb
      by_cases hE : Even b
      · have hdiv : n ≠ b / 2 := by
          intro hd
          rcases hE with ⟨k, hk⟩
          have : b = 2 * n := by omega
          exact h (this ▸ hb)
        simp [hE, hdiv, eq_comm]
      · simp [hE]

lemma expand_evenPart {R : Type*} [CommSemiring R] (F : R[X])
    (hF : ∀ n : ℕ, ¬ Even n → F.coeff n = 0) :
    expand R 2 (evenPart F) = F := by
  classical
  ext n
  rw [coeff_expand (by norm_num : 0 < 2)]
  by_cases h : 2 ∣ n
  · rcases h with ⟨k, hk⟩
    subst n
    simp [evenPart_coeff, Nat.mul_comm]
  · have hnodd : ¬ Even n := by
      rintro ⟨k, hk⟩
      exact h ⟨k, by omega⟩
    simp [h, hF n hnodd]

/-- The square-power polynomial `P₂` of `P`:  `P₂(X²) = (-1)^deg P · P(X) · P(-X)`. -/
def pow2 {R : Type*} [CommRing R] (P : R[X]) : R[X] :=
  evenPart ((-1 : R) ^ P.natDegree • (P * P.comp (-X)))

/-- The fourth-power polynomial: `P₄ = (P₂)₂`. -/
def pow4 {R : Type*} [CommRing R] (P : R[X]) : R[X] := pow2 (pow2 P)

/-- Sum of two powers of `-1` with an odd sum of exponents is zero (in any ring). -/
lemma neg_one_pow_add_neg_one_pow {R : Type*} [Ring R] {i j : ℕ}
    (hij : ¬ Even (i + j)) : (-1 : R) ^ i + (-1 : R) ^ j = 0 := by
  rw [neg_one_pow_eq_ite, neg_one_pow_eq_ite]
  by_cases hi : Even i
  · have hjn : ¬ Even j := by
      intro hj
      have : Even (i + j) := by
        rcases hi with ⟨a, rfl⟩
        rcases hj with ⟨b, rfl⟩
        refine ⟨a + b, ?_⟩
        omega
      exact hij this
    simp [hi, hjn]
  · have hjn : Even j := by
      by_contra h
      have hio : Odd i := Nat.not_even_iff_odd.mp hi
      have hjo : Odd j := Nat.not_even_iff_odd.mp h
      exact hij (Odd.add_odd hio hjo)
    simp [hi, hjn]

/-- `P(X)P(-X)` has vanishing odd-degree coefficients in any commutative ring. -/
lemma mul_comp_neg_coeff_odd_any {R : Type*} [CommRing R] (P : R[X]) :
    ∀ n : ℕ, ¬ Even n → (P * P.comp (-X)).coeff n = 0 := by
  classical
  intro n hn
  let p : ℕ → R := fun i => P.coeff i
  have hmem_coeff : (P * P.comp (-X)).coeff n =
      ∑ x ∈ Finset.antidiagonal n, p x.1 * ((-1 : R) ^ x.2 * p x.2) := by
    rw [coeff_mul]
    apply Finset.sum_congr rfl
    intro x hx
    simp [p, Submission.PowersOdd.coeff_comp_neg_X P x.2]
  have hsum0 :
      (∑ x ∈ Finset.antidiagonal n, p x.1 * ((-1 : R) ^ x.2 * p x.2)) = 0 := by
    let f : ℕ × ℕ → R := fun x => p x.1 * ((-1 : R) ^ x.2 * p x.2)
    change (∑ x ∈ Finset.antidiagonal n, f x) = 0
    refine Finset.sum_involution (fun x _ => Prod.swap x) ?_ ?_ ?_ ?_
    · intro x hx
      rcases x with ⟨i, j⟩
      have hij : i + j = n := (Finset.mem_antidiagonal.mp hx)
      have hodd : ¬ Even (i + j) := by simpa [hij] using hn
      have hpow : (-1 : R) ^ i + (-1 : R) ^ j = 0 := neg_one_pow_add_neg_one_pow hodd
      calc
        p i * ((-1 : R) ^ j * p j) + p j * ((-1 : R) ^ i * p i)
            = p i * p j * ((-1 : R) ^ i + (-1 : R) ^ j) := by ring
        _ = 0 := by rw [hpow]; ring
    · intro x hx hf
      rcases x with ⟨i, j⟩
      have hij : i + j = n := (Finset.mem_antidiagonal.mp hx)
      intro hfix
      have hji : j = i := by simpa using congrArg Prod.fst hfix
      have hn' : Even n := by
        refine ⟨i, ?_⟩
        omega
      exact hn hn'
    · intro x hx
      rcases x with ⟨i, j⟩
      have hij : i + j = n := (Finset.mem_antidiagonal.mp hx)
      change (j, i) ∈ Finset.antidiagonal n
      rw [Finset.mem_antidiagonal]
      omega
    · intro x hx
      simp
  rw [hmem_coeff]
  exact hsum0

/-- `P₂(X²) = (-1)^deg P · P(X) · P(-X)`. -/
lemma pow2_expand {R : Type*} [CommRing R] (P : R[X]) :
    expand R 2 (pow2 P) = (-1 : R) ^ P.natDegree • (P * P.comp (-X)) := by
  unfold pow2
  apply expand_evenPart
  intro n hn
  simp [mul_comp_neg_coeff_odd_any P n hn]

/-- For a monic `P`, `P₂` is monic. -/
lemma pow2_monic {R : Type*} [CommRing R] (P : R[X]) (hP : P.Monic) :
    (pow2 P).Monic := by
  classical
  rw [Monic.def]
  rw [← Polynomial.leadingCoeff_expand (p := 2) (f := pow2 P) (by norm_num : 0 < 2)]
  rw [pow2_expand P]
  have hGm : (((-1 : R) ^ P.natDegree) • (P * P.comp (-X))).Monic := by
    rw [smul_eq_C_mul]
    have hC : C ((-1 : R) ^ P.natDegree) = (-1 : R[X]) ^ P.natDegree := by
      rw [C_pow]
      congr 1
      simp
    rw [hC]
    have hEq : (-1 : R[X]) ^ P.natDegree * (P * P.comp (-X)) =
        P * ((-1 : R[X]) ^ P.natDegree * P.comp (-X)) := by
      ring
    rw [hEq]
    exact hP.mul (Polynomial.Monic.neg_one_pow_natDegree_mul_comp_neg_X hP)
  exact hGm.leadingCoeff

/-- Evaluating the defining identity `P₂(X²) = (-1)^deg P · P(X)P(-X)` at `x`. -/
lemma pow2_eval_sq {R : Type*} [CommRing R] (P : R[X]) (x : R) :
    eval (x ^ 2) (pow2 P) = (-1 : R) ^ P.natDegree • (eval x P * eval (-x) P) := by
  classical
  let c : R := (-1 : R) ^ P.natDegree
  let G : R[X] := P * P.comp (-X)
  have hodd : ∀ n : ℕ, ¬ Even n → G.coeff n = 0 := by
    intro n hn
    exact mul_comp_neg_coeff_odd_any P n hn
  have h1 : expand R 2 (pow2 P) = c • G := by
    dsimp [pow2, c, G]
    apply expand_evenPart
    intro n hn
    have hc0 : (P * P.comp (-X)).coeff n = 0 := mul_comp_neg_coeff_odd_any P n hn
    simp [hc0]
  calc
    eval (x ^ 2) (pow2 P) = eval x ((pow2 P).comp (X ^ 2)) := by
      rw [eval_comp]
      congr 1
      simp
    _ = eval x (expand R 2 (pow2 P)) := by
      rw [Polynomial.expand_eq_comp_X_pow 2]
    _ = eval x (c • G) := by rw [h1]
    _ = c • eval x G := by rw [eval_smul]
    _ = c • (eval x P * eval (-x) P) := by
      congr 1
      dsimp [G]
      rw [eval_mul]
      congr 1
      rw [eval_comp]
      congr 1
      simp
    _ = (-1 : R) ^ P.natDegree • (eval x P * eval (-x) P) := by
      simp [c]

end Submission.Powers

end
