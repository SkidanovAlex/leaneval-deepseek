import Submission.ZagierHoffmanProof.StepA3
import Submission.Commons.FieldTheory.Finite.sum_pow_eq
import Submission.Commons.FieldTheory.Polynomial.X_pow_card_sub_X_eq_prod_X_sub_C

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped BigOperators

/-!
# Step K5: the first level-1 power-sum evaluation: `A F 1 = -1` (base of R1(0))

`A n = Σ_c (qPoly F c)^n` is the level-one power-sum numerator polynomial
(`qPoly F c = ∏_{b ≠ c} (X + C b)`), and `A F 1 = Σ_c qPoly F c`.  We prove
`A F 1 = -1` in `F[X]`:

  - `qPoly F c = (X^(q-1) − 1) ∘ (X + C c)` (from qPoly_zero + qPoly_comp_add), so
  - `(qPoly F c).eval θ = (θ + c)^(q-1) − 1` for every θ ∈ F, hence
  - `(A F 1).eval θ = Σ_c ((θ+c)^(q-1) − 1) = -1` for every θ ∈ F
    (`Σ_{x∈F} x^(q-1) = -1` by Commons.FieldTheory.Finite.sum_pow_eq, and `(q : F) = 0`),
  - and `A F 1` has degree `< q`, so `A F 1 + 1` has all `q` elements of `F` as roots and
    degree `< q`; hence `carlitzOne F = ∏_{c∈F}(X - C c)` divides it and the degree
    bound forces `A F 1 + 1 = 0`.

This is the base case `P_1(1) = -1/D1` (R1(0)) at the polynomial level: via
`P_one_eq_sum_translate`, `P F 1 1 = Σ_c (X + C c)^{-1} = A F 1 / carlitzOne = -1/carlitzOne`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `qPoly F c = (X^{q-1} − 1) ∘ (X + C c)` (from qPoly_zero + qPoly_comp_add). -/
lemma qPoly_eq_pow_sub_comp (c : F) :
    letI : Fintype F := Fintype.ofFinite F
    qPoly F c = ((X ^ (Nat.card F - 1) - 1) : F[X]).comp (X + C c) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  calc
    qPoly F c = qPoly F (0 + c) := by rw [zero_add]
    _ = (qPoly F 0).comp (X + C c) := by
          rw [qPoly_comp_add F 0 c]
    _ = ((X ^ (Nat.card F - 1) - 1) : F[X]).comp (X + C c) := by
          rw [qPoly_zero F]

/-- `(qPoly F c).eval θ = (θ + c)^{q−1} − 1`. -/
lemma eval_qPoly (c θ : F) :
    letI : Fintype F := Fintype.ofFinite F
    (qPoly F c).eval θ = (θ + c) ^ (Nat.card F - 1) - 1 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  calc
    (qPoly F c).eval θ
        = (((X ^ (Nat.card F - 1) - 1) : F[X]).comp (X + C c)).eval θ := by
          rw [qPoly_eq_pow_sub_comp F c]
    _ = ((X ^ (Nat.card F - 1) - 1) : F[X]).eval (θ + c) := by
          rw [Polynomial.eval_comp]
          congr 1
          rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    _ = (θ + c) ^ (Nat.card F - 1) - 1 := by
          rw [Polynomial.eval_sub, Polynomial.eval_pow]
          simp

/-- `Σ_c (θ + c)^{q−1} = -1` for every θ (power sums over a finite field). -/
lemma sum_add_pow_card_sub_one (θ : F) :
    letI : Fintype F := Fintype.ofFinite F
    (∑ c : F, (θ + c) ^ (Nat.card F - 1)) = -1 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hpos : 0 < Nat.card F - 1 := by
    have hq : 2 ≤ Nat.card F := by
      rw [← Fintype.card_eq_nat_card]
      exact Fintype.one_lt_card
    omega
  have hpow : (∑ x : F, x ^ (Nat.card F - 1)) =
      if Fintype.card F - 1 ∣ Nat.card F - 1 then (-1 : F) else 0 := by
    exact Commons.FieldTheory.Finite.sum_pow_eq (K := F) hpos
  have hcond : Fintype.card F - 1 ∣ Nat.card F - 1 := by
    rw [Fintype.card_eq_nat_card]
  have hval : (∑ x : F, x ^ (Nat.card F - 1)) = -1 := by
    rw [hpow, if_pos hcond]
  calc
    (∑ c : F, (θ + c) ^ (Nat.card F - 1)) = ∑ x : F, x ^ (Nat.card F - 1) := by
          apply Finset.sum_bij (s := (Finset.univ : Finset F)) (t := (Finset.univ : Finset F))
            (i := fun c hc => θ + c)
          · intro c hc; simp
          · intro c1 hc1 c2 hc2 h
            exact add_left_cancel h
          · intro x hx
            refine ⟨x - θ, by simp, ?_⟩
            rw [add_comm, sub_add_cancel]
          · intro c hc; rfl
    _ = -1 := hval

/-- `carlitzOne = ∏_c (X - C c)` (the standard root form). -/
lemma carlitzOne_eq_prod_X_sub_C :
    letI : Fintype F := Fintype.ofFinite F
    carlitzOne F = ∏ c : F, (X - C c) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have h1 := Commons.FieldTheory.Polynomial.X_pow_card_sub_X_eq_prod_X_sub_C (F := F)
  rw [← h1]
  change X ^ Nat.card F - X = X ^ Fintype.card F - X
  rw [Fintype.card_eq_nat_card]

/-- ★ `A F 1 = -1`: the level-1 power-sum polynomial `Σ_c Q_c` is the constant −1. -/
lemma A_one_eq_neg_one :
    letI : Fintype F := Fintype.ofFinite F
    A F 1 = -1 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  let P : F[X] := A F 1
  have hdeg : P.natDegree < Nat.card F := by
    have hle : P.natDegree ≤ 1 * (Nat.card F - 1) := by
      simpa [P] using A_natDegree_le F 1
    have hq : 2 ≤ Nat.card F := by
      rw [← Fintype.card_eq_nat_card]
      exact Fintype.one_lt_card
    omega
  have hcard_zero : (Nat.card F : F) = 0 := by
    rw [← Fintype.card_eq_nat_card]
    exact Nat.cast_card_eq_zero F
  have heval : ∀ θ : F, P.eval θ = -1 := by
    intro θ
    calc
      P.eval θ = (A F 1).eval θ := rfl
      _ = (∑ c : F, (qPoly F c) ^ 1).eval θ := by rfl
      _ = ∑ c : F, ((qPoly F c) ^ 1).eval θ := by
            rw [Polynomial.eval_finsetSum]
      _ = ∑ c : F, (qPoly F c).eval θ := by
            apply Finset.sum_congr rfl
            intro c hc
            simp
      _ = ∑ c : F, ((θ + c) ^ (Nat.card F - 1) - 1) := by
            apply Finset.sum_congr rfl
            intro c hc
            have he := eval_qPoly F c θ
            change (qPoly F c).eval θ = (θ + c) ^ (Nat.card F - 1) - 1 at he
            rw [he]
      _ = (∑ c : F, (θ + c) ^ (Nat.card F - 1)) - ∑ c : F, (1 : F) := by
            rw [Finset.sum_sub_distrib]
      _ = -1 - (Nat.card F : F) := by
            have hs := sum_add_pow_card_sub_one F θ
            change (∑ c : F, (θ + c) ^ (Nat.card F - 1)) = -1 at hs
            rw [hs]
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            rw [Fintype.card_eq_nat_card]
            simp
      _ = -1 := by
            rw [hcard_zero]
            simp
  let Q : F[X] := P + 1
  have hdegQ : Q.natDegree < Nat.card F := by
    have h1 : Q.natDegree ≤ max P.natDegree (1 : F[X]).natDegree := by
      dsimp [Q]
      exact Polynomial.natDegree_add_le P (1 : F[X])
    have hq : 1 ≤ Nat.card F := by
      have hq2 : 2 ≤ Nat.card F := by
        rw [← Fintype.card_eq_nat_card]
        exact Fintype.one_lt_card
      omega
    have hOne : (1 : F[X]).natDegree = 0 := by simp
    have hmax : max P.natDegree (1 : F[X]).natDegree < Nat.card F := by
      rw [hOne]
      omega
    omega
  have hlin (x : F) : (X - C x : F[X]) = X + C (-x) := by
    rw [sub_eq_add_neg]
    congr 1
    rw [← Polynomial.C_neg]
  have hdiv : carlitzOne F ∣ Q := by
    have hfac : ∀ c : F, (X - C c : F[X]) ∣ Q := by
      intro c
      rw [Polynomial.dvd_iff_isRoot]
      change Q.eval c = 0
      dsimp [Q]
      rw [Polynomial.eval_add, heval c]
      simp
    have hcop : ((Finset.univ : Finset F) : Set F).Pairwise (Function.onFun IsCoprime (fun c : F => (X - C c : F[X]))) := by
      intro a ha b hb hab
      have hneq : -a ≠ -b := by
        intro h
        apply hab
        exact neg_injective h
      change IsCoprime (X - C a : F[X]) (X - C b : F[X])
      rw [hlin a, hlin b]
      exact linFactor_coprime F hneq
    have hprod := Finset.prod_dvd_of_coprime (s := fun c : F => (X - C c : F[X])) (t := (Finset.univ : Finset F)) hcop (fun i hi => hfac i)
    have hcp := carlitzOne_eq_prod_X_sub_C F
    change carlitzOne F = ∏ c : F, (X - C c : F[X]) at hcp
    rw [hcp]
    exact hprod
  have hcarl0 : carlitzOne F ≠ 0 := by
    intro hz
    have hn := carlitzOne_natDegree F
    rw [hz, Polynomial.natDegree_zero] at hn
    have hc : 0 < Nat.card F := by
      rw [← Fintype.card_eq_nat_card]
      exact Fintype.card_pos
    omega
  have hQ0 : Q = 0 := by
    rcases hdiv with ⟨R, hR⟩
    by_cases hR0 : R = 0
    · rw [hR0, mul_zero] at hR
      exact hR
    · exfalso
      have hdegmul := Polynomial.natDegree_mul hcarl0 hR0
      rw [hR, hdegmul] at hdegQ
      have hcarl : (carlitzOne F).natDegree = Nat.card F := carlitzOne_natDegree F
      rw [hcarl] at hdegQ
      omega
  have hP : P = -1 := by
    have := congrArg (fun q : F[X] => q - 1) hQ0
    dsimp [Q] at this
    simpa using this
  simpa [P] using hP

end ZagierHoffmanPositiveChar
