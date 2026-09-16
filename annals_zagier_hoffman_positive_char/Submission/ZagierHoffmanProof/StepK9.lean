import Submission.ZagierHoffmanProof.StepK8

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped BigOperators

/-!
# Step K9: Frobenius lemma — `P_e(q) = (P_e(1))^q` in the completion

With `q = |F|` (a power of the characteristic), the level-`e` power sum satisfies
`P_e(q) = (P_e(1))^q`: over characteristic `p`, the `q`-th power map is additive on the
(finite) power-sum sums (freshman's dream), and `P_e(q) = Σ a^{-q} = (Σ a^{-1})^q`.
Proved at the `RatFunc F` level (`Hsum`) and embedded into the completion via
`P_eq_coe_Hsum`/`map_pow`.  This supplies `P_e(1) ≠ 0` in the outer R1 induction
(from the base `P_0(1) = 1` and `R1Prop(d−1)`, see PLAN Session 106).
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Finite-sum freshman's dream: `(Σ_{x∈s} f x)^(p^n) = Σ_{x∈s} (f x)^(p^n)` in
characteristic `p`. -/
lemma sum_pow_char_pow' {ι : Type*} {R : Type*} [CommSemiring R] (p n : ℕ)
    [Fact (Nat.Prime p)] [CharP R p] (s : Finset ι) (f : ι → R) :
    (∑ x ∈ s, f x) ^ (p ^ n) = ∑ x ∈ s, (f x) ^ (p ^ n) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact zero_pow (pow_ne_zero n (Nat.Prime.ne_zero (Fact.out)))
  | insert a s ha ih =>
      calc
        (∑ x ∈ insert a s, f x) ^ (p ^ n)
            = (f a + ∑ x ∈ s, f x) ^ (p ^ n) := by
              rw [Finset.sum_insert ha]
        _ = (f a) ^ (p ^ n) + (∑ x ∈ s, f x) ^ (p ^ n) := by
              exact add_pow_char_pow (f a) (∑ x ∈ s, f x) p n
        _ = (f a) ^ (p ^ n) + ∑ x ∈ s, (f x) ^ (p ^ n) := by
              rw [ih]
        _ = ∑ x ∈ insert a s, (f x) ^ (p ^ n) := by
              rw [Finset.sum_insert ha]

/-- In a field, `(x^n)⁻¹ = (x⁻¹)^n`. -/
lemma inv_pow_field {K : Type*} [Field K] (x : K) (n : ℕ) :
    (x ^ n)⁻¹ = (x⁻¹) ^ n := by
  rw [inv_pow]

/-- RatFunc-level Frobenius: `Hsum_d(q) = (Hsum_d(1))^q`. -/
lemma Hsum_q_eq_pow_one (d : ℕ) :
    Hsum F d (Nat.card F) = (Hsum F d 1) ^ (Nat.card F) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F (ringChar F) := ringChar.charP F
  rcases FiniteField.card (K := F) (p := ringChar F) with ⟨n, hprime, hcard⟩
  haveI : Fact (Nat.Prime (ringChar F)) := ⟨hprime⟩
  have hcard' : Nat.card F = (ringChar F) ^ (n : ℕ) := by
    rw [← Fintype.card_eq_nat_card]
    exact hcard
  have hf := sum_pow_char_pow' (p := ringChar F) (n := (n : ℕ)) (R := RatFunc F)
    (s := (Finset.univ : Finset (HeadD F d)))
    (f := fun p : HeadD F d => (((p.1 : RatFunc F) ^ 1)⁻¹))
  calc
    Hsum F d (Nat.card F)
        = ∑ p : HeadD F d, (((p.1 : RatFunc F) ^ Nat.card F)⁻¹) := by
          rfl
    _ = ∑ p : HeadD F d, (((p.1 : RatFunc F) ^ 1)⁻¹) ^ Nat.card F := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [inv_pow_field, pow_one]
    _ = (∑ p : HeadD F d, (((p.1 : RatFunc F) ^ 1)⁻¹)) ^ Nat.card F := by
          rw [hcard']
          -- apply hf (symm) after matching the type-sum to the membership sum
          simpa using hf.symm

/-- ★ Frobenius lemma: `P_e(q) = (P_e(1))^q` in the completion (`q = |F|`). -/
lemma P_d_q_eq_pow_one (d : ℕ) :
    P F d (qExp F) = (P F d oneExp) ^ (Nat.card F) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have h1 := P_eq_coe_Hsum F d (qExp F)
  have h2 := P_eq_coe_Hsum F d oneExp
  -- P F d (qExp F) = cast(Hsum F d (Nat.card F)); P F d oneExp = cast(Hsum F d 1)
  rw [h1, h2]
  -- goal: cast(Hsum d q) = (cast(Hsum d 1)) ^ Nat.card F
  have hr := congrArg (fun t : RatFunc F => (t : RatFunc.CompletionAtInfty F)) (Hsum_q_eq_pow_one F d)
  -- hr : cast(Hsum d q) = cast((Hsum d 1)^q)
  calc
    ((Hsum F d (Nat.card F) : RatFunc F) : RatFunc.CompletionAtInfty F)
        = (((Hsum F d 1) ^ Nat.card F : RatFunc F) : RatFunc.CompletionAtInfty F) := hr
    _ = (((Hsum F d 1 : RatFunc F) : RatFunc.CompletionAtInfty F)) ^ Nat.card F := by
          -- the completion embedding is a ring hom: map_pow
          simpa [rat_cast_eq_algebraMap F] using
            (map_pow (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) (Hsum F d 1) (Nat.card F))

end ZagierHoffmanPositiveChar
