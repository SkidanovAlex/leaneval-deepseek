import Mathlib.FieldTheory.Finite.Basic
import Submission.ZagierHoffmanProof.StepA

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial
open scoped BigOperators

/-!
# Step A (continued): translation structure of `[1]`, `Q_c` and `A_n`

Every ingredient of the level-one shuffle identity is *translation invariant* under
`X ↦ X + θ` (`θ ∈ F`): the Carlitz polynomial `[1] = X^q - X`, the product `Q_c`
(shifts to `Q_{c+θ}`), and the power sum `A_n`.  This file proves those facts, plus
the basic evaluation identities (values at the roots of `[1]`, factorization of the
leading factor `Q_0`), which are the stepping stones toward the degree-one shuffle
identity.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Translating the variable `X ↦ X + θ` sends the factor `X + C c` to `X + C (c + θ)`. -/
lemma linFactor_comp_add (c θ : F) :
    (X + C c).comp (X + C θ) = X + C (c + θ) := by
  simp [Polynomial.C_add, add_comm, add_left_comm, add_assoc]

/-- Translation invariance of `[1] = X^q - X`: `[1](X + θ) = [1](X)`. -/
lemma carlitzOne_comp_add (θ : F) :
    letI : Fintype F := Fintype.ofFinite F
    (carlitzOne F).comp (X + C θ) = carlitzOne F := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  calc
    (carlitzOne F).comp (X + C θ)
        = (∏ c : F, (X + C c)).comp (X + C θ) := by rw [carlitzOne_eq_prod_X_add_C F]
    _ = ∏ c : F, (X + C c).comp (X + C θ) := by
          rw [Polynomial.prod_comp]
    _ = ∏ c : F, (X + C (c + θ)) := by
          apply Finset.prod_congr rfl
          intro c hc
          exact linFactor_comp_add F c θ
    _ = ∏ d : F, (X + C d) := by
          -- reindex c ↦ c + θ (a bijection of F)
          apply Finset.prod_bij (fun c hc => c + θ) (by intro c hc; exact Finset.mem_univ _)
            (by intro c1 hc1 c2 hc2 h; exact add_right_cancel h)
            (by intro d hd; refine ⟨d - θ, Finset.mem_univ _, ?_⟩; simp)
            (by intro c hc; rfl)
    _ = carlitzOne F := (carlitzOne_eq_prod_X_add_C F).symm

/-- Translating the variable sends `Q_c` to `Q_{c+θ}`. -/
lemma qPoly_comp_add (c θ : F) :
    letI : Fintype F := Fintype.ofFinite F
    (qPoly F c).comp (X + C θ) = qPoly F (c + θ) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  calc
    (qPoly F c).comp (X + C θ)
        = (∏ b ∈ (Finset.univ : Finset F).erase c, (X + C b)).comp (X + C θ) := rfl
    _ = ∏ b ∈ (Finset.univ : Finset F).erase c, (X + C b).comp (X + C θ) := by
          rw [Polynomial.prod_comp]
    _ = ∏ b ∈ (Finset.univ : Finset F).erase c, (X + C (b + θ)) := by
          apply Finset.prod_congr rfl
          intro b hb
          exact linFactor_comp_add F b θ
    _ = ∏ d ∈ (Finset.univ : Finset F).erase (c + θ), (X + C d) := by
          -- reindex b ↦ b + θ:  {b | b ≠ c} ↦ {d | d ≠ c + θ}
          let s : Finset F := (Finset.univ : Finset F).erase c
          let t : Finset F := (Finset.univ : Finset F).erase (c + θ)
          change (∏ b ∈ s, (X + C (b + θ))) = ∏ d ∈ t, (X + C d)
          apply Finset.prod_bij (fun b hb => b + θ)
          · intro b hb
            rw [Finset.mem_erase] at hb ⊢
            constructor
            · intro hz
              apply hb.1
              exact add_right_cancel hz
            · exact Finset.mem_univ _
          · intro b1 hb1 b2 hb2 h
            exact add_right_cancel h
          · intro d hd
            rw [Finset.mem_erase] at hd
            refine ⟨d - θ, ?_, ?_⟩
            · rw [Finset.mem_erase]
              constructor
              · intro hz
                apply hd.1
                calc
                  d = (d - θ) + θ := by rw [sub_add_cancel]
                  _ = c + θ := by rw [hz]
              · exact Finset.mem_univ _
            · rw [sub_add_cancel]
          · intro b hb
            rfl
    _ = qPoly F (c + θ) := rfl

/-- Translation invariance of the power sum `A_n`: `A_n(X + θ) = A_n(X)`. -/
lemma A_comp_add (n : ℕ) (θ : F) :
    letI : Fintype F := Fintype.ofFinite F
    (A F n).comp (X + C θ) = A F n := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  calc
    (A F n).comp (X + C θ)
        = (∑ c : F, (qPoly F c) ^ n).comp (X + C θ) := rfl
    _ = ∑ c : F, ((qPoly F c).comp (X + C θ)) ^ n := by
          rw [Polynomial.sum_comp]
          apply Finset.sum_congr rfl
          intro c hc
          exact Polynomial.pow_comp (qPoly F c) (X + C θ) n
    _ = ∑ c : F, (qPoly F (c + θ)) ^ n := by
          apply Finset.sum_congr rfl
          intro c hc
          rw [qPoly_comp_add F c θ]
    _ = ∑ d : F, (qPoly F d) ^ n := by
          apply Finset.sum_bij (fun c hc => c + θ) (by intro c hc; exact Finset.mem_univ _)
            (by intro c1 hc1 c2 hc2 h; exact add_right_cancel h)
            (by intro d hd; refine ⟨d - θ, Finset.mem_univ _, ?_⟩; rw [sub_add_cancel])
            (by intro c hc; rfl)
    _ = A F n := rfl

/-- `Q_0 = ∏_{b ≠ 0} (X + C b)` is `X^(q-1) - 1`. -/
lemma qPoly_zero :
    letI : Fintype F := Fintype.ofFinite F
    qPoly F 0 = X ^ (Nat.card F - 1) - 1 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hq : carlitzOne F = (X + C (0 : F)) * qPoly F 0 := carlitzOne_eq_mul_qPoly F (0 : F)
  have hX : X ≠ (0 : F[X]) := by simp
  have hp : (X : F[X]) ^ Nat.card F = (X : F[X]) * (X : F[X]) ^ (Nat.card F - 1) := by
    have h1 : 1 < Nat.card F := by
      rw [← Fintype.card_eq_nat_card]
      exact Fintype.one_lt_card
    have hc : (Nat.card F - 1) + 1 = Nat.card F :=
      Nat.sub_add_cancel (Nat.le_of_lt h1)
    calc
      (X : F[X]) ^ Nat.card F = (X : F[X]) ^ ((Nat.card F - 1) + 1) := by rw [hc]
      _ = (X : F[X]) * (X : F[X]) ^ (Nat.card F - 1) := by rw [pow_succ']
  have hmul : X * qPoly F 0 = X * (X ^ (Nat.card F - 1) - 1) := by
    calc
      X * qPoly F 0 = (X + C (0 : F)) * qPoly F 0 := by rw [Polynomial.C_0, add_zero]
      _ = carlitzOne F := hq.symm
      _ = (X : F[X]) ^ (Nat.card F) - X := rfl
      _ = X * X ^ (Nat.card F - 1) - X := by rw [hp]
      _ = X * (X ^ (Nat.card F - 1) - 1) := by rw [mul_sub]; simp [mul_comm]
  exact mul_left_cancel₀ hX hmul

/-- Translation invariance: `A_n` is unchanged by any additive shift `X ↦ X + C c`. -/
lemma A_comp_C_add (n : ℕ) (c : F) :
    letI : Fintype F := Fintype.ofFinite F
    (A F n).comp (C c + X) = A F n := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  simpa [add_comm, add_left_comm, add_assoc] using (A_comp_add F n c)

/-- The product of all non-zero elements of a finite field is `-1`
(unit version: `∏ u : Fˣ, (u : F) = -1`). -/
lemma prod_units_eq_neg_one :
    letI : Fintype F := Fintype.ofFinite F
    letI : Fintype Fˣ := Fintype.ofFinite Fˣ
    (∏ u : Fˣ, (u : F)) = -1 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : Fintype Fˣ := Fintype.ofFinite Fˣ
  have h := FiniteField.prod_univ_units_id_eq_neg_one (K := F)
  have hmap := congrArg (Units.coeHom F) h
  rw [map_prod] at hmap
  simpa using hmap
