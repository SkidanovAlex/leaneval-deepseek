import Submission.ZagierHoffmanProof.StepK9

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped BigOperators

/-!
# Step K10: the Carlitz factorial ℓ_d and its recursion

With `q = |F|`, the Carlitz factorial is `ℓ_d := ∏_{i=1}^d (X − X^{q^i})` in `F[X]`
(`ℓ_0 = 1`).  Session-109's ID2 route needs: the power-sum evaluation `P_d(1) = 1/ℓ_d`
(equivalently `U_d/U_{d+1} = X − X^{q^{d+1}}`), the `F[X]` freshman's dream
`(X − X^{q^d})^q = X^q − X^{q^{d+1}}`, and the assembly.  This file records `ℓ_d` and
its elementary recursion (all sorry-free).
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- the Carlitz factorial `ℓ_d := ∏_{i=1}^d (X − X^{q^i})`, `ℓ_0 = 1`. -/
noncomputable def lFact (d : ℕ) : F[X] :=
  ∏ j ∈ Finset.range d, (X - X ^ ((Nat.card F) ^ (j + 1)))

/-- `ℓ_0 = 1`. -/
lemma lFact_zero : lFact F 0 = 1 := by
  classical
  dsimp [lFact]

/-- `ℓ_{d+1} = ℓ_d · (X − X^{q^{d+1}})` (the one-step recursion). -/
lemma lFact_succ (d : ℕ) :
    lFact F (d + 1) = lFact F d * (X - X ^ ((Nat.card F) ^ (d + 1))) := by
  classical
  dsimp [lFact]
  rw [Finset.prod_range_succ]
/-- `ℓ_{d+1} = (X − X^{q^{d+1}}) · ℓ_d` (commuted version). -/
lemma lFact_succ' (d : ℕ) :
    lFact F (d + 1) = (X - X ^ ((Nat.card F) ^ (d + 1))) * lFact F d := by
  rw [lFact_succ F d]
  ring

/-- the ratio `ℓ_{d+1}/ℓ_d = X − X^{q^{d+1}}` is exactly the appended factor
(equivalent to `ℓ_{d+1} = ℓ_d · factor`; recorded as the ratio identity). -/
lemma lFact_ratio (d : ℕ) :
    lFact F (d + 1) = lFact F d * (X - X ^ ((Nat.card F) ^ (d + 1))) :=
  lFact_succ F d

/-- Freshman's dream in `F[X]` for a monomial difference, `q = |F|`:
`(X − X^m)^q = X^q − X^(m·q)`. -/
lemma X_sub_X_pow_card (m : ℕ) :
    (X - X ^ m : F[X]) ^ (Nat.card F) =
      X ^ (Nat.card F) - X ^ (m * Nat.card F) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F (ringChar F) := ringChar.charP F
  rcases FiniteField.card (K := F) (p := ringChar F) with ⟨n, hprime, hcard⟩
  haveI : Fact (Nat.Prime (ringChar F)) := ⟨hprime⟩
  have hcard' : Nat.card F = (ringChar F) ^ (n : ℕ) := by
    rw [← Fintype.card_eq_nat_card]
    exact hcard
  haveI : CharP (F[X]) (ringChar F) := by
    refine charP_of_injective_algebraMap (R := F) (A := F[X]) ?_ (ringChar F)
    intro a b h
    exact Polynomial.C_injective h
  calc
    (X - X ^ m : F[X]) ^ (Nat.card F)
        = (X - X ^ m : F[X]) ^ ((ringChar F) ^ (n : ℕ)) := by
          rw [hcard']
    _ = X ^ ((ringChar F) ^ (n : ℕ)) - (X ^ m) ^ ((ringChar F) ^ (n : ℕ)) := by
          exact sub_pow_char_pow X (X ^ m) (n : ℕ)
    _ = X ^ (Nat.card F) - X ^ (m * Nat.card F) := by
          rw [hcard']
          rw [pow_mul]

/-- The ID2-route form: `(X − X^{q^d})^q = X^q − X^{q^{d+1}}`. -/
lemma X_sub_X_pow_card_iter (d : ℕ) :
    (X - X ^ ((Nat.card F) ^ d) : F[X]) ^ (Nat.card F) =
      X ^ (Nat.card F) - X ^ ((Nat.card F) ^ (d + 1)) := by
  classical
  have h := X_sub_X_pow_card F ((Nat.card F) ^ d)
  rw [h]
  congr 1

end ZagierHoffmanPositiveChar
