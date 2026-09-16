import Submission.ZagierHoffmanProof.StepL51

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L52: level-2 CASE-2 members — explicit 2-admissible member facts (MAIN(2) base)

For a level-2 CASE-2 input `s = (s₁, q)` (`s₁ < q`, depth 2, 2-inadmissible) the
Step-1 chain (`k=2, j=1`) collapses (`n = k−j−1 = 0` `BC_q`-steps): the type-2
member is `(s₁, 1, q−1)` = `consVec s₁ (pair oneExp (qMinusExp F))` and the type-3
member is `(s₁+1, q−1)` = `pair ⟨s₁+1⟩ (qMinusExp F)`.  Both are DIRECTLY
`2`-admissible of weight `s₁+q` — the level-2 CASE-2 recursion needs no descent
(β-free base component of MAIN(2)).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The type-2 member `(s₁, 1, q−1)` of the level-2 CASE-2 chain is 2-admissible. -/
lemma twoAdm_s1_one_qminus (s₁ : ℕ+) (hs₁ : (s₁ : ℕ) < Nat.card F) :
    kAdmissible (Nat.card F) (consVec s₁ (pair oneExp (qMinusExp F))) 2 := by
  classical
  constructor
  · intro x hx
    by_cases hx0 : x = 0
    · subst x
      have h00 : 0 < 3 := by omega
      rw [pad0_of_lt (consVec s₁ (pair oneExp (qMinusExp F))) h00]
      have hc := congrArg (fun t : ℕ+ => (t : ℕ)) (consVec_zero s₁ (pair oneExp (qMinusExp F)))
      rw [hc]
      exact le_of_lt hs₁
    · have hx1 : x = 1 := by omega
      subst x
      have hp : pad0 (consVec s₁ (pair oneExp (qMinusExp F))) 1 =
          pad0 (pair oneExp (qMinusExp F)) 0 := pad0_consVec s₁ (pair oneExp (qMinusExp F)) 0
      rw [hp]
      have h00 : 0 < 2 := by omega
      rw [pad0_of_lt (pair oneExp (qMinusExp F)) h00]
      have hpz := congrArg (fun t : ℕ+ => (t : ℕ)) (pair_zero oneExp (qMinusExp F))
      rw [hpz]
      have hq1 : 1 ≤ Nat.card F := by
        have h2 : 2 ≤ Nat.card F := card_ge_two F
        omega
      exact hq1
  · intro hc2
    rcases hc2 with ⟨hr1, hrk, hall, hlast⟩
    -- depth 3 > 2, so no 2-adm witness
    omega

/-- The type-3 member `(s₁+1, q−1)` of the level-2 CASE-2 chain is 2-admissible. -/
lemma twoAdm_s1succ_qminus (s₁ : ℕ+) (hs₁ : (s₁ : ℕ) < Nat.card F) :
    kAdmissible (Nat.card F)
      (pair ⟨(s₁ : ℕ) + 1, Nat.succ_pos (s₁ : ℕ)⟩ (qMinusExp F)) 2 := by
  classical
  constructor
  · intro x hx
    by_cases hx0 : x = 0
    · subst x
      have h00 : 0 < 2 := by omega
      rw [pad0_of_lt (pair ⟨(s₁ : ℕ) + 1, Nat.succ_pos (s₁ : ℕ)⟩ (qMinusExp F)) h00]
      have hc := congrArg (fun t : ℕ+ => (t : ℕ))
        (pair_zero ⟨(s₁ : ℕ) + 1, Nat.succ_pos (s₁ : ℕ)⟩ (qMinusExp F))
      rw [hc]
      change (s₁ : ℕ) + 1 ≤ Nat.card F
      omega
    · have hx1 : x = 1 := by omega
      subst x
      have h01 : 1 < 2 := by omega
      rw [pad0_of_lt (pair ⟨(s₁ : ℕ) + 1, Nat.succ_pos (s₁ : ℕ)⟩ (qMinusExp F)) h01]
      have hc := congrArg (fun t : ℕ+ => (t : ℕ))
        (pair_one ⟨(s₁ : ℕ) + 1, Nat.succ_pos (s₁ : ℕ)⟩ (qMinusExp F))
      rw [hc]
      have hq1 : 1 ≤ Nat.card F := by
        have h2 : 2 ≤ Nat.card F := card_ge_two F
        omega
      have hqmin : (qMinusExp F : ℕ) = Nat.card F - 1 := by rfl
      rw [hqmin]
      omega
  · intro hc2
    rcases hc2 with ⟨hr1, hrk, hall, hlast⟩
    -- depth 2 ≤ 2: witness needs last = q, but last = q−1 ≠ q
    have hlast1 : ((pair ⟨(s₁ : ℕ) + 1, Nat.succ_pos (s₁ : ℕ)⟩ (qMinusExp F))
        ⟨2 - 1, by omega⟩ : ℕ) = Nat.card F - 1 := by
      have hc := congrArg (fun t : ℕ+ => (t : ℕ))
        (pair_one ⟨(s₁ : ℕ) + 1, Nat.succ_pos (s₁ : ℕ)⟩ (qMinusExp F))
      have hqmin : (qMinusExp F : ℕ) = Nat.card F - 1 := by rfl
      rw [hc, hqmin]
    have hq2 : 2 ≤ Nat.card F := card_ge_two F
    have hne : Nat.card F - 1 ≠ Nat.card F := by omega
    apply hne
    calc
      Nat.card F - 1 = ((pair ⟨(s₁ : ℕ) + 1, Nat.succ_pos (s₁ : ℕ)⟩ (qMinusExp F))
          ⟨2 - 1, by omega⟩ : ℕ) := hlast1.symm
      _ = Nat.card F := hlast

/-- Weight of the type-2 member: `s₁ + 1 + (q−1) = s₁ + q`. -/
lemma weight_s1_one_qminus (s₁ : ℕ+) :
    weight 3 (consVec s₁ (pair oneExp (qMinusExp F))) = (s₁ : ℕ) + Nat.card F := by
  classical
  rw [weight_consVec]
  rw [weight_pair]
  have hq1 : 1 ≤ Nat.card F := by
    have h2 : 2 ≤ Nat.card F := card_ge_two F
    omega
  rw [show (oneExp : ℕ) = 1 by rfl]
  rw [show (qMinusExp F : ℕ) = Nat.card F - 1 by rfl]
  omega

/-- Weight of the type-3 member: `(s₁+1) + (q−1) = s₁ + q`. -/
lemma weight_s1succ_qminus (s₁ : ℕ+) :
    weight 2 (pair ⟨(s₁ : ℕ) + 1, Nat.succ_pos (s₁ : ℕ)⟩ (qMinusExp F)) =
      (s₁ : ℕ) + Nat.card F := by
  classical
  calc
    weight 2 (pair ⟨(s₁ : ℕ) + 1, Nat.succ_pos (s₁ : ℕ)⟩ (qMinusExp F))
        = ((⟨(s₁ : ℕ) + 1, Nat.succ_pos (s₁ : ℕ)⟩ : ℕ+) : ℕ) + (qMinusExp F : ℕ) :=
          weight_pair ⟨(s₁ : ℕ) + 1, Nat.succ_pos (s₁ : ℕ)⟩ (qMinusExp F)
    _ = (s₁ : ℕ) + Nat.card F := by
          change ((s₁ : ℕ) + 1) + (qMinusExp F : ℕ) = (s₁ : ℕ) + Nat.card F
          have hq1 : 1 ≤ Nat.card F := by
            have h2 : 2 ≤ Nat.card F := card_ge_two F
            omega
          rw [show (qMinusExp F : ℕ) = Nat.card F - 1 by rfl]
          omega

end ZagierHoffmanPositiveChar
