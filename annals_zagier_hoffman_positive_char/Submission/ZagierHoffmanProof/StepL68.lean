import Submission.ZagierHoffmanProof.StepL67
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L68: CASE-1 weight bound w ≥ q + 2

  ★ case1_weight_ge_q_add_two (s hr hbigp) : Nat.card F + 2 ≤ weight r s
  — for a depth-≥2 tuple with second entry > q (the CASE-1 form): the two entries
  at positions 0,1 contribute ≥ 1 + (q+1) (two_entries_le_weight + PNat pos +
  q < pad0 s 1), so the weight is ≥ q+2.  CONSEQUENCE (PLAN SESSION 220): every
  Step-1 member of a CASE-1 j=1 input has weight w ≥ q+2 > q, so NO member is the
  ¬1-adm depth-1 (q)-form — the member dispatch is a sharp two-case split
  (2-adm → self; ¬2-adm → in-domain via kAdm_one_iff_front from the front alone).
NEXT: the CASE-1 front-bound assembly (member pad0 0 ≤ q from StepL64/65's heads
+ this bound for the depth-1 exclusion), then the per-member e dispatch for the
type-3 family in main2_case1_j1.  Named gates unchanged.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ CASE-1 weight bound: a tuple with depth ≥ 2 and second entry > q has weight
≥ q + 2.  Every Step-1 member of a CASE-1 j=1 input therefore has weight > q, so
no member is the ¬1-adm depth-1 (q)-form. -/
lemma case1_weight_ge_q_add_two {r : ℕ} (s : Fin r → ℕ+) (hr : 2 ≤ r)
    (hbigp : (Nat.card F : ℕ) < pad0 s 1) : Nat.card F + 2 ≤ weight r s := by
  have h01 : (s ⟨0, by omega⟩ : ℕ) + (s ⟨1, by omega⟩ : ℕ) ≤ weight r s :=
    two_entries_le_weight s (by
      intro h
      have hv := congrArg (fun i : Fin r => (i : ℕ)) h
      have hz : (0 : ℕ) = 1 := by simpa using hv
      omega)
  have hs1 : 1 ≤ (s ⟨0, by omega⟩ : ℕ) := (s ⟨0, by omega⟩).pos
  have hs2 : Nat.card F + 1 ≤ (s ⟨1, by omega⟩ : ℕ) := by
    have hp : pad0 s 1 = (s ⟨1, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 1 < r)
    rw [← hp]
    omega
  omega
end ZagierHoffmanPositiveChar
