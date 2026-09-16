import Submission.ZagierHoffmanProof.StepL123
import Submission.ZagierHoffmanProof.StepL119
import Submission.ZagierHoffmanProof.StepL47
import Submission.ZagierHoffmanProof.StepL33
set_option autoImplicit false
set_option maxHeartbeats 200000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L124: the MIXED MainkStep member facts at an output level (option-(b)
continuation infrastructure, SESSION 258n)

The (b)-continuation recursion (expanding a ¬(k−1)-adm member at the fixed
tower level k by decomposing at its OWN first-bad level a ≤ k−1) dispatches the
outputs of the (a, j)-chain with MainkStep measured at the OUTPUT level o ≥ a:
  • type-2 members: psum (member₂) o < psum s o  (strict) — from
    type2_psum_ge_k_lt at ℓ = o when a < o, else type2_psum_lt_k at ℓ = a = o;
  • type-3 members: psum (member₃) o ≤ psum s o ∧ InitLt q s (member₃) — from
    type3_psum_ge_k_le at ℓ = o + type3_Init_gt (Init is level-independent) —
    hence MainkStep o (Nat.card F) s (member₃) via mk_member_step.
(The type-1 (i₀≠u) members at ℓ > a are ≤ only — maink_mixed_type1_le/StepL123 —
NOT a MainkStep claim; whether they are STRICT is the open (b1)/(b2) question
recorded in PLAN.md SESSION 258n.  Note the EASY case o = a is exactly
maink_chain_step_all's content at the chain level — these lemmas are the
level-`o` generalizations needed when a ¬(k−1)-adm tuple is re-decomposed at
its own level a < o.)
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ A type-2 member of the (a, j)-chain satisfies MainkStep at every output
level o with a ≤ o ≤ r: psum (member₂) o < psum s o. -/
theorem maink_mixed_type2_step (r : ℕ) (s : Fin r → ℕ+) (a o j : ℕ)
    (hk1 : 1 ≤ a) (hkr : a ≤ r) (hao : a ≤ o) (hor : o ≤ r)
    (hj1 : 1 ≤ j) (hjk : j ≤ a - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨a - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < a - 1 → (s i : ℕ) = Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1)
    (hbndB : ∀ j' : R0.ιB, ∀ m : ℕ,
      psum (expTail (R0.cB j')) m ≤ psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s a hk1 hkr hbig) (sTail r s a hkr))) m) :
    let D := RelData.BCqIter F (a - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (a - j - 1) R0 e)
        (RelData.iterate_merge_hv F (a - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB, MainkStep o (Nat.card F) s (Q.c (Sum.inr (Sum.inl i))) := by
  classical
  intro D Bs Q i
  by_cases hao' : a < o
  · have hlt := type2_psum_ge_k_lt F r s a j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd hbndB i o hao' hor
    exact Or.inl hlt
  · have heq : a = o := by omega
    have hlt := type2_psum_lt_k F r s a j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i
    have hlt' : psum (Q.c (Sum.inr (Sum.inl i))) o < psum s o := by
      rw [← heq]
      exact hlt
    exact Or.inl hlt'

/-- ★ A type-3 member of the (a, j)-chain satisfies MainkStep at every output
level o with a ≤ o ≤ r: psum (member₃) o ≤ psum s o with InitLt q s (member₃). -/
theorem maink_mixed_type3_step (r : ℕ) (s : Fin r → ℕ+) (a o j : ℕ)
    (hk1 : 1 ≤ a) (hkr : a ≤ r) (hao : a ≤ o) (hor : o ≤ r)
    (hj1 : 1 ≤ j) (hjk : j ≤ a - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨a - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hsleq : ∀ x : ℕ, x < a - 1 → pad0 s x ≤ Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < a - 1 → (s i : ℕ) = Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1)
    (hbndB : ∀ j' : R0.ιB, ∀ m : ℕ,
      psum (expTail (R0.cB j')) m ≤ psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s a hk1 hkr hbig) (sTail r s a hkr))) m) :
    let D := RelData.BCqIter F (a - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (a - j - 1) R0 e)
        (RelData.iterate_merge_hv F (a - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB, MainkStep o (Nat.card F) s (Q.c (Sum.inr (Sum.inr i))) := by
  classical
  intro D Bs Q i
  have hle := type3_psum_ge_k_le F r s a j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd hbndB i o hao hor
  have hinit := type3_Init_gt F r s a j hk1 hkr hj1 hjk hbig hsj hsleq R0 hbhd i
  refine mk_member_step o (Nat.card F) s (Q.c (Sum.inr (Sum.inr i))) ?_
  right
  exact ⟨hle, hinit⟩

end ZagierHoffmanPositiveChar
