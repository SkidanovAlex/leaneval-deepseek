import Submission.ZagierHoffmanProof.StepL117
set_option autoImplicit false
set_option maxHeartbeats 200000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L119: the (k,j)-chain measure interface — every chain member is a
MainkStep recursion call (SESSION 258i, route (i) easy case)

Route (i)'s main(k) recursion (¬k-adm ∧ depth ≥ k inputs) re-processes ¬k-adm
members of its chains.  Well-foundedness needs: every kept member m of a chain
step from s satisfies MainkStep k q s m (strict prefix-k drop, or equality +
InitLt), so the lkμ measure (psum-k, initVal) decreases along every recursion
call (lkμ_lt_of_psum_lt / lkμ_lt_of_psum_eq_initLt, StepL107).

EASY CASE (this module): for the (k, j)-chains of an in-domain-at-level-k input
(bad entry at the chain's own level k), the per-member drops are the (k,j)-
generic lemmas already proven: type-1 via type1_psum_lt_k (strict), type-2 via
type2_psum_lt_k (strict), type-3 via type3_psum_k_le_X (≤, with the X-bound)
+ type3_Init_gt (InitLt) → mk_member_step.  ★ maink_chain_step_all packages
all three as one interface theorem over the (k,j)-chain lets, given the
config conjuncts (hhead, hbndB) that maink_config_full provides.
MIXED CASE (k₁ < k — next subgoal, NOT in this module): the chain at the
input's own first-bad index k₁ < k must be measured at the OUTPUT level k; the
per-member psum-k drops then need the member/s tail structure (the paper's
Prop-2.12 "s_i ≤ (s_{k₁},…) / t ≤ (q^{k₁−j−1}, s_{k₁}−1,…)" LePad bounds) —
the interface's harder half, recorded in PLAN.md SESSION 258i.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Every member of the (k, j)-chain of an in-domain-at-level-k input s is a
MainkStep recursion call from s (the easy-case measure interface). -/
theorem maink_chain_step_all (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (hsleq : ∀ x : ℕ, x < k - 1 → pad0 s x ≤ Nat.card F)
    (R0 : BinaryRel F) (u : R0.ιA)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1)
    (hhead : ∀ i₀ : R0.ιA, i₀ ≠ u →
      ((R0.cA i₀) ⟨0, R0.hdepA i₀⟩ : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hbndB : ∀ j' : R0.ιB, ∀ m : ℕ,
      psum (expTail (R0.cB j')) m ≤ psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    (∀ i₀ : R0.ιA, i₀ ≠ u → MainkStep k (Nat.card F) s
        (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)))) ∧
    (∀ i : D.ιB, MainkStep k (Nat.card F) s (Q.c (Sum.inr (Sum.inl i)))) ∧
    (∀ i : D.ιB, MainkStep k (Nat.card F) s (Q.c (Sum.inr (Sum.inr i)))) := by
  classical
  intro D Bs Q
  constructor
  · intro i₀ hi₀
    apply Or.inl
    exact type1_psum_lt_k F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i₀ (hhead i₀ hi₀)
  · constructor
    · intro i
      apply Or.inl
      exact type2_psum_lt_k F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i
    · intro i
      apply mk_member_step k (Nat.card F) s (Q.c (Sum.inr (Sum.inr i)))
      right
      constructor
      · have hle := type3_psum_k_le_X F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd
          (fun mm : ℕ => psumSeq (tupPadSum (single (qMinusExp F))
            (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) mm)
          hbndB (lemma29_X1_le F r s k hk1 hkr hbig) i
        exact hle
      · exact type3_Init_gt F r s k j hk1 hkr hj1 hjk hbig hsj hsleq R0 hbhd i

end ZagierHoffmanPositiveChar
