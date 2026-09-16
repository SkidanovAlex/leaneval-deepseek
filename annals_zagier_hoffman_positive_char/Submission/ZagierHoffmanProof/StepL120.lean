import Submission.ZagierHoffmanProof.StepL119
set_option autoImplicit false
set_option maxHeartbeats 200000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L120: the type-1 tail facts at the input's own first-bad index (SESSION
258j — the mixed-case structural seed)

Route (i)'s mixed case (chains at the input's first-bad index k₁ ≤ k, measured
at the output level k) rests on the paper's Prop-2.12 type-1 tail facts for the
Lemma-2.9 a-outputs s_i:
  • TAIL:  s_i ≤ (s_{k₁}, s_{k₁+1}, …)  — in the library's shape: the a-outputs
    R0.cA i (i ≠ u) of the data at (r−k₁, w1 := w1Of-at-k₁ = s⟨k₁−1⟩ − q,
    B := sTail-at-k₁) have prefix bounds
        psum (R0.cA i) m ≤ psumSeq (tupPadSum (single (qExp F))
          (consVec (w1Of F r s k₁ hk1 hkr hbig) (sTail r s k₁ hkr))) m,
    i.e. s_i ≤ (q, s_{k₁}−q, s_{k₁+1}, …) — the member tail after its q-block
    (the q + (s_{k₁}−q) = s_{k₁} identity is what lets the member match s);
  • HEAD:  s_{i1} < s_{k₁}  — (R0.cA i)⟨0⟩ < s⟨k₁−1⟩ (the library's hhead).
These are exactly the conjuncts lemma_2_9_rel/maink_config_full already
expose at EVERY parameter k — so StepL120 packages them at the concrete
parameter k₁ as the named interface theorem the mixed-type-1 assembly will
reference.  (STRUCTURAL NOTE for that assembly: with these facts the type-1
member satisfies psum m k ≤ psum s k at the output level, with EQUALITY
possible — the mixed-type-1 drop is NOT strict, so the mixed MainkStep needs
the paper's Init/entry-drop machinery for the equality case, unlike the easy
case's type1_psum_lt_k.  The type-2/3 tails (t ≤ (q^{k₁−j−1}, s_{k₁}−1, …))
follow the same shape from hbndB/hleB.)
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ The type-1 tail facts at the input's first-bad index k₁ (paper
Prop-2.12): the Lemma-2.9 a-outputs (i ≠ u) over W := (s⟨k₁−1⟩−q,
sTail-at-k₁) satisfy the TAIL prefix bound against (q, W) and the HEAD bound
s_{i1} < s_{k₁}. -/
theorem type1_tail_facts (k₁ r : ℕ) (s : Fin r → ℕ+) (hk1 : 1 ≤ k₁) (hkr : k₁ ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k₁ - 1, by omega⟩ : ℕ)) :
    ∃ (R0 : BinaryRel F) (u : R0.ιA),
      R0.aA u = 1 ∧
      (∀ i : R0.ιA, i ≠ u → ∀ m : ℕ,
        psum (R0.cA i) m ≤ psumSeq (tupPadSum (single (qExp F))
          (consVec (w1Of F r s k₁ hk1 hkr hbig) (sTail r s k₁ hkr))) m) ∧
      (∀ i : R0.ιA, i ≠ u → ((R0.cA i) ⟨0, R0.hdepA i⟩ : ℕ) < (s ⟨k₁ - 1, by omega⟩ : ℕ)) := by
  classical
  rcases maink_config_full F k₁ r s hk1 hkr hbig with
    ⟨R0, u, hdepu, hau, hc0, hbhd, hwtA, hhead, hXw, hbndB, hpref, _⟩
  exact ⟨R0, u, hau, hpref, hhead⟩

end ZagierHoffmanPositiveChar
