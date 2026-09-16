import Submission.ZagierHoffmanProof.StepL60
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L63: member-head facts — B*_v a-side head (item (2), core)

Item (2) of the main2_case1_j1 dispatch (PLAN SESSION 213 NOTE): the type-1/type-2
member head at x = 0 is the B*_{s₁} (ofBstarOver) head — at k=2, j=1 the prependList
prefix sPrefix r s 1 is EMPTY (length j−1 = 0), so Q.c (Sum.inl ·) = Bs.c (Sum.inl ·)
= consVec s₁ (D.cA i).  This module commits the core facts (all sorry-free):
  bstar_c_inl : (ofBstarOver D v).c (Sum.inl i) = consVec v (D.cA i)  [rfl — the
    c-field of ofBstarOver is definitionally consVec v (D.cA i)];
  ★ bstar_c_inl_head : pad0 ((ofBstarOver D v).c (Sum.inl i)) 0 = (v : ℕ)
    [pad0_of_lt at the hdep index + dsimp + consVec_zero, aligned by simpa].
With Bs := ofBstarOver F D s₁ (the empty-prependList identification Q = Bs and the
iterIdx F 0 identity at n = 0), these give pad0 (Q.c (Sum.inl (iterIdx … i₀))) 0 =
(s₁ : ℕ) = pad0 s 0 for every type-1 member — the kAdm_one_iff_front input.  The
type-2 head is the same statement with Sum.inr (Sum.inl i) and consVec v (D.cB i).
NEXT: instantiate at the package (k=2, j=1) to the Q-level member-head lemma, then
the hid fold and admExp_combine splice of main2_case1_j1.  Named gates unchanged.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Type-1 member tuple of B*_v: `(ofBstarOver D v).c (Sum.inl i)` is `v :: (D.cA i)`. -/
lemma bstar_c_inl (D : RelData F) (v : ℕ+)
    (hvalid : ∀ e : ℕ, RelData.level F D e = 0)
    (hv : ∀ p : D.ιB, (v : ℕ) + ((D.cB p) ⟨0, D.hdepB p⟩ : ℕ) ≤ Nat.card F)
    (i : D.ιA) :
    (ofBstarOver F D v hvalid hv).c (Sum.inl i) = consVec v (D.cA i) := by
  rfl

/-- ★ The B*_v a-side member head: pad0 at index 0 is v. -/
lemma bstar_c_inl_head (D : RelData F) (v : ℕ+)
    (hvalid : ∀ e : ℕ, RelData.level F D e = 0)
    (hv : ∀ p : D.ιB, (v : ℕ) + ((D.cB p) ⟨0, D.hdepB p⟩ : ℕ) ≤ Nat.card F)
    (i : D.ιA) :
    pad0 ((ofBstarOver F D v hvalid hv).c (Sum.inl i)) 0 = (v : ℕ) := by
  classical
  have hdep : 0 < (ofBstarOver F D v hvalid hv).dep (Sum.inl i) :=
    (ofBstarOver F D v hvalid hv).hdep (Sum.inl i)
  rw [pad0_of_lt ((ofBstarOver F D v hvalid hv).c (Sum.inl i)) hdep]
  dsimp [ofBstarOver]
  have hv0 := consVec_zero v (D.cA i)
  simpa using congrArg (fun t : ℕ+ => (t : ℕ)) hv0
end ZagierHoffmanPositiveChar
