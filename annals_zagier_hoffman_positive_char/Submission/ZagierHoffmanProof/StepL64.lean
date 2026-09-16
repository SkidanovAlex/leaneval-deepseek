import Submission.ZagierHoffmanProof.StepL63
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L64: member-head instantiation at Q (k = 2, j = 1) — item (2) complete

The Q-level member-head instantiation of main2_case1_j1 (PLAN SESSION 209+): at
k = 2, j = 1 the prependList prefix sPrefix r s 1 is EMPTY (length j − 1 = 0), so
Q = Bs (prependList Bs [] = Bs by rfl) and every member head at index 0 is the
B*_{s₁} head:
  ★ q_type1_member_head (r s hcase hs1v R0 hbhd) : ∀ i₀ : R0.ιA,
      pad0 (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) 0 = (s⟨0⟩ : ℕ);
  ★ q_type2_member_head : ∀ i : D.ιB,
      pad0 (Q.c (Sum.inr (Sum.inl i))) 0 = (s⟨0⟩ : ℕ).
  (with the lets D := BCqIter F 0 (toData F R0), Bs := ofBstarOver F D (s⟨0⟩) …,
  Q := prependList F Bs (sPrefix r s 1 …)).
  Proof: dsimp [Q, Bs, D]; sPrefix r s 1 = [] by simp [sPrefix]; rw; exact
  bstar_c_inl_head / bstar_c_inr_inl_head (the B*-head facts of StepL63/this
  module).  The iterIdx F 0 index is used directly (no identity needed — it is the
  inl-index of Bs's a-family, D.ιA-defeq).
Also commits the B*-level type-2 facts: bstar_c_inr_inl (rfl: c (inr (inl i)) =
consVec v (D.cB i)) and bstar_c_inr_inl_head (pad0 … 0 = v).
Together with StepL63 these give every type-1/type-2 member's head value
pad0 (member) 0 = (s₁ : ℕ) = pad0 s 0 ≤ q (1-adm of s) — the kAdm_one_iff_front
input — completing item (2).  NEXT: the type-3 head (front s₁+1 via
type3_sjadd_one_at at position 0, already pinned) then the hid fold and
admExp_combine splice of main2_case1_j1.  Named gates unchanged.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Q-level type-1 member head at k=2, j=1: with the empty sPrefix, Q = Bs and the
member head (iterIdx-wrapped Sum.inl) is s₁ = pad0 s 0. -/
lemma q_type1_member_head (r : ℕ) (s : Fin r → ℕ+) (hcase : 2 ≤ r)
    (hs1v : (s ⟨0, by omega⟩ : ℕ) + 1 ≤ Nat.card F)
    (R0 : BinaryRel F) (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F 0 (toData F R0)
    let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
        (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
    ∀ i₀ : R0.ιA,
      pad0 (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) 0 =
        (s ⟨0, by omega⟩ : ℕ) := by
  classical
  intro D Bs Q
  intro i₀
  dsimp [Q, Bs, D]
  have hpre : sPrefix r s 1 (by omega : 1 ≤ r) (by omega : 1 ≤ r) = [] := by
    simp [sPrefix]
  rw [hpre]
  exact bstar_c_inl_head F (RelData.BCqIter F 0 (toData F R0)) (s ⟨0, by omega⟩)
    (fun e => BCqIter_valid F 0 R0 e)
    (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
    (RelData.iterIdx F 0 (toData F R0) i₀)

/-- Type-2 member tuple of B*_v: `(ofBstarOver D v).c (Sum.inr (Sum.inl i))` is
`v :: (D.cB i)`. -/
lemma bstar_c_inr_inl (D : RelData F) (v : ℕ+)
    (hvalid : ∀ e : ℕ, RelData.level F D e = 0)
    (hv : ∀ p : D.ιB, (v : ℕ) + ((D.cB p) ⟨0, D.hdepB p⟩ : ℕ) ≤ Nat.card F)
    (i : D.ιB) :
    (ofBstarOver F D v hvalid hv).c (Sum.inr (Sum.inl i)) = consVec v (D.cB i) := by
  rfl

/-- The B*_v type-2 member head: pad0 at index 0 is v. -/
lemma bstar_c_inr_inl_head (D : RelData F) (v : ℕ+)
    (hvalid : ∀ e : ℕ, RelData.level F D e = 0)
    (hv : ∀ p : D.ιB, (v : ℕ) + ((D.cB p) ⟨0, D.hdepB p⟩ : ℕ) ≤ Nat.card F)
    (i : D.ιB) :
    pad0 ((ofBstarOver F D v hvalid hv).c (Sum.inr (Sum.inl i))) 0 = (v : ℕ) := by
  classical
  have hdep : 0 < (ofBstarOver F D v hvalid hv).dep (Sum.inr (Sum.inl i)) :=
    (ofBstarOver F D v hvalid hv).hdep (Sum.inr (Sum.inl i))
  rw [pad0_of_lt ((ofBstarOver F D v hvalid hv).c (Sum.inr (Sum.inl i))) hdep]
  dsimp [ofBstarOver]
  have hv0 := consVec_zero v (D.cB i)
  simpa using congrArg (fun t : ℕ+ => (t : ℕ)) hv0

/-- Q-level type-2 member head at k=2, j=1: the member head (Sum.inr (Sum.inl i))
is s₁ = pad0 s 0. -/
lemma q_type2_member_head (r : ℕ) (s : Fin r → ℕ+) (hcase : 2 ≤ r)
    (hs1v : (s ⟨0, by omega⟩ : ℕ) + 1 ≤ Nat.card F)
    (R0 : BinaryRel F) (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F 0 (toData F R0)
    let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
        (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
    ∀ i : D.ιB,
      pad0 (Q.c (Sum.inr (Sum.inl i))) 0 = (s ⟨0, by omega⟩ : ℕ) := by
  classical
  intro D Bs Q
  intro i
  dsimp [Q, Bs, D]
  have hpre : sPrefix r s 1 (by omega : 1 ≤ r) (by omega : 1 ≤ r) = [] := by
    simp [sPrefix]
  rw [hpre]
  exact bstar_c_inr_inl_head F (RelData.BCqIter F 0 (toData F R0)) (s ⟨0, by omega⟩)
    (fun e => BCqIter_valid F 0 R0 e)
    (RelData.iterate_merge_hv F 0 R0 (s ⟨0, by omega⟩) (by omega) hbhd) i

end ZagierHoffmanPositiveChar
