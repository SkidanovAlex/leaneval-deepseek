import Submission.ZagierHoffmanProof.StepL20

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L21: the leading member through the (2.11)→(2.13)→(2.14) chain

`leading_member_coeff` tracks the distinguished `a`-output `u` of the Lemma-2.9
relation through the whole chain: the type-1 member `inl u'` (`u' := iterIdx n
(toData R0) u`, the image of `u` through `n` `BC_q`-steps) keeps coefficient
`R0.aA u` through the B*_v step and the prefix `xs` (`prependList_a` +
`ofBstarOver`'s `a`-field + `BCqIter_aA_at`).  `FixedOver.prependList_dep` /
`sPrefix_length` / `leading_member_dep` record the depth bookkeeping: each prepend
adds one, so the leading depth is the iterate depth plus the prefix length
(`j − 1` for Prop 2.12's prefix).  These are the hooks for the leading-tuple = `s`
identification (tuple values via the value-tracking lemmas + `w1Of_add_pnat` +
StepL8 concat).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ The leading member of the whole (2.11)→(2.13)→(2.14) chain: the type-1 member
`inl u'` (`u' := iterIdx n (toData R0) u` — the image of the distinguished output `u`
through the `n` `BC_q`-steps) keeps coefficient `R0.aA u` (and hence `1` when
`R0.aA u = 1`), through the B*_v step and the prefix `xs`. -/
lemma leading_member_coeff (n : ℕ) (R0 : BinaryRel F) (u : R0.ιA) (v : ℕ+)
    (hvalid : ∀ e : ℕ, RelData.level F (RelData.BCqIter F n (toData F R0)) e = 0)
    (hv : ∀ p : (RelData.BCqIter F n (toData F R0)).ιB,
      (v : ℕ) + (((RelData.BCqIter F n (toData F R0)).cB p)
        ⟨0, (RelData.BCqIter F n (toData F R0)).hdepB p⟩ : ℕ) ≤ Nat.card F)
    (xs : List ℕ+) :
    (FixedOver.prependList F
        (ofBstarOver F (RelData.BCqIter F n (toData F R0)) v hvalid hv) xs).a
        (Sum.inl (RelData.iterIdx F n (toData F R0) u)) = R0.aA u := by
  classical
  let D : RelData F := RelData.BCqIter F n (toData F R0)
  let R : FixedOver F (D.ιA ⊕ (D.ιB ⊕ D.ιB)) := ofBstarOver F D v hvalid hv
  calc
    (FixedOver.prependList F R xs).a (Sum.inl (RelData.iterIdx F n (toData F R0) u))
        = R.a (Sum.inl (RelData.iterIdx F n (toData F R0) u)) :=
          FixedOver.prependList_a F R xs (Sum.inl (RelData.iterIdx F n (toData F R0) u))
    _ = D.aA (RelData.iterIdx F n (toData F R0) u) := by rfl
    _ = (toData F R0).aA u := by
          have h1 := RelData.BCqIter_aA_at F n (toData F R0) u
          simpa [D] using h1
    _ = R0.aA u := by rfl



/-- Depths grow by one per prepend: the depth at index `i` after a prefix list is the
original depth plus the list length. -/
lemma FixedOver.prependList_dep {ι : Type} [Fintype ι] (R : FixedOver F ι) (xs : List ℕ+) (i : ι) :
    (FixedOver.prependList F R xs).dep i = R.dep i + xs.length := by
  induction xs generalizing R with
  | nil => simp [FixedOver.prependList]
  | cons x xs ih =>
      change (FixedOver.prependList F (FixedOver.prepend F R x) xs).dep i = R.dep i + (x :: xs).length
      calc
        (FixedOver.prependList F (FixedOver.prepend F R x) xs).dep i
            = (FixedOver.prepend F R x).dep i + xs.length := ih (FixedOver.prepend F R x)
        _ = (R.dep i + 1) + xs.length := by rfl
        _ = R.dep i + (xs.length + 1) := by omega
        _ = R.dep i + (x :: xs).length := by simp

/-- The length of the (2.14) prefix `(s_{j-1}, …, s_1)` is `j − 1`. -/
lemma sPrefix_length (r : ℕ) (s : Fin r → ℕ+) (j : ℕ) (hr1 : 1 ≤ r) (hj : j ≤ r) :
    (sPrefix r s j hr1 hj).length = j - 1 := by
  simp [sPrefix]

/-- The depth of the leading member after the whole chain: original iterate depth
plus the prefix length. -/
lemma leading_member_dep (n : ℕ) (R0 : BinaryRel F) (u : R0.ιA) (v : ℕ+)
    (hvalid : ∀ e : ℕ, RelData.level F (RelData.BCqIter F n (toData F R0)) e = 0)
    (hv : ∀ p : (RelData.BCqIter F n (toData F R0)).ιB,
      (v : ℕ) + (((RelData.BCqIter F n (toData F R0)).cB p)
        ⟨0, (RelData.BCqIter F n (toData F R0)).hdepB p⟩ : ℕ) ≤ Nat.card F)
    (xs : List ℕ+) :
    (FixedOver.prependList F
        (ofBstarOver F (RelData.BCqIter F n (toData F R0)) v hvalid hv) xs).dep
        (Sum.inl (RelData.iterIdx F n (toData F R0) u)) =
      (RelData.BCqIter F n (toData F R0)).depA (RelData.iterIdx F n (toData F R0) u) + 1 + xs.length := by
  classical
  calc
    (FixedOver.prependList F
        (ofBstarOver F (RelData.BCqIter F n (toData F R0)) v hvalid hv) xs).dep
        (Sum.inl (RelData.iterIdx F n (toData F R0) u))
        = (ofBstarOver F (RelData.BCqIter F n (toData F R0)) v hvalid hv).dep
            (Sum.inl (RelData.iterIdx F n (toData F R0) u)) + xs.length := by
          rw [FixedOver.prependList_dep]
    _ = (RelData.BCqIter F n (toData F R0)).depA (RelData.iterIdx F n (toData F R0) u) + 1 + xs.length := by
          rfl


end ZagierHoffmanPositiveChar
