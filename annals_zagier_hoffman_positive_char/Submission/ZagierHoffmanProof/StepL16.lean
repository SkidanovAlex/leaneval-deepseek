import Submission.ZagierHoffmanProof.StepL15

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L16: the prefixed chain validity (2.11)→(2.13)→(2.14)

`RelData.iterate_merge_hv` derives the B*_v merge condition on the `n`-iterate from
`v + 1 ≤ q` and `1`-headed `b`-tuples (`BCqIter_head_one`).  `prefixed_ofBstar_valid`
is the crank of Prop 2.12's prefix step: `level (prependList xs (ofBstar D v)) d = 0`
at every level, directly from `FixedRel.prependList_valid`.
★ `chain_prefix_valid` is the full composite validity: from the `n`-iterate of a
BinaryRel, apply B*_v and then an arbitrary prefix list — the fixed relation is valid
at every level.  This is paper (2.11)→(2.13)→(2.14) as a committed theorem.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The merge condition for B*_v on the `n`-iterate follows from `v + 1 ≤ q` and the
`1`-headedness of `R`'s `b`-tuples. -/
lemma RelData.iterate_merge_hv (n : ℕ) (R : BinaryRel F) (v : ℕ+)
    (hvq : (v : ℕ) + 1 ≤ Nat.card F)
    (hbhead : ∀ j : R.ιB, ((R.cB j) ⟨0, R.hdepB j⟩ : ℕ) = 1) :
    ∀ p : (RelData.BCqIter F n (toData F R)).ιB,
      (v : ℕ) + (((RelData.BCqIter F n (toData F R)).cB p)
        ⟨0, (RelData.BCqIter F n (toData F R)).hdepB p⟩ : ℕ) ≤ Nat.card F := by
  classical
  intro p
  have hh := RelData.BCqIter_head_one F n R hbhead p
  -- hh : head of (BCqIter n (toData R)).cB p = oneExp ; value = 1
  have hv1 : (((RelData.BCqIter F n (toData F R)).cB p)
      ⟨0, (RelData.BCqIter F n (toData F R)).hdepB p⟩ : ℕ) = 1 := by
    calc
      (((RelData.BCqIter F n (toData F R)).cB p)
          ⟨0, (RelData.BCqIter F n (toData F R)).hdepB p⟩ : ℕ) = (oneExp : ℕ) := by
        simpa using congrArg (fun t : ℕ+ => (t : ℕ)) hh
      _ = 1 := by simp [oneExp]
  omega

/-- ★ The prefixed B*_v output is valid at every level (paper (2.13) followed by the
prefix prepends): `level (prependList xs (ofBstar D v)) d = 0`.  Plug of
`FixedRel.prependList_valid`. -/
theorem prefixed_ofBstar_valid (D : RelData F) (v : ℕ+) (xs : List ℕ+)
    (hvalid : ∀ e : ℕ, RelData.level F D e = 0)
    (hv : ∀ p : D.ιB, (v : ℕ) + ((D.cB p) ⟨0, D.hdepB p⟩ : ℕ) ≤ Nat.card F) (d : ℕ) :
    FixedRel.level F (FixedRel.prependList F (FixedRel.ofBstar F D v hvalid hv) xs) d = 0 := by
  exact FixedRel.prependList_valid F (FixedRel.ofBstar F D v hvalid hv) xs d

/-- ★ The full chain from the `n`-iterate of a BinaryRel: B*_v then any prefix list,
valid at every level — the composite of `bstar_iterated` (StepL13) with the
`prependList` mechanism (StepL14).  This is paper (2.11)→(2.13)→(2.14) validity. -/
theorem chain_prefix_valid (n : ℕ) (R : BinaryRel F) (v : ℕ+) (xs : List ℕ+)
    (hvq : (v : ℕ) + 1 ≤ Nat.card F)
    (hbhead : ∀ j : R.ιB, ((R.cB j) ⟨0, R.hdepB j⟩ : ℕ) = 1) (d : ℕ) :
    FixedRel.level F (FixedRel.prependList F
        (FixedRel.ofBstar F (RelData.BCqIter F n (toData F R)) v
          (fun e => BCqIter_valid F n R e)
          (RelData.iterate_merge_hv F n R v hvq hbhead)) xs) d = 0 := by
  exact prefixed_ofBstar_valid F (RelData.BCqIter F n (toData F R)) v xs
    (fun e => BCqIter_valid F n R e)
    (RelData.iterate_merge_hv F n R v hvq hbhead) d

end ZagierHoffmanPositiveChar
