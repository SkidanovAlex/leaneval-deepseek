import Submission.ZagierHoffmanProof.StepL13

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L14: FixedRel — the fixed-relation carrier of (2.13)/(2.14)

`FixedRel` packages a fixed relation (one family of tuples all at the same level `d`,
valid at every level).  `FixedRel.level` is its level-`d` value; `FixedRel.prepend`
and `FixedRel.prependList` prepend one entry / a list of entries to every tuple,
preserving validity (Cor 2.6 / the prefix-prepend mechanism of Prop 2.12).
`FixedRel.ofBstar` packages the B*_v output on a RelData (paper (2.13)) as a
`FixedRel` over `D.ιA ⊕ D.ιB ⊕ D.ιB`; `ofBstar_a_term` exposes the family-1
(`a`-side) member at any index.  Prop 2.12's `j−1` prefix prepends (s_{j−1},…,s_1)
are `prependList [s_{j−1},…,s_1] (ofBstar …)`.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- A fixed relation: one family of tuples all at the same level `d`, valid at every
level — the carrier of Prop 2.12's (2.13)/(2.14) fixed relations. -/
structure FixedRel (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)] where
  ι : Type
  fin : Fintype ι
  dep : ι → ℕ
  hdep : ∀ i, 0 < dep i
  c : ∀ i, Fin (dep i) → ℕ+
  a : ι → RatFunc F
  valid : ∀ d : ℕ,
    (∑ i : ι, (((a i : RatFunc F) : RatFunc.CompletionAtInfty F) *
      S F (dep i) (hdep i) (c i) d)) = 0

attribute [instance] FixedRel.fin

/-- The level-`d` value of a fixed relation. -/
noncomputable def FixedRel.level (R : FixedRel F) (d : ℕ) : RatFunc.CompletionAtInfty F :=
  ∑ i : R.ι, (((R.a i : RatFunc F) : RatFunc.CompletionAtInfty F) *
      S F (R.dep i) (R.hdep i) (R.c i) d)

/-- Prepend one entry `x` to every tuple of a fixed relation (Cor 2.6, S-level). -/
noncomputable def FixedRel.prepend (R : FixedRel F) (x : ℕ+) : FixedRel F :=
  { ι := R.ι
    fin := R.fin
    dep := fun i => R.dep i + 1
    hdep := fun i => by
      have hd : 0 < R.dep i := R.hdep i
      omega
    c := fun i => consVec x (R.c i)
    a := R.a
    valid := by
      intro d
      exact fixed_rel_prepend F R.dep R.hdep R.c R.a x R.valid d }

/-- Prepend a list of entries (in order) to every tuple of a fixed relation. -/
noncomputable def FixedRel.prependList (R : FixedRel F) : List ℕ+ → FixedRel F
  | [] => R
  | x :: xs => FixedRel.prependList (FixedRel.prepend F R x) xs

/-- ★ Base case: the empty prefix list is the identity (level values unchanged). -/
lemma FixedRel.prependList_nil_level (R : FixedRel F) (d : ℕ) :
    FixedRel.level F (FixedRel.prependList F R []) d = FixedRel.level F R d := by
  rfl

/-- ★ One recursive prepend step: the level value of the tail list applied to the
one-prepended relation. -/
lemma FixedRel.prependList_cons_level (R : FixedRel F) (x : ℕ+) (xs : List ℕ+) (d : ℕ) :
    FixedRel.level F (FixedRel.prependList F R (x :: xs)) d =
      FixedRel.level F (FixedRel.prependList F (FixedRel.prepend F R x) xs) d := by
  rfl

/-- ★ Validity is preserved by the list prepend (induction over the list): every
level value of the prefixed relation is `0`. -/
lemma FixedRel.prependList_valid (R : FixedRel F) (xs : List ℕ+) (d : ℕ) :
    FixedRel.level F (FixedRel.prependList F R xs) d = 0 := by
  induction xs generalizing R with
  | nil => exact R.valid d
  | cons x xs ih =>
      change FixedRel.level F (FixedRel.prependList F (FixedRel.prepend F R x) xs) d = 0
      exact ih (FixedRel.prepend F R x)



/-- ★ The combined fixed relation of the B*_v output on a RelData `D` with level
validity: family over `D.ιA ⊕ D.ιB ⊕ D.ιB` (family 1 = `a`-tuples with `v` prepended,
families 2,3 = the split `b`-terms).  Paper (2.13) as a `FixedRel`. -/
noncomputable def FixedRel.ofBstar (D : RelData F) (v : ℕ+)
    (hvalid : ∀ e : ℕ, RelData.level F D e = 0)
    (hv : ∀ p : D.ιB, (v : ℕ) + ((D.cB p) ⟨0, D.hdepB p⟩ : ℕ) ≤ Nat.card F) : FixedRel F :=
  { ι := D.ιA ⊕ (D.ιB ⊕ D.ιB)
    fin := by infer_instance
    dep := fun p => match p with
      | Sum.inl i => D.depA i + 1
      | Sum.inr (Sum.inl p') => D.depB p' + 1
      | Sum.inr (Sum.inr p') => D.depB p'
    hdep := by
      intro p
      cases p with
      | inl i => dsimp; omega
      | inr q => cases q with
        | inl p' => dsimp; omega
        | inr p' => dsimp; exact D.hdepB p'
    c := fun p => match p with
      | Sum.inl i => consVec v (D.cA i)
      | Sum.inr (Sum.inl p') => consVec v (D.cB p')
      | Sum.inr (Sum.inr p') => headAdd v (D.hdepB p') (D.cB p')
    a := fun p => match p with
      | Sum.inl i => D.aA i
      | Sum.inr (Sum.inl p') => D.aB p'
      | Sum.inr (Sum.inr p') => D.aB p'
    valid := by
      intro d
      have hb := bstar_pure F (depA := D.depA) (hdepA := D.hdepA) (cA := D.cA) (aA := D.aA)
        (depB := D.depB) (hdepB := D.hdepB) (hB2 := D.hB2) (cB := D.cB) (aB := D.aB)
        v (fun e => by simpa [RelData.level] using hvalid e) hv d
      rw [Fintype.sum_sum_type]
      rw [Fintype.sum_sum_type]
      simpa [add_assoc] using hb }

/-- The level value of the B*_v output is zero at every level. -/
lemma FixedRel.ofBstar_valid (D : RelData F) (v : ℕ+)
    (hvalid : ∀ e : ℕ, RelData.level F D e = 0)
    (hv : ∀ p : D.ιB, (v : ℕ) + ((D.cB p) ⟨0, D.hdepB p⟩ : ℕ) ≤ Nat.card F) (d : ℕ) :
    FixedRel.level F (FixedRel.ofBstar F D v hvalid hv) d = 0 := by
  exact (FixedRel.ofBstar F D v hvalid hv).valid d

/-- The `a`-side of the B*_v fixed relation (family 1): the coefficient at index
`i : D.ιA` is `D.aA i` and its tuple is `v :: (D.cA i)`. -/
lemma FixedRel.ofBstar_a_term (D : RelData F) (v : ℕ+)
    (hvalid : ∀ e : ℕ, RelData.level F D e = 0)
    (hv : ∀ p : D.ιB, (v : ℕ) + ((D.cB p) ⟨0, D.hdepB p⟩ : ℕ) ≤ Nat.card F)
    (i : D.ιA) (d : ℕ) :
    (((FixedRel.ofBstar F D v hvalid hv).a (Sum.inl i) : RatFunc F) :
        RatFunc.CompletionAtInfty F) *
        S F ((FixedRel.ofBstar F D v hvalid hv).dep (Sum.inl i))
          ((FixedRel.ofBstar F D v hvalid hv).hdep (Sum.inl i))
          ((FixedRel.ofBstar F D v hvalid hv).c (Sum.inl i)) d =
      ((D.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
        S F (D.depA i + 1) (by omega : 0 < D.depA i + 1) (consVec v (D.cA i)) d := by
  rfl



end ZagierHoffmanPositiveChar
