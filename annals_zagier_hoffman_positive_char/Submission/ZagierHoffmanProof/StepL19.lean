import Submission.ZagierHoffmanProof.StepL18

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L19: FixedOver — the prefix recursion over a constant index type

`FixedOver F ι` is a fixed relation over a FIXED index type `ι` (no `ι` field, unlike
`FixedRel`).  Because `FixedOver.prepend` / `FixedOver.prependList` keep `ι` constant,
the level sum of the fully prefixed relation remains a sum over `ι` and is
partitionable by `triple_sum_split` (StepL18) with no depth-domain gymnastics.
`ofBstarOver` packages the B*_v output (`FixedRel.ofBstar` content) as a `FixedOver`
over `D.ιA ⊕ (D.ιB ⊕ D.ιB)`; `prefixed_a_member` identifies the type-1 members of the
prefixed relation (coefficient `D.aA i` at `inl i`).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- A fixed relation over a FIXED index type `ι` (no `ι` field): the prefix-prepend
recursion keeps `ι` constant, so the final level sum is partitionable by
`triple_sum_split` without any depth-domain gymnastics. -/
structure FixedOver (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]
    (ι : Type) [Fintype ι] where
  dep : ι → ℕ
  hdep : ∀ i, 0 < dep i
  c : ∀ i, Fin (dep i) → ℕ+
  a : ι → RatFunc F
  valid : ∀ d : ℕ,
    (∑ i : ι, (((a i : RatFunc F) : RatFunc.CompletionAtInfty F) *
      S F (dep i) (hdep i) (c i) d)) = 0

/-- The level-`d` value of a `FixedOver`. -/
noncomputable def FixedOver.level {ι : Type} [Fintype ι] (R : FixedOver F ι) (d : ℕ) : RatFunc.CompletionAtInfty F :=
  ∑ i : ι, (((R.a i : RatFunc F) : RatFunc.CompletionAtInfty F) *
      S F (R.dep i) (R.hdep i) (R.c i) d)

/-- Prepend one entry `x` to every tuple (index type unchanged). -/
noncomputable def FixedOver.prepend {ι : Type} [Fintype ι] (R : FixedOver F ι) (x : ℕ+) : FixedOver F ι :=
  { dep := fun i => R.dep i + 1
    hdep := fun i => by
      have hd : 0 < R.dep i := R.hdep i
      omega
    c := fun i => consVec x (R.c i)
    a := R.a
    valid := by
      intro d
      exact fixed_rel_prepend F R.dep R.hdep R.c R.a x R.valid d }

/-- Prepend a list of entries (in order), keeping the index type. -/
noncomputable def FixedOver.prependList {ι : Type} [Fintype ι] (R : FixedOver F ι) : List ℕ+ → FixedOver F ι
  | [] => R
  | x :: xs => FixedOver.prependList (FixedOver.prepend F R x) xs

/-- ★ Base case and recursive push (rfl). -/
lemma FixedOver.prependList_nil_level {ι : Type} [Fintype ι] (R : FixedOver F ι) (d : ℕ) :
    FixedOver.level F (FixedOver.prependList F R []) d = FixedOver.level F R d := by rfl

lemma FixedOver.prependList_cons_level {ι : Type} [Fintype ι] (R : FixedOver F ι) (x : ℕ+) (xs : List ℕ+) (d : ℕ) :
    FixedOver.level F (FixedOver.prependList F R (x :: xs)) d =
      FixedOver.level F (FixedOver.prependList F (FixedOver.prepend F R x) xs) d := by rfl

/-- ★ Validity is preserved: every level value of the prefixed relation is `0`. -/
lemma FixedOver.prependList_valid {ι : Type} [Fintype ι] (R : FixedOver F ι) (xs : List ℕ+) (d : ℕ) :
    FixedOver.level F (FixedOver.prependList F R xs) d = 0 := by
  induction xs generalizing R with
  | nil => exact R.valid d
  | cons x xs ih =>
      change FixedOver.level F (FixedOver.prependList F (FixedOver.prepend F R x) xs) d = 0
      exact ih (FixedOver.prepend F R x)

/-- Coefficients are untouched by prepends (index type is fixed). -/
lemma FixedOver.prependList_a {ι : Type} [Fintype ι] (R : FixedOver F ι) (xs : List ℕ+) (i : ι) :
    (FixedOver.prependList F R xs).a i = R.a i := by
  induction xs generalizing R with
  | nil => rfl
  | cons x xs ih =>
      change (FixedOver.prependList F (FixedOver.prepend F R x) xs).a i = R.a i
      calc
        (FixedOver.prependList F (FixedOver.prepend F R x) xs).a i = (FixedOver.prepend F R x).a i := ih (FixedOver.prepend F R x)
        _ = R.a i := by rfl

/-- The combined (2.13) fixed relation as a `FixedOver` over `D.ιA ⊕ (D.ιB ⊕ D.ιB)`. -/
noncomputable def ofBstarOver (D : RelData F) (v : ℕ+)
    (hvalid : ∀ e : ℕ, RelData.level F D e = 0)
    (hv : ∀ p : D.ιB, (v : ℕ) + ((D.cB p) ⟨0, D.hdepB p⟩ : ℕ) ≤ Nat.card F) :
    FixedOver F (D.ιA ⊕ (D.ιB ⊕ D.ιB)) :=
  { dep := fun p => match p with
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

/-- ★ Type-1 members of the prefixed (2.13) relation: at `inl i` the coefficient is
`D.aA i` and the tuple is the prefix-prepend of `v :: (D.cA i)`; here we record the
coefficient identification (used by the leading-term argument). -/
lemma prefixed_a_member (D : RelData F) (v : ℕ+)
    (hvalid : ∀ e : ℕ, RelData.level F D e = 0)
    (hv : ∀ p : D.ιB, (v : ℕ) + ((D.cB p) ⟨0, D.hdepB p⟩ : ℕ) ≤ Nat.card F)
    (xs : List ℕ+) (i : D.ιA) :
    (FixedOver.prependList F (ofBstarOver F D v hvalid hv) xs).a (Sum.inl i) = D.aA i := by
  calc
    (FixedOver.prependList F (ofBstarOver F D v hvalid hv) xs).a (Sum.inl i)
        = (ofBstarOver F D v hvalid hv).a (Sum.inl i) := FixedOver.prependList_a F (ofBstarOver F D v hvalid hv) xs (Sum.inl i)
    _ = D.aA i := by rfl

end ZagierHoffmanPositiveChar
