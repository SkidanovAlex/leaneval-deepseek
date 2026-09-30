import Mathlib
import Submission.Work.Pi6.SQM.Defs
import Submission.Work.Pi6.SQM.SqmValLemmas
import Submission.Work.Pi6.SQM.Cup3Identities
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Setup for the mod-2 `∪₃` coboundary formula (`Work.Pi6.SQM.Cup3Cob`)

This file contains the combinatorial skeleton of the proof of

`δ(u ∪₃ v) = u ∪₂ v + v ∪₂ u + (δu) ∪₃ v + u ∪₃ (δv)`

for area SQ's `cup2` and SQM's `cup3`.

## The index set of the identity

For an `(n+m-2)`-simplex `σ`, both sides of the identity are sums of products
`u(F)·v(G)` over explicit families of faces `F` (an `n`-face) and `G` (an `m`-face) of `σ`.
The five families are

* `L3Idx` (`(k,a,b,c)`): the faces of `δ(u∪₃v)(σ)`, coming from the faces `δ_k σ` of `σ` and
  the `∪₃`-configuration `(a,b,c)` of the deleted simplex;
* `T3Idx` (`(a,b,c,j)`): the `j`-th face of the `u`-part of the `(a,b,c)`-term of `(δu)∪₃v`
  together with the `v`-part (`C3`);
* `T4Idx` (`(a,b,c,j)`): the `u`-part of the `(a,b,c)`-term of `u∪₃(δv)` together with the
  `j`-th face of the `v`-part (`C4`);
* `T1Idx` (`(a,b)`): the `(a,b)`-term of `u∪₂v`;
* `T2Idx` (`(a,b)`): the `(a,b)`-term of `v∪₂u`.

The identity follows from a fixed-point-free involution `cup3Swap` of the disjoint union of
these five index sets which preserves the term `cup3Term` and pairs `L3` with the "generic"
`T3`/`T4` indices, the cluster/immovable `T3`/`T4` indices with each other and with `T1`/`T2`.

The involution is the explicit bijection between the differences of the two sides; the
combinatorial content is recorded in `Submission/Work/Pi6/SQM/Cup3Identities.lean`
(the identities `reg1u/v … reg5u/v`, `B1 … B8iii`, `C1u/v … C6u/v`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQM

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff)

/-- The degree of both sides of the `∪₃` coboundary formula. -/
abbrev N3 (n m : ℕ) : ℕ := n + m - 2

/-! ## The five index families -/

/-- The `L`-indices `(k,a,b,c)`: deleted vertex `k` and the `∪₃`-configuration `(a,b,c)`. -/
abbrev L3Idx (n m : ℕ) :=
  {p : Fin ((n + m - 3) + 2) × (Fin (n - 2) × Fin (m - 2) × Fin (n - 2)) //
    p.2.1.val + p.2.2.2.val + 3 ≤ n}

/-- The `T3`-indices `(a,b,c,j)` of `(δu)∪₃v`. -/
abbrev T3Idx (n m : ℕ) :=
  {p : Fin (n - 1) × (Fin (m - 2) × Fin (n - 1) × Fin (n + 2)) //
    p.1.val + p.2.2.1.val + 3 ≤ n + 1}

/-- The `T4`-indices `(a,b,c,j)` of `u∪₃(δv)`. -/
abbrev T4Idx (n m : ℕ) :=
  {p : Fin (n - 2) × (Fin (m - 1) × Fin (n - 2) × Fin (m + 2)) //
    p.1.val + p.2.2.1.val + 3 ≤ n}

/-- The `T1`-indices `(a,b)` of `u ∪₂ v`. -/
abbrev T1Idx (n m : ℕ) := Fin (n - 1) × Fin (m - 1)

/-- The `T2`-indices `(a,b)` of `v ∪₂ u`. -/
abbrev T2Idx (n m : ℕ) := Fin (m - 1) × Fin (n - 1)

/-- The disjoint union of all five index families. -/
abbrev Idx3 (n m : ℕ) :=
  Sum (L3Idx n m) (Sum (T3Idx n m) (Sum (T4Idx n m) (Sum (T1Idx n m) (T2Idx n m))))

/-! ## Accessors and constructors -/

def L3k {n m : ℕ} (p : L3Idx n m) : Fin ((n + m - 3) + 2) := p.1.1
def L3a {n m : ℕ} (p : L3Idx n m) : Fin (n - 2) := p.1.2.1
def L3b {n m : ℕ} (p : L3Idx n m) : Fin (m - 2) := p.1.2.2.1
def L3c {n m : ℕ} (p : L3Idx n m) : Fin (n - 2) := p.1.2.2.2
lemma L3h {n m : ℕ} (p : L3Idx n m) : (L3a p).val + (L3c p).val + 3 ≤ n := p.2

def C3a {n m : ℕ} (p : T3Idx n m) : Fin (n - 1) := p.1.1
def C3b {n m : ℕ} (p : T3Idx n m) : Fin (m - 2) := p.1.2.1
def C3c {n m : ℕ} (p : T3Idx n m) : Fin (n - 1) := p.1.2.2.1
def C3j {n m : ℕ} (p : T3Idx n m) : Fin (n + 2) := p.1.2.2.2
lemma C3h {n m : ℕ} (p : T3Idx n m) : (C3a p).val + (C3c p).val + 3 ≤ n + 1 := p.2

def C4a {n m : ℕ} (p : T4Idx n m) : Fin (n - 2) := p.1.1
def C4b {n m : ℕ} (p : T4Idx n m) : Fin (m - 1) := p.1.2.1
def C4c {n m : ℕ} (p : T4Idx n m) : Fin (n - 2) := p.1.2.2.1
def C4j {n m : ℕ} (p : T4Idx n m) : Fin (m + 2) := p.1.2.2.2
lemma C4h {n m : ℕ} (p : T4Idx n m) : (C4a p).val + (C4c p).val + 3 ≤ n := p.2

def mkL (n m : ℕ) (k a b c : ℕ) (hk : k < (n + m - 3) + 2) (ha : a < n - 2) (hb : b < m - 2)
    (hc : c < n - 2) (h : a + c + 3 ≤ n) : L3Idx n m :=
  ⟨(⟨k, hk⟩, (⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩)), h⟩

def mkT3 (n m : ℕ) (a b c j : ℕ) (ha : a < n - 1) (hb : b < m - 2) (hc : c < n - 1)
    (hj : j < n + 2) (h : a + c + 3 ≤ n + 1) : T3Idx n m :=
  ⟨(⟨a, ha⟩, (⟨b, hb⟩, ⟨c, hc⟩, ⟨j, hj⟩)), h⟩

def mkT4 (n m : ℕ) (a b c j : ℕ) (ha : a < n - 2) (hb : b < m - 1) (hc : c < n - 2)
    (hj : j < m + 2) (h : a + c + 3 ≤ n) : T4Idx n m :=
  ⟨(⟨a, ha⟩, (⟨b, hb⟩, ⟨c, hc⟩, ⟨j, hj⟩)), h⟩

def mkT1 (n m : ℕ) (a b : ℕ) (ha : a < n - 1) (hb : b < m - 1) : T1Idx n m :=
  (⟨a, ha⟩, ⟨b, hb⟩)

def mkT2 (n m : ℕ) (a b : ℕ) (ha : a < m - 1) (hb : b < n - 1) : T2Idx n m :=
  (⟨a, ha⟩, ⟨b, hb⟩)

def idxL {n m : ℕ} (p : L3Idx n m) : Idx3 n m := Sum.inl p
def idxC3 {n m : ℕ} (p : T3Idx n m) : Idx3 n m := Sum.inr (Sum.inl p)
def idxC4 {n m : ℕ} (p : T4Idx n m) : Idx3 n m := Sum.inr (Sum.inr (Sum.inl p))
def idxT1 {n m : ℕ} (p : T1Idx n m) : Idx3 n m := Sum.inr (Sum.inr (Sum.inr (Sum.inl p)))
def idxT2 {n m : ℕ} (p : T2Idx n m) : Idx3 n m := Sum.inr (Sum.inr (Sum.inr (Sum.inr p)))

/-! ## The faces of the five families -/

/-- `u`-face of the `L`-family. -/
def lU (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (k : Fin ((n + m - 3) + 2)) (a : Fin (n - 2))
    (b : Fin (m - 2)) (c : Fin (n - 2)) (h : a.val + c.val + 3 ≤ n) : ⦋n⦌ ⟶ ⦋N3 n m⦌ :=
  cup3U n m a.val (b.val + 1) (c.val + 1) (by have := b.isLt; omega)
      (by have := b.isLt; omega) (by omega) (by omega) ≫
    SimplexCategory.δ (⟨k.val, k.isLt⟩ : Fin ((n + m - 3) + 2)) ≫ shL n m hn hm

/-- `v`-face of the `L`-family. -/
def lV (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (k : Fin ((n + m - 3) + 2)) (a : Fin (n - 2))
    (b : Fin (m - 2)) (c : Fin (n - 2)) (h : a.val + c.val + 3 ≤ n) : ⦋m⦌ ⟶ ⦋N3 n m⦌ :=
  cup3V n m a.val (b.val + 1) (c.val + 1) (by have := b.isLt; omega)
      (by have := b.isLt; omega) (by omega) (by omega) ≫
    SimplexCategory.δ (⟨k.val, k.isLt⟩ : Fin ((n + m - 3) + 2)) ≫ shL n m hn hm

/-- `u`-face of the `C3`-family. -/
def c3U (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (a : Fin (n - 1)) (b : Fin (m - 2))
    (c : Fin (n - 1)) (j : Fin (n + 2)) (h : a.val + c.val + 3 ≤ n + 1) :
    ⦋n⦌ ⟶ ⦋N3 n m⦌ :=
  SimplexCategory.δ j ≫
    (cup3U (n + 1) m a.val (b.val + 1) (c.val + 1) (by have := b.isLt; omega)
        (by have := b.isLt; omega) (by omega) (by omega) ≫ sh3 n m hn hm)

/-- `v`-face of the `C3`-family. -/
def c3V (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (a : Fin (n - 1)) (b : Fin (m - 2))
    (c : Fin (n - 1)) (j : Fin (n + 2)) (h : a.val + c.val + 3 ≤ n + 1) :
    ⦋m⦌ ⟶ ⦋N3 n m⦌ :=
  cup3V (n + 1) m a.val (b.val + 1) (c.val + 1) (by have := b.isLt; omega)
      (by have := b.isLt; omega) (by omega) (by omega) ≫ sh3 n m hn hm

/-- `u`-face of the `C4`-family. -/
def c4U (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (a : Fin (n - 2)) (b : Fin (m - 1))
    (c : Fin (n - 2)) (j : Fin (m + 2)) (h : a.val + c.val + 3 ≤ n) :
    ⦋n⦌ ⟶ ⦋N3 n m⦌ :=
  cup3U n (m + 1) a.val (b.val + 1) (c.val + 1) (by omega)
      (by have := b.isLt; omega) (by omega) (by omega) ≫ sh4 n m hn hm

/-- `v`-face of the `C4`-family. -/
def c4V (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (a : Fin (n - 2)) (b : Fin (m - 1))
    (c : Fin (n - 2)) (j : Fin (m + 2)) (h : a.val + c.val + 3 ≤ n) :
    ⦋m⦌ ⟶ ⦋N3 n m⦌ :=
  SimplexCategory.δ j ≫
    (cup3V n (m + 1) a.val (b.val + 1) (c.val + 1) (by omega)
        (by have := b.isLt; omega) (by omega) (by omega) ≫ sh4 n m hn hm)

/-- `u`-face of the `T1`-family. -/
def t1U (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (a : Fin (n - 1)) (b : Fin (m - 1)) :
    ⦋n⦌ ⟶ ⦋N3 n m⦌ :=
  Work.Pi6.SQ.cup2U n m a.val (b.val + 1) (by omega) (by omega)
    (by have := b.isLt; omega)

/-- `v`-face of the `T1`-family. -/
def t1V (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (a : Fin (n - 1)) (b : Fin (m - 1)) :
    ⦋m⦌ ⟶ ⦋N3 n m⦌ :=
  Work.Pi6.SQ.cup2V n m a.val (b.val + 1) (by omega) (by omega)
    (by have := b.isLt; omega)

/-- `u`-face of the `T2`-family. -/
def t2U (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (a : Fin (m - 1)) (b : Fin (n - 1)) :
    ⦋n⦌ ⟶ ⦋N3 n m⦌ :=
  Work.Pi6.SQ.cup2V m n a.val (b.val + 1) (by omega) (by omega)
      (by have := b.isLt; omega) ≫ shT2 n m hn hm

/-- `v`-face of the `T2`-family. -/
def t2V (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (a : Fin (m - 1)) (b : Fin (n - 1)) :
    ⦋m⦌ ⟶ ⦋N3 n m⦌ :=
  Work.Pi6.SQ.cup2U m n a.val (b.val + 1) (by omega) (by omega)
      (by have := b.isLt; omega) ≫ shT2 n m hn hm

/-- The `u`-face attached to an element of the disjoint union of all index families. -/
def faceU (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) : Idx3 n m → (⦋n⦌ ⟶ ⦋N3 n m⦌) := fun x =>
  match x with
  | Sum.inl p => lU n m hn hm (L3k p) (L3a p) (L3b p) (L3c p) (L3h p)
  | Sum.inr (Sum.inl p) => c3U n m hn hm (C3a p) (C3b p) (C3c p) (C3j p) (C3h p)
  | Sum.inr (Sum.inr (Sum.inl p)) => c4U n m hn hm (C4a p) (C4b p) (C4c p) (C4j p) (C4h p)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl p))) => t1U n m hn hm p.1 p.2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr p))) => t2U n m hn hm p.1 p.2

/-- The `v`-face attached to an element of the disjoint union of all index families. -/
def faceV (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) : Idx3 n m → (⦋m⦌ ⟶ ⦋N3 n m⦌) := fun x =>
  match x with
  | Sum.inl p => lV n m hn hm (L3k p) (L3a p) (L3b p) (L3c p) (L3h p)
  | Sum.inr (Sum.inl p) => c3V n m hn hm (C3a p) (C3b p) (C3c p) (C3j p) (C3h p)
  | Sum.inr (Sum.inr (Sum.inl p)) => c4V n m hn hm (C4a p) (C4b p) (C4c p) (C4j p) (C4h p)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl p))) => t1V n m hn hm p.1 p.2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr p))) => t2V n m hn hm p.1 p.2

/-- The term attached to an element of the disjoint union of all index families. -/
def cup3Term (X : SSet) (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (u : Cochain F2 X n)
    (v : Cochain F2 X m) (σ : X _⦋N3 n m⦌) (x : Idx3 n m) : F2 :=
  genEval F2 X u (X.map (faceU n m hn hm x).op σ) *
    genEval F2 X v (X.map (faceV n m hn hm x).op σ)

@[simp] lemma cup3Term_inl (X : SSet) (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (u : Cochain F2 X n) (v : Cochain F2 X m) (σ : X _⦋N3 n m⦌) (p : L3Idx n m) :
    cup3Term X n m hn hm u v σ (Sum.inl p) =
      genEval F2 X u (X.map (lU n m hn hm (L3k p) (L3a p) (L3b p) (L3c p) (L3h p)).op σ) *
        genEval F2 X v (X.map (lV n m hn hm (L3k p) (L3a p) (L3b p) (L3c p) (L3h p)).op σ) :=
  rfl

@[simp] lemma cup3Term_C3 (X : SSet) (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (u : Cochain F2 X n) (v : Cochain F2 X m) (σ : X _⦋N3 n m⦌) (p : T3Idx n m) :
    cup3Term X n m hn hm u v σ (Sum.inr (Sum.inl p)) =
      genEval F2 X u (X.map (c3U n m hn hm (C3a p) (C3b p) (C3c p) (C3j p) (C3h p)).op σ) *
        genEval F2 X v (X.map (c3V n m hn hm (C3a p) (C3b p) (C3c p) (C3j p) (C3h p)).op σ) :=
  rfl

@[simp] lemma cup3Term_C4 (X : SSet) (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (u : Cochain F2 X n) (v : Cochain F2 X m) (σ : X _⦋N3 n m⦌) (p : T4Idx n m) :
    cup3Term X n m hn hm u v σ (Sum.inr (Sum.inr (Sum.inl p))) =
      genEval F2 X u (X.map (c4U n m hn hm (C4a p) (C4b p) (C4c p) (C4j p) (C4h p)).op σ) *
        genEval F2 X v (X.map (c4V n m hn hm (C4a p) (C4b p) (C4c p) (C4j p) (C4h p)).op σ) :=
  rfl

@[simp] lemma cup3Term_T1 (X : SSet) (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (u : Cochain F2 X n) (v : Cochain F2 X m) (σ : X _⦋N3 n m⦌) (p : T1Idx n m) :
    cup3Term X n m hn hm u v σ (Sum.inr (Sum.inr (Sum.inr (Sum.inl p)))) =
      genEval F2 X u (X.map (t1U n m hn hm p.1 p.2).op σ) *
        genEval F2 X v (X.map (t1V n m hn hm p.1 p.2).op σ) :=
  rfl

@[simp] lemma cup3Term_T2 (X : SSet) (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (u : Cochain F2 X n) (v : Cochain F2 X m) (σ : X _⦋N3 n m⦌) (p : T2Idx n m) :
    cup3Term X n m hn hm u v σ (Sum.inr (Sum.inr (Sum.inr (Sum.inr p)))) =
      genEval F2 X u (X.map (t2U n m hn hm p.1 p.2).op σ) *
        genEval F2 X v (X.map (t2V n m hn hm p.1 p.2).op σ) :=
  rfl

/-- A general conversion: a sum over a subtype is a sum of the `if`-guarded values. -/
lemma sum_subtype_eq_ite {α : Type} [Fintype α] (p : α → Prop) [DecidablePred p] {M : Type}
    [AddCommMonoid M] (g : {x // p x} → M) :
    (∑ x : {x // p x}, g x) = ∑ x : α, if h : p x then g ⟨x, h⟩ else 0 := by
  have hB : (∑ x ∈ Finset.univ.filter p, (if h : p x then g ⟨x,h⟩ else 0)) = ∑ x : {x // p x}, g x := by
    rw [Finset.sum_subtype (s := Finset.univ.filter p) (p := p) (fun x => by simp)
        (fun x => if h : p x then g ⟨x,h⟩ else 0)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [dif_pos x.property]
  have hBC : (∑ x ∈ Finset.univ.filter p, (if h : p x then g ⟨x,h⟩ else 0))
      = ∑ x : α, (if h : p x then g ⟨x,h⟩ else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hp : p x
    · rw [if_pos hp, dif_pos hp]
    · rw [if_neg hp, dif_neg hp]
  rw [← hB, hBC]

/-! ## The pairing involution

`cup3Swap` is the fixed-point-free involution of the disjoint union
`L3Idx ⊕ T3Idx ⊕ T4Idx ⊕ T1Idx ⊕ T2Idx` described in the header: it pairs every term of the
left hand side `δ(u∪₃v)` with a term of the right hand side (through the "generic" regimes
`reg1u/v … reg5u/v`), and pairs the remaining terms of the right hand side among themselves
(the "cluster moves" `B1 … B8iii`) or with `T1`/`T2` (the "immovable" cases `C1u/v … C6u/v`).
-/

/-! ### Which `Cup3Identities` lemma closes which branch

In the two `faceU_swap_*`/`faceV_swap_*` lemmas the goal is, in every branch of the `if`-chain,
an equality of *composites of interval maps*; it is closed either by the corresponding
identity of `Submission/Work/Pi6/SQM/Cup3Identities.lean` (whose hypotheses are the branch
conditions of the `if`-chain) or, for the few branches with no listed identity, by direct
vertex computation (the tactic macro `imap` of `Cup3Identities.lean`, or the same
`refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext; simp only [...]; split_ifs <;> omega`
pattern).

`swapL` (regimes of the deleted vertex `k`, with reg-parameters `(a, b+1, c+1)`):

* `h1 : k ≤ a`                → `reg1u`, `reg1v`
* `h2 : k ≤ a+b+1`            → `reg2u`, `reg2v`
* `h3 : k ≤ a+b+c+2`          → `reg3u`, `reg3v`
* `h4 : k ≤ a+c+m`            → `reg4u`, `reg4v`
* otherwise                   → `reg5u`, `reg5v`

`swapC3` (deleted vertex `j` of the `u`-argument):

* `h1 : j+1 ≤ a`                          → `reg1u`, `reg1v` (reversed)
* `h2 : j = a`, `1 ≤ a`                   → `B1`
* `h2 : j = a`, `a = 0`                   → `C1u`, `C1v`
* `h3 : j = a+1`, `1 ≤ c`                 → `B2i`
* `h3`, `c = 0`, `b+4 ≤ m`                → `B2ii`
* `h3`, `c = 0`, `b = m-3`, `a+3 ≤ n`     → `B2iii`
* `h3`, `c = 0`, `b = m-3`, `a = n-2`     → `C6u`, `C6v`
* `h4 : a+2 ≤ j ≤ a+c+1`                  → `reg3u`, `reg3v` (reversed)
* `h5 : j = a+c+2`, `1 ≤ c`               → `B3i`
* `h5`, `c = 0`, `1 ≤ b`                  → `B3ii`
* `h5`, `c = 0`, `b = 0`, `1 ≤ a`         → `B3iii`
* `h5`, `c = 0`, `b = 0`, `a = 0`         → `C2`
* `h6 : j = a+c+3`, `a+c+3 ≤ n`           → `B8i`
* `h6`, `a+c+2 = n`                       → `C4u`, `C4v`
* otherwise (`j ≥ a+c+4`)                 → `reg5u`, `reg5v` (reversed)

`swapC4` (deleted vertex `j` of the `v`-argument):

* `h1 : j = 0`, `1 ≤ B`                   → `B1` (reversed)
* `h1`, `B = 0`, `1 ≤ C`                  → `B5ii`
* `h1`, `B = C = 0`, `m = 2`              → no listed identity: direct computation
  (`C4(A,0,0,0)` has `u`-face `cup3U n (m+1) A 1 1 ≫ sh4` and `v`-face `δ_0 ≫ cup3V n (m+1) A 1 1 ≫ sh4`)
* `h1`, `B = C = 0`, `m ≥ 3`              → `B3iii` (reversed)
* `h2 : 1 ≤ j ≤ B`                        → `reg2u`, `reg2v` (reversed)
* `h3 : j = B+1`, `1 ≤ B`                 → `B6i`
* `h3`, `B = 0`, `1 ≤ A`                  → `B5ii` (reversed)
* `h3`, `B = A = 0`                       → `C3`
* `h4 : j = B+2`, `B+3 ≤ m`               → `B7i`
* `h4`, `B = m-2`, `A+C+4 ≤ n`            → `B7ii`
* `h4`, `B = m-2`, `A+C+3 = n`            → `C5`
* `h5 : B+3 ≤ j ≤ m`                      → `reg4u`, `reg4v` (reversed)
* `h6 : j = m+1`, `B+3 ≤ m`               → `B8i`
* `h6`, `B = m-2`, `1 ≤ C`                → `B8iii`
* `h6`, `B = m-2`, `C = 0`, `m = 2`       → no listed identity: direct computation
* `h6`, `B = m-2`, `C = 0`, `m ≥ 3`       → `B2iii` (reversed)

`swapT1`, `swapT2`: every branch is `T1`/`T2` ↔ `T3`/`T4` and is closed by the identity above
that has the corresponding `T3`/`T4` index (or, again, by direct computation).
-/

/-- The `L`-family branch of the pairing involution (the five regimes of the deleted vertex). -/
def swapL (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (p : L3Idx n m) : Idx3 n m :=
  have ha := (L3a p).isLt
  have hb := (L3b p).isLt
  have hc := (L3c p).isLt
  have hk := (L3k p).isLt
  have hp := L3h p
  if h1 : (L3k p).val ≤ (L3a p).val then
    idxC3 (mkT3 n m ((L3a p).val + 1) (L3b p).val (L3c p).val (L3k p).val
      (by omega) (by omega) (by omega) (by omega) (by omega))
  else if h2 : (L3k p).val ≤ (L3a p).val + (L3b p).val + 1 then
    idxC4 (mkT4 n m (L3a p).val ((L3b p).val + 1) (L3c p).val ((L3k p).val - (L3a p).val)
      (by omega) (by omega) (by omega) (by omega) (by omega))
  else if h3 : (L3k p).val ≤ (L3a p).val + (L3b p).val + (L3c p).val + 2 then
    idxC3 (mkT3 n m (L3a p).val (L3b p).val ((L3c p).val + 1) ((L3k p).val - (L3b p).val)
      (by omega) (by omega) (by omega) (by omega) (by omega))
  else if h4 : (L3k p).val ≤ (L3a p).val + (L3c p).val + m then
    idxC4 (mkT4 n m (L3a p).val (L3b p).val (L3c p).val
      ((L3k p).val - (L3a p).val - (L3c p).val)
      (by omega) (by omega) (by omega) (by omega) (by omega))
  else
    idxC3 (mkT3 n m (L3a p).val (L3b p).val (L3c p).val ((L3k p).val - m + 3)
      (by omega) (by omega) (by omega) (by omega) (by omega))

/-- The `T3`-family branch of the pairing involution. -/
def swapC3 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (p : T3Idx n m) : Idx3 n m :=
  have ha := (C3a p).isLt
  have hb := (C3b p).isLt
  have hc := (C3c p).isLt
  have hj := (C3j p).isLt
  have hp := C3h p
  if h1 : (C3j p).val + 1 ≤ (C3a p).val then
    idxL (mkL n m (C3j p).val ((C3a p).val - 1) (C3b p).val (C3c p).val
      (by omega) (by omega) (by omega) (by omega) (by omega))
  else if h2 : (C3j p).val = (C3a p).val then
    if h2' : 1 ≤ (C3a p).val then
      idxC4 (mkT4 n m ((C3a p).val - 1) ((C3b p).val + 1) (C3c p).val 0
        (by omega) (by omega) (by omega) (by omega) (by omega))
    else
      idxT2 (mkT2 n m ((C3b p).val + 1) (C3c p).val (by omega) (by omega))
  else if h3 : (C3j p).val = (C3a p).val + 1 then
    if h3' : 1 ≤ (C3c p).val then
      idxC4 (mkT4 n m (C3a p).val ((C3b p).val + 1) ((C3c p).val - 1) ((C3b p).val + 2)
        (by omega) (by omega) (by omega) (by omega) (by omega))
    else if h3'' : (C3b p).val + 4 ≤ m then
      idxC3 (mkT3 n m (C3a p).val ((C3b p).val + 1) 0 ((C3a p).val + 2)
        (by omega) (by omega) (by omega) (by omega) (by omega))
    else if h3''' : (C3a p).val + 3 ≤ n then
      idxC4 (mkT4 n m (C3a p).val (m - 2) 0 (m + 1)
        (by omega) (by omega) (by omega) (by omega) (by omega))
    else
      idxT1 (mkT1 n m (C3a p).val (m - 2) (by omega) (by omega))
  else if h4 : (C3j p).val ≤ (C3a p).val + (C3c p).val + 1 then
    idxL (mkL n m ((C3j p).val + (C3b p).val) (C3a p).val (C3b p).val ((C3c p).val - 1)
      (by omega) (by omega) (by omega) (by omega) (by omega))
  else if h5 : (C3j p).val = (C3a p).val + (C3c p).val + 2 then
    if h5' : 1 ≤ (C3c p).val then
      idxC4 (mkT4 n m (C3a p).val (C3b p).val ((C3c p).val - 1) ((C3b p).val + 2)
        (by omega) (by omega) (by omega) (by omega) (by omega))
    else if h5'' : 1 ≤ (C3b p).val then
      idxC3 (mkT3 n m (C3a p).val ((C3b p).val - 1) 0 ((C3a p).val + 1)
        (by omega) (by omega) (by omega) (by omega) (by omega))
    else if h5''' : 1 ≤ (C3a p).val then
      idxC4 (mkT4 n m ((C3a p).val - 1) 0 0 0
        (by omega) (by omega) (by omega) (by omega) (by omega))
    else
      idxT2 (mkT2 n m 0 0 (by omega) (by omega))
  else if h6 : (C3j p).val = (C3a p).val + (C3c p).val + 3 then
    if h6' : (C3a p).val + (C3c p).val + 3 ≤ n then
      idxC4 (mkT4 n m (C3a p).val (C3b p).val (C3c p).val (m + 1)
        (by omega) (by omega) (by omega) (by omega) (by omega))
    else
      idxT1 (mkT1 n m (C3a p).val (C3b p).val (by omega) (by omega))
  else
    idxL (mkL n m ((C3j p).val + m - 3) (C3a p).val (C3b p).val (C3c p).val
      (by omega) (by omega) (by omega) (by omega) (by omega))

/-- The `T4`-family branch of the pairing involution. -/
def swapC4 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (p : T4Idx n m) : Idx3 n m :=
  have ha := (C4a p).isLt
  have hb := (C4b p).isLt
  have hc := (C4c p).isLt
  have hj := (C4j p).isLt
  have hp := C4h p
  if h1 : (C4j p).val = 0 then
    if h1' : 1 ≤ (C4b p).val then
      idxC3 (mkT3 n m ((C4a p).val + 1) ((C4b p).val - 1) (C4c p).val ((C4a p).val + 1)
        (by omega) (by omega) (by omega) (by omega) (by omega))
    else if h1'' : 1 ≤ (C4c p).val then
      idxC4 (mkT4 n m ((C4a p).val + 1) 0 ((C4c p).val - 1) 1
        (by omega) (by omega) (by omega) (by omega) (by omega))
    else if h1''' : m = 2 then
      if h1'''' : (C4a p).val + 3 = n then
        idxT1 (mkT1 n m ((C4a p).val + 1) 0 (by omega) (by omega))
      else
        idxC4 (mkT4 n m ((C4a p).val + 1) 0 0 3
          (by omega) (by omega) (by omega) (by omega) (by omega))
    else
      idxC3 (mkT3 n m ((C4a p).val + 1) 0 0 ((C4a p).val + 3)
        (by omega) (by omega) (by omega) (by omega) (by omega))
  else if h2 : (C4j p).val ≤ (C4b p).val then
    idxL (mkL n m ((C4j p).val + (C4a p).val) (C4a p).val ((C4b p).val - 1) (C4c p).val
      (by omega) (by omega) (by omega) (by omega) (by omega))
  else if h3 : (C4j p).val ≤ (C4b p).val + 1 then
    if h3' : 1 ≤ (C4b p).val then
      idxC3 (mkT3 n m (C4a p).val ((C4b p).val - 1) ((C4c p).val + 1) ((C4a p).val + 1)
        (by omega) (by omega) (by omega) (by omega) (by omega))
    else if h3'' : 1 ≤ (C4a p).val then
      idxC4 (mkT4 n m ((C4a p).val - 1) 0 ((C4c p).val + 1) 0
        (by omega) (by omega) (by omega) (by omega) (by omega))
    else
      idxT2 (mkT2 n m 0 ((C4c p).val + 1) (by omega) (by omega))
  else if h4 : (C4j p).val ≤ (C4b p).val + 2 then
    if h4' : (C4b p).val + 3 ≤ m then
      idxC3 (mkT3 n m (C4a p).val (C4b p).val ((C4c p).val + 1)
        ((C4a p).val + (C4c p).val + 3)
        (by omega) (by omega) (by omega) (by omega) (by omega))
    else if h4'' : (C4a p).val + (C4c p).val + 4 ≤ n then
      idxC4 (mkT4 n m (C4a p).val (m - 2) ((C4c p).val + 1) (m + 1)
        (by omega) (by omega) (by omega) (by omega) (by omega))
    else
      idxT1 (mkT1 n m (C4a p).val (m - 2) (by omega) (by omega))
  else if h5 : (C4j p).val ≤ m then
    idxL (mkL n m ((C4j p).val + (C4a p).val + (C4c p).val) (C4a p).val (C4b p).val (C4c p).val
      (by omega) (by omega) (by omega) (by omega) (by omega))
  else if h6 : (C4b p).val + 3 ≤ m then
    idxC3 (mkT3 n m (C4a p).val (C4b p).val (C4c p).val ((C4a p).val + (C4c p).val + 3)
      (by omega) (by omega) (by omega) (by omega) (by omega))
  else if h6' : 1 ≤ (C4c p).val then
    idxC4 (mkT4 n m (C4a p).val (m - 2) ((C4c p).val - 1) m
      (by omega) (by omega) (by omega) (by omega) (by omega))
  else if h6'' : m = 2 then
    if h6''' : (C4a p).val = 0 then
      idxT2 (mkT2 n m 0 0 (by omega) (by omega))
    else
      idxC4 (mkT4 n m ((C4a p).val - 1) 0 0 0
        (by omega) (by omega) (by omega) (by omega) (by omega))
  else
    idxC3 (mkT3 n m (C4a p).val (m - 3) 0 ((C4a p).val + 1)
      (by omega) (by omega) (by omega) (by omega) (by omega))

/-- The `T1`-family branch of the pairing involution. -/
def swapT1 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (p : T1Idx n m) : Idx3 n m :=
  have ha := p.1.isLt
  have hb := p.2.isLt
  if h1 : p.2.val + 3 ≤ m then
    idxC3 (mkT3 n m p.1.val p.2.val (n - 2 - p.1.val) (n + 1)
      (by omega) (by omega) (by omega) (by omega) (by omega))
  else if h2 : p.1.val + 3 ≤ n then
    idxC4 (mkT4 n m p.1.val (m - 2) (n - 3 - p.1.val) m
      (by omega) (by omega) (by omega) (by omega) (by omega))
  else if h3 : m = 2 then
    if h3' : n = 2 then
      idxT2 (mkT2 n m 0 0 (by omega) (by omega))
    else
      idxC4 (mkT4 n m (n - 3) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))
  else
    idxC3 (mkT3 n m (n - 2) (m - 3) 0 (n - 1)
      (by omega) (by omega) (by omega) (by omega) (by omega))

/-- The `T2`-family branch of the pairing involution. -/
def swapT2 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (p : T2Idx n m) : Idx3 n m :=
  have ha := p.1.isLt
  have hb := p.2.isLt
  if h1 : 1 ≤ p.1.val then
    idxC3 (mkT3 n m 0 (p.1.val - 1) p.2.val 0
      (by omega) (by omega) (by omega) (by omega) (by omega))
  else if h2 : 1 ≤ p.2.val then
    idxC4 (mkT4 n m 0 0 (p.2.val - 1) 1
      (by omega) (by omega) (by omega) (by omega) (by omega))
  else if h3 : m = 2 then
    if h3' : n = 2 then
      idxT1 (mkT1 n m 0 0 (by omega) (by omega))
    else
      idxC4 (mkT4 n m 0 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))
  else
    idxC3 (mkT3 n m 0 0 0 2 (by omega) (by omega) (by omega) (by omega) (by omega))

/-- The pairing involution (see the header). -/
def cup3Swap (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) : Idx3 n m → Idx3 n m := fun x =>
  match x with
  | Sum.inl p => swapL n m hn hm p
  | Sum.inr (Sum.inl p) => swapC3 n m hn hm p
  | Sum.inr (Sum.inr (Sum.inl p)) => swapC4 n m hn hm p
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl p))) => swapT1 n m hn hm p
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr p))) => swapT2 n m hn hm p

@[simp] lemma cup3Swap_inl (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (p : L3Idx n m) :
    cup3Swap n m hn hm (Sum.inl p) = swapL n m hn hm p := rfl

@[simp] lemma cup3Swap_C3 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (p : T3Idx n m) :
    cup3Swap n m hn hm (Sum.inr (Sum.inl p)) = swapC3 n m hn hm p := rfl

@[simp] lemma cup3Swap_C4 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (p : T4Idx n m) :
    cup3Swap n m hn hm (Sum.inr (Sum.inr (Sum.inl p))) = swapC4 n m hn hm p := rfl

@[simp] lemma cup3Swap_T1 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (p : T1Idx n m) :
    cup3Swap n m hn hm (Sum.inr (Sum.inr (Sum.inr (Sum.inl p)))) = swapT1 n m hn hm p := rfl

@[simp] lemma cup3Swap_T2 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (p : T2Idx n m) :
    cup3Swap n m hn hm (Sum.inr (Sum.inr (Sum.inr (Sum.inr p)))) = swapT2 n m hn hm p := rfl

end

end Work.Pi6.SQM
