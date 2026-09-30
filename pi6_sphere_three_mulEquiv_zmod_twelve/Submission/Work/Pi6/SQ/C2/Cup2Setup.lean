import Mathlib
import Submission.Work.Pi6.SQM.Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Setup for the mod-2 `∪₂` coboundary formula (`Work.Pi6.SQM.Cup2Cob`)

This file contains the combinatorial skeleton of the proof of

`δ(u ∪₂ v) = u ∪₁ v + v ∪₁ u + (δu) ∪₂ v + u ∪₂ (δv)`

for area SQ's `Work.Pi6.SQ.cup2` and `Work.Pi6.SQ.cup1m`.

## The index set of the identity

For an `(n+m-1)`-simplex `σ`, both sides of the identity are sums of products
`u(F)·v(G)` over explicit families of faces `F` (an `n`-face) and `G` (an `m`-face) of `σ`:

* `L`  (index of the form `(k,a,b)`): the faces of `δ(u∪₂v)(σ)`, coming from the faces
  `δ_k σ` of `σ` and the `(a,b)`-term of `u∪₂v`;
* `C3` (`(A,B,j)`): the `j`-th face of the `u`-part of the `(A,B)`-term of `(δu)∪₂v`
  together with the `v`-part;
* `C4` (`(A,B,j)`): the `u`-part of `(A,B)`-term of `u∪₂(δv)` together with the `j`-th
  face of the `v`-part;
* `T1` (`s`): the `s`-th term of `u∪₁v` (from `cup1m n m u v`);
* `T2` (`s`): the `s`-th term of `v∪₁u` (from `cup1m m n v u`).

The identity then follows from a fixed-point-free involution `cobSwap` of the disjoint union
of these five index sets which preserves the term, pairs `L` with the "generic" `C3`/`C4`
indices and pairs the remaining `C3`/`C4` indices with each other and with `T1`/`T2`.
The involution is the combinatorial content of the classical "interval" proof of the
cup-2 coboundary formula: it is the explicit bijection between the differences of the two
sides, verified numerically by `scratch/design5.py`.

Since all faces are described by order maps `⦋n⦌ ⟶ ⦋n+m-1⦌` (resp. `⦋m⦌ ⟶ ⦋n+m-1⦌`), the
term functions below are the natural ones.
-/

set_option maxHeartbeats 3200000


open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQ.C2

open Work.Pi6.SQM (F2)

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff)

/-! ## Degree-shift maps

The four RHS terms live in degree `n+m-1` but are built from cochains in degrees
`(n+1)+m-2`, `n+(m+1)-2`, `m+n-1`, `n+m-1`; the corresponding `shmap`s are the degree
identifications appearing in the statement. -/

/-- The shift `(n+1)+m-2 = n+m-1`. -/
def shv (n m : ℕ) : ⦋(n + 1) + m - 2⦌ ⟶ ⦋n + m - 1⦌ :=
  Work.Cohomology.shmap ((n + 1) + m - 2) (n + m - 1) (by omega)

/-- The shift `n+(m+1)-2 = n+m-1`. -/
def shu (n m : ℕ) : ⦋n + (m + 1) - 2⦌ ⟶ ⦋n + m - 1⦌ :=
  Work.Cohomology.shmap (n + (m + 1) - 2) (n + m - 1) (by omega)

/-- The shift `m+n-1 = n+m-1`. -/
def sh1 (n m : ℕ) : ⦋m + n - 1⦌ ⟶ ⦋n + m - 1⦌ :=
  Work.Cohomology.shmap (m + n - 1) (n + m - 1) (by omega)

/-- The shift `n+m-1 = m+n-1`. -/
def sh2 (n m : ℕ) : ⦋n + m - 1⦌ ⟶ ⦋m + n - 1⦌ :=
  Work.Cohomology.shmap (n + m - 1) (m + n - 1) (by omega)

@[simp] lemma shv_val (n m : ℕ) (i : Fin (((n + 1) + m - 2) + 1)) :
    ((ConcreteCategory.hom (shv n m)) i).val = i.val := Work.Cohomology.shmap_val _ _ _ i

@[simp] lemma shu_val (n m : ℕ) (i : Fin ((n + (m + 1) - 2) + 1)) :
    ((ConcreteCategory.hom (shu n m)) i).val = i.val := Work.Cohomology.shmap_val _ _ _ i

@[simp] lemma sh1_val (n m : ℕ) (i : Fin ((m + n - 1) + 1)) :
    ((ConcreteCategory.hom (sh1 n m)) i).val = i.val := Work.Cohomology.shmap_val _ _ _ i

@[simp] lemma sh2_val (n m : ℕ) (i : Fin ((n + m - 1) + 1)) :
    ((ConcreteCategory.hom (sh2 n m)) i).val = i.val := Work.Cohomology.shmap_val _ _ _ i

/-- The face map deleting the vertex `k` of an `(n+m-2)`-simplex. -/
def delv (n m : ℕ) (k : ℕ) (_hk : k < n + m) (h2 : 2 ≤ n + m) :
    ⦋n + m - 2⦌ ⟶ ⦋n + m - 1⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i => ⟨if i.val < k then i.val else i.val + 1, by
        have := i.isLt; simp only [SimplexCategory.len_mk] at this ⊢
        split_ifs <;> omega⟩
      monotone' := fun i j hij => by
        simp only [Fin.le_def] at hij ⊢
        split_ifs <;> omega }

@[simp] lemma delv_val (n m k : ℕ) (hk : k < n + m) (h2 : 2 ≤ n + m)
    (i : Fin ((n + m - 2) + 1)) :
    ((ConcreteCategory.hom (delv n m k hk h2)) i).val = if i.val < k then i.val else i.val + 1 := rfl

/-- `delv` is the composite "delete the `k`-th vertex, then reindex". -/
lemma delv_eq (n m k : ℕ) (hk : k < n + m) (h2 : 2 ≤ n + m)
    (h : (n + m - 2) + 1 = n + m - 1) :
    delv n m k hk h2 = SimplexCategory.δ (⟨k, by omega⟩ : Fin ((n + m - 2) + 2)) ≫
      Work.Cohomology.shmap ((n + m - 2) + 1) (n + m - 1) h := by
  refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
  apply Fin.ext
  rw [CategoryTheory.comp_apply, Work.Cohomology.shmap_val, SimplexCategory.coe_δ, delv_val,
    Work.Cohomology.succAbove_val_if']

/-! ## Helper lemmas for the face computations -/

/-- Two order maps are equal if they have the same vertex values. -/
lemma hom_ext_val {p N : ℕ} {φ ψ : ⦋p⦌ ⟶ ⦋N⦌}
    (h : ∀ i : Fin (p + 1), ((ConcreteCategory.hom φ) i).val = ((ConcreteCategory.hom ψ) i).val) :
    φ = ψ := by
  refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
  apply Fin.ext
  exact h i

/-- `shmap` does not depend on the proof of the degree equality. -/
lemma shmap_congr {p q : ℕ} (h h' : p = q) :
    Work.Cohomology.shmap p q h = Work.Cohomology.shmap p q h' := by
  rw [Subsingleton.elim h h']

/-! ## The index sets -/

/-- Index of the `δ(u∪₂v)`-sum: `(k,a,b)`. -/
abbrev LIdx (n m : ℕ) := Fin (n + m) × (Fin (n - 1) × Fin (m - 1))

/-- Index of the `(δu)∪₂v`-sum: `(A,B,j)`. -/
abbrev C3Idx (n m : ℕ) := Fin n × (Fin (m - 1) × Fin (n + 2))

/-- Index of the `u∪₂(δv)`-sum: `(A,B,j)`. -/
abbrev C4Idx (n m : ℕ) := Fin (n - 1) × (Fin m × Fin (m + 2))

/-- The disjoint union of all five index families. -/
abbrev cobIdx (n m : ℕ) :=
  Sum (LIdx n m) (Sum (C3Idx n m) (Sum (C4Idx n m) (Sum (Fin n) (Fin m))))

/-! ## Value lemmas for the interval maps of `Work.Pi6.SQ` -/

@[simp] lemma cup2U_apply_val (n m a b : ℕ) (ha : a + 2 ≤ n) (hb1 : 1 ≤ b) (hb3 : b + 1 ≤ m)
    (i : Fin (n + 1)) :
    ((ConcreteCategory.hom (Work.Pi6.SQ.cup2U n m a b ha hb1 hb3)) i).val
      = if i.val ≤ a then i.val else i.val + (b - 1) := rfl

@[simp] lemma cup2V_apply_val (n m a b : ℕ) (ha : a + 2 ≤ n) (hb1 : 1 ≤ b) (hb3 : b + 1 ≤ m)
    (j : Fin (m + 1)) :
    ((ConcreteCategory.hom (Work.Pi6.SQ.cup2V n m a b ha hb1 hb3)) j).val
      = if j.val ≤ b then a + j.val else j.val + (n - 2) := rfl

/-! ## The faces of the five families -/

/-- `u`-face of the `L`-family. -/
def lU (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (k : Fin (n + m)) (a : Fin (n - 1))
    (b : Fin (m - 1)) : ⦋n⦌ ⟶ ⦋n + m - 1⦌ :=
  Work.Pi6.SQ.cup2U n m a.val (b.val + 1) (by omega) (by omega) (by omega) ≫
    delv n m k.val (by omega) (by omega)

/-- `v`-face of the `L`-family. -/
def lV (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (k : Fin (n + m)) (a : Fin (n - 1))
    (b : Fin (m - 1)) : ⦋m⦌ ⟶ ⦋n + m - 1⦌ :=
  Work.Pi6.SQ.cup2V n m a.val (b.val + 1) (by omega) (by omega) (by omega) ≫
    delv n m k.val (by omega) (by omega)

/-- `u`-face of the `C3`-family. -/
def c3U (n m : ℕ) (A : Fin n) (B : Fin (m - 1)) (j : Fin (n + 2)) : ⦋n⦌ ⟶ ⦋n + m - 1⦌ :=
  SimplexCategory.δ j ≫
    (Work.Pi6.SQ.cup2U (n + 1) m A.val (B.val + 1) (by omega) (by omega) (by omega) ≫ shv n m)

/-- `v`-face of the `C3`-family. -/
def c3V (n m : ℕ) (A : Fin n) (B : Fin (m - 1)) (_j : Fin (n + 2)) : ⦋m⦌ ⟶ ⦋n + m - 1⦌ :=
  Work.Pi6.SQ.cup2V (n + 1) m A.val (B.val + 1) (by omega) (by omega) (by omega) ≫ shv n m

/-- `u`-face of the `C4`-family. -/
def c4U (n m : ℕ) (A : Fin (n - 1)) (B : Fin m) (_j : Fin (m + 2)) : ⦋n⦌ ⟶ ⦋n + m - 1⦌ :=
  Work.Pi6.SQ.cup2U n (m + 1) A.val (B.val + 1) (by omega) (by omega) (by omega) ≫ shu n m

/-- `v`-face of the `C4`-family. -/
def c4V (n m : ℕ) (A : Fin (n - 1)) (B : Fin m) (j : Fin (m + 2)) : ⦋m⦌ ⟶ ⦋n + m - 1⦌ :=
  SimplexCategory.δ j ≫
    (Work.Pi6.SQ.cup2V n (m + 1) A.val (B.val + 1) (by omega) (by omega) (by omega) ≫ shu n m)

/-- `u`-face of the `T1`-family. -/
def t1U (n m : ℕ) (s : Fin n) : ⦋n⦌ ⟶ ⦋n + m - 1⦌ :=
  Work.Cohomology.Gface m n s.val (by omega) ≫ sh1 n m

/-- `v`-face of the `T1`-family. -/
def t1V (n m : ℕ) (s : Fin n) : ⦋m⦌ ⟶ ⦋n + m - 1⦌ :=
  Work.Cohomology.Fface m n s.val (by omega) ≫ sh1 n m

/-- `u`-face of the `T2`-family. -/
def t2U (n m : ℕ) (s : Fin m) : ⦋n⦌ ⟶ ⦋n + m - 1⦌ :=
  Work.Cohomology.Fface n m s.val (by omega) ≫ sh2 n m ≫ sh1 n m

/-- `v`-face of the `T2`-family. -/
def t2V (n m : ℕ) (s : Fin m) : ⦋m⦌ ⟶ ⦋n + m - 1⦌ :=
  Work.Cohomology.Gface n m s.val (by omega) ≫ sh2 n m ≫ sh1 n m

/-! ## The term functions -/

/-- The `(k,a,b)`-term of the `δ(u∪₂v)`-sum. -/
def lTerm (X : SSet) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (u : Cochain F2 X n)
    (v : Cochain F2 X m) (σ : X _⦋n + m - 1⦌) (i : LIdx n m) : F2 :=
  genEval F2 X u (X.map (lU n m hn hm i.1 i.2.1 i.2.2).op σ) *
    genEval F2 X v (X.map (lV n m hn hm i.1 i.2.1 i.2.2).op σ)

/-- The `(A,B,j)`-term of the `(δu)∪₂v`-sum. -/
def c3Term (X : SSet) (n m : ℕ) (u : Cochain F2 X n) (v : Cochain F2 X m) (σ : X _⦋n + m - 1⦌)
    (i : C3Idx n m) : F2 :=
  genEval F2 X u (X.map (c3U n m i.1 i.2.1 i.2.2).op σ) *
    genEval F2 X v (X.map (c3V n m i.1 i.2.1 i.2.2).op σ)

/-- The `(A,B,j)`-term of the `u∪₂(δv)`-sum. -/
def c4Term (X : SSet) (n m : ℕ) (u : Cochain F2 X n) (v : Cochain F2 X m) (σ : X _⦋n + m - 1⦌)
    (i : C4Idx n m) : F2 :=
  genEval F2 X u (X.map (c4U n m i.1 i.2.1 i.2.2).op σ) *
    genEval F2 X v (X.map (c4V n m i.1 i.2.1 i.2.2).op σ)

/-- The `s`-term of the `u∪₁v`-sum. -/
def t1Term (X : SSet) (n m : ℕ) (u : Cochain F2 X n) (v : Cochain F2 X m) (σ : X _⦋n + m - 1⦌)
    (s : Fin n) : F2 :=
  genEval F2 X u (X.map (t1U n m s).op σ) * genEval F2 X v (X.map (t1V n m s).op σ)

/-- The `s`-term of the `v∪₁u`-sum. -/
def t2Term (X : SSet) (n m : ℕ) (u : Cochain F2 X n) (v : Cochain F2 X m) (σ : X _⦋n + m - 1⦌)
    (s : Fin m) : F2 :=
  genEval F2 X u (X.map (t2U n m s).op σ) * genEval F2 X v (X.map (t2V n m s).op σ)

/-! ## Index-level equality helpers (for the case analysis on `cobSwap`) -/

lemma cobL_eq {n m : ℕ} {k k' : Fin (n + m)} {a a' : Fin (n - 1)} {b b' : Fin (m - 1)}
    (h1 : k.val = k'.val) (h2 : a.val = a'.val) (h3 : b.val = b'.val) :
    (Sum.inl (k, (a, b)) : cobIdx n m) = Sum.inl (k', (a', b')) := by
  obtain rfl : k = k' := Fin.ext h1
  obtain rfl : a = a' := Fin.ext h2
  obtain rfl : b = b' := Fin.ext h3
  rfl

lemma cobC3_eq {n m : ℕ} {A A' : Fin n} {B B' : Fin (m - 1)} {j j' : Fin (n + 2)}
    (h1 : A.val = A'.val) (h2 : B.val = B'.val) (h3 : j.val = j'.val) :
    (Sum.inr (Sum.inl (A, (B, j))) : cobIdx n m) = Sum.inr (Sum.inl (A', (B', j'))) := by
  obtain rfl : A = A' := Fin.ext h1
  obtain rfl : B = B' := Fin.ext h2
  obtain rfl : j = j' := Fin.ext h3
  rfl

lemma cobC4_eq {n m : ℕ} {A A' : Fin (n - 1)} {B B' : Fin m} {j j' : Fin (m + 2)}
    (h1 : A.val = A'.val) (h2 : B.val = B'.val) (h3 : j.val = j'.val) :
    (Sum.inr (Sum.inr (Sum.inl (A, (B, j)))) : cobIdx n m)
      = Sum.inr (Sum.inr (Sum.inl (A', (B', j')))) := by
  obtain rfl : A = A' := Fin.ext h1
  obtain rfl : B = B' := Fin.ext h2
  obtain rfl : j = j' := Fin.ext h3
  rfl

lemma cobT1_eq {n m : ℕ} {s s' : Fin n} (h : s.val = s'.val) :
    (Sum.inr (Sum.inr (Sum.inr (Sum.inl s))) : cobIdx n m)
      = Sum.inr (Sum.inr (Sum.inr (Sum.inl s'))) := by
  rw [Fin.ext h]

lemma cobT2_eq {n m : ℕ} {s s' : Fin m} (h : s.val = s'.val) :
    (Sum.inr (Sum.inr (Sum.inr (Sum.inr s))) : cobIdx n m)
      = Sum.inr (Sum.inr (Sum.inr (Sum.inr s'))) := by
  rw [Fin.ext h]

/-! ## The pairing involution

`cobSwap` is the fixed-point-free involution of the disjoint union
`LIdx ⊕ C3Idx ⊕ C4Idx ⊕ T1Idx ⊕ T2Idx` described in the header: it pairs every term of the
left hand side `δ(u∪₂v)` with a term of the right hand side (through the "generic" faces),
and pairs the remaining terms of the right hand side among themselves. -/

/-- The pairing involution (see the header of the file). -/
def cobSwap (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) : cobIdx n m → cobIdx n m := fun x =>
  match x with
  | Sum.inl ⟨k, ⟨a, b⟩⟩ =>
      if h1 : k.val ≤ a.val then
        Sum.inr (Sum.inl (⟨a.val + 1, by omega⟩, (b, ⟨k.val, by omega⟩)))
      else if h2 : k.val ≤ a.val + (b.val + 1) then
        Sum.inr (Sum.inr (Sum.inl (a, (⟨b.val + 1, by omega⟩,
          ⟨k.val - a.val, by omega⟩))))
      else if h3 : k.val ≤ n - 1 + (b.val + 1) then
        Sum.inr (Sum.inl (⟨a.val, by omega⟩, (b, ⟨k.val - (b.val + 1) + 1, by omega⟩)))
      else
        Sum.inr (Sum.inr (Sum.inl (⟨a.val, by omega⟩, (⟨b.val, by omega⟩, ⟨k.val - n + 2, by omega⟩))))
  | Sum.inr (Sum.inl ⟨A, ⟨B, j⟩⟩) =>
      if h1 : j.val + 1 ≤ A.val then
        Sum.inl (⟨j.val, by omega⟩, (⟨A.val - 1, by omega⟩, B))
      else if h2 : A.val + 2 ≤ j.val ∧ j.val ≤ n then
        Sum.inl (⟨j.val + B.val, by omega⟩, (⟨A.val, by omega⟩, B))
      else if h3 : j.val = A.val then
        if h4 : 1 ≤ A.val then
          Sum.inr (Sum.inr (Sum.inl (⟨A.val - 1, by omega⟩,
            (⟨B.val + 1, by omega⟩, ⟨0, by omega⟩))))
        else
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (⟨B.val + 1, by omega⟩))))
      else if h5 : j.val = A.val + 1 then
        if h6 : A.val + 2 ≤ n then
          Sum.inr (Sum.inr (Sum.inl (⟨A.val, by omega⟩, (⟨B.val + 1, by omega⟩,
            ⟨B.val + 2, by omega⟩))))
        else if h7 : B.val + 3 ≤ m then
          Sum.inr (Sum.inl (⟨n - 1, by omega⟩, (⟨B.val + 1, by omega⟩, ⟨n + 1, by omega⟩)))
        else
          Sum.inr (Sum.inr (Sum.inr (Sum.inl (⟨n - 1, by omega⟩))))
      else
        if h8 : A.val + 2 ≤ n then
          Sum.inr (Sum.inr (Sum.inl (⟨A.val, by omega⟩, (⟨B.val, by omega⟩,
            ⟨B.val + 2, by omega⟩))))
        else if h9 : 2 ≤ B.val + 1 then
          Sum.inr (Sum.inl (⟨n - 1, by omega⟩, (⟨B.val - 1, by omega⟩, ⟨n, by omega⟩)))
        else if h10 : 2 ≤ n then
          Sum.inr (Sum.inr (Sum.inl (⟨n - 2, by omega⟩, (⟨0, by omega⟩, ⟨0, by omega⟩))))
        else
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (⟨0, by omega⟩))))
  | Sum.inr (Sum.inr (Sum.inl ⟨A, ⟨B, j⟩⟩)) =>
      if h1 : 1 ≤ j.val ∧ j.val ≤ B.val then
        Sum.inl (⟨j.val + A.val, by omega⟩, (A, ⟨B.val - 1, by omega⟩))
      else if h2 : B.val + 3 ≤ j.val then
        Sum.inl (⟨j.val + n - 2, by omega⟩, (A, ⟨B.val, by omega⟩))
      else if h3 : j.val = 0 then
        if h4 : 2 ≤ B.val + 1 then
          Sum.inr (Sum.inl (⟨A.val + 1, by omega⟩, (⟨B.val - 1, by omega⟩,
            ⟨A.val + 1, by omega⟩)))
        else if h5 : A.val + 3 ≤ n then
          Sum.inr (Sum.inr (Sum.inl (⟨A.val + 1, by omega⟩, (⟨0, by omega⟩, ⟨1, by omega⟩))))
        else if h6 : 2 ≤ m then
          Sum.inr (Sum.inl (⟨n - 1, by omega⟩, (⟨0, by omega⟩, ⟨n + 1, by omega⟩)))
        else
          Sum.inr (Sum.inr (Sum.inr (Sum.inl (⟨n - 1, by omega⟩))))
      else if h7 : j.val = B.val + 1 then
        if h8 : 2 ≤ B.val + 1 then
          Sum.inr (Sum.inl (⟨A.val, by omega⟩, (⟨B.val - 1, by omega⟩, ⟨A.val + 1, by omega⟩)))
        else if h9 : 1 ≤ A.val then
          Sum.inr (Sum.inr (Sum.inl (⟨A.val - 1, by omega⟩, (⟨0, by omega⟩, ⟨0, by omega⟩))))
        else
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (⟨0, by omega⟩))))
      else
        if h11 : B.val + 1 ≤ m - 1 then
          Sum.inr (Sum.inl (⟨A.val, by omega⟩, (⟨B.val, by omega⟩, ⟨n + 1, by omega⟩)))
        else
          Sum.inr (Sum.inr (Sum.inr (Sum.inl (⟨A.val, by omega⟩))))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl s))) =>
      if h1 : s.val + 2 ≤ n then
        Sum.inr (Sum.inr (Sum.inl (⟨s.val, by omega⟩, (⟨m - 1, by omega⟩, ⟨m + 1, by omega⟩))))
      else if h2 : 2 ≤ m then
        Sum.inr (Sum.inl (⟨n - 1, by omega⟩, (⟨m - 2, by omega⟩, ⟨n, by omega⟩)))
      else if h3 : 2 ≤ n then
        Sum.inr (Sum.inr (Sum.inl (⟨n - 2, by omega⟩, (⟨0, by omega⟩, ⟨0, by omega⟩))))
      else
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (⟨0, by omega⟩))))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr s))) =>
      if h1 : 1 ≤ s.val then
        Sum.inr (Sum.inl (⟨0, by omega⟩, (⟨s.val - 1, by omega⟩, ⟨0, by omega⟩)))
      else if h2 : 2 ≤ n then
        Sum.inr (Sum.inr (Sum.inl (⟨0, by omega⟩, (⟨0, by omega⟩, ⟨1, by omega⟩))))
      else if h3 : 2 ≤ m then
        Sum.inr (Sum.inl (⟨0, by omega⟩, (⟨0, by omega⟩, ⟨n + 1, by omega⟩)))
      else
        Sum.inr (Sum.inr (Sum.inr (Sum.inl (⟨0, by omega⟩))))

/-- The term attached to an element of the disjoint union of all index families. -/
def cobTerm (X : SSet) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (u : Cochain F2 X n)
    (v : Cochain F2 X m) (σ : X _⦋n + m - 1⦌) : cobIdx n m → F2 :=
  Sum.elim (lTerm X n m hn hm u v σ)
    (Sum.elim (c3Term X n m u v σ) (Sum.elim (c4Term X n m u v σ)
      (Sum.elim (t1Term X n m u v σ) (t2Term X n m u v σ))))

end

end Work.Pi6.SQ.C2
