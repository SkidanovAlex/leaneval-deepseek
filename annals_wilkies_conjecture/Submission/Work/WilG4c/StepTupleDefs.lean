/-
  WilG4c / `StepTupleDefs` — the index sets and the tuple of BNZ §5.4.

  BNZ §5.4 applies Corollary 5.5 (`F1Affine`) to the tuple consisting of

  * the coordinates of the near-maximising curves `γ_{i,α}` (clamped into `(0,1)`), and
  * the surrogates `(∂^{β} F_i (·, γ_{i,α}) + 2)/4` of the pure-`y` derivatives along the curves,

  for all multiindices `α` of order `≤ r`.  To keep the *number* of tuple members — which
  enters the count bound of the chart family — polynomial in `r`, the multiindices are indexed
  not by lists but by *counting vectors*: `n` is fixed, `(r+1)^n` is polynomial in `r`, and every
  list `M` with `|M| ≤ r` has a canonical representative `canonList (count vector of M)`.

  This file fixes the vocabulary: the index sets `CIdx` (counting vectors of order `≤ r`) and
  `MIdx` (pairs `(j,c)` with `j + ∑ c ≤ r`), the canonical list `canonList`, the direction list
  `LcOf` of a canonical multiindex, the canonicalisation of an arbitrary pair `(j,M)`, and the
  tuple `tupleFam`; it also proves the length and cardinality bounds that the count bookkeeping
  of the assembly needs.
-/
import Mathlib
import Submission.Work.WilG4c.SlicedSurrogateDefs
import Submission.Work.WilG4c.CurveFamAlphaListPureSliced
import Submission.Work.WilG4c.SurrogateSliceFamGraphMem
import Submission.Work.WilG4c.famGraph_gam_eq_graphOf
import Submission.Work.WilG4c.clampFamGraph
import Submission.Work.WilG4c.countvec_perm
import Submission.Work.WilG4c.card_countvec_le
import Submission.Work.WilG4c.ClampDefs

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. Counting vectors and canonical multiindices -/

/-- The counting vectors of order `≤ r`: a vector `c : Fin n → Fin (r+1)` whose entries add up
to at most `r`. -/
abbrev CIdx (n r : ℕ) : Type := {c : Fin n → Fin (r + 1) // (∑ i, (c i : ℕ)) ≤ r}

/-- The canonical multiindices `(j,c)` of order `≤ r`: `j` counts the `x`-directions and `c`
is the counting vector of the `y`-directions, subject to `j + ∑ c ≤ r`. -/
abbrev MIdx (n r : ℕ) : Type :=
  {p : Fin (r + 1) × (Fin n → Fin (r + 1)) // (∑ i, (p.2 i : ℕ)) ≤ r - (p.1 : ℕ)}

instance (n r : ℕ) : Fintype (CIdx n r) := inferInstance

instance (n r : ℕ) : Fintype (MIdx n r) := inferInstance

/-- There are at most `(r+1)^n` counting vectors of order `≤ r` (the cast of
`Work.WilG4c.card_countvec_le` to this file's spelling). -/
theorem card_CIdx_le (n r : ℕ) : Fintype.card (CIdx n r) ≤ (r + 1) ^ n := by
  have h := Work.WilG4c.card_countvec_le n r
  simpa only [CIdx] using h

/-- There are at most `(r+1)^(n+1)` canonical multiindices of order `≤ r`. -/
theorem card_MIdx_le (n r : ℕ) : Fintype.card (MIdx n r) ≤ (r + 1) ^ (n + 1) := by
  calc Fintype.card (MIdx n r)
      ≤ Fintype.card (Fin (r + 1) × (Fin n → Fin (r + 1))) := Fintype.card_subtype_le _
    _ = (r + 1) * (r + 1) ^ n := by
        simp [Fintype.card_prod, Fintype.card_fun]
    _ = (r + 1) ^ (n + 1) := by rw [pow_succ]; ring

/-- The canonical list of a counting vector `c : Fin n → ℕ`: the listing of the multiset
`∑ i, c i • {i}`. -/
noncomputable def canonList {n : ℕ} (c : Fin n → ℕ) : List (Fin n) :=
  (Finset.univ.sum (fun i : Fin n => c i • ({i} : Multiset (Fin n)))).toList

/-- The length of the canonical list is the sum of the counting vector. -/
theorem canonList_length {n : ℕ} (c : Fin n → ℕ) :
    (canonList c).length = ∑ i, c i := by
  rw [canonList, Multiset.length_toList, Multiset.card_sum]
  simp [Multiset.card_nsmul]

/-- The multiset of the canonical list is the multiset `∑ i, c i • {i}`. -/
theorem canonList_coe {n : ℕ} (c : Fin n → ℕ) :
    (canonList c : Multiset (Fin n)) = ∑ i, c i • ({i} : Multiset (Fin n)) := by
  rw [canonList, Multiset.coe_toList]

/-- The direction list of a canonical multiindex `(j,c)` of BNZ §5.4: `j` copies of the
`x`-direction followed by the `y`-directions of the canonical list of `c`. -/
def LcOf {n r : ℕ} (m : MIdx n r) : List (Fin (n + 1)) :=
  List.replicate (m.1.1 : ℕ) (0 : Fin (n + 1)) ++
    (canonList (fun i => (m.1.2 i : ℕ))).map Fin.succ

/-- The length of the direction list of a canonical multiindex, symbolically. -/
theorem LcOf_length {n r : ℕ} (m : MIdx n r) :
    (LcOf m).length = (m.1.1 : ℕ) + ∑ i, (m.1.2 i : ℕ) := by
  rw [LcOf, List.length_append, List.length_replicate, List.length_map, canonList_length]

/-- The direction list of a canonical multiindex of order `≤ r` has length `≤ r`. -/
theorem LcOf_length_le {n r : ℕ} (m : MIdx n r) : (LcOf m).length ≤ r := by
  rw [LcOf_length]
  have := m.2
  omega

/-! ## 2. Canonicalising an arbitrary pair `(j,M)` -/

/-- The counting vector of a list `M` of length `≤ r`, as an element of `Fin n → Fin (r+1)`. -/
noncomputable def cntVec {n : ℕ} (M : List (Fin n)) (r : ℕ) (h : M.length ≤ r) :
    Fin n → Fin (r + 1) :=
  fun i => ⟨(Multiset.ofList M).count i, by
    have h1 : (Multiset.ofList M).count i ≤ M.length :=
      Multiset.count_le_card i (Multiset.ofList M)
    omega⟩

/-- The sum of the counts of a list is its length. -/
theorem sum_count_eq_length {n : ℕ} (M : List (Fin n)) :
    (∑ i, (Multiset.ofList M).count i) = M.length := by
  classical
  calc (∑ i, (Multiset.ofList M).count i)
      = ∑ a ∈ (Multiset.ofList M).toFinset, Multiset.count a (Multiset.ofList M) :=
        (Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => by
          rw [Multiset.mem_toFinset] at hx
          exact Multiset.count_eq_zero.mpr hx)).symm
    _ = (Multiset.ofList M).card := Multiset.toFinset_sum_count_eq _
    _ = M.length := rfl

/-- The value of `cntVec` is the count. -/
@[simp] theorem cntVec_apply {n : ℕ} (M : List (Fin n)) (r : ℕ) (h : M.length ≤ r)
    (i : Fin n) : ((cntVec M r h i : Fin (r + 1)) : ℕ) = (Multiset.ofList M).count i := rfl

/-- The canonical list of the counting vector of `M` is a permutation of `M`. -/
theorem canonList_cntVec_perm {n : ℕ} (M : List (Fin n)) (r : ℕ) (h : M.length ≤ r) :
    M.Perm (canonList (fun i => (cntVec M r h i : ℕ))) := by
  have h1 : (fun i : Fin n => (cntVec M r h i : ℕ)) = fun i => (Multiset.ofList M).count i :=
    funext fun i => rfl
  rw [h1]
  exact Work.WilG4c.countvec_perm M h

/-- The counting vector of a list `M` of length `≤ r`, as an element of `CIdx`. -/
noncomputable def cntCIdx {n : ℕ} (M : List (Fin n)) (r : ℕ) (h : M.length ≤ r) : CIdx n r :=
  ⟨cntVec M r h, by
    have h2 : (∑ i, ((cntVec M r h) i : ℕ)) = ∑ i, (Multiset.ofList M).count i :=
      Finset.sum_congr rfl (fun i _ => rfl)
    rw [h2, sum_count_eq_length]
    exact h⟩

@[simp] theorem cntCIdx_apply {n r : ℕ} (M : List (Fin n)) (h : M.length ≤ r) (i : Fin n) :
    ((cntCIdx M r h).1 i : ℕ) = (Multiset.ofList M).count i := rfl

/-- The canonical list of the counting vector of a `CIdx`-element of `M` is a permutation. -/
theorem canonList_cntCIdx_perm {n r : ℕ} (M : List (Fin n)) (h : M.length ≤ r) :
    M.Perm (canonList (fun i => ((cntCIdx M r h).1 i : ℕ))) :=
  canonList_cntVec_perm M r h

/-- The canonical multiindex of an arbitrary pair `(j, M)` with `j + |M| ≤ r`: `j` and the
counting vector of `M`. -/
noncomputable def curveIdx {n : ℕ} (j : ℕ) (M : List (Fin n)) (r : ℕ)
    (h : j + M.length ≤ r) : MIdx n r :=
  ⟨(⟨j, by omega⟩, cntVec M r (by omega)), by
    show (∑ i, ((cntVec M r (by omega)) i : ℕ)) ≤ r - j
    have h2 : (∑ i, ((cntVec M r (by omega)) i : ℕ)) =
        ∑ i, (Multiset.ofList M).count i :=
      Finset.sum_congr rfl (fun i _ => rfl)
    rw [h2, sum_count_eq_length]
    omega⟩

@[simp] theorem curveIdx_fst {n : ℕ} (j : ℕ) (M : List (Fin n)) (r : ℕ)
    (h : j + M.length ≤ r) : ((curveIdx j M r h).1.1 : ℕ) = j := rfl

/-- The direction list of the canonical multiindex of `(j,M)` is `j` copies of the
`x`-direction followed by the canonical list of the counting vector of `M`. -/
theorem LcOf_curveIdx {n : ℕ} (j : ℕ) (M : List (Fin n)) (r : ℕ) (h : j + M.length ≤ r)
    (h' : M.length ≤ r) :
    LcOf (curveIdx j M r h)
      = List.replicate j (0 : Fin (n + 1))
        ++ (canonList (fun i => ((cntVec M r h' i) : ℕ))).map Fin.succ := rfl

/-- The canonical list of the counting vector of `M` (inside `curveIdx`) is a permutation
of `M`. -/
theorem curveIdx_perm {n : ℕ} (j : ℕ) (M : List (Fin n)) (r : ℕ) (h : j + M.length ≤ r) :
    M.Perm (canonList (fun i => (((curveIdx j M r h).1.2) i : ℕ))) := by
  rw [curveIdx]
  exact canonList_cntVec_perm M r (by omega)

/-! ## 3. The tuple of BNZ §5.4 -/

/-- The index set of the tuple of BNZ §5.4 passed to Corollary 5.5:
`k` members `×` canonical multiindices `×` (`y`-coordinates `⊕` derivative multiindices). -/
abbrev TupleIdx (k n r : ℕ) : Type := Fin k × MIdx n r × (Fin n ⊕ CIdx n r)

/-- The clamped curve coordinates: the clamping is what makes the tuple members globally take
values in `(0,1)`, as Corollary 5.5 requires (its conclusion holds only for `l ∈ Λ`, and the
final chart family has to be valid for all `l`). -/
noncomputable def gclOf {k p n r : ℕ}
    (γs : (i : Fin k) → MIdx n r → (Fin p → ℝ) → ℝ → (Fin n → ℝ))
    (i : Fin k) (m : MIdx n r) : (Fin p → ℝ) → ℝ → (Fin n → ℝ) :=
  fun l x ι => Work.WilG4c.clamp01 (γs i m l x ι)

/-- The tuple of BNZ §5.4, as a function of the index set: the clamped curve coordinates
(the `Sum.inl` part) and the sliced surrogates of the pure-`y` derivatives along the curves
(the `Sum.inr` part). -/
noncomputable def tupleFunc {k p n r : ℕ} (F : Family k p (n + 1))
    (γs : (i : Fin k) → MIdx n r → (Fin p → ℝ) → ℝ → (Fin n → ℝ)) :
    TupleIdx k n r → (Fin p → ℝ) → (Fin 1 → ℝ) → ℝ :=
  fun x =>
    match x with
    | ⟨i, m, Sum.inl ι⟩ => fun l t => gclOf γs i m l (t 0) ι
    | ⟨i, m, Sum.inr c'⟩ =>
        fun l t => Work.WilkG4c.surrogateSlice p n (F i) (gclOf γs i m)
          (canonList (fun i => (c'.1 i : ℕ))) l (t 0)

@[simp] theorem tupleFunc_inl {k p n r : ℕ} (F : Family k p (n + 1))
    (γs : (i : Fin k) → MIdx n r → (Fin p → ℝ) → ℝ → (Fin n → ℝ)) (i : Fin k) (m : MIdx n r)
    (ι : Fin n) :
    tupleFunc F γs ⟨i, m, Sum.inl ι⟩
      = fun l t => Work.WilG4c.clamp01 (γs i m l (t 0) ι) := rfl

@[simp] theorem tupleFunc_inr {k p n r : ℕ} (F : Family k p (n + 1))
    (γs : (i : Fin k) → MIdx n r → (Fin p → ℝ) → ℝ → (Fin n → ℝ)) (i : Fin k) (m : MIdx n r)
    (c' : CIdx n r) :
    tupleFunc F γs ⟨i, m, Sum.inr c'⟩
      = fun l t => Work.WilkG4c.surrogateSlice p n (F i) (gclOf γs i m)
          (canonList (fun i => (c'.1 i : ℕ))) l (t 0) := rfl

/-- The number of tuple members. -/
def tupleSize (k n r : ℕ) : ℕ := Fintype.card (TupleIdx k n r)

/-- The tuple of BNZ §5.4 as a `Fin`-indexed family, ready for `F1Affine`. -/
noncomputable def tupleFam {k p n r : ℕ} (F : Family k p (n + 1))
    (γs : (i : Fin k) → MIdx n r → (Fin p → ℝ) → ℝ → (Fin n → ℝ)) :
    Family (tupleSize k n r) p 1 :=
  fun j => tupleFunc F γs ((Fintype.equivFin (TupleIdx k n r)).symm j)

/-- The tuple member at an index of the index set is the corresponding `Fin`-indexed member. -/
theorem tupleFam_apply {k p n r : ℕ} (F : Family k p (n + 1))
    (γs : (i : Fin k) → MIdx n r → (Fin p → ℝ) → ℝ → (Fin n → ℝ)) (x : TupleIdx k n r) :
    tupleFam F γs (Fintype.equivFin (TupleIdx k n r) x) = tupleFunc F γs x := by
  dsimp only [tupleFam]
  rw [Equiv.symm_apply_apply]

/-- The number of tuple members is at most `k (r+1)^(n+1) (n + (r+1)^n)` — a polynomial in
`r` for fixed `n`. -/
theorem tupleSize_le (k n r : ℕ) :
    tupleSize k n r ≤ k * ((r + 1) ^ (n + 1) * (n + (r + 1) ^ n)) := by
  rw [tupleSize, Fintype.card_prod, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_fin]
  exact Nat.mul_le_mul (le_refl k)
    (Nat.mul_le_mul (card_MIdx_le n r) (Nat.add_le_add_left (card_CIdx_le n r) n))

/-! ## 4. The direction list of a multiindex `(j,M)` -/

/-- The canonical listing of the multiset of a list `M` — the count vector of `M` in list
form.  This is the list whose `y`-directions are used by the sliced choice lemma for the
multiindex `(j,M)`. -/
noncomputable def cvList {n : ℕ} (M : List (Fin n)) : List (Fin n) :=
  canonList (fun i => (Multiset.ofList M).count i)

/-- The direction list of the multiindex `(j,M)`: `j` copies of the `x`-direction followed by
the canonical listing `cvList M` of the `y`-directions.  These are exactly the lists on which
the sliced choice lemma `Work.WilG4c.CurveFamAlphaListPureSliced` is applied. -/
noncomputable def LdirOf {n : ℕ} (j : ℕ) (M : List (Fin n)) : List (Fin (n + 1)) :=
  List.replicate j (0 : Fin (n + 1)) ++ (cvList M).map Fin.succ

/-- The canonical multiindex of `(j,M)` has direction list `LdirOf j M`. -/
theorem LcOf_curveIdx_eq {n : ℕ} (j : ℕ) (M : List (Fin n)) (r : ℕ) (h : j + M.length ≤ r)
    (h' : M.length ≤ r) : LcOf (curveIdx j M r h) = LdirOf j M := by
  rw [LcOf_curveIdx j M r h h', LdirOf, cvList]
  congr 1

/-- The tuple size padded to the explicit polynomial bound `k (r+1)^(n+1) (n + (r+1)^n)`.
Passing *this* number of members to `F1Affine` makes the resulting count polynomial an explicit
substitution of `k` and `r`, with no monotonicity argument needed. -/
def tupleSizeBig (k n r : ℕ) : ℕ := k * ((r + 1) ^ (n + 1) * (n + (r + 1) ^ n))

/-- The number of tuple members is at most the padded size. -/
theorem tupleSize_le_big (k n r : ℕ) :
    Fintype.card (TupleIdx k n r) ≤ tupleSizeBig k n r :=
  tupleSize_le k n r

/-- The `Fin (tupleSizeBig k n r)`-indexed tuple of BNZ §5.4: on the first
`Fintype.card (TupleIdx k n r)` indices the members of `tupleFam`, and on the remaining
(padding) indices the constant `1/2`.  The padding is what lets `F1Affine` be applied with the
explicit polynomial member count `tupleSizeBig k n r`; only the genuine members are ever read
off, and the padding members have `Ω`-bounded graphs and values in `(0,1)` as well. -/
noncomputable def tupleFamBig {k p n r : ℕ} (F : Family k p (n + 1))
    (γs : (i : Fin k) → MIdx n r → (Fin p → ℝ) → ℝ → (Fin n → ℝ)) :
    Family (tupleSizeBig k n r) p 1 :=
  fun j => if h : (j : ℕ) < Fintype.card (TupleIdx k n r) then
      tupleFunc F γs ((Fintype.equivFin (TupleIdx k n r)).symm ⟨(j : ℕ), h⟩)
    else fun _ _ => (1 / 2 : ℝ)

/-- The padded tuple agrees with the tuple at every genuine index. -/
theorem tupleFamBig_eq {k p n r : ℕ} (F : Family k p (n + 1))
    (γs : (i : Fin k) → MIdx n r → (Fin p → ℝ) → ℝ → (Fin n → ℝ)) (x : TupleIdx k n r) :
    tupleFamBig F γs ⟨((Fintype.equivFin (TupleIdx k n r)) x : ℕ),
        lt_of_lt_of_le (Fintype.equivFin (TupleIdx k n r) x).isLt (tupleSize_le_big k n r)⟩
      = tupleFunc F γs x := by
  rw [tupleFamBig]
  split_ifs with h
  · congr 1
    exact Equiv.symm_apply_apply _ _
  · exact absurd (Fintype.equivFin (TupleIdx k n r) x).isLt h

/-- The padded tuple is the constant `1/2` on the padding indices. -/
theorem tupleFamBig_dummy {k p n r : ℕ} (F : Family k p (n + 1))
    (γs : (i : Fin k) → MIdx n r → (Fin p → ℝ) → ℝ → (Fin n → ℝ))
    {j : Fin (tupleSizeBig k n r)} (hj : ¬ (j : ℕ) < Fintype.card (TupleIdx k n r)) :
    tupleFamBig F γs j = fun _ _ => (1 / 2 : ℝ) := by
  rw [tupleFamBig]
  exact dite_eq_right hj

/-- The canonical listing of `M` has the same length as `M`. -/
theorem cvList_length {n : ℕ} (M : List (Fin n)) : (cvList M).length = M.length := by
  rw [cvList, canonList_length]
  exact sum_count_eq_length M

/-- The direction list of `(j,M)` has length `j + |M|`. -/
theorem LdirOf_length {n : ℕ} (j : ℕ) (M : List (Fin n)) :
    (LdirOf j M).length = j + M.length := by
  rw [LdirOf, List.length_append, List.length_replicate, List.length_map, cvList_length]

end Work.WilkG4c
