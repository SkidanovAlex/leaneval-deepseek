import Mathlib
import Submission.Work.SimplyConnected.ABS.engulfs_filling

/-!
# The filling step: adding the relatively compact complementary components

`Work.Topology.Engulf.exists_filled_isCompact_closure` asks for an open connected relatively compact
`Ω ⊇ K` with **no** relatively compact complementary component.  The construction is: take a
relatively compact open connected `Ω₀ ⊇ K` (landed:
`exists_isOpen_isConnected_isCompact_closure_superset`) and add the relatively compact components of
`Ω₀ᶜ`.  The two structural facts that make this work — and the point-set heart of ABS Theorem 12 —
are isolated here; they need only that the relatively compact part of `Ω₀ᶜ` is a *finite union of
closed connected pieces* `Z : ι → Set X`:

* **openness**: the complement of `Ω₀ ∪ ⋃ {Z i | IsCompact (closure (Z i))}` is the union of the
  remaining `Z i`, a finite union of closed sets, hence closed;
* **no relatively compact complementary component**: every connected component of that complement
  contains one of the `Z i` with `¬ IsCompact (closure (Z i))`, and a set containing a set with
  non-compact closure has non-compact closure (`not_isCompact_closure_connectedComponentIn_of_isPreconnected_subset`,
  the key pointwise statement, proved below);
* **precompactness**: `closure Ω ⊆ closure Ω₀ ∪ ⋃ {Z i | IsCompact (closure (Z i))}`, a finite union
  of compact sets (`isCompact_closure_of_subset_closure_union`).

The wildness obstruction recorded in `engulfs_filling.lean` (the filling of a *wild* compact set need
not be open) does not arise: for a cluster of tiles of the locally finite disc tiling the complement
decomposes into finitely many closed pieces, which is exactly the hypothesis used here.
-/

namespace Work.Topology.Engulf

open Set

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- **The key pointwise statement of the filling step.**

If `Z ⊆ Ωᶜ` is preconnected and has non-compact closure, then for any `x ∈ Z` the component of `x` in
`Ωᶜ` has non-compact closure: that component contains `Z`. -/
theorem not_isCompact_closure_connectedComponentIn_of_isPreconnected_subset {Ω Z : Set X}
    (hZc : IsPreconnected Z) (hZsub : Z ⊆ Ωᶜ) {x : X} (hx : x ∈ Z)
    (h : ¬ IsCompact (closure Z)) : ¬ IsCompact (closure (connectedComponentIn (Ωᶜ) x)) := by
  intro hc
  exact h (hc.of_isClosed_subset isClosed_closure
    (closure_mono (hZc.subset_connectedComponentIn hx hZsub)))

/-- **Precompactness of the filled set.**  If `Ω ⊆ closure Ω₀ ∪ W` with `closure Ω₀` and `W` compact,
then `closure Ω` is compact. -/
theorem isCompact_closure_of_subset_closure_union {Ω Ω₀ W : Set X}
    (hΩpre : IsCompact (closure Ω₀)) (hW : IsCompact W) (h : Ω ⊆ closure Ω₀ ∪ W) :
    IsCompact (closure Ω) := by
  have hcl : closure (closure Ω₀ ∪ W) = closure Ω₀ ∪ W :=
    closure_eq_iff_isClosed.mpr (hΩpre.isClosed.union hW.isClosed)
  have hsub : closure Ω ⊆ closure Ω₀ ∪ W := (closure_mono h).trans hcl.le
  exact (hΩpre.union hW).of_isClosed_subset isClosed_closure hsub

/-- **Openness of the filled set.**  If the complement of `Ω` is a finite union of closed sets, `Ω` is
open. -/
theorem isOpen_of_compl_eq_iUnion {ι : Type*} [Fintype ι] {Ω : Set X} (Z : ι → Set X)
    (hZcl : ∀ i, IsClosed (Z i)) (h : Ωᶜ = ⋃ i, Z i) : IsOpen Ω :=
  isClosed_compl_iff.mp (h ▸ isClosed_iUnion_of_finite fun i => hZcl i)

/-- **Connectedness of the filled set.**  If `Ω₀` is preconnected, every `Z i` is preconnected, and
every `Z i` with `i ∈ s` meets `closure Ω₀`, then `Ω₀ ∪ ⋃ i ∈ s, Z i` is preconnected: add the pieces
one at a time (`isPreconnected_union_of_inter_closure_nonempty`) and use that `closure Ω₀` is
contained in the closure of everything met so far. -/
theorem isPreconnected_union_biUnion_of_inter_closure {Ω₀ : Set X} {ι : Type*} (Z : ι → Set X)
    {s : Finset ι} (hΩc : IsPreconnected Ω₀) (hZc : ∀ i, IsPreconnected (Z i))
    (hatt : ∀ i ∈ s, (Z i ∩ closure Ω₀).Nonempty) :
    IsPreconnected (Ω₀ ∪ ⋃ i ∈ s, Z i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using hΩc
  | insert a t ha ih =>
      have hcong : Ω₀ ∪ ⋃ i ∈ insert a t, Z i = (Ω₀ ∪ ⋃ i ∈ t, Z i) ∪ Z a := by
        rw [Work.SimplyConnected.ABS.biUnion_insert_eq]
        ac_rfl
      rw [hcong]
      have hstep := Work.SimplyConnected.ABS.isPreconnected_union_of_inter_closure_nonempty
        (S := Z a) (T := Ω₀ ∪ ⋃ i ∈ t, Z i) (hZc a)
        (ih (fun i hi => hatt i (Finset.mem_insert_of_mem hi)))
        ((hatt a (Finset.mem_insert_self a t)).imp
          (fun x hx => ⟨hx.1, closure_mono subset_union_left hx.2⟩))
      rwa [Set.union_comm] at hstep

/-- The type-indexed form of `isPreconnected_union_biUnion_of_inter_closure`. -/
theorem isPreconnected_union_iUnion_of_inter_closure {Ω₀ : Set X} {ι : Type*} [Fintype ι]
    (A : ι → Set X)
    (hΩc : IsPreconnected Ω₀) (hAc : ∀ i, IsPreconnected (A i))
    (hatt : ∀ i, (A i ∩ closure Ω₀).Nonempty) : IsPreconnected (Ω₀ ∪ ⋃ i, A i) := by
  simpa using isPreconnected_union_biUnion_of_inter_closure (s := Finset.univ) A hΩc hAc
    (fun i _ => hatt i)

/-- **The assembly of the filling step.**  `Ω := Ω₀ ∪ ⋃ {relatively compact pieces}` where the
relatively compact part of `Ω₀ᶜ` is the finite family `A` and the rest of `Ω₀ᶜ` is the finite family
`B`.  Then `Ω` is open, connected, relatively compact, contains `Ω₀`, and has no relatively compact
complementary component: the four landed structural facts, discharged. -/
theorem isOpen_isConnected_isCompact_closure_of_finite_decomposition {Ω₀ Ω : Set X}
    {σ τ : Type*} [Fintype σ] [Fintype τ] (A : σ → Set X) (B : τ → Set X)
    (hΩo : IsOpen Ω₀) (hΩc : IsPreconnected Ω₀) (hΩne : Ω₀.Nonempty)
    (hΩpre : IsCompact (closure Ω₀))
    (hBcl : ∀ i, IsClosed (B i)) (hAc : ∀ i, IsPreconnected (A i))
    (hBc : ∀ i, IsPreconnected (B i))
    (hΩ : Ω = Ω₀ ∪ ⋃ i, A i) (hcompl : Ωᶜ = ⋃ i, B i) (hBsub : ∀ i, B i ⊆ Ωᶜ)
    (hAcomp : ∀ i, IsCompact (closure (A i))) (hatt : ∀ i, (A i ∩ closure Ω₀).Nonempty)
    (hne : Nonempty τ) (hBnt : ∀ i, ¬ IsCompact (closure (B i))) :
    IsOpen Ω ∧ IsConnected Ω ∧ IsCompact (closure Ω) ∧ Ω₀ ⊆ Ω ∧
      ∀ x : X, x ∉ Ω → ¬ IsCompact (closure (connectedComponentIn (Ωᶜ) x)) := by
  classical
  have hsub : Ω₀ ⊆ Ω := by rw [hΩ]; exact subset_union_left
  have hpc : IsPreconnected Ω := by
    rw [hΩ]
    exact isPreconnected_union_iUnion_of_inter_closure A hΩc hAc hatt
  have hsub' : Ω ⊆ closure Ω₀ ∪ ⋃ i, closure (A i) := by
    rw [hΩ]
    rintro x (hx | hx)
    · exact Or.inl (subset_closure hx)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact Or.inr (mem_iUnion.mpr ⟨i, subset_closure hi⟩)
  refine ⟨isOpen_of_compl_eq_iUnion B hBcl hcompl, ⟨hΩne.mono hsub, hpc⟩,
    isCompact_closure_of_subset_closure_union hΩpre (isCompact_iUnion fun i => hAcomp i) hsub',
    hsub, ?_⟩
  intro x hx
  have hx' : x ∈ Ωᶜ := hx
  rw [hcompl] at hx'
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx'
  exact not_isCompact_closure_connectedComponentIn_of_isPreconnected_subset (hBc i) (hBsub i)
    hi (hBnt i)

/-- **The complement computation of the filling step.**  If the pieces `Z i` lie in `Ω₀ᶜ`, cover it,
and are pairwise disjoint, and the index set is split into the finite sets `s` and `t`, then

  `(Ω₀ ∪ ⋃ i ∈ s, Z i)ᶜ = ⋃ i ∈ t, Z i`

— this is the `hcompl` consumed by `isOpen_isConnected_isCompact_closure_of_finite_decomposition`
(and `hΩ` there is the definition of `Ω` itself).  `s` is the family of *relatively compact* pieces
and `t` the rest; the only inputs are the cover, the inclusion, the disjointness and the split. -/
theorem compl_union_biUnion_eq_biUnion {Ω₀ : Set X} {ι : Type*} {Z : ι → Set X}
    (hZsub : ∀ i, Z i ⊆ Ω₀ᶜ) (hcover : Ω₀ᶜ ⊆ ⋃ i, Z i)
    (hdisj : ∀ i j, i ≠ j → ∀ x, x ∈ Z i → x ∈ Z j → False)
    {s t : Finset ι} (hsplit : ∀ i, i ∈ s ∨ i ∈ t) (hst : ∀ i, i ∈ s → i ∈ t → False) :
    (Ω₀ ∪ ⋃ i ∈ s, Z i)ᶜ = ⋃ i ∈ t, Z i := by
  ext x
  constructor
  · intro hx
    have hxΩ₀ : x ∉ Ω₀ := fun h => hx (Or.inl h)
    have hxs : x ∉ ⋃ i ∈ s, Z i := fun h => hx (Or.inr h)
    obtain ⟨j, hj⟩ : ∃ j, x ∈ Z j := by
      simpa only [Set.mem_iUnion] using hcover hxΩ₀
    rcases hsplit j with hj' | hj'
    · exact absurd (mem_biUnion hj' hj) hxs
    · exact mem_biUnion hj' hj
  · intro hx
    obtain ⟨j, hjt, hxj⟩ : ∃ j, j ∈ t ∧ x ∈ Z j := by
      simpa only [Set.mem_iUnion, exists_prop] using hx
    intro hy
    rcases hy with hy | hy
    · exact hZsub j hxj hy
    · obtain ⟨i, his, hxi⟩ : ∃ i, i ∈ s ∧ x ∈ Z i := by
        simpa only [Set.mem_iUnion, exists_prop] using hy
      exact hdisj i j (fun hEq => hst i his (hEq ▸ hjt)) x hxi hxj

/-! ## The pieces of the complement of `Ω₀` (the tile-data obligations that need no tiling)

The filling assembly consumes a family `Z` of pieces of `Ω₀ᶜ` together with the cover, the inclusion
into `Ω₀ᶜ`, pairwise disjointness and the split.  Taking `Z` to be the family of *connected components*
of `Ω₀ᶜ` (indexed by the points of `Ω₀ᶜ`), the inclusion is `connectedComponentIn_subset`, the cover
is `eq_iUnion_connectedComponentIn`, and disjointness is `connectedComponentIn_eq_or_notMem`: three of
the five obligations, independently of the disc tiling. -/

/-- **The complement is the union of its connected components** (the cover obligation). -/
theorem eq_iUnion_connectedComponentIn (F : Set X) :
    F = ⋃ x ∈ F, connectedComponentIn F x := by
  ext y
  constructor
  · intro hy
    exact mem_biUnion hy (mem_connectedComponentIn hy)
  · intro hy
    obtain ⟨x, -, hyx⟩ : ∃ x, x ∈ F ∧ y ∈ connectedComponentIn F x := by
      simpa only [Set.mem_iUnion, exists_prop] using hy
    exact connectedComponentIn_subset F x hyx

/-- **Two connected components of a set are equal or disjoint** (the disjointness obligation, in the
explicit form used by the filling assembly). -/
theorem connectedComponentIn_eq_or_notMem {F : Set X} (x y : X) :
    connectedComponentIn F x = connectedComponentIn F y ∨
      ∀ z, z ∈ connectedComponentIn F x → z ∈ connectedComponentIn F y → False := by
  by_cases h : (connectedComponentIn F x ∩ connectedComponentIn F y).Nonempty
  · obtain ⟨z, hzx, hzy⟩ := h
    exact Or.inl (by
      first
      | exact (connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm
      | exact (connectedComponentIn_eq hzx).symm.trans (connectedComponentIn_eq hzy))
  · exact Or.inr fun z hzx hzy => h ⟨z, hzx, hzy⟩

/-! ## Closedness and preconnectedness of the pieces (tile-data obligation 1)

Preconnectedness of a component is Mathlib's `isPreconnected_connectedComponentIn`.  Closedness is
subtler than it looks: a component of a closed set is closed **in that set** (the corpus's
`Work.SimplyConnected.ABS.eq_of_mem_closure_connectedComponentIn`), but not necessarily in the ambient
space — the classical counterexample is `{(0,0)} ∪ {(x, sin (1/x)) : x > 0}`-type sets, whose
components accumulate outside the set.  What the assembly consumes is ambient closedness of the
*union* of the pieces, so the tile data must either provide finitely many pieces (then the union of
the pieces outside the cluster is a finite union of closed sets) or local connectedness of `X`
together with the cluster being a finite union of closed discs.  Both facts are recorded here in the
sharpest form currently available. -/

/-- **The pieces are preconnected, and closed in `Ω₀ᶜ`.** -/
theorem isPreconnected_connectedComponentIn_and_closedIn (F : Set X) (x : X) :
    IsPreconnected (connectedComponentIn F x) ∧
      ∀ y, y ∈ closure (connectedComponentIn F x) → y ∈ F → y ∈ connectedComponentIn F x :=
  ⟨isPreconnected_connectedComponentIn, fun y hy hyF =>
    Work.SimplyConnected.ABS.eq_of_mem_closure_connectedComponentIn hyF hy⟩

/-- **The type-indexed complement computation.**  The two families `A` (relatively compact pieces) and
`B` (the rest) cover `Ω₀ᶜ`, lie in it, and are pairwise disjoint (within and across the families);
then `(Ω₀ ∪ ⋃ A)ᶜ = ⋃ B`. -/
theorem compl_union_iUnion_eq_iUnion {Ω₀ : Set X} {σ τ : Type*} (A : σ → Set X) (B : τ → Set X)
    (hZsubA : ∀ i, A i ⊆ Ω₀ᶜ) (hZsubB : ∀ j, B j ⊆ Ω₀ᶜ)
    (hcover : Ω₀ᶜ ⊆ (⋃ i, A i) ∪ (⋃ j, B j))
    (hdA : ∀ i j, i ≠ j → ∀ x, x ∈ A i → x ∈ A j → False)
    (hdB : ∀ i j, i ≠ j → ∀ x, x ∈ B i → x ∈ B j → False)
    (hdAB : ∀ i j, ∀ x, x ∈ A i → x ∈ B j → False) :
    (Ω₀ ∪ ⋃ i, A i)ᶜ = ⋃ j, B j := by
  ext x
  constructor
  · intro hx
    have hxΩ₀ : x ∉ Ω₀ := fun h => hx (Or.inl h)
    have hxA : x ∉ ⋃ i, A i := fun h => hx (Or.inr h)
    rcases hcover hxΩ₀ with hx' | hx'
    · obtain ⟨i, hi⟩ : ∃ i, x ∈ A i := by simpa only [Set.mem_iUnion] using hx'
      exact absurd (mem_iUnion.mpr ⟨i, hi⟩) hxA
    · simpa only [Set.mem_iUnion] using hx'
  · intro hx
    obtain ⟨j, hxj⟩ : ∃ j, x ∈ B j := by simpa only [Set.mem_iUnion] using hx
    intro hy
    rcases hy with hy | hy
    · exact hZsubB j hxj hy
    · obtain ⟨i, hi⟩ : ∃ i, x ∈ A i := by simpa only [Set.mem_iUnion] using hy
      exact hdAB i j x hi hxj

/-- **The tile-data lemma.**  Given the decomposition of `Ω₀ᶜ` into the finite families `A` (relatively
compact pieces) and `B` (the rest), with the five obligations of §11 — closedness (`hAcl`, `hBcl`),
preconnectedness, inclusion, cover, pairwise disjointness — plus attachment `A i ∩ closure Ω₀ ≠ ∅`,
compactness of `closure (A i)`, and `Nonempty τ` with `¬ IsCompact (closure (B j))`, the filled set
`Ω := Ω₀ ∪ ⋃ A` satisfies the conclusion of (FILL):

  `Ω` open, connected, relatively compact, containing `Ω₀`, with no relatively compact complementary
  component.

It is the assembled filling step; what remains for the tile bookkeeping is to *produce* `A`, `B` for a
cluster of tiles (in particular to discharge `hBcl`, see §13), not to redo this. -/
theorem exists_fill_of_finite_closed_pieces {Ω₀ : Set X} {σ τ : Type*} [Fintype σ] [Fintype τ]
    (A : σ → Set X) (B : τ → Set X)
    (hΩo : IsOpen Ω₀) (hΩc : IsPreconnected Ω₀) (hΩne : Ω₀.Nonempty)
    (hΩpre : IsCompact (closure Ω₀))
    (hAcl : ∀ i, IsClosed (A i)) (hBcl : ∀ j, IsClosed (B j))
    (hAc : ∀ i, IsPreconnected (A i)) (hBc : ∀ j, IsPreconnected (B j))
    (hZsubA : ∀ i, A i ⊆ Ω₀ᶜ) (hZsubB : ∀ j, B j ⊆ Ω₀ᶜ)
    (hcover : Ω₀ᶜ ⊆ (⋃ i, A i) ∪ (⋃ j, B j))
    (hdA : ∀ i j, i ≠ j → ∀ x, x ∈ A i → x ∈ A j → False)
    (hdB : ∀ i j, i ≠ j → ∀ x, x ∈ B i → x ∈ B j → False)
    (hdAB : ∀ i j, ∀ x, x ∈ A i → x ∈ B j → False)
    (hAcomp : ∀ i, IsCompact (closure (A i))) (hatt : ∀ i, (A i ∩ closure Ω₀).Nonempty)
    (hne : Nonempty τ) (hBnt : ∀ j, ¬ IsCompact (closure (B j))) :
    ∃ Ω : Set X, IsOpen Ω ∧ IsConnected Ω ∧ IsCompact (closure Ω) ∧ Ω₀ ⊆ Ω ∧
      ∀ x : X, x ∉ Ω → ¬ IsCompact (closure (connectedComponentIn (Ωᶜ) x)) := by
  have hBsub : ∀ j, B j ⊆ (Ω₀ ∪ ⋃ i, A i)ᶜ := by
    intro j x hx
    rintro (hxΩ₀ | hxA)
    · exact hZsubB j hx hxΩ₀
    · obtain ⟨i, hi⟩ : ∃ i, x ∈ A i := by simpa only [Set.mem_iUnion] using hxA
      exact hdAB i j x hi hx
  exact ⟨Ω₀ ∪ ⋃ i, A i,
    isOpen_isConnected_isCompact_closure_of_finite_decomposition A B hΩo hΩc hΩne hΩpre
      hBcl hAc hBc rfl
      (compl_union_iUnion_eq_iUnion A B hZsubA hZsubB hcover hdA hdB hdAB) hBsub hAcomp hatt hne hBnt⟩

/-! ## Attachment: a relatively compact piece meets `closure Ω₀`

The `hatt` obligation of `exists_fill_of_finite_closed_pieces`.  Contrapositive: if a component `A` of
`Ω₀ᶜ` misses `closure Ω₀`, then `A ⊆ interior Ω₀ᶜ`; `A` is closed in `X` (Ω₀ᶜ is closed and contains
`closure A`, and a limit point of `A` inside `Ω₀ᶜ` lies in `A`), and `A` is open in `X` (local
connectedness: the component in `interior Ω₀ᶜ` of a point of `A` is a neighbourhood of it contained in
`A`).  So `A` is clopen, hence `A = X` by connectedness, hence `closure A = X` is compact — contradicting
the relative compactness of the piece. -/
theorem inter_closure_nonempty_of_isCompact_closure_connectedComponentIn [LocallyConnectedSpace X]
    [ConnectedSpace X] (hX : ¬ CompactSpace X) {Ω₀ : Set X} (hΩo : IsOpen Ω₀) {x : X}
    (hx : x ∈ Ω₀ᶜ) (hc : IsCompact (closure (connectedComponentIn (Ω₀ᶜ) x))) :
    (connectedComponentIn (Ω₀ᶜ) x ∩ closure Ω₀).Nonempty := by
  classical
  set A := connectedComponentIn (Ω₀ᶜ) x with hA
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have hAsub : A ⊆ Ω₀ᶜ := connectedComponentIn_subset (Ω₀ᶜ) x
  have hcl_compl : IsClosed (Ω₀ᶜ) := isClosed_compl_iff.mpr hΩo
  have hAcl : IsClosed A := by
    rw [← closure_subset_iff_isClosed]
    intro y hy
    refine Work.SimplyConnected.ABS.eq_of_mem_closure_connectedComponentIn ?_ hy
    exact closure_minimal hAsub hcl_compl hy
  have hAsub' : A ⊆ (closure Ω₀)ᶜ := by
    intro y hy hyc
    have hmem : y ∈ A ∩ closure Ω₀ := ⟨hy, hyc⟩
    rw [hcon] at hmem
    exact Set.notMem_empty y hmem
  have hAop : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    refine Filter.mem_of_superset
      (connectedComponentIn_mem_nhds ((isClosed_closure.isOpen_compl).mem_nhds (hAsub' hy))) ?_
    intro z hz
    have h1 : z ∈ connectedComponentIn (Ω₀ᶜ) y :=
      IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
        (mem_connectedComponentIn (hAsub' hy))
        (fun w hw hwΩ => connectedComponentIn_subset ((closure Ω₀)ᶜ) y hw (subset_closure hwΩ))
        hz
    first
    | rwa [connectedComponentIn_eq hy] at h1
    | rwa [← connectedComponentIn_eq hy] at h1
  have huniv : A = Set.univ := IsClopen.eq_univ ⟨hAcl, hAop⟩ ⟨x, mem_connectedComponentIn hx⟩
  rw [huniv, closure_univ] at hc
  exact hX (isCompact_univ_iff.mp hc)

/-! ## Components of a closed set are closed in the ambient space

This is the fact §13 doubted and the review of §19 forced out: a component of a **closed** set `F` is
closed in `X`, because `closure (connectedComponentIn F x) ⊆ closure F = F` and any point of `F` in that
closure already lies in the component
(`Work.SimplyConnected.ABS.eq_of_mem_closure_connectedComponentIn`).  The classical warning — a
component accumulating outside its set, e.g. `{(0,0)} ∪ {(x, sin (1/x)) : x > 0}` — does not apply,
because that set is *not closed* (its closure contains `{0} × [-1,1]`).

Consequence for the filling: with `Ω₀` open, `Ω₀ᶜ` is closed, so **every** piece is closed in `X`, and
with finitely many pieces (FIN) the union of the `B`-pieces is a finite union of closed sets, hence
closed: §18's obligation is discharged. -/
theorem isClosed_connectedComponentIn_of_isClosed {F : Set X} (hF : IsClosed F) (x : X) :
    IsClosed (connectedComponentIn F x) := by
  rw [← closure_subset_iff_isClosed]
  intro y hy
  have hyF : y ∈ F := hF.closure_eq ▸ (closure_mono (connectedComponentIn_subset F x)) hy
  exact Work.SimplyConnected.ABS.eq_of_mem_closure_connectedComponentIn hyF hy

/-! ## The first FIN-supplied hypothesis of the packaging: `Nonempty τ`

`exists_fill_of_finite_closed_pieces` needs a *non-relatively-compact* component of `Ω₀ᶜ` to exist
(otherwise `Ω = Ω₀ ∪ ⋃ A = X` and there is nothing to prove about its complement).  With finitely many
components this follows from non-compactness of `X`: if every component had compact closure, `Ω₀ᶜ` would
be contained in a finite union of compact sets, hence compact, and `X = Ω₀ ∪ Ω₀ᶜ` would be compact. -/
theorem exists_not_isCompact_closure_connectedComponentIn {Ω₀ : Set X} (hΩo : IsOpen Ω₀)
    (hΩk : IsCompact (closure Ω₀)) (hX : ¬ CompactSpace X)
    (hfin : {Z : Set X | ∃ x, Z = connectedComponentIn (Ω₀ᶜ) x}.Finite) :
    ∃ x, ¬ IsCompact (closure (connectedComponentIn (Ω₀ᶜ) x)) := by
  classical
  by_contra hcon
  push_neg at hcon
  have hK : IsCompact (⋃ Z ∈ hfin.toFinset, closure Z) :=
    Finset.isCompact_biUnion _ fun Z hZ => by
      obtain ⟨x, rfl⟩ := hfin.mem_toFinset.mp hZ
      exact hcon x
  have hsub : Ω₀ᶜ ⊆ ⋃ Z ∈ hfin.toFinset, closure Z := by
    intro x hx
    exact mem_biUnion (hfin.mem_toFinset.mpr ⟨x, rfl⟩) (subset_closure (mem_connectedComponentIn hx))
  have hcomp : IsCompact (Ω₀ᶜ) :=
    hK.of_isClosed_subset (isClosed_compl_iff.mpr hΩo) hsub
  have huniv : IsCompact (Set.univ : Set X) :=
    (hΩk.union hcomp).of_isClosed_subset isClosed_univ (by
      rw [← union_compl_self Ω₀]
      exact fun x hx => hx.elim (fun h1 => Or.inl (subset_closure h1)) (fun h2 => Or.inr h2))
  exact hX (isCompact_univ_iff.mp huniv)

/-! ## The corrected σ/τ indexing, and `hatt` on it (§25)

The families must be indexed by points of `Ω₀ᶜ`: `connectedComponentIn Ω₀ᶜ x = ∅` for `x ∉ Ω₀ᶜ`, so the
naive index set contains `∅`, whose closure is compact, and `hatt` (`A i ∩ closure Ω₀ ≠ ∅`) fails on it.
With the corrected indexing, `hatt` is the landed attachment lemma verbatim. -/
theorem inter_closure_nonempty_of_isCompact_closure_of_mem_components {Ω₀ : Set X}
    [LocallyConnectedSpace X] [ConnectedSpace X] (hX : ¬ CompactSpace X) (hΩo : IsOpen Ω₀)
    {Z : Set X} (hZ : ∃ x ∈ Ω₀ᶜ, Z = connectedComponentIn (Ω₀ᶜ) x)
    (hc : IsCompact (closure Z)) : (Z ∩ closure Ω₀).Nonempty := by
  obtain ⟨x, hx, rfl⟩ := hZ
  exact inter_closure_nonempty_of_isCompact_closure_connectedComponentIn hX hΩo hx hc

/-! ## The finset table (§26): rows for `hfin.toFinset`

The bookkeeping of `exists_fill_of_finite_components` runs off the finset of components that FIN
supplies.  Its first row — the pieces cover `Ω₀ᶜ` — is proved here; every other row leans on it. -/

/-- **The cover row.**  `Ω₀ᶜ` is the union of the (finitely many) components of `Ω₀ᶜ`. -/
theorem compl_eq_biUnion_toFinset {Ω₀ : Set X}
    (hfin : {Z : Set X | ∃ x, Z = connectedComponentIn (Ω₀ᶜ) x}.Finite) :
    Ω₀ᶜ = ⋃ Z ∈ hfin.toFinset, Z := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    exact mem_biUnion (hfin.mem_toFinset.mpr ⟨x, rfl⟩) (mem_connectedComponentIn hx)
  · intro x hx
    obtain ⟨Z, hZt, hxZ⟩ : ∃ Z, Z ∈ hfin.toFinset ∧ x ∈ Z := by
      simpa only [Set.mem_iUnion, exists_prop] using hx
    obtain ⟨y, hy⟩ := hfin.mem_toFinset.mp hZt
    exact connectedComponentIn_subset (Ω₀ᶜ) y (hy ▸ hxZ)

/-- **The membership row (`htmem`).**  The elements of `hfin.toFinset` are exactly the connected
components of `Ω₀ᶜ`. -/
theorem mem_toFinset_components {Ω₀ : Set X}
    (hfin : {Z : Set X | ∃ x, Z = connectedComponentIn (Ω₀ᶜ) x}.Finite) {Z : Set X} :
    Z ∈ hfin.toFinset ↔ ∃ x, Z = connectedComponentIn (Ω₀ᶜ) x :=
  hfin.mem_toFinset

/-! ## The openness row of the finset table

Two steps: each piece is closed (`isClosed_connectedComponentIn_of_isClosed`, since `Ω₀ᶜ` is closed when
`Ω₀` is open), and a finite union of pieces is closed.  With `compl_eq_biUnion_toFinset` and the
disjointness of distinct components, these give that `Ωᶜ` is closed, i.e. that the filled set is open. -/

/-- **Each piece is closed.** -/
theorem isClosed_connectedComponentIn_compl {Ω₀ : Set X} (hΩo : IsOpen Ω₀) {Z : Set X}
    (hZ : ∃ x, Z = connectedComponentIn (Ω₀ᶜ) x) : IsClosed Z := by
  obtain ⟨x, rfl⟩ := hZ
  exact isClosed_connectedComponentIn_of_isClosed (isClosed_compl_iff.mpr hΩo) x

/-- **A finite union of pieces is closed.** -/
theorem isClosed_biUnion_components {Ω₀ : Set X} (hΩo : IsOpen Ω₀) {t : Finset (Set X)}
    (ht : ∀ Z ∈ t, ∃ x, Z = connectedComponentIn (Ω₀ᶜ) x) :
    IsClosed (⋃ Z ∈ t, Z) := by
  classical
  exact isClosed_biUnion_finset fun Z hZ => isClosed_connectedComponentIn_compl hΩo (ht Z hZ)

/-- **The identification of the openness row.**  If `sG` is the family of relatively compact components
of `Ω₀ᶜ` and `sB` the complementary family (both as finsets characterised by membership), and the two
families are disjoint pointwise, then

  `(Ω₀ ∪ ⋃ Z ∈ sG, Z)ᶜ = ⋃ Z ∈ sB, Z`.

Used with `isClosed_biUnion_components` (landed) this makes the filled set open, since each member of
`sB` is closed.  The proof is set algebra over `compl_eq_biUnion_toFinset` (cover) and the disjointness. -/
theorem compl_union_eq_biUnion_of_not_isCompact {Ω₀ : Set X}
    (hfin : {Z : Set X | ∃ x, Z = connectedComponentIn (Ω₀ᶜ) x}.Finite)
    {sG sB : Finset (Set X)}
    (hsG : ∀ Z, Z ∈ sG ↔ IsCompact (closure Z) ∧ ∃ x ∈ Ω₀ᶜ, Z = connectedComponentIn (Ω₀ᶜ) x)
    (hsB : ∀ Z, Z ∈ sB ↔ ¬ IsCompact (closure Z) ∧ ∃ x ∈ Ω₀ᶜ, Z = connectedComponentIn (Ω₀ᶜ) x)
    (hdisj : ∀ Z ∈ sG, ∀ Z' ∈ sB, ∀ x, x ∈ Z → x ∈ Z' → False) :
    (Ω₀ ∪ ⋃ Z ∈ sG, Z)ᶜ = ⋃ Z ∈ sB, Z := by
  ext x
  constructor
  · intro hx
    have hxΩ : x ∉ Ω₀ := fun h => hx (Or.inl h)
    have hxG : ∀ Z ∈ sG, x ∉ Z := fun Z hZ hxZ => hx (Or.inr (mem_biUnion hZ hxZ))
    have hxU : x ∈ ⋃ Z ∈ hfin.toFinset, Z := by
      rw [← compl_eq_biUnion_toFinset hfin]
      exact hxΩ
    obtain ⟨Z, hZt, hxZ⟩ : ∃ Z, Z ∈ hfin.toFinset ∧ x ∈ Z := by
      simpa only [Set.mem_iUnion, exists_prop] using hxU
    obtain ⟨y, hy⟩ : ∃ y, Z = connectedComponentIn (Ω₀ᶜ) y :=
      (mem_toFinset_components hfin).mp hZt
    have hyΩ : y ∈ Ω₀ᶜ := by
      by_contra hyc
      have hZempty : Z = ∅ := by rw [hy, connectedComponentIn_eq_empty hyc]
      rw [hZempty] at hxZ
      exact Set.notMem_empty x hxZ
    have hZnc : ¬ IsCompact (closure Z) :=
      fun hc => hxG Z ((hsG Z).mpr ⟨hc, y, hyΩ, hy⟩) hxZ
    exact mem_biUnion ((hsB Z).mpr ⟨hZnc, y, hyΩ, hy⟩) hxZ
  · intro hx
    obtain ⟨Z, hZsB, hxZ⟩ : ∃ Z, Z ∈ sB ∧ x ∈ Z := by
      simpa only [Set.mem_iUnion, exists_prop] using hx
    obtain ⟨hZc, a, ha, hZa⟩ := (hsB Z).mp hZsB
    refine fun hy => ?_
    rcases hy with hy | hy
    · exact (connectedComponentIn_subset (Ω₀ᶜ) a (hZa ▸ hxZ)) hy
    · obtain ⟨Z', hZ'sG, hxZ'⟩ : ∃ Z', Z' ∈ sG ∧ x ∈ Z' := by
        simpa only [Set.mem_iUnion, exists_prop] using hy
      exact hdisj Z' hZ'sG Z hZsB x hxZ' hxZ

/-! ## Restored rows (see NOTES §35: an editing slip)

The preconnectedness, compactness and pointwise rows, restored verbatim after a block replacement
accidentally removed them. -/
theorem isPreconnected_union_iUnion_of_isCompact_closure_components {Ω₀ : Set X}
    [LocallyConnectedSpace X] [ConnectedSpace X] (hX : ¬ CompactSpace X) (hΩo : IsOpen Ω₀)
    (hΩc : IsPreconnected Ω₀) {σ : Type*} [Fintype σ] {A : σ → Set X}
    (hA : ∀ i, IsCompact (closure (A i)) ∧ ∃ x ∈ Ω₀ᶜ, A i = connectedComponentIn (Ω₀ᶜ) x) :
    IsPreconnected (Ω₀ ∪ ⋃ i, A i) := by
  refine isPreconnected_union_iUnion_of_inter_closure A hΩc (fun i => ?_) (fun i => ?_)
  · obtain ⟨-, a, -, ha⟩ := hA i
    exact ha ▸ isPreconnected_connectedComponentIn
  · obtain ⟨hc, a, ha, hAa⟩ := hA i
    exact inter_closure_nonempty_of_isCompact_closure_of_mem_components hX hΩo ⟨a, ha, hAa⟩ hc

theorem isCompact_closure_union_iUnion_of_isCompact_closure_components {Ω₀ : Set X}
    {σ : Type*} [Fintype σ] {A : σ → Set X} (hΩpre : IsCompact (closure Ω₀))
    (hA : ∀ i, IsCompact (closure (A i))) :
    IsCompact (closure (Ω₀ ∪ ⋃ i, A i)) := by
  refine isCompact_closure_of_subset_closure_union hΩpre (isCompact_iUnion fun i => hA i) ?_
  rintro x (hx | hx)
  · exact Or.inl (subset_closure hx)
  · obtain ⟨i, hi⟩ : ∃ i, x ∈ A i := by simpa only [Set.mem_iUnion] using hx
    exact Or.inr (mem_iUnion.mpr ⟨i, subset_closure hi⟩)

theorem not_isCompact_closure_componentIn_union_components {Ω₀ : Set X} {σ : Type*}
    {A : σ → Set X}
    (hA : ∀ i, ∃ y ∈ Ω₀ᶜ, A i = connectedComponentIn (Ω₀ᶜ) y)
    (hcov : ∀ Z, (∃ y ∈ Ω₀ᶜ, Z = connectedComponentIn (Ω₀ᶜ) y) → IsCompact (closure Z) →
      ∃ i, A i = Z) :
    ∀ x, x ∉ Ω₀ ∪ ⋃ i, A i →
      ¬ IsCompact (closure (connectedComponentIn ((Ω₀ ∪ ⋃ i, A i)ᶜ) x)) := by
  intro x hx
  have hxΩ₀ : x ∉ Ω₀ := fun h => hx (Or.inl h)
  have hxA : ∀ i, x ∉ A i := fun i hi => hx (Or.inr (mem_iUnion.mpr ⟨i, hi⟩))
  have hZsub : connectedComponentIn (Ω₀ᶜ) x ⊆ ((Ω₀ ∪ ⋃ i, A i))ᶜ := by
    intro z hz
    have hzΩ : z ∉ Ω₀ := connectedComponentIn_subset (Ω₀ᶜ) x hz
    rintro (h1 | h1)
    · exact hzΩ h1
    · obtain ⟨i, hi⟩ : ∃ i, z ∈ A i := by simpa only [Set.mem_iUnion] using h1
      obtain ⟨b, hb, hAb⟩ := hA i
      rcases connectedComponentIn_eq_or_notMem (F := Ω₀ᶜ) b x with heq | hdis
      · exact hxA i (hAb ▸ heq ▸ mem_connectedComponentIn hxΩ₀)
      · exact hdis z (hAb ▸ hi) hz
  have hZnc : ¬ IsCompact (closure (connectedComponentIn (Ω₀ᶜ) x)) := by
    intro hc
    obtain ⟨i, hi⟩ := hcov _ ⟨x, hxΩ₀, rfl⟩ hc
    exact hxA i (hi ▸ mem_connectedComponentIn hxΩ₀)
  exact not_isCompact_closure_connectedComponentIn_of_isPreconnected_subset
    isPreconnected_connectedComponentIn hZsub (mem_connectedComponentIn hxΩ₀) hZnc

end Work.Topology.Engulf
