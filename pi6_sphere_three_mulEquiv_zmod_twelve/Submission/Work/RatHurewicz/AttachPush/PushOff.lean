import Mathlib
import Submission.Work.RatHurewicz.AttachPush.PushOffAux

/-!
# The push-off homotopy

A continuous map `h : X → attachCells n Y ι f` which misses every cell centre is homotopic, through
maps missing the centres, into the range of `attachIncl`: push every cell radially from its centre
onto its boundary sphere.  The push is defined on the complement of the centres and descends to
`attachCells n Y ι f` because it fixes the boundary spheres, which is where the gluing happens.
-/

set_option maxHeartbeats 1600000

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellSphere n, Y)}

/-! ### Membership in the push domain -/

theorem mem_pushDomain_iff (a : Y ⊕ (Σ _ : ι, cellDisk n)) :
    a ∈ pushDomain n Y ι f ↔
      (∃ y : Y, a = Sum.inl y) ∨
        ∃ (i : ι) (x : cellDisk n), (x : CellVec n) ≠ 0 ∧ a = Sum.inr ⟨i, x⟩ := by
  constructor
  · intro ha
    rcases a with y | p
    · exact Or.inl ⟨y, rfl⟩
    · refine Or.inr ⟨p.1, p.2, ?_, rfl⟩
      intro h0
      refine ha ⟨p.1, ?_⟩
      show cellOrigin n Y ι f p.1 = Quotient.mk'' (Sum.inr (⟨p.1, p.2⟩ : Σ _ : ι, cellDisk n))
      have hxeq : p.2 = cellDiskCentre n := Subtype.ext h0
      rw [hxeq]
      rfl
  · rintro (⟨y, rfl⟩ | ⟨i, x, hx, rfl⟩)
    · intro hQ
      obtain ⟨j, hj⟩ := Set.mem_range.mp hQ
      refine cellOrigin_notMem_range_attachIncl (f := f) j ?_
      rw [hj]
      exact ⟨y, rfl⟩
    · intro hQ
      obtain ⟨j, hj⟩ := Set.mem_range.mp hQ
      exact cellMap_ne_cellOrigin hx j hj.symm

/-! ### The two kinds of points of the push domain -/

/-- The points of the push domain lying over `Y`. -/
def pushPieceInl (Y : Type) (ι : Type) (n : ℕ) : Set (Y ⊕ (Σ _ : ι, cellDisk n)) :=
  {a | ∃ y : Y, a = Sum.inl y}

/-- The non-boundary points of the `i`-th summand, inside the push domain. -/
def pushPieceInr (Y : Type) (ι : Type) (n : ℕ) (i : ι) : Set (Y ⊕ (Σ _ : ι, cellDisk n)) :=
  {a | ∃ x : cellDisk n, (x : CellVec n) ≠ 0 ∧ a = Sum.inr ⟨i, x⟩}

theorem isOpen_puncturedSet : IsOpen ({x : cellDisk n | (x : CellVec n) ≠ 0} : Set (cellDisk n)) :=
  (isClosed_singleton (x := (0 : CellVec n))).isOpen_compl.preimage continuous_subtype_val

theorem isOpen_pushPieceInl : IsOpen (pushPieceInl Y ι n) := by
  rw [isOpen_sum_iff]
  refine ⟨?_, ?_⟩
  · have h : Sum.inl ⁻¹' pushPieceInl Y ι n = Set.univ := by
      ext y
      exact ⟨fun _ => trivial, fun _ => ⟨y, rfl⟩⟩
    rw [h]; exact isOpen_univ
  · have h : Sum.inr ⁻¹' pushPieceInl Y ι n = ∅ := by
      ext p
      constructor
      · rintro ⟨y, hy⟩
        exact absurd hy (Sum.inr_ne_inl)
      · intro h; exact absurd h (Set.notMem_empty p)
    rw [h]; exact isOpen_empty

theorem isOpen_pushPieceInr (i : ι) : IsOpen (pushPieceInr Y ι n i) := by
  rw [isOpen_sum_iff]
  refine ⟨?_, ?_⟩
  · have h : Sum.inl ⁻¹' pushPieceInr Y ι n i = ∅ := by
      ext y
      constructor
      · rintro ⟨x, -, hy⟩
        exact absurd hy (Sum.inl_ne_inr)
      · intro h; exact absurd h (Set.notMem_empty y)
    rw [h]; exact isOpen_empty
  · rw [isOpen_sigma_iff]
    intro j
    by_cases hji : j = i
    · subst j
      have h : Sigma.mk i ⁻¹' (Sum.inr ⁻¹' pushPieceInr Y ι n i) =
          {x : cellDisk n | (x : CellVec n) ≠ 0} := by
        ext x
        constructor
        · rintro ⟨x', hx', h⟩
          have h2 : (⟨i, x⟩ : Σ _ : ι, cellDisk n) = ⟨i, x'⟩ := Sum.inr.inj h
          have h3 : x = x' := congrArg (fun p : Σ _ : ι, cellDisk n => p.2) h2
          rwa [h3]
        · intro hx
          exact ⟨x, hx, rfl⟩
      rw [h]
      exact isOpen_puncturedSet
    · have h : Sigma.mk j ⁻¹' (Sum.inr ⁻¹' pushPieceInr Y ι n i) = ∅ := by
        ext x
        constructor
        · rintro ⟨x', -, h⟩
          have h2 : (⟨j, x⟩ : Σ _ : ι, cellDisk n) = ⟨i, x'⟩ := Sum.inr.inj h
          exact absurd (congrArg (fun p : Σ _ : ι, cellDisk n => p.1) h2) hji
        · intro h; exact absurd h (Set.notMem_empty x)
      rw [h]; exact isOpen_empty

theorem pushDomain_eq_pieces :
    pushDomain n Y ι f = pushPieceInl Y ι n ∪ ⋃ i, pushPieceInr Y ι n i := by
  ext a
  rw [mem_pushDomain_iff]
  constructor
  · rintro (⟨y, rfl⟩ | ⟨i, x, hx, rfl⟩)
    · exact Or.inl ⟨y, rfl⟩
    · exact Or.inr (Set.mem_iUnion.mpr ⟨i, x, hx, rfl⟩)
  · rintro (⟨y, hy⟩ | h)
    · exact Or.inl ⟨y, hy⟩
    · obtain ⟨i, x, hx, hxa⟩ := Set.mem_iUnion.mp h
      exact Or.inr ⟨i, x, hx, hxa⟩

/-! ### The radial push, as a function on the disjoint union -/

/-- The radial push of the cells, as a (total) function on the disjoint union; the branch at the
centres is a junk value and is never used, because the push is only evaluated on
`pushDomain n Y ι f`. -/
def pushGarbage (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) (a : Y ⊕ (Σ _ : ι, cellDisk n)) (s : I) :
    attachCells n Y ι f :=
  Sum.elim (fun y : Y => attachIncl n Y ι f y)
    (fun p : Σ _ : ι, cellDisk n =>
      if h : (p.2 : CellVec n) ≠ 0 then
        cellMap n Y ι f p.1 (cellPush n (⟨p.2, h⟩, s))
      else cellOrigin n Y ι f p.1) a

@[simp] theorem pushGarbage_inl (y : Y) (s : I) :
    pushGarbage n Y ι f (Sum.inl y) s = attachIncl n Y ι f y := rfl

theorem pushGarbage_inr {i : ι} {x : cellDisk n} (hx : (x : CellVec n) ≠ 0) (s : I) :
    pushGarbage n Y ι f (Sum.inr ⟨i, x⟩) s =
      cellMap n Y ι f i (cellPush n (⟨x, hx⟩, s)) := by
  show (if h : (x : CellVec n) ≠ 0 then
      cellMap n Y ι f i (cellPush n (⟨x, h⟩, s)) else cellOrigin n Y ι f i) = _
  rw [dif_pos hx]

/-- The push domain is saturated for the gluing relation. -/
theorem mem_pushDomain_of_eqvGen {a b : Y ⊕ (Σ _ : ι, cellDisk n)}
    (hab : Relation.EqvGen (attachRel n Y ι f) a b) (ha : a ∈ pushDomain n Y ι f) :
    b ∈ pushDomain n Y ι f := by
  have hq : (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f)) a : attachCells n Y ι f)
      = Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f)) b :=
    Quotient.sound (s := Relation.EqvGen.setoid (attachRel n Y ι f)) hab
  intro hb
  exact ha (hq.symm ▸ hb)

/-- **The push is well defined on the quotient**: points related by the gluing have the same push. -/
theorem pushGarbage_eq_of_eqvGen :
    ∀ (s : I) {a b : Y ⊕ (Σ _ : ι, cellDisk n)},
      Relation.EqvGen (attachRel n Y ι f) a b → a ∈ pushDomain n Y ι f →
      b ∈ pushDomain n Y ι f → pushGarbage n Y ι f a s = pushGarbage n Y ι f b s := by
  intro s a b hab
  induction hab with
  | rel a b hab =>
    intro ha hb
    obtain ⟨i, z, rfl, rfl⟩ := hab
    rw [pushGarbage_inl]
    rw [pushGarbage_inr (i := i) (x := cellSphereToDisk n z)
      (hx := ne_zero_of_mem_pushDomain hb) s]
    have hzne : ((cellSphereToDisk n z : cellDisk n) : CellVec n) ≠ 0 :=
      ne_zero_of_mem_pushDomain hb
    have hkey : cellPush n ((⟨cellSphereToDisk n z, hzne⟩ : ↥(puncturedCellDisk n)), s)
        = cellSphereToDisk n z :=
      Subtype.ext (cellPushVec_sphere n s (norm_cellSphereToDisk n z))
    rw [hkey, ← attachIncl_attachRel n Y ι f i z]
  | refl a => intro ha hb; rfl
  | symm a b hab ih => intro ha hb; exact (ih hb ha).symm
  | trans a b c hab hbc ih1 ih2 =>
    intro ha hc
    exact (ih1 ha (mem_pushDomain_of_eqvGen hab ha)).trans
      (ih2 (mem_pushDomain_of_eqvGen hab ha) hc)

/-! ### Elementary properties of the push -/

/-- At time `0` the push is the identity. -/
theorem pushGarbage_zero {a : Y ⊕ (Σ _ : ι, cellDisk n)} (ha : a ∈ pushDomain n Y ι f) :
    pushGarbage n Y ι f a 0 = (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f))
      a : attachCells n Y ι f) := by
  have ha' := (mem_pushDomain_iff (n := n) (Y := Y) (ι := ι) (f := f) a).mp ha
  rcases ha' with ⟨y, rfl⟩ | ⟨i, x, hx, rfl⟩
  · rw [pushGarbage_inl]; rfl
  · rw [pushGarbage_inr (i := i) (hx := hx)]
    exact congrArg (cellMap n Y ι f i) (cellPush_zero n ⟨x, hx⟩)

/-- At time `1` the push lands on the boundary spheres, i.e. in the range of `attachIncl`. -/
theorem pushGarbage_one_mem {a : Y ⊕ (Σ _ : ι, cellDisk n)} (ha : a ∈ pushDomain n Y ι f) :
    pushGarbage n Y ι f a 1 ∈ Set.range (attachIncl n Y ι f) := by
  have ha' := (mem_pushDomain_iff (n := n) (Y := Y) (ι := ι) (f := f) a).mp ha
  rcases ha' with ⟨y, rfl⟩ | ⟨i, x, hx, rfl⟩
  · rw [pushGarbage_inl]; exact ⟨y, rfl⟩
  · rw [pushGarbage_inr (i := i) (hx := hx)]
    have hsphere := cellPush_one_mem_sphere n ⟨x, hx⟩
    let z : cellSphere n := ⟨(cellPush n (⟨x, hx⟩, 1) : cellDisk n), hsphere⟩
    have hz : cellSphereToDisk n z = cellPush n (⟨x, hx⟩, 1) := Subtype.ext rfl
    rw [← hz, ← attachIncl_attachRel n Y ι f i z]
    exact ⟨f i z, rfl⟩

/-- The push is the identity on the range of `attachIncl`. -/
theorem pushGarbage_fix {a : Y ⊕ (Σ _ : ι, cellDisk n)} (ha : a ∈ pushDomain n Y ι f)
    (hA : (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f)) a :
      attachCells n Y ι f) ∈ Set.range (attachIncl n Y ι f)) (s : I) :
    pushGarbage n Y ι f a s = (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f))
      a : attachCells n Y ι f) := by
  obtain ⟨y, hy⟩ := hA
  have hb : (Sum.inl y : Y ⊕ (Σ _ : ι, cellDisk n)) ∈ pushDomain n Y ι f := by
    intro hQ
    obtain ⟨j, hj⟩ := Set.mem_range.mp hQ
    exact cellOrigin_notMem_range_attachIncl (f := f) j (by rw [hj]; exact ⟨y, rfl⟩)
  have hrel : Relation.EqvGen (attachRel n Y ι f) a (Sum.inl y) :=
    Quotient.exact (s := Relation.EqvGen.setoid (attachRel n Y ι f))
      (show (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f)) a :
          attachCells n Y ι f)
        = Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f)) (Sum.inl y)
        from hy.symm)
  rw [pushGarbage_eq_of_eqvGen s hrel ha hb, pushGarbage_inl]
  exact hy


/-! ### Continuity of the push -/

/-- Continuity is local for an open cover. -/
theorem continuous_of_isOpen_cover {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    {κ : Type*} {U : κ → Set X} (hU : ∀ k, IsOpen (U k)) (hcov : (⋃ k, U k) = Set.univ)
    {g : X → Z} (hg : ∀ k, Continuous fun x : ↥(U k) => g x) : Continuous g := by
  rw [continuous_def]
  intro O hO
  have hpre : g ⁻¹' O = ⋃ k, Subtype.val '' ((fun x : ↥(U k) => g x) ⁻¹' O) := by
    ext x
    constructor
    · intro hx
      have hxU : x ∈ ⋃ k, U k := by rw [hcov]; trivial
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hxU
      exact Set.mem_iUnion.mpr ⟨k, ⟨⟨x, hk⟩, hx, rfl⟩⟩
    · intro hx
      obtain ⟨k, y, hy, hxy⟩ := Set.mem_iUnion.mp hx
      rw [← hxy]
      exact hy
  rw [hpre]
  refine isOpen_iUnion fun k => ?_
  obtain ⟨W, hW, hWeq⟩ := isOpen_induced_iff.mp ((hg k).isOpen_preimage O hO)
  have hWk : Subtype.val '' ((fun x : ↥(U k) => g x) ⁻¹' O) = U k ∩ W := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      show y ∈ Subtype.val ⁻¹' W
      rw [hWeq]
      exact hy
    · rintro ⟨hxU, hxW⟩
      refine ⟨⟨x, hxU⟩, ?_, rfl⟩
      rw [← hWeq]
      exact hxW
  rw [hWk]
  exact (hU k).inter hW

theorem isOpen_sumInl_image {S : Set Y} (hS : IsOpen S) :
    IsOpen ((Sum.inl '' S) : Set (Y ⊕ (Σ _ : ι, cellDisk n))) := by
  rw [isOpen_sum_iff]
  refine ⟨?_, ?_⟩
  · have h : Sum.inl ⁻¹' (Sum.inl '' S : Set (Y ⊕ (Σ _ : ι, cellDisk n))) = S := by
      ext y
      constructor
      · rintro ⟨y', hy', hyy⟩
        exact (Sum.inl.inj hyy) ▸ hy'
      · intro hy
        exact ⟨y, hy, rfl⟩
    rw [h]; exact hS
  · have h : Sum.inr ⁻¹' (Sum.inl '' S : Set (Y ⊕ (Σ _ : ι, cellDisk n))) = ∅ := by
      ext p
      constructor
      · rintro ⟨y, -, hp⟩
        exact Sum.inl_ne_inr hp
      · intro h; exact absurd h (Set.notMem_empty p)
    rw [h]; exact isOpen_empty

theorem isOpen_sumInr_image {S : Set (cellDisk n)} (hS : IsOpen S) (i : ι) :
    IsOpen ((Sum.inr '' (Sigma.mk i '' S)) : Set (Y ⊕ (Σ _ : ι, cellDisk n))) := by
  rw [isOpen_sum_iff]
  refine ⟨?_, ?_⟩
  · have h : Sum.inl ⁻¹' (Sum.inr '' (Sigma.mk i '' S) : Set (Y ⊕ (Σ _ : ι, cellDisk n))) = ∅ := by
      ext y
      constructor
      · rintro ⟨p, -, hy⟩
        exact Sum.inr_ne_inl hy
      · intro h; exact absurd h (Set.notMem_empty y)
    rw [h]; exact isOpen_empty
  · rw [isOpen_sigma_iff]
    intro j
    by_cases hji : j = i
    · subst j
      have h : Sigma.mk i ⁻¹' (Sum.inr ⁻¹'
          (Sum.inr '' (Sigma.mk i '' S) : Set (Y ⊕ (Σ _ : ι, cellDisk n)))) = S := by
        ext x
        constructor
        · rintro ⟨p, hp, h⟩
          obtain ⟨x', hx', hx'p⟩ := hp
          have h2 : p = (⟨i, x⟩ : Σ _ : ι, cellDisk n) := Sum.inr.inj h
          have h3 : x' = x := by
            rw [← hx'p] at h2
            exact congrArg (fun r : Σ _ : ι, cellDisk n => r.2) h2
          rw [← h3]
          exact hx'
        · intro hx
          exact ⟨⟨i, x⟩, ⟨x, hx, rfl⟩, rfl⟩
      rw [h]; exact hS
    · have h : Sigma.mk j ⁻¹' (Sum.inr ⁻¹'
          (Sum.inr '' (Sigma.mk i '' S) : Set (Y ⊕ (Σ _ : ι, cellDisk n)))) = ∅ := by
        ext x
        constructor
        · rintro ⟨p, hp, hpj⟩
          have h2 : p = (⟨j, x⟩ : Σ _ : ι, cellDisk n) := Sum.inr.inj hpj
          have h3 : j = p.1 :=
            (congrArg (fun r : Σ _ : ι, cellDisk n => r.1) h2).symm
          have h4 : p.1 = i := by
            obtain ⟨x', -, hx'p⟩ := hp
            rw [← hx'p]
          exact hji (h3.trans h4)
        · intro h; exact absurd h (Set.notMem_empty x)
      rw [h]; exact isOpen_empty

/-- **The push is continuous on the push domain.** -/
theorem continuous_pushGarbage :
    Continuous fun p : ↥(pushDomain n Y ι f) × I =>
      pushGarbage n Y ι f (p.1 : Y ⊕ (Σ _ : ι, cellDisk n)) p.2 := by
  classical
  set U : (Unit ⊕ ι) → Set (↥(pushDomain n Y ι f) × I) := fun k =>
    match k with
    | Sum.inl _ => {p | ∃ y : Y, (p.1 : Y ⊕ (Σ _ : ι, cellDisk n)) = Sum.inl y}
    | Sum.inr i => {p | ∃ x : cellDisk n,
        (x : CellVec n) ≠ 0 ∧ (p.1 : Y ⊕ (Σ _ : ι, cellDisk n)) = Sum.inr ⟨i, x⟩} with hUdef
  refine continuous_of_isOpen_cover (U := U) ?_ ?_ ?_
  · rintro (⟨⟩ | i)
    · have hset : U (Sum.inl ()) =
          (fun p : ↥(pushDomain n Y ι f) × I => (p.1 : Y ⊕ (Σ _ : ι, cellDisk n))) ⁻¹'
            pushPieceInl Y ι n := rfl
      rw [hset]
      exact isOpen_pushPieceInl.preimage (by fun_prop)
    · have hset : U (Sum.inr i) =
          (fun p : ↥(pushDomain n Y ι f) × I => (p.1 : Y ⊕ (Σ _ : ι, cellDisk n))) ⁻¹'
            pushPieceInr Y ι n i := rfl
      rw [hset]
      exact (isOpen_pushPieceInr i).preimage (by fun_prop)
  · apply Set.eq_univ_of_forall
    intro p
    have hp : (p.1 : Y ⊕ (Σ _ : ι, cellDisk n)) ∈
        pushPieceInl Y ι n ∪ ⋃ i, pushPieceInr Y ι n i := by
      rw [← pushDomain_eq_pieces]
      exact p.1.2
    rcases hp with h | h
    · exact Set.mem_iUnion.mpr ⟨Sum.inl (), h⟩
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
      exact Set.mem_iUnion.mpr ⟨Sum.inr i, hi⟩
  · rintro (⟨⟩ | i)
    · -- the piece over `Y`
      let ex : ↥(U (Sum.inl ())) → Y := fun q => Classical.choose q.2
      have hex_spec : ∀ q : ↥(U (Sum.inl ())),
          (q.1.1 : Y ⊕ (Σ _ : ι, cellDisk n)) = Sum.inl (ex q) :=
        fun q => Classical.choose_spec q.2
      have hex_cont : Continuous ex := by
        rw [continuous_def]
        intro S hS
        have hpre : ex ⁻¹' S =
            (fun q : ↥(U (Sum.inl ())) => (q.1.1 : Y ⊕ (Σ _ : ι, cellDisk n))) ⁻¹'
              (Sum.inl '' S) := by
          ext q
          constructor
          · intro hq
            exact ⟨ex q, hq, (hex_spec q).symm⟩
          · rintro ⟨y, hy, hyy⟩
            have h1 : (Sum.inl y : Y ⊕ (Σ _ : ι, cellDisk n)) = Sum.inl (ex q) :=
              hyy.trans (hex_spec q)
            show ex q ∈ S
            exact (Sum.inl.inj h1) ▸ hy
        rw [hpre]
        exact (isOpen_sumInl_image hS).preimage (by fun_prop)
      have hform : (fun q : ↥(U (Sum.inl ())) =>
            pushGarbage n Y ι f (q.1.1 : Y ⊕ (Σ _ : ι, cellDisk n)) q.1.2) =
          fun q => attachIncl n Y ι f (ex q) := by
        funext q
        rw [hex_spec q, pushGarbage_inl]
      rw [hform]
      exact (attachIncl n Y ι f).continuous.comp hex_cont
    · -- the piece over the `i`-th cell
      let exi : ↥(U (Sum.inr i)) → ↥(puncturedCellDisk n) :=
        fun q => ⟨Classical.choose q.2, (Classical.choose_spec q.2).1⟩
      have hex_spec : ∀ q : ↥(U (Sum.inr i)),
          (q.1.1 : Y ⊕ (Σ _ : ι, cellDisk n)) = Sum.inr ⟨i, (Classical.choose q.2 : cellDisk n)⟩ :=
        fun q => (Classical.choose_spec q.2).2
      have hex_cont : Continuous exi := by
        rw [continuous_def]
        intro S hS
        obtain ⟨S', hS', hS'eq⟩ := isOpen_induced_iff.mp hS
        rw [← hS'eq]
        have hpre : exi ⁻¹' (Subtype.val ⁻¹' S') =
            (fun q : ↥(U (Sum.inr i)) => (q.1.1 : Y ⊕ (Σ _ : ι, cellDisk n))) ⁻¹'
              (Sum.inr '' (Sigma.mk i '' S')) := by
          ext q
          constructor
          · intro hq
            exact ⟨⟨i, Classical.choose q.2⟩,
              ⟨Classical.choose q.2, by
                show ((exi q : ↥(puncturedCellDisk n)) : cellDisk n) ∈ S'
                exact hq, rfl⟩, (hex_spec q).symm⟩
          · rintro ⟨r, hr, hrq⟩
            obtain ⟨x, hx, rfl⟩ := hr
            have h1 : (⟨i, x⟩ : Σ _ : ι, cellDisk n) = ⟨i, Classical.choose q.2⟩ :=
              Sum.inr.inj (hrq.trans (hex_spec q))
            have h3 : x = Classical.choose q.2 :=
              congrArg (fun r : Σ _ : ι, cellDisk n => r.2) h1
            show ((exi q : ↥(puncturedCellDisk n)) : cellDisk n) ∈ S'
            rw [show ((exi q : ↥(puncturedCellDisk n)) : cellDisk n) = Classical.choose q.2 from rfl,
              ← h3]
            exact hx
        rw [hpre]
        exact (isOpen_sumInr_image hS' i).preimage (by fun_prop)
      have hform : (fun q : ↥(U (Sum.inr i)) =>
            pushGarbage n Y ι f (q.1.1 : Y ⊕ (Σ _ : ι, cellDisk n)) q.1.2) =
          fun q => cellMap n Y ι f i (cellPush n (exi q, q.1.2)) := by
        funext q
        rw [hex_spec q]
        exact pushGarbage_inr (i := i) (x := Classical.choose q.2)
          (hx := (Classical.choose_spec q.2).1) q.1.2
      rw [hform]
      exact (cellMap n Y ι f i).continuous.comp
        ((cellPush n).continuous.comp
          (hex_cont.prodMk (continuous_snd.comp continuous_subtype_val)))

/-! ### The push-off homotopy -/

theorem pushGarbage_zero_apply (w : ↥(pushDomain n Y ι f)) :
    pushGarbage n Y ι f (w : Y ⊕ (Σ _ : ι, cellDisk n)) 0 =
      (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f))
        (w : Y ⊕ (Σ _ : ι, cellDisk n)) : attachCells n Y ι f) :=
  pushGarbage_zero w.2

theorem pushGarbage_fix_apply (w : ↥(pushDomain n Y ι f))
    (hA : (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f))
      (w : Y ⊕ (Σ _ : ι, cellDisk n)) : attachCells n Y ι f) ∈ Set.range (attachIncl n Y ι f))
    (s : I) :
    pushGarbage n Y ι f (w : Y ⊕ (Σ _ : ι, cellDisk n)) s =
      (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f))
        (w : Y ⊕ (Σ _ : ι, cellDisk n)) : attachCells n Y ι f) :=
  pushGarbage_fix w.2 hA s

/-- **A map missing every cell centre can be pushed, through maps missing the centres, into the
range of `attachIncl`.** -/
theorem exists_pushOff_homotopy (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) {X : Type} [TopologicalSpace X]
    (h : C(X, attachCells n Y ι f))
    (havoid : ∀ (i : ι) (x : X), h x ≠ cellOrigin n Y ι f i) :
    ∃ H : C(X × I, attachCells n Y ι f),
      (∀ x, H (x, 0) = h x) ∧
      (∀ x, h x ∈ Set.range (attachIncl n Y ι f) → ∀ t : I, H (x, t) = h x) ∧
      (∀ x, H (x, 1) ∈ Set.range (attachIncl n Y ι f)) := by
  classical
  set qr : ↥(pushDomain n Y ι f) → ↥((cellCentres n Y ι f)ᶜ) :=
    ((cellCentres n Y ι f)ᶜ).restrictPreimage
      (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f))) with hqrdef
  have hqr : Topology.IsQuotientMap qr :=
    Topology.IsQuotientMap.restrictPreimage_isOpen
      (isQuotientMap_quotient_mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f)))
      (isClosed_cellCentres n Y ι f).isOpen_compl
  set G : ↥((cellCentres n Y ι f)ᶜ) × I → attachCells n Y ι f := fun p =>
    pushGarbage n Y ι f ((Classical.choose (hqr.surjective p.1) : ↥(pushDomain n Y ι f)) :
      Y ⊕ (Σ _ : ι, cellDisk n)) p.2 with hGdef
  have hG_zero : ∀ v : ↥((cellCentres n Y ι f)ᶜ), G (v, 0) = (v : attachCells n Y ι f) := by
    intro v
    show pushGarbage n Y ι f ((Classical.choose (hqr.surjective v) : ↥(pushDomain n Y ι f)) :
      Y ⊕ (Σ _ : ι, cellDisk n)) (0 : I) = (v : attachCells n Y ι f)
    rw [pushGarbage_zero_apply (Classical.choose (hqr.surjective v))]
    exact congrArg (fun w : ↥((cellCentres n Y ι f)ᶜ) => (w : attachCells n Y ι f))
      (Classical.choose_spec (hqr.surjective v))
  have hG_one : ∀ v : ↥((cellCentres n Y ι f)ᶜ),
      G (v, 1) ∈ Set.range (attachIncl n Y ι f) := by
    intro v
    show pushGarbage n Y ι f ((Classical.choose (hqr.surjective v) : ↥(pushDomain n Y ι f)) :
      Y ⊕ (Σ _ : ι, cellDisk n)) (1 : I) ∈ Set.range (attachIncl n Y ι f)
    exact pushGarbage_one_mem (Classical.choose (hqr.surjective v)).2
  have hG_fix : ∀ (v : ↥((cellCentres n Y ι f)ᶜ)) (t : I),
      (v : attachCells n Y ι f) ∈ Set.range (attachIncl n Y ι f) →
      G (v, t) = (v : attachCells n Y ι f) := by
    intro v t hv
    have hv' : (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f))
        ((Classical.choose (hqr.surjective v) : ↥(pushDomain n Y ι f)) :
          Y ⊕ (Σ _ : ι, cellDisk n)) : attachCells n Y ι f) ∈
        Set.range (attachIncl n Y ι f) := by
      have hspec := Classical.choose_spec (hqr.surjective v)
      have hq_eq : (qr (Classical.choose (hqr.surjective v)) : attachCells n Y ι f) =
          (v : attachCells n Y ι f) :=
        congrArg (fun w : ↥((cellCentres n Y ι f)ᶜ) => (w : attachCells n Y ι f)) hspec
      show (qr (Classical.choose (hqr.surjective v)) : attachCells n Y ι f) ∈
        Set.range (attachIncl n Y ι f)
      rw [hq_eq]
      exact hv
    show pushGarbage n Y ι f ((Classical.choose (hqr.surjective v) : ↥(pushDomain n Y ι f)) :
      Y ⊕ (Σ _ : ι, cellDisk n)) t = (v : attachCells n Y ι f)
    rw [pushGarbage_fix_apply (Classical.choose (hqr.surjective v)) hv' t]
    exact congrArg (fun w : ↥((cellCentres n Y ι f)ᶜ) => (w : attachCells n Y ι f))
      (Classical.choose_spec (hqr.surjective v))
  have hG_cont : Continuous G := by
    refine Topology.IsQuotientMap.continuous_lift_prod_left hqr ?_
    have hcomp : (fun p : ↥(pushDomain n Y ι f) × I => G (qr p.1, p.2)) =
        fun p : ↥(pushDomain n Y ι f) × I =>
          pushGarbage n Y ι f (p.1 : Y ⊕ (Σ _ : ι, cellDisk n)) p.2 := by
      funext p
      show pushGarbage n Y ι f ((Classical.choose (hqr.surjective (qr p.1)) :
        ↥(pushDomain n Y ι f)) : Y ⊕ (Σ _ : ι, cellDisk n)) p.2 = _
      exact pushGarbage_eq_of_eqvGen p.2
        (Quotient.exact (s := Relation.EqvGen.setoid (attachRel n Y ι f))
          (show (Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f))
              ((Classical.choose (hqr.surjective (qr p.1)) : ↥(pushDomain n Y ι f)) :
                Y ⊕ (Σ _ : ι, cellDisk n)) : attachCells n Y ι f)
            = Quotient.mk' (s := Relation.EqvGen.setoid (attachRel n Y ι f))
              (p.1 : Y ⊕ (Σ _ : ι, cellDisk n))
            from congrArg (fun w : ↥((cellCentres n Y ι f)ᶜ) => (w : attachCells n Y ι f))
              (Classical.choose_spec (hqr.surjective (qr p.1)))))
        (Classical.choose (hqr.surjective (qr p.1))).2 p.1.2
    rw [hcomp]
    exact continuous_pushGarbage
  have hnotcentres : ∀ x : X, h x ∈ (cellCentres n Y ι f)ᶜ := by
    intro x
    rintro ⟨i, hi⟩
    exact havoid i x hi.symm
  have hmap : Continuous fun p : X × I => (⟨h p.1, hnotcentres p.1⟩ :
      ↥((cellCentres n Y ι f)ᶜ)) :=
    (h.continuous.comp continuous_fst).subtype_mk _
  refine ⟨⟨fun p : X × I => G ((⟨h p.1, hnotcentres p.1⟩ :
      ↥((cellCentres n Y ι f)ᶜ)), p.2), hG_cont.comp (hmap.prodMk continuous_snd)⟩, ?_, ?_, ?_⟩
  · intro x
    exact hG_zero ⟨h x, hnotcentres x⟩
  · intro x hx t
    exact hG_fix ⟨h x, hnotcentres x⟩ t hx
  · intro x
    exact hG_one ⟨h x, hnotcentres x⟩

end

end Work.RatHurewicz
