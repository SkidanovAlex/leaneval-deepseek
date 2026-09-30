/-
# Filtrations of the cellular and subdivided complexes by the support on a set of cells

For a `PolyCW` `P` and a *finset* `S` of cells we consider the subcomplexes

* `cellSMod P hdd S k` — the cellular `k`-chains supported on the cells of `S` of dimension `k`,
* `sdSMod P S k` — the simplicial `k`-chains of the barycentric subdivision supported on the
  simplices all of whose vertices lie in `S`,

and, when `S` is *lower* (closed under faces), the corresponding subcomplexes
`cellS P hdd S` of `cellChain P hdd` and `sdS P S` of `sdChain P`.

These are the localized ("star") versions of the skeletal filtrations `cellSubMod`/`sdSubMod`: with
`S = {f // f ≤ e}` one recovers the closed cell of `e` (`leSub`-side) and with `S = {f // f < e}`
its boundary.  The point of this formulation (as opposed to the "dimension" filtrations) is that
the quotient of the two complexes of `S ∪ {a}` by those of `S`, for a cell `a` whose faces lie in
`S`, is *literally* the pair `(Iio a, Iic a)` of the cell `a`: this is what lets the local
condition at the cells of the boundary be pushed around.
-/
import Mathlib
import Submission.Work.Subdivision.Level
import Submission.Work.Subdivision.PieceQuot
import Submission.Work.MbarHomology.Local.CellLe

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

namespace Work.Subdivision

open CategoryTheory

universe u

noncomputable section

namespace PolyCW

variable (P : PolyCW.{u})

/-! ### The support of a finset of cells -/

/-- The cells of a finset `S` of dimension `k`, as a submodule of the cellular `k`-chains. -/
def cellSMod (hdd : P.HasDdZero) (S : Finset P.Cell) (k : ℕ) :
    Submodule ℤ ((cellChain P hdd).X k) :=
  Submodule.span ℤ {y : (cellChain P hdd).X k |
    ∃ e : {e : P.Cell // P.dim e = k}, e.1 ∈ S ∧ y = cellElem P hdd k e}

/-- The `k`-simplices of the barycentric subdivision all of whose vertices are cells of `S`. -/
def sdSMod (S : Finset P.Cell) (k : ℕ) : Submodule ℤ ((sdChain P).X k) :=
  Submodule.span ℤ {y : (sdChain P).X k |
    ∃ σ : Simplex P.Cell k, (∀ i, σ i ∈ S) ∧ y = sdElem P σ}

theorem cellElem_mem_cellSMod (hdd : P.HasDdZero) (S : Finset P.Cell) (k : ℕ)
    (e : {e : P.Cell // P.dim e = k}) (he : e.1 ∈ S) :
    cellElem P hdd k e ∈ cellSMod P hdd S k :=
  Submodule.subset_span ⟨e, he, rfl⟩

theorem sdElem_mem_sdSMod (S : Finset P.Cell) (k : ℕ) (σ : Simplex P.Cell k)
    (hσ : ∀ i, σ i ∈ S) : sdElem P σ ∈ sdSMod P S k :=
  Submodule.subset_span ⟨σ, hσ, rfl⟩

/-- Membership in `cellSMod` is detected on the support of the `Finsupp`. -/
theorem mem_cellSMod_of_support (hdd : P.HasDdZero) (S : Finset P.Cell) (k : ℕ)
    {x : (cellChain P hdd).X k} (h : ∀ e ∈ x.support, e.1 ∈ S) : x ∈ cellSMod P hdd S k := by
  have hset : {y : (cellChain P hdd).X k |
      ∃ e : {e : P.Cell // P.dim e = k}, e.1 ∈ S ∧ y = cellElem P hdd k e}
      = {y : (cellChain P hdd).X k |
          ∃ b ∈ {e : {e : P.Cell // P.dim e = k} | e.1 ∈ S}, y = Finsupp.single b 1} := by
    ext y
    constructor <;> rintro ⟨e, he, rfl⟩ <;> exact ⟨e, he, by simp [cellElem]⟩
  rw [cellSMod, hset]
  exact (Finsupp.mem_span_single_one_iff (R := ℤ)
    (B := {e : {e : P.Cell // P.dim e = k} | e.1 ∈ S})).2 fun e he => h e he

theorem cellSMod_support (hdd : P.HasDdZero) (S : Finset P.Cell) (k : ℕ)
    {x : (cellChain P hdd).X k} (hx : x ∈ cellSMod P hdd S k) :
    ∀ e ∈ x.support, e.1 ∈ S := by
  have hset : {y : (cellChain P hdd).X k |
      ∃ e : {e : P.Cell // P.dim e = k}, e.1 ∈ S ∧ y = cellElem P hdd k e}
      = {y : (cellChain P hdd).X k |
          ∃ b ∈ {e : {e : P.Cell // P.dim e = k} | e.1 ∈ S}, y = Finsupp.single b 1} := by
    ext y
    constructor <;> rintro ⟨e, he, rfl⟩ <;> exact ⟨e, he, by simp [cellElem]⟩
  rw [cellSMod, hset] at hx
  exact fun e he =>
    (Finsupp.mem_span_single_one_iff (R := ℤ)
      (B := {e : {e : P.Cell // P.dim e = k} | e.1 ∈ S})).1 hx he

/-- Membership in `sdSMod` is detected on the support of the `Finsupp`. -/
theorem mem_sdSMod_of_support (S : Finset P.Cell) (k : ℕ) {x : (sdChain P).X k}
    (h : ∀ σ ∈ x.support, ∀ i, σ i ∈ S) : x ∈ sdSMod P S k := by
  have hset : {y : (sdChain P).X k |
      ∃ σ : Simplex P.Cell k, (∀ i, σ i ∈ S) ∧ y = sdElem P σ}
      = {y : (sdChain P).X k |
          ∃ b ∈ {σ : Simplex P.Cell k | ∀ i, σ i ∈ S}, y = Finsupp.single b 1} := by
    ext y
    constructor <;> rintro ⟨σ, hσ, rfl⟩ <;> exact ⟨σ, hσ, by simp [sdElem]⟩
  rw [sdSMod, hset]
  exact (Finsupp.mem_span_single_one_iff (R := ℤ)
    (B := {σ : Simplex P.Cell k | ∀ i, σ i ∈ S})).2 fun σ hσ => h σ hσ

theorem sdSMod_support (S : Finset P.Cell) (k : ℕ) {x : (sdChain P).X k}
    (hx : x ∈ sdSMod P S k) : ∀ σ ∈ x.support, ∀ i, σ i ∈ S := by
  have hset : {y : (sdChain P).X k |
      ∃ σ : Simplex P.Cell k, (∀ i, σ i ∈ S) ∧ y = sdElem P σ}
      = {y : (sdChain P).X k |
          ∃ b ∈ {σ : Simplex P.Cell k | ∀ i, σ i ∈ S}, y = Finsupp.single b 1} := by
    ext y
    constructor <;> rintro ⟨σ, hσ, rfl⟩ <;> exact ⟨σ, hσ, by simp [sdElem]⟩
  rw [sdSMod, hset] at hx
  exact fun σ hσ =>
    (Finsupp.mem_span_single_one_iff (R := ℤ)
      (B := {σ : Simplex P.Cell k | ∀ i, σ i ∈ S})).1 hx hσ

/-- A finset of cells is *lower* if it is closed under taking faces. -/
def IsLowerFinset (S : Finset P.Cell) : Prop := ∀ f ∈ S, ∀ g : P.Cell, g ≤ f → g ∈ S

theorem isLowerFinset_filter_le (e : P.Cell) :
    IsLowerFinset P (Finset.univ.filter (fun f => f ≤ e)) := by
  intro f hf g hg
  rw [Finset.mem_filter] at hf ⊢
  exact ⟨Finset.mem_univ g, le_trans hg hf.2⟩

theorem isLowerFinset_filter_lt (e : P.Cell) :
    IsLowerFinset P (Finset.univ.filter (fun f => f < e)) := by
  intro f hf g hg
  rw [Finset.mem_filter] at hf ⊢
  exact ⟨Finset.mem_univ g, lt_of_le_of_lt hg hf.2⟩

theorem mem_filter_le_iff (e f : P.Cell) :
    f ∈ (Finset.univ.filter (fun f => f ≤ e)) ↔ f ≤ e := by
  simp

theorem mem_filter_lt_iff (e f : P.Cell) :
    f ∈ (Finset.univ.filter (fun f => f < e)) ↔ f < e := by
  simp

end PolyCW


namespace PolyCW

variable (P : PolyCW.{u})

/-! ### Monotonicity -/

theorem cellSMod_mono (hdd : P.HasDdZero) {S S' : Finset P.Cell} (h : S ⊆ S') (k : ℕ) :
    cellSMod P hdd S k ≤ cellSMod P hdd S' k := by
  rw [cellSMod, cellSMod, Submodule.span_le]
  rintro y ⟨e, he, rfl⟩
  exact cellElem_mem_cellSMod P hdd S' k e (h he)

theorem sdSMod_mono {S S' : Finset P.Cell} (h : S ⊆ S') (k : ℕ) :
    sdSMod P S k ≤ sdSMod P S' k := by
  rw [sdSMod, sdSMod, Submodule.span_le]
  rintro y ⟨σ, hσ, rfl⟩
  exact sdElem_mem_sdSMod P S' k σ fun i => h (hσ i)

/-- The differential of the cellular chains supported on a lower finset stays supported there. -/
theorem cellSMod_d_mem (hdd : P.HasDdZero) {S : Finset P.Cell} (hS : IsLowerFinset P S) (k : ℕ) :
    cellSMod P hdd S (k + 1) ≤
      Submodule.comap (((cellChain P hdd).d (k + 1) k).hom) (cellSMod P hdd S k) := by
  rw [cellSMod, Submodule.span_le]
  rintro y ⟨e, he, rfl⟩
  refine Submodule.mem_comap.mpr ?_
  rw [show cellElem P hdd (k + 1) e = Finsupp.single e (1 : ℤ) from rfl, cellChain_d]
  show cellD P k (Finsupp.single e 1) ∈ cellSMod P hdd S k
  rw [cellD_single]
  rw [cellDval]
  refine Submodule.sum_mem _ fun x hx => Submodule.smul_mem _ _ ?_
  have hx' := (P.mem_facets e.1 x.1).1 x.2
  have hdim : P.dim x.1 = k := by
    have h1 : P.dim e.1 = P.dim x.1 + 1 := hx'.2
    have h2 : P.dim e.1 = k + 1 := e.2
    omega
  exact cellElem_mem_cellSMod P hdd S k ⟨x.1, hdim⟩ (hS e.1 he x.1 hx'.1.le)

/-- The differential of the subdivided chains supported on a finset stays supported there. -/
theorem sdSMod_d_mem (S : Finset P.Cell) (k : ℕ) :
    sdSMod P S (k + 1) ≤
      Submodule.comap (((sdChain P).d (k + 1) k).hom) (sdSMod P S k) := by
  rw [sdSMod, Submodule.span_le]
  rintro y ⟨σ, hσ, rfl⟩
  refine Submodule.mem_comap.mpr ?_
  rw [sdChain_d]
  show D (α := P.Cell) k (sdElem P σ) ∈ sdSMod P S k
  rw [D_sdElem]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact sdElem_mem_sdSMod P S k (Simplex.face i σ) fun j => hσ (i.succAbove j)

/-- The cellular chains supported on a lower finset, as a subcomplex. -/
def cellS (hdd : P.HasDdZero) (S : Finset P.Cell) (hS : IsLowerFinset P S) :
    SubData (cellChain P hdd) where
  sub k := cellSMod P hdd S k
  d_mem k x hx := Submodule.mem_comap.mp (cellSMod_d_mem P hdd hS k hx)

/-- The subdivided chains supported on a finset, as a subcomplex. -/
def sdS (S : Finset P.Cell) : SubData (sdChain P) where
  sub k := sdSMod P S k
  d_mem k x hx := Submodule.mem_comap.mp (sdSMod_d_mem P S k hx)

@[simp] theorem cellS_sub (hdd : P.HasDdZero) (S : Finset P.Cell) (hS : IsLowerFinset P S) (k : ℕ) :
    (cellS P hdd S hS).sub k = cellSMod P hdd S k := rfl

@[simp] theorem sdS_sub (S : Finset P.Cell) (k : ℕ) :
    (sdS P S).sub k = sdSMod P S k := rfl

/-- **The subdivision respects the support filtration.** -/
theorem subdivCpt_mem_S (hdd : P.HasDdZero) (haug : P.HasAugZero) {S : Finset P.Cell}
    (hS : IsLowerFinset P S) (k : ℕ) :
    cellSMod P hdd S k ≤
      (sdSMod P S k).comap ((subdiv P hdd haug).f k).hom := by
  rw [cellSMod, Submodule.span_le]
  rintro y ⟨e, he, rfl⟩
  refine Submodule.mem_comap.mpr ?_
  show subdivLM P k (cellElem P hdd k e) ∈ sdSMod P S k
  rw [cellElem, subdivLM_single]
  exact mem_sdSMod_of_support P S k fun σ hσ i => hS e.1 he (σ i) (subdivCell_support P k e σ hσ i)

end PolyCW


namespace PolyCW

variable (P : PolyCW.{u})

/-! ### Adding a single cell to a stage

A *stage* for a cell `a` is a lower finset of cells of dimension at most `P.dim a`, not containing
`a` and containing all the proper faces of `a`.  These are exactly the intermediate stages of the
cell-by-cell filtration of the closed cell of `a` (or of any lower set containing it).

At such a stage, the quotient of the two complexes of `insert a T` by those of `T` is the pair
`(Iio a, Iic a)` of the cell `a` itself: `sdSMod (insert a T)` is generated by `sdSMod T` and
`leSub a`, and these meet in `ltSub a`. -/

/-- A stage for the cell `a`. -/
structure IsStage (a : P.Cell) (T : Finset P.Cell) : Prop where
  /-- The stage is closed under faces. -/
  lower : IsLowerFinset P T
  /-- The new cell is not in the stage. -/
  notMem : a ∉ T
  /-- Every cell of the stage has dimension at most that of `a`. -/
  dim_le : ∀ f ∈ T, P.dim f ≤ P.dim a
  /-- Every proper face of `a` is in the stage. -/
  faces : ∀ f : P.Cell, f < a → f ∈ T

theorem IsStage.subset_insert {a : P.Cell} {T : Finset P.Cell} (h : IsStage P a T) :
    T ⊆ insert a T :=
  Finset.subset_insert a T

theorem IsStage.insert_lower {a : P.Cell} {T : Finset P.Cell} (h : IsStage P a T) :
    IsLowerFinset P (insert a T) := by
  intro f hf g hg
  rw [Finset.mem_insert] at hf ⊢
  rcases hf with hfa | hf
  · have hga' : g ≤ a := by rw [hfa] at hg; exact hg
    by_cases hga : g = a
    · exact Or.inl hga
    · exact Or.inr (h.faces g (lt_of_le_of_ne hga' hga))
  · exact Or.inr (h.lower f hf g hg)

/-- A vertex of a simplex supported on `insert a T` which is `≥ a` is `a` itself. -/
theorem eq_of_le_of_mem_insert {a : P.Cell} {T : Finset P.Cell} (h : IsStage P a T)
    {k : ℕ} {σ : Simplex P.Cell k}
    (hσ : ∀ i, σ i ∈ insert a T) {i : Fin (k + 1)} (hi : a ≤ σ i) : σ i = a := by
  have hmem := hσ i
  rw [Finset.mem_insert] at hmem
  rcases hmem with h' | h'
  · exact h'
  · by_contra hne
    have h1 : P.dim (σ i) ≤ P.dim a := h.dim_le (σ i) h'
    have h2 : P.dim a ≤ P.dim (σ i) := P.dim_le hi
    have h4 : P.dim a < P.dim (σ i) := P.dim_lt hi (fun hc => hne hc.symm)
    omega

/-- Every simplex supported on `insert a T` and containing `a` has all its vertices `≤ a`. -/
theorem le_of_mem_insert {a : P.Cell} {T : Finset P.Cell} (h : IsStage P a T)
    {k : ℕ} {σ : Simplex P.Cell k}
    (hσ : ∀ i, σ i ∈ insert a T) {j : Fin (k + 1)} (hj : σ j = a) (i : Fin (k + 1)) :
    σ i ≤ a := by
  rcases le_total i j with hij | hij
  · rw [← hj]
    exact σ.strictMono.monotone hij
  · have hai : a ≤ σ i := by
      rw [← hj]
      exact σ.strictMono.monotone hij
    rw [eq_of_le_of_mem_insert P h hσ hai]

/-- Every chain with all vertices `≤ a` is supported on `insert a T`. -/
theorem leSub_le_sdSMod_insert {a : P.Cell} {T : Finset P.Cell} (h : IsStage P a T) (k : ℕ) :
    leSub P a k ≤ sdSMod P (insert a T) k := by
  intro x hx
  refine mem_sdSMod_of_support P (insert a T) k fun σ hσ i => ?_
  have hle : σ i ≤ a := leSub_support P hx σ hσ i
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [heq]; exact Finset.mem_insert_self a T
  · exact Finset.mem_insert_of_mem (h.faces (σ i) hlt)

/-- The chains with all vertices `< a` are supported on any stage of `a`. -/
theorem ltSub_le_sdSMod {a : P.Cell} {T : Finset P.Cell} (h : IsStage P a T) (k : ℕ) :
    ltSub P a k ≤ sdSMod P T k := by
  intro x hx
  exact mem_sdSMod_of_support P T k fun σ hσ i => h.faces (σ i) (ltSub_support P hx σ hσ i)

/-- **The subdivided filtration of `insert a T` is generated by that of `T` and the closed cell
of `a`.** -/
theorem sdSMod_insert {a : P.Cell} {T : Finset P.Cell} (h : IsStage P a T) (k : ℕ) :
    sdSMod P (insert a T) k = sdSMod P T k ⊔ leSub P a k := by
  refine le_antisymm ?_ ?_
  · rw [sdSMod, Submodule.span_le]
    rintro y ⟨σ, hσ, rfl⟩
    by_cases ha : ∃ j, σ j = a
    · obtain ⟨j, hj⟩ := ha
      refine Submodule.mem_sup_right (sdElem_mem_leSub P fun i => ?_)
      exact le_of_mem_insert P h hσ hj i
    · refine Submodule.mem_sup_left (sdElem_mem_sdSMod P T k σ fun i => ?_)
      have hmem := hσ i
      rw [Finset.mem_insert] at hmem
      rcases hmem with h' | h'
      · exact absurd ⟨i, h'⟩ ha
      · exact h'
  · refine sup_le (sdSMod_mono P (Finset.subset_insert a T) k) ?_
    exact leSub_le_sdSMod_insert P h k

/-- **The intersection of the subdivided filtration of a stage with the closed cell of the new
cell is the boundary of the new cell.** -/
theorem sdSMod_inf_leSub {a : P.Cell} {T : Finset P.Cell} (h : IsStage P a T) (k : ℕ) :
    sdSMod P T k ⊓ leSub P a k = ltSub P a k := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hx
    refine mem_ltSub_of_support P fun σ hσ i => ?_
    have hle : σ i ≤ a := leSub_support P h2 σ hσ i
    rcases eq_or_lt_of_le hle with heq | hlt
    · exfalso
      exact h.notMem (heq ▸ sdSMod_support P T k h1 σ hσ i)
    · exact hlt
  · intro x hx
    exact Submodule.mem_inf.mpr ⟨ltSub_le_sdSMod P h k hx, ltSub_le_leSub P a k hx⟩

/-! ### The cellular side -/

/-- In degree other than `dim a` the cellular filtration of `insert a T` is that of `T`. -/
theorem cellSMod_insert_of_ne (hdd : P.HasDdZero) {a : P.Cell} {T : Finset P.Cell}
    (h : IsStage P a T) {k : ℕ} (hk : k ≠ P.dim a) :
    cellSMod P hdd (insert a T) k = cellSMod P hdd T k := by
  refine le_antisymm ?_ (cellSMod_mono P hdd (Finset.subset_insert a T) k)
  rw [cellSMod, Submodule.span_le]
  rintro y ⟨e, he, rfl⟩
  rw [Finset.mem_insert] at he
  rcases he with hea | he
  · have hd : P.dim a = k := by
      rw [← congrArg P.dim hea]
      exact e.2
    exact absurd hd.symm hk
  · exact cellElem_mem_cellSMod P hdd T k e he

/-- The cellular filtration of `insert a T` in degree `dim a`. -/
theorem cellSMod_insert_eq (hdd : P.HasDdZero) {a : P.Cell} {T : Finset P.Cell}
    (h : IsStage P a T) :
    cellSMod P hdd (insert a T) (P.dim a) =
      cellSMod P hdd T (P.dim a) ⊔
        Submodule.span ℤ ({cellElem P hdd (P.dim a) ⟨a, rfl⟩} :
          Set ((cellChain P hdd).X (P.dim a))) := by
  refine le_antisymm ?_ ?_
  · rw [cellSMod, Submodule.span_le]
    rintro y ⟨e, he, rfl⟩
    rw [Finset.mem_insert] at he
    rcases he with hea | he
    · have he' : e = ⟨a, rfl⟩ := Subtype.ext hea
      rw [he']
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    · exact Submodule.mem_sup_left (cellElem_mem_cellSMod P hdd T (P.dim a) e he)
  · refine sup_le (cellSMod_mono P hdd (Finset.subset_insert a T) (P.dim a)) ?_
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact cellElem_mem_cellSMod P hdd (insert a T) (P.dim a) ⟨a, rfl⟩
      (Finset.mem_insert_self a T)


/-! ### The closed cell and the boundary of a cell as support filtrations -/

/-- The finset of cells of the closed cell of `e`. -/
abbrev icF (e : P.Cell) : Finset P.Cell := Finset.univ.filter (fun f => f ≤ e)

/-- The finset of proper faces of `e`. -/
abbrev ioF (e : P.Cell) : Finset P.Cell := Finset.univ.filter (fun f => f < e)

/-- The cellular chains supported on the closed cell of `e` are exactly the chains of the
subcomplex `Work.MbarHomology.cellLe`. -/
theorem cellSMod_icF (hdd : P.HasDdZero) (e : P.Cell) (k : ℕ) :
    cellSMod P hdd (icF P e) k = Work.MbarHomology.cellSubMod P e k := by
  apply le_antisymm
  · rw [cellSMod]
    refine Submodule.span_le.mpr ?_
    rintro y ⟨f, hf, rfl⟩
    exact Work.MbarHomology.mem_cellSubMod_single P e k f (by simpa [icF] using hf)
  · rw [Work.MbarHomology.cellSubMod]
    refine Submodule.span_le.mpr ?_
    rintro y ⟨f, hf, rfl⟩
    exact cellElem_mem_cellSMod P hdd (icF P e) k f (by simpa [icF] using hf)

/-- The subdivided chains supported on the closed cell of `e` are the chains of the order complex
of `Iic e`. -/
theorem sdSMod_icF (e : P.Cell) (k : ℕ) :
    sdSMod P (icF P e) k = leSub P e k := by
  apply le_antisymm
  · rw [sdSMod]
    refine Submodule.span_le.mpr ?_
    rintro y ⟨σ, hσ, rfl⟩
    exact sdElem_mem_leSub P fun i => by simpa [icF] using hσ i
  · rw [leSub]
    refine Submodule.span_le.mpr ?_
    rintro y ⟨σ, hσ, rfl⟩
    exact sdElem_mem_sdSMod P (icF P e) k σ fun i => by simpa [icF] using hσ i

/-- The subdivided chains supported on the proper faces of `e` are the chains of the order complex
of `Iio e`. -/
theorem sdSMod_ioF (e : P.Cell) (k : ℕ) :
    sdSMod P (ioF P e) k = ltSub P e k := by
  apply le_antisymm
  · rw [sdSMod]
    refine Submodule.span_le.mpr ?_
    rintro y ⟨σ, hσ, rfl⟩
    exact sdElem_mem_ltSub P fun i => by simpa [ioF] using hσ i
  · rw [ltSub]
    refine Submodule.span_le.mpr ?_
    rintro y ⟨σ, hσ, rfl⟩
    exact sdElem_mem_sdSMod P (ioF P e) k σ fun i => by simpa [ioF] using hσ i

/-- The cellular chains supported on the proper faces of `e`, as a submodule of the chains of its
closed cell. -/
theorem cellSMod_ioF_le_icF (hdd : P.HasDdZero) (e : P.Cell) (k : ℕ) :
    cellSMod P hdd (ioF P e) k ≤ cellSMod P hdd (icF P e) k := by
  refine cellSMod_mono P hdd ?_ k
  intro f hf
  rw [ioF, Finset.mem_filter] at hf
  rw [icF, Finset.mem_filter]
  exact ⟨Finset.mem_univ f, hf.2.le⟩

/-- The order complex of the closed cell of `e`. -/
noncomputable abbrev leSubCx (e : P.Cell) : ChainComplex (ModuleCat ℤ) ℕ :=
  (sdS P (icF P e)).chain

/-- The order complex of the proper faces of `e`. -/
noncomputable abbrev ltSubCx (e : P.Cell) : ChainComplex (ModuleCat ℤ) ℕ :=
  (sdS P (ioF P e)).chain

/-- The closed cell of `e` as a chain complex, in support form. -/
noncomputable abbrev cellIcCx (hdd : P.HasDdZero) (e : P.Cell) : ChainComplex (ModuleCat ℤ) ℕ :=
  (cellS P hdd (icF P e) (isLowerFinset_filter_le P e)).chain

/-- The boundary of `e` as a chain complex, in support form. -/
noncomputable abbrev cellIoCx (hdd : P.HasDdZero) (e : P.Cell) : ChainComplex (ModuleCat ℤ) ℕ :=
  (cellS P hdd (ioF P e) (isLowerFinset_filter_lt P e)).chain

/-- The support form of the closed cell agrees with `Work.MbarHomology.cellLe`. -/
theorem cellIcCx_eq_cellLe (hdd : P.HasDdZero) (e : P.Cell) :
    cellIcCx P hdd e = Work.MbarHomology.cellLe P hdd e := by
  refine congrArg SubData.chain (SubData.ext fun k => ?_)
  exact cellSMod_icF P hdd e k

end PolyCW

end

end Work.Subdivision
