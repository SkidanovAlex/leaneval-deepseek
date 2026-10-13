/-
  `Work.WilCrux` — vocabulary for the isolated graph sheet (lemma `IsolatedSheet`, node N1 of
  `WilCrux/DESIGN.md`).

  A cylindrical cell of `ℝ^{m+N}` over a base cell of `ℝ^m` is described level by level: level
  `j` (`0 ≤ j ≤ N`) is the projection to the first `m+j` coordinates, and each level step is
  either a *graph* (of a function continuous on the level below) or a *band* (between two
  continuous `EReal`-valued functions).  The *type word* records the sequence of levels from the
  bottom up: it is a function `Fin N → CellType`, entry `j` describing level `m+j+1`.

  The sheet attached to a word `w` places the *band* levels in the `nBand` extra parameters and
  the *graph* levels in the values of a map `φ : ℝ^{m+nBand} → ℝ^{nGraph}`; the equivalence
  `wordEquiv w : Fin N ≃ Fin (nBand w + nGraph w)` is the bookkeeping that turns this into the
  coordinate map `sheetPt` of `WilCrux/Defs`.

  This file contains definitions and their immediate API (no `sorry`).
-/
import Mathlib
import Submission.Work.Wilkies.Defs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilCrux

open WilkiesDesign WilkiesConjecture

/-! ## 0. The sheet parametrisation

`sheetPtM` is verbatim the parametrisation `sheetPt` of `WilCrux/Defs` (the vocabulary file of
the area).  It is repeated here so that this file — the interface every lemma about the isolated
sheet is stated against — does not depend on it.  `Work.WilCrux.sheetPtM = Work.WilCrux.sheetPt`
is `rfl`. -/

/-- The point of `ℝ^{m+N}` lying over `v = (w, y_A) ∈ ℝ^{m+n₁}` with fibre coordinates
`Fin.append y_A u` reindexed by `e`. -/
def sheetPtM {m n1 n2 N : ℕ} (e : Fin N ≃ Fin (n1 + n2)) (v : Fin (m + n1) → ℝ)
    (u : Fin n2 → ℝ) : Fin (m + N) → ℝ :=
  Fin.append (fun i : Fin m => v (Fin.castAdd n1 i))
    (fun j : Fin N => (Fin.append (fun k : Fin n1 => v (Fin.natAdd m k)) u) (e j))

@[simp] theorem sheetPtM_castAdd {m n1 n2 N : ℕ} (e : Fin N ≃ Fin (n1 + n2))
    (v : Fin (m + n1) → ℝ) (u : Fin n2 → ℝ) (i : Fin m) :
    sheetPtM e v u (Fin.castAdd N i) = v (Fin.castAdd n1 i) :=
  Fin.append_left _ _ _

@[simp] theorem sheetPtM_natAdd {m n1 n2 N : ℕ} (e : Fin N ≃ Fin (n1 + n2))
    (v : Fin (m + n1) → ℝ) (u : Fin n2 → ℝ) (j : Fin N) :
    sheetPtM e v u (Fin.natAdd m j) =
      (Fin.append (fun k : Fin n1 => v (Fin.natAdd m k)) u) (e j) :=
  Fin.append_right _ _ _

theorem continuous_sheetPtM {m n1 n2 N : ℕ} (e : Fin N ≃ Fin (n1 + n2)) :
    Continuous (fun p : (Fin (m + n1) → ℝ) × (Fin n2 → ℝ) => sheetPtM e p.1 p.2) := by
  have hA : Continuous fun p : (Fin (m + n1) → ℝ) × (Fin n2 → ℝ) =>
      (fun i : Fin m => p.1 (Fin.castAdd n1 i)) :=
    continuous_pi fun i => (continuous_apply (Fin.castAdd n1 i)).comp continuous_fst
  have hC : Continuous fun p : (Fin (m + n1) → ℝ) × (Fin n2 → ℝ) =>
      ((fun k : Fin n1 => p.1 (Fin.natAdd m k)), p.2) :=
    (continuous_pi fun k =>
      (continuous_apply (Fin.natAdd m k)).comp continuous_fst).prodMk continuous_snd
  have hD : Continuous fun p : (Fin (m + n1) → ℝ) × (Fin n2 → ℝ) =>
      Fin.append (fun k : Fin n1 => p.1 (Fin.natAdd m k)) p.2 :=
    (Fin.continuous_append n1 n2).comp hC
  have hB : Continuous fun p : (Fin (m + n1) → ℝ) × (Fin n2 → ℝ) =>
      (fun j : Fin N => (Fin.append (fun k : Fin n1 => p.1 (Fin.natAdd m k)) p.2) (e j)) :=
    continuous_pi fun j => (continuous_apply (e j)).comp hD
  exact (Fin.continuous_append m N).comp (hA.prodMk hB)

theorem sheetPtM_injective {m n1 n2 N : ℕ} (e : Fin N ≃ Fin (n1 + n2)) :
    Function.Injective (fun p : (Fin (m + n1) → ℝ) × (Fin n2 → ℝ) => sheetPtM e p.1 p.2) := by
  rintro ⟨v, u⟩ ⟨v', u'⟩ h
  have h' : sheetPtM e v u = sheetPtM e v' u' := h
  have hv : v = v' := by
    funext i
    refine Fin.addCases (m := m) (n := n1) (motive := fun i => v i = v' i) ?_ ?_ i
    · intro i'
      have h1 := congrFun h' (Fin.castAdd N i')
      simpa only [sheetPtM_castAdd] using h1
    · intro k'
      have h1 := congrFun h' (Fin.natAdd m (e.symm (Fin.castAdd n2 k')))
      simpa only [sheetPtM_natAdd, Equiv.apply_symm_apply, Fin.append_left] using h1
  subst hv
  have hu : u = u' := by
    funext k
    have h1 := congrFun h' (Fin.natAdd m (e.symm (Fin.natAdd n1 k)))
    simpa only [sheetPtM_natAdd, Equiv.apply_symm_apply, Fin.append_right] using h1
  subst hu
  rfl

/-! ## 1. The level vocabulary of a cylindrical cell -/

/-- The type of a level cell of a cylindrical cell: a graph, or a band between two
`EReal`-valued functions. -/
inductive CellType where
  | graph : CellType
  | band : CellType
  deriving DecidableEq, Repr

/-- The base of a set in `ℝ^{p+1}`: the projection dropping the last coordinate. -/
def base {p : ℕ} (κ : Set (Fin (p + 1) → ℝ)) : Set (Fin p → ℝ) := Fin.init '' κ

/-- `κ` is the graph of a function over the base `D`, the function being continuous on `D`. -/
def IsGraphCellAt {p : ℕ} (κ : Set (Fin (p + 1) → ℝ)) (D : Set (Fin p → ℝ)) : Prop :=
  ∃ f : (Fin p → ℝ) → ℝ, ContinuousOn f D ∧
    κ = {z : Fin (p + 1) → ℝ | Fin.init z ∈ D ∧ z (Fin.last p) = f (Fin.init z)}

/-- `κ` is a band cell over the base `D`. -/
def IsBandCellAt {p : ℕ} (κ : Set (Fin (p + 1) → ℝ)) (D : Set (Fin p → ℝ)) : Prop :=
  ∃ a b : (Fin p → ℝ) → EReal, ContinuousOn a D ∧ ContinuousOn b D ∧
    (∀ x ∈ D, a x < b x) ∧
    κ = {z : Fin (p + 1) → ℝ | Fin.init z ∈ D ∧
      a (Fin.init z) < ((z (Fin.last p) : ℝ) : EReal) ∧
      ((z (Fin.last p) : ℝ) : EReal) < b (Fin.init z)}

/-- The type of the top level of `κ` (junk — `band` — when `κ` is not a graph cell). -/
def levelType {p : ℕ} (κ : Set (Fin (p + 1) → ℝ)) : CellType :=
  if IsGraphCellAt κ (base κ) then CellType.graph else CellType.band

/-- The type word of a set over a base cell of `ℝ^m`: the type of level `m+j+1` for
`j : Fin N`. -/
def word (m : ℕ) : (N : ℕ) → Set (Fin (m + N) → ℝ) → (Fin N → CellType)
  | 0, _ => fun j => j.elim0
  | N + 1, κ => Fin.snoc (word m N (base κ)) (levelType κ)

@[simp] theorem word_zero (m : ℕ) (κ : Set (Fin (m + 0) → ℝ)) :
    word m 0 κ = fun j => j.elim0 := rfl

theorem word_succ (m N : ℕ) (κ : Set (Fin (m + (N + 1)) → ℝ)) :
    word m (N + 1) κ = Fin.snoc (word m N (base κ)) (levelType κ) := rfl

/-- Lexicographic comparison of type words from the bottom level up, with `band > graph`. -/
def LexLt {N : ℕ} (w w' : Fin N → CellType) : Prop :=
  ∃ j : Fin N, w j = CellType.graph ∧ w' j = CellType.band ∧
    ∀ i : Fin N, i < j → w i = w' i

/-- `LexLt` is irreflexive. -/
theorem LexLt.irrefl {N : ℕ} (w : Fin N → CellType) : ¬ LexLt w w := by
  rintro ⟨j, hg, hb, -⟩
  rw [hg] at hb
  exact CellType.noConfusion hb

/-- `LexLt` is transitive. -/
theorem LexLt.trans {N : ℕ} {u v w : Fin N → CellType} (h1 : LexLt u v) (h2 : LexLt v w) :
    LexLt u w := by
  obtain ⟨j, hju, hjv, h1agree⟩ := h1
  obtain ⟨j', hjv', hjw, h2agree⟩ := h2
  rcases lt_trichotomy j j' with hlt | heq | hgt
  · refine ⟨j, hju, ?_, fun i hi => (h1agree i hi).trans (h2agree i (lt_trans hi hlt))⟩
    rw [← h2agree j hlt]; exact hjv
  · subst heq
    exact ⟨j, hju, hjw, fun i hi => (h1agree i hi).trans (h2agree i hi)⟩
  · refine ⟨j', ?_, hjw, fun i hi => (h1agree i (lt_trans hi hgt)).trans (h2agree i hi)⟩
    rw [h1agree j' hgt]; exact hjv'

/-- Two type words are `LexLt`-comparable or equal. -/
theorem LexLt.trichotomy {N : ℕ} (w w' : Fin N → CellType) :
    LexLt w w' ∨ w = w' ∨ LexLt w' w := by
  classical
  by_cases h : ∃ j : Fin N, w j ≠ w' j
  · obtain ⟨j₀, hj₀diff, hj₀least⟩ :
        ∃ j : Fin N, w j ≠ w' j ∧ ∀ i : Fin N, i < j → w i = w' i := by
      set S : Finset (Fin N) := Finset.univ.filter (fun j => w j ≠ w' j) with hS
      have hSne : S.Nonempty := by
        obtain ⟨j, hj⟩ := h
        exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
      refine ⟨S.min' hSne, (Finset.mem_filter.mp (Finset.min'_mem S hSne)).2, ?_⟩
      intro i hi
      by_contra hne
      exact absurd hi
        (not_lt.mpr (Finset.min'_le S i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)))
    rcases hw : w j₀ with _ | _ <;> rcases hw' : w' j₀ with _ | _
    · exact absurd (by rw [hw, hw']) hj₀diff
    · exact Or.inl ⟨j₀, hw, hw', hj₀least⟩
    · exact Or.inr (Or.inr ⟨j₀, hw', hw, fun i hi => (hj₀least i hi).symm⟩)
    · exact absurd (by rw [hw, hw']) hj₀diff
  · push_neg at h
    exact Or.inr (Or.inl (funext h))

/-! ## 2. Cells over a base, and their words -/

/-- `IsCellOver m N C₀ κ`: `κ ⊆ ℝ^{m+N}` is a cylindrical cell all of whose level cells are
nonempty and whose projection to `ℝ^m` is `C₀`. -/
def IsCellOver (m : ℕ) : (N : ℕ) → Set (Fin m → ℝ) → Set (Fin (m + N) → ℝ) → Prop
  | 0, C₀, κ => κ = C₀ ∧ κ.Nonempty
  | N + 1, C₀, κ => κ.Nonempty ∧ IsCell (m + (N + 1)) κ ∧ IsCellOver m N C₀ (base κ)

/-! ## 3. Counting the band and graph levels of a word -/

/-- `1` on a band level, `0` on a graph level. -/
def bandBit : CellType → ℕ
  | .graph => 0
  | .band => 1

/-- `1` on a graph level, `0` on a band level. -/
def graphBit : CellType → ℕ
  | .graph => 1
  | .band => 0

@[simp] theorem bandBit_graph : bandBit CellType.graph = 0 := rfl
@[simp] theorem bandBit_band : bandBit CellType.band = 1 := rfl
@[simp] theorem graphBit_graph : graphBit CellType.graph = 1 := rfl
@[simp] theorem graphBit_band : graphBit CellType.band = 0 := rfl

/-- The number of band levels of a word. -/
def nBand : (N : ℕ) → (Fin N → CellType) → ℕ
  | 0, _ => 0
  | N + 1, w => nBand N (Fin.init w) + bandBit (w (Fin.last N))

/-- The number of graph levels of a word. -/
def nGraph : (N : ℕ) → (Fin N → CellType) → ℕ
  | 0, _ => 0
  | N + 1, w => nGraph N (Fin.init w) + graphBit (w (Fin.last N))

@[simp] theorem nBand_zero (w : Fin 0 → CellType) : nBand 0 w = 0 := rfl

@[simp] theorem nGraph_zero (w : Fin 0 → CellType) : nGraph 0 w = 0 := rfl

@[simp] theorem nBand_succ (N : ℕ) (w : Fin (N + 1) → CellType) :
    nBand (N + 1) w = nBand N (Fin.init w) + bandBit (w (Fin.last N)) := rfl

@[simp] theorem nGraph_succ (N : ℕ) (w : Fin (N + 1) → CellType) :
    nGraph (N + 1) w = nGraph N (Fin.init w) + graphBit (w (Fin.last N)) := rfl

theorem nBand_eq_card (N : ℕ) (w : Fin N → CellType) :
    nBand N w = (Finset.univ.filter (fun i : Fin N => bandBit (w i) = 1)).card := by
  induction N with
  | zero => simp [nBand]
  | succ N ih =>
      rw [nBand, ih (Fin.init w)]
      rw [Finset.card_filter, Finset.card_filter,
        Fin.sum_univ_castSucc (f := fun i : Fin (N + 1) =>
          if bandBit (w i) = 1 then (1 : ℕ) else 0)]
      rw [show (∑ i : Fin N, if bandBit (Fin.init w i) = 1 then (1 : ℕ) else 0) =
            (∑ i : Fin N, if bandBit (w i.castSucc) = 1 then (1 : ℕ) else 0) from
        Finset.sum_congr rfl (fun i _ => rfl)]
      cases w (Fin.last N) <;> simp [bandBit]

theorem nGraph_eq_card (N : ℕ) (w : Fin N → CellType) :
    nGraph N w = (Finset.univ.filter (fun i : Fin N => graphBit (w i) = 1)).card := by
  induction N with
  | zero => simp [nGraph]
  | succ N ih =>
      rw [nGraph, ih (Fin.init w)]
      rw [Finset.card_filter, Finset.card_filter,
        Fin.sum_univ_castSucc (f := fun i : Fin (N + 1) =>
          if graphBit (w i) = 1 then (1 : ℕ) else 0)]
      rw [show (∑ i : Fin N, if graphBit (Fin.init w i) = 1 then (1 : ℕ) else 0) =
            (∑ i : Fin N, if graphBit (w i.castSucc) = 1 then (1 : ℕ) else 0) from
        Finset.sum_congr rfl (fun i _ => rfl)]
      cases w (Fin.last N) <;> simp [graphBit]

theorem nBand_add_nGraph (N : ℕ) (w : Fin N → CellType) : nBand N w + nGraph N w = N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [nBand_succ, nGraph_succ]
      have hb : bandBit (w (Fin.last N)) + graphBit (w (Fin.last N)) = 1 := by
        cases w (Fin.last N) <;> rfl
      have h := ih (Fin.init w)
      omega

theorem nBand_le (N : ℕ) (w : Fin N → CellType) : nBand N w ≤ N := by
  have := nBand_add_nGraph N w; omega

theorem nGraph_le (N : ℕ) (w : Fin N → CellType) : nGraph N w ≤ N := by
  have := nBand_add_nGraph N w; omega

/-- The number of band levels strictly below `j`. -/
def bandRank {N : ℕ} (w : Fin N → CellType) (j : Fin N) : ℕ :=
  (Finset.univ.filter (fun i : Fin N => i < j ∧ bandBit (w i) = 1)).card

/-- The number of graph levels strictly below `j`. -/
def graphRank {N : ℕ} (w : Fin N → CellType) (j : Fin N) : ℕ :=
  (Finset.univ.filter (fun i : Fin N => i < j ∧ graphBit (w i) = 1)).card

theorem bandRank_le_nBand {N : ℕ} (w : Fin N → CellType) (j : Fin N) :
    bandRank w j ≤ nBand N w := by
  rw [nBand_eq_card]
  exact Finset.card_le_card fun i hi => by
    rw [Finset.mem_filter] at hi ⊢; exact ⟨hi.1, hi.2.2⟩

theorem graphRank_le_nGraph {N : ℕ} (w : Fin N → CellType) (j : Fin N) :
    graphRank w j ≤ nGraph N w := by
  rw [nGraph_eq_card]
  exact Finset.card_le_card fun i hi => by
    rw [Finset.mem_filter] at hi ⊢; exact ⟨hi.1, hi.2.2⟩

theorem bandRank_lt_nBand {N : ℕ} (w : Fin N → CellType) {j : Fin N}
    (hj : bandBit (w j) = 1) : bandRank w j < nBand N w := by
  rw [nBand_eq_card]
  refine Finset.card_lt_card ?_
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro i hi
    rw [Finset.mem_filter] at hi ⊢; exact ⟨hi.1, hi.2.2⟩
  · intro heq
    have hmem : j ∈ Finset.univ.filter (fun i : Fin N => bandBit (w i) = 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
    rw [← heq] at hmem
    rw [Finset.mem_filter] at hmem
    exact absurd hmem.2.1 (lt_irrefl j)

theorem graphRank_lt_nGraph {N : ℕ} (w : Fin N → CellType) {j : Fin N}
    (hj : graphBit (w j) = 1) : graphRank w j < nGraph N w := by
  rw [nGraph_eq_card]
  refine Finset.card_lt_card ?_
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro i hi
    rw [Finset.mem_filter] at hi ⊢; exact ⟨hi.1, hi.2.2⟩
  · intro heq
    have hmem : j ∈ Finset.univ.filter (fun i : Fin N => graphBit (w i) = 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
    rw [← heq] at hmem
    rw [Finset.mem_filter] at hmem
    exact absurd hmem.2.1 (lt_irrefl j)

theorem graphBit_eq_one {t : CellType} (h : ¬ bandBit t = 1) : graphBit t = 1 := by
  cases t <;> simp_all [bandBit, graphBit]

theorem graphRank_lt_nGraph' {N : ℕ} (w : Fin N → CellType) {j : Fin N}
    (h : ¬ bandBit (w j) = 1) : graphRank w j < nGraph N w :=
  graphRank_lt_nGraph w (graphBit_eq_one h)

theorem graphRank_lt_nGraph_of_zero {N : ℕ} (w : Fin N → CellType) {j : Fin N}
    (h : bandBit (w j) = 0) : graphRank w j < nGraph N w :=
  graphRank_lt_nGraph' w (by rw [h]; simp)

theorem bandRank_lt_sum {N : ℕ} (w : Fin N → CellType) {j : Fin N}
    (h : bandBit (w j) = 1) : bandRank w j < nBand N w + nGraph N w :=
  lt_of_lt_of_le (bandRank_lt_nBand w h) (Nat.le_add_right _ _)

theorem graphRank_add_lt_sum {N : ℕ} (w : Fin N → CellType) {j : Fin N}
    (h : ¬ bandBit (w j) = 1) : nBand N w + graphRank w j < nBand N w + nGraph N w :=
  Nat.add_lt_add_left (graphRank_lt_nGraph' w h) _

theorem bandRank_lt_of_lt {N : ℕ} (w : Fin N → CellType) {j j' : Fin N}
    (hj : bandBit (w j) = 1) (h : j < j') : bandRank w j < bandRank w j' := by
  refine Finset.card_lt_card ?_
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, lt_trans hi.2.1 h, hi.2.2⟩
  · intro heq
    have hmem : j ∈ Finset.univ.filter (fun i : Fin N => i < j' ∧ bandBit (w i) = 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, h, hj⟩
    rw [← heq] at hmem
    rw [Finset.mem_filter] at hmem
    exact absurd hmem.2.1 (lt_irrefl j)

theorem graphRank_lt_of_lt {N : ℕ} (w : Fin N → CellType) {j j' : Fin N}
    (hj : graphBit (w j) = 1) (h : j < j') : graphRank w j < graphRank w j' := by
  refine Finset.card_lt_card ?_
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, lt_trans hi.2.1 h, hi.2.2⟩
  · intro heq
    have hmem : j ∈ Finset.univ.filter (fun i : Fin N => i < j' ∧ graphBit (w i) = 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, h, hj⟩
    rw [← heq] at hmem
    rw [Finset.mem_filter] at hmem
    exact absurd hmem.2.1 (lt_irrefl j)


/-! ## 5. The iterated projection of a cell onto its base -/

/-- The projection of a set in `ℝ^{m+N}` onto the first `m` coordinates, by iterating
`Fin.init`. -/
def projOver (m : ℕ) : (N : ℕ) → Set (Fin (m + N) → ℝ) → Set (Fin m → ℝ)
  | 0, κ => κ
  | N + 1, κ => projOver m N (base κ)

@[simp] theorem projOver_zero (m : ℕ) (κ : Set (Fin (m + 0) → ℝ)) :
    projOver m 0 κ = κ := rfl

@[simp] theorem projOver_succ (m N : ℕ) (κ : Set (Fin (m + (N + 1)) → ℝ)) :
    projOver m (N + 1) κ = projOver m N (base κ) := rfl

theorem projOver_of_cellOver {m N : ℕ} {C₀ : Set (Fin m → ℝ)}
    {κ : Set (Fin (m + N) → ℝ)} (h : IsCellOver m N C₀ κ) : projOver m N κ = C₀ := by
  induction N with
  | zero => simpa using h.1
  | succ N ih => simpa using ih h.2.2

/-- The level-`m` decomposition obtained from a decomposition of `ℝ^{m+N}` by iterating the
projection `Fin.init` (which drops the last coordinate). -/
def projDecomp (m : ℕ) : (N : ℕ) → Finset (Set (Fin (m + N) → ℝ)) → Finset (Set (Fin m → ℝ))
  | 0, C => C
  | N + 1, C => projDecomp m N (C.image (fun κ => Fin.init '' κ))

/-! ## 6. The coordinate selection attached to a word -/

/-- The increasing enumeration of the band levels of a word. -/
def bandIdx {N : ℕ} (w : Fin N → CellType) : Fin (nBand N w) → Fin N :=
  fun k => ((Finset.univ.filter (fun j : Fin N => bandBit (w j) = 1)).orderEmbOfFin
    (by rw [nBand_eq_card])) k

/-- The increasing enumeration of the graph levels of a word. -/
def graphIdx {N : ℕ} (w : Fin N → CellType) : Fin (nGraph N w) → Fin N :=
  fun k => ((Finset.univ.filter (fun j : Fin N => graphBit (w j) = 1)).orderEmbOfFin
    (by rw [nGraph_eq_card])) k

theorem bandIdx_band {N : ℕ} (w : Fin N → CellType) (k : Fin (nBand N w)) :
    bandBit (w (bandIdx w k)) = 1 := by
  have h := Finset.orderEmbOfFin_mem (Finset.univ.filter (fun j : Fin N => bandBit (w j) = 1))
    (by rw [nBand_eq_card]) k
  exact (Finset.mem_filter.mp h).2

theorem graphIdx_graph {N : ℕ} (w : Fin N → CellType) (k : Fin (nGraph N w)) :
    graphBit (w (graphIdx w k)) = 1 := by
  have h := Finset.orderEmbOfFin_mem (Finset.univ.filter (fun j : Fin N => graphBit (w j) = 1))
    (by rw [nGraph_eq_card]) k
  exact (Finset.mem_filter.mp h).2

/-- The coordinate selection keeping the parameters and the band coordinates. -/
def selBand (m : ℕ) {N : ℕ} (w : Fin N → CellType) : Fin (m + nBand N w) → Fin (m + N) :=
  Fin.addCases (fun i : Fin m => Fin.castAdd N i) (fun k => Fin.natAdd m (bandIdx w k))

/-- The coordinate selection keeping the parameters and the graph coordinates. -/
def selGraph (m : ℕ) {N : ℕ} (w : Fin N → CellType) : Fin (m + nGraph N w) → Fin (m + N) :=
  Fin.addCases (fun i : Fin m => Fin.castAdd N i) (fun k => Fin.natAdd m (graphIdx w k))

/-- The coordinate selection keeping the parameters, the band coordinates and one graph
coordinate (placed last). -/
def selBandGraph (m : ℕ) {N : ℕ} (w : Fin N → CellType) (j : Fin (nGraph N w)) :
    Fin (m + nBand N w + 1) → Fin (m + N) :=
  Fin.addCases (selBand m w) (fun _ : Fin 1 => Fin.natAdd m (graphIdx w j))

@[simp] theorem selBand_castAdd (m : ℕ) {N : ℕ} (w : Fin N → CellType) (i : Fin m) :
    selBand m w (Fin.castAdd (nBand N w) i) = Fin.castAdd N i :=
  Fin.addCases_left _

@[simp] theorem selBand_natAdd (m : ℕ) {N : ℕ} (w : Fin N → CellType) (k : Fin (nBand N w)) :
    selBand m w (Fin.natAdd m k) = Fin.natAdd m (bandIdx w k) :=
  Fin.addCases_right _

@[simp] theorem selGraph_castAdd (m : ℕ) {N : ℕ} (w : Fin N → CellType) (i : Fin m) :
    selGraph m w (Fin.castAdd (nGraph N w) i) = Fin.castAdd N i :=
  Fin.addCases_left _

@[simp] theorem selGraph_natAdd (m : ℕ) {N : ℕ} (w : Fin N → CellType) (k : Fin (nGraph N w)) :
    selGraph m w (Fin.natAdd m k) = Fin.natAdd m (graphIdx w k) :=
  Fin.addCases_right _

@[simp] theorem selBandGraph_castAdd (m : ℕ) {N : ℕ} (w : Fin N → CellType)
    (j : Fin (nGraph N w)) (i : Fin (m + nBand N w)) :
    selBandGraph m w j (Fin.castAdd 1 i) = selBand m w i :=
  Fin.addCases_left _

@[simp] theorem selBandGraph_last (m : ℕ) {N : ℕ} (w : Fin N → CellType)
    (j : Fin (nGraph N w)) :
    selBandGraph m w j (Fin.last (m + nBand N w)) = Fin.natAdd m (graphIdx w j) := by
  rw [show Fin.last (m + nBand N w) = Fin.natAdd (m + nBand N w) (0 : Fin 1) from
    Fin.ext (by simp [Fin.natAdd])]
  exact Fin.addCases_right 0

/-! ## 4. The slot map and the sheet equivalence -/

/-- The position of level `j` of the word `w` in the list (band coordinates, graph
coordinates) of the sheet. -/
def slot {N : ℕ} (w : Fin N → CellType) (j : Fin N) : Fin (nBand N w + nGraph N w) :=
  if h : bandBit (w j) = 1 then
    ⟨bandRank w j, bandRank_lt_sum w h⟩
  else
    ⟨nBand N w + graphRank w j, graphRank_add_lt_sum w h⟩

theorem slot_val {N : ℕ} (w : Fin N → CellType) (j : Fin N) :
    (slot w j).val = if bandBit (w j) = 1 then bandRank w j else nBand N w + graphRank w j := by
  unfold slot
  by_cases h : bandBit (w j) = 1 <;> simp [h]

theorem slot_band {N : ℕ} (w : Fin N → CellType) {j : Fin N} (h : bandBit (w j) = 1) :
    slot w j = ⟨bandRank w j, bandRank_lt_sum w h⟩ := by
  unfold slot
  rw [dif_pos h]

theorem slot_graph {N : ℕ} (w : Fin N → CellType) {j : Fin N} (h : ¬ bandBit (w j) = 1) :
    slot w j = ⟨nBand N w + graphRank w j, graphRank_add_lt_sum w h⟩ := by
  unfold slot
  rw [dif_neg h]

theorem slot_injective {N : ℕ} (w : Fin N → CellType) : Function.Injective (slot w) := by
  intro j j' h
  have hval : (slot w j).val = (slot w j').val := by rw [h]
  rw [slot_val, slot_val] at hval
  by_cases hj : bandBit (w j) = 1
  · rw [if_pos hj] at hval
    have hj' : bandBit (w j') = 1 := by
      by_contra hc
      rw [if_neg hc] at hval
      have hlt := bandRank_lt_nBand w hj
      omega
    rw [if_pos hj'] at hval
    rcases lt_trichotomy j j' with hlt | heq | hgt
    · exact absurd hval (ne_of_lt (bandRank_lt_of_lt w hj hlt))
    · exact heq
    · exact absurd hval.symm (ne_of_lt (bandRank_lt_of_lt w hj' hgt))
  · rw [if_neg hj] at hval
    have hj' : ¬ bandBit (w j') = 1 := by
      intro hc
      rw [if_pos hc] at hval
      have hlt := bandRank_lt_nBand w hc
      omega
    rw [if_neg hj'] at hval
    have hrank : graphRank w j = graphRank w j' := by omega
    rcases lt_trichotomy j j' with hlt | heq | hgt
    · exact absurd hrank (ne_of_lt (graphRank_lt_of_lt w (graphBit_eq_one hj) hlt))
    · exact heq
    · exact absurd hrank.symm
        (ne_of_lt (graphRank_lt_of_lt w (graphBit_eq_one hj') hgt))

/-- The sheet equivalence attached to a type word: band levels first, graph levels last. -/
def wordEquiv {N : ℕ} (w : Fin N → CellType) : Fin N ≃ Fin (nBand N w + nGraph N w) :=
  Equiv.ofBijective (slot w) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨slot_injective w, ?_⟩
    simp [nBand_add_nGraph])

theorem wordEquiv_apply {N : ℕ} (w : Fin N → CellType) (j : Fin N) :
    wordEquiv w j = slot w j := Equiv.ofBijective_apply _ _ _

/-- The `j`-th fibre coordinate of a sheet point is a band coordinate when level `j` of the
word is a band, and a graph coordinate otherwise. -/
theorem sheetPt_wordEquiv_band {m N : ℕ} (w : Fin N → CellType)
    (v : Fin (m + nBand N w) → ℝ) (u : Fin (nGraph N w) → ℝ) (j : Fin N)
    (h : bandBit (w j) = 1) :
    sheetPtM (wordEquiv w) v u (Fin.natAdd m j) =
      v (Fin.natAdd m ⟨bandRank w j, bandRank_lt_nBand w h⟩) := by
  rw [sheetPtM_natAdd, wordEquiv_apply, slot_band w h]
  rw [show (⟨bandRank w j, _⟩ : Fin (nBand N w + nGraph N w)) =
      Fin.castAdd (nGraph N w) ⟨bandRank w j, bandRank_lt_nBand w h⟩ from Fin.ext rfl]
  exact Fin.append_left _ _ _

theorem sheetPt_wordEquiv_graph {m N : ℕ} (w : Fin N → CellType)
    (v : Fin (m + nBand N w) → ℝ) (u : Fin (nGraph N w) → ℝ) (j : Fin N)
    (h : bandBit (w j) = 0) :
    sheetPtM (wordEquiv w) v u (Fin.natAdd m j) =
      u ⟨graphRank w j, graphRank_lt_nGraph_of_zero w h⟩ := by
  have h' : ¬ bandBit (w j) = 1 := by rw [h]; simp
  rw [sheetPtM_natAdd, wordEquiv_apply, slot_graph w h']
  rw [show (⟨nBand N w + graphRank w j, _⟩ : Fin (nBand N w + nGraph N w)) =
      Fin.natAdd (nBand N w) ⟨graphRank w j, graphRank_lt_nGraph_of_zero w h⟩ from
    Fin.ext rfl]
  exact Fin.append_right _ _ _

end Work.WilCrux
