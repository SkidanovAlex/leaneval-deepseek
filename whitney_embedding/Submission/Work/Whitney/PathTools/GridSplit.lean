import Submission.Work.Whitney.PathTools.Grid

/-!
# Splitting a `1`-chain along separated cell complexes

Algebraic heart of Janiszewski's theorem in the `ZMod 2` grid model of `Grid.lean`:
if a chain from `p` to `q` avoids a cell complex `S₁`, another chain from `p` to `q`
avoids `S₂`, and the two complexes are separated in the grid, then there is a chain
from `p` to `q` avoiding `S₁ ∪ S₂`.
-/

namespace Work.Whitney.PathTools.Grid

open scoped BigOperators

/-- The two cells having a given edge as a face. -/
def edgeCells : Edge → Finset Cell
  | (false, i, j) => {(i, j), (i - 1, j)}
  | (true, i, j) => {(i, j), (i, j - 1)}

/-- The four edges of a cell. -/
def cellEdges (c : Cell) : Finset Edge :=
  {(false, c.1, c.2), (false, c.1 + 1, c.2), (true, c.1, c.2), (true, c.1, c.2 + 1)}

/-- The edges of the cells of a set of cells. -/
def edgeSet (S : Set Cell) : Set Edge := {e | ∃ c ∈ S, e ∈ cellEdges c}

/-- Incidence is symmetric: `c` is a face-cell of `e` iff `e` is an edge of `c`. -/
lemma mem_edgeCells_iff {c : Cell} {e : Edge} : c ∈ edgeCells e ↔ e ∈ cellEdges c := by
  obtain ⟨b, i, j⟩ := e
  obtain ⟨a, k⟩ := c
  cases b <;> simp [edgeCells, cellEdges] <;> constructor <;> intro h <;> omega

/-- The cells sharing an edge with (or equal to) a cell of `S`. -/
def starCells (S : Set Cell) : Set Cell := {c | ∃ c' ∈ S, ∃ e ∈ cellEdges c, e ∈ cellEdges c'}

lemma bdry2_apply (w : C2) (e : Edge) : bdry2 w e = ∑ c ∈ edgeCells e, w c := by
  obtain ⟨b, i, j⟩ := e
  cases b
  · simp only [bdry2, edgeCells]
    rw [Finset.sum_pair (by intro h; simp only [Prod.mk.injEq] at h; omega : ((i, j) : ℤ × ℤ) ≠ (i - 1, j))]
  · simp only [bdry2, edgeCells]
    rw [Finset.sum_pair (by intro h; simp only [Prod.mk.injEq] at h; omega : ((i, j) : ℤ × ℤ) ≠ (i, j - 1))]

/-- The boundary of a chain vanishing off `S` is supported on the edges of the cells of `S`. -/
lemma support_bdry2 (w : C2) {S : Set Cell} (hw : ∀ c ∉ S, w c = 0) {e : Edge}
    (he : bdry2 w e ≠ 0) : e ∈ edgeSet S := by
  rw [bdry2_apply] at he
  by_contra hcon
  refine he (Finset.sum_eq_zero fun c hc => ?_)
  exact hw c fun hcs => hcon ⟨c, hcs, mem_edgeCells_iff.mp hc⟩

/-- The restriction of a `2`-chain to a set of cells. -/
noncomputable def arestrict (w : C2) (S : Set Cell) : C2 := S.indicator w

lemma arestrict_zero (w : C2) (S : Set Cell) : ∀ c ∉ S, arestrict w S c = 0 :=
  fun c hc => Set.indicator_of_notMem hc w

lemma arestrict_self (w : C2) (S : Set Cell) : ∀ c ∈ S, arestrict w S c = w c :=
  fun c hc => Set.indicator_of_mem hc w

lemma add_arestrict_mem (w : C2) (S : Set Cell) {c : Cell} (h : c ∈ S) :
    w c + arestrict w S c = 0 := by
  rw [arestrict_self w S c h, CharTwo.add_self_eq_zero]

lemma add_arestrict_notMem (w : C2) (S : Set Cell) {c : Cell} (h : c ∉ S) :
    w c + arestrict w S c = w c := by
  rw [arestrict_zero w S c h, add_zero]

lemma edgeSet_finite {S : Set Cell} (hS : S.Finite) : (edgeSet S).Finite := by
  classical
  have h : edgeSet S ⊆ ⋃ c ∈ hS.toFinset, (cellEdges c : Set Edge) := by
    rintro e ⟨c, hc, he⟩
    exact Set.mem_biUnion (hS.mem_toFinset.mpr hc) he
  exact Set.Finite.subset (hS.toFinset.finite_toSet.biUnion fun c _ => (cellEdges c).finite_toSet) h

lemma starCells_finite {S : Set Cell} (hS : S.Finite) : (starCells S).Finite := by
  classical
  have h : starCells S ⊆ ⋃ e ∈ (edgeSet_finite hS).toFinset, (edgeCells e : Set Cell) := by
    rintro c ⟨c', hc', e, he, he'⟩
    refine Set.mem_biUnion ((edgeSet_finite hS).mem_toFinset.mpr ⟨c', hc', he'⟩) ?_
    exact mem_edgeCells_iff.mpr he
  exact Set.Finite.subset ((edgeSet_finite hS).toFinset.finite_toSet.biUnion
    fun e _ => (edgeCells e).finite_toSet) h

/-- **Splitting lemma.**  Let `S₁`, `S₂` be cell sets with disjoint edge sets and such that every
cell sharing an edge with `S₁` and with `S₂` already lies in `S₁`.  If `l₁`, `l₂` are chains with
the same boundary avoiding `S₁` respectively `S₂`, then there is a chain with the same boundary
avoiding `S₁ ∪ S₂`. -/
theorem exists_chain_avoiding_union {S₁ S₂ : Set Cell} (hS₁ : S₁.Finite)
    (hdisj : Disjoint (edgeSet S₁) (edgeSet S₂))
    (hsep : ∀ c, c ∈ starCells S₁ → c ∈ starCells S₂ → c ∈ S₁)
    {l₁ l₂ : Chain1} (hb : bdry1 (l₁ : Edge → ZMod 2) = bdry1 (l₂ : Edge → ZMod 2))
    (h₁ : ∀ e ∈ l₁.support, e ∉ edgeSet S₁)
    (h₂ : ∀ e ∈ l₂.support, e ∉ edgeSet S₂) :
    ∃ l₀ : Edge → ZMod 2, bdry1 l₀ = bdry1 (l₁ : Edge → ZMod 2) ∧
      (Function.support l₀).Finite ∧
      ∀ e, l₀ e ≠ 0 → e ∉ edgeSet S₁ ∧ e ∉ edgeSet S₂ := by
  classical
  set c : Chain1 := l₁ + l₂ with hc
  have hcb : bdry1 (c : Edge → ZMod 2) = 0 := by
    rw [hc, Finsupp.coe_add, bdry1_add, hb, CharTwo.add_self_eq_zero]
  set w : C2 := fill c with hw
  have hwb : bdry2 w = (c : Edge → ZMod 2) := bdry2_fill c hcb
  have hcw : ∀ e, bdry2 w e = (l₁ : Edge → ZMod 2) e + (l₂ : Edge → ZMod 2) e := by
    intro e
    have := congrFun hwb e
    rw [hc, Finsupp.coe_add] at this
    simpa using this
  set T : Set Cell := starCells S₁ with hT
  -- the chain we produce
  set l₀ : Edge → ZMod 2 := fun e => (l₂ : Edge → ZMod 2) e + bdry2 (arestrict w T) e with hl₀def
  have hTfin : T.Finite := by rw [hT]; exact starCells_finite hS₁
  refine ⟨l₀, ?_, ?_, ?_⟩
  · have h1 : bdry1 l₀ = bdry1 (l₂ : Edge → ZMod 2) + bdry1 (bdry2 (arestrict w T)) := by
      rw [← bdry1_add]; rfl
    rw [h1, bdry1_bdry2, add_zero]; exact hb.symm
  · have hsub : Function.support l₀ ⊆ l₂.support ∪ edgeSet T := by
      intro e he
      rw [Function.mem_support] at he
      by_cases h₂e : (l₂ : Edge → ZMod 2) e = 0
      · have hb' : bdry2 (arestrict w T) e ≠ 0 := by
          intro h0
          exact he (by rw [hl₀def]; simp only; rw [h₂e, h0, add_zero])
        exact Or.inr (support_bdry2 (arestrict w T) (arestrict_zero w T) hb')
      · exact Or.inl (Finsupp.mem_support_iff.mpr h₂e)
    exact (l₂.support.finite_toSet.union (edgeSet_finite hTfin)).subset hsub
  · set w' : C2 := fun cc => w cc + arestrict w T cc with hw'def
    have hw'zero : ∀ cc ∈ T, w' cc = 0 := by
      intro cc hcc
      simp only [hw'def]
      rw [add_arestrict_mem w T hcc]
    have hsplit : ∀ e, bdry2 w' e = bdry2 w e + bdry2 (arestrict w T) e := by
      intro e
      simp only [bdry2_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun c _ => by simp [hw'def]
    have hdecomp : ∀ e, l₀ e = bdry2 w' e + (l₁ : Edge → ZMod 2) e := by
      intro e
      rw [hl₀def, hsplit e, hcw e]
      simp only
      rw [show ((l₁ : Edge → ZMod 2) e + (l₂ : Edge → ZMod 2) e + bdry2 (arestrict w T) e)
            + (l₁ : Edge → ZMod 2) e
          = (l₂ : Edge → ZMod 2) e + bdry2 (arestrict w T) e
            + ((l₁ : Edge → ZMod 2) e + (l₁ : Edge → ZMod 2) e) from by abel,
        CharTwo.add_self_eq_zero, add_zero]
    intro e he
    refine ⟨?_, ?_⟩
    · rw [hdecomp e] at he
      by_cases hl₁ : (l₁ : Edge → ZMod 2) e = 0
      · have hb' : bdry2 w' e ≠ 0 := by
          intro h0; exact he (by rw [h0, hl₁, add_zero])
        obtain ⟨c, hcT, hce⟩ := support_bdry2 w' (S := Tᶜ)
          (fun cc hcc => hw'zero cc (by simpa using hcc)) hb'
        rintro ⟨c₁, hc₁, hc₁e⟩
        exact hcT ⟨c₁, hc₁, e, hce, hc₁e⟩
      · exact fun hc₁ => h₁ e (Finsupp.mem_support_iff.mpr hl₁) hc₁
    · by_cases hl₂ : (l₂ : Edge → ZMod 2) e = 0
      · have hb' : bdry2 (arestrict w T) e ≠ 0 := by
          intro h0
          refine he ?_
          rw [hl₀def]
          simp only
          rw [hl₂, h0, add_zero]
        obtain ⟨c, hcT, hce⟩ := support_bdry2 (arestrict w T) (arestrict_zero w T) hb'
        rintro ⟨c₂, hc₂, hc₂e⟩
        have hcT' : c ∈ starCells S₁ := hT ▸ hcT
        have hcS₂ : c ∈ starCells S₂ := ⟨c₂, hc₂, e, hce, hc₂e⟩
        have hcS₁ : c ∈ S₁ := hsep c hcT' hcS₂
        exact (hdisj.le_bot ⟨⟨c, hcS₁, hce⟩, ⟨c₂, hc₂, hc₂e⟩⟩).elim
      · exact fun hc₂ => h₂ e (Finsupp.mem_support_iff.mpr hl₂) hc₂

end Work.Whitney.PathTools.Grid
