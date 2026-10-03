import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.winE_mono
import Submission.Work.OROneRel.twoLetterTlDefs
import Submission.Work.OROneRel.unionAmalgamDefs

/-!
# Gate bookkeeping for the line amalgam of band domains

The `N = 1` normal form (`Submission/Work/OROneRel/unionAmalgam_normalForm.lean`) reduces the
iteration to instantiating the union/amalgam van Kampen for **consecutive band domains**
`D_0 = winE c lo hi`, `D_1 = winE c (lo+1) (hi+1)`.  This file supplies the bookkeeping that
instantiation needs — purely set-theoretic, no `π₁`:

* `winTree_mono` — the gauge tree of a *sub*window is the restriction of that of the window
  (`winE` is monotone and "trivial loop class" is window-independent).  This makes the successive
  spanning trees **agree on the overlap**: the gate's spanning tree is a subtree of each piece's.
* `winE_inter_shift` — **the gate**: `winE c lo hi ∩ winE c (lo+t) (hi+t) = winE c (lo+t) hi`.
* `winTree_gate_subset` — the gate's spanning tree is contained in *both* pieces' spanning trees.
* `winE_union_shift` — **coverage**: for the two-letter weight `tlW p q` and a window of length at
  least one period (`lo + p*q ≤ hi`), the two pieces cover the union,
  `winE c lo hi ∪ winE c (lo+1) (hi+1) = winE c lo (hi+1)` (the hypothesis `hE` of
  `presentedGroup_union_amalgam`).
* `gateTreeRel_map_subset₁` / `_₂` — the **relator compatibility** (the hypotheses `h₁`/`h₂` of
  `presentedGroup_union_amalgam`): the gate's tree-edge relators (`gateTreeRel`) map into each
  piece's tree-edge relators (`treeRel`).

Together these are exactly the gate-side inputs the union/amalgam van Kampen needs; the remaining
`2`-cell part of `S₁`/`S₂` is independent of the gate, since the gate `winE c (lo+1) hi` carries no
`2`-cell as soon as `hi ≤ lo + pq`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- **The gauge tree of a subwindow is the restriction of that of the window.** -/
theorem winTree_mono (Wt : ℤ → FreeGroup α) (c : α → ℤ) {lo hi lo' hi' : ℤ}
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    winTree Wt c lo hi ⊆ winTree Wt c lo' hi' := by
  intro e he
  rw [mem_winTree] at he ⊢
  exact ⟨winE_mono c hlo hhi he.1, he.2⟩

/-- **The gate.**  The intersection of two shifted windows is the band swept out by the shift. -/
theorem winE_inter_shift (c : α → ℤ) (lo hi t : ℤ) (ht : 0 ≤ t) :
    winE c lo hi ∩ winE c (lo + t) (hi + t) = winE c (lo + t) hi := by
  ext e
  simp only [Set.mem_inter_iff, mem_winE]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7, h8⟩
    exact ⟨h5, h2, h7, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨by linarith, h2, by linarith, h4⟩, ⟨h1, by linarith, h3, by linarith⟩⟩

/-- **The gate's spanning tree is a subtree of both pieces'.** -/
theorem winTree_gate_subset (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) :
    winTree Wt c (lo + 1) hi ⊆ winTree Wt c lo hi ∩ winTree Wt c (lo + 1) (hi + 1) := by
  intro e he
  exact ⟨winTree_mono Wt c (lo := lo + 1) (hi := hi) (lo' := lo) (hi' := hi)
      (by linarith) le_rfl he,
    winTree_mono Wt c (lo := lo + 1) (hi := hi) (lo' := lo + 1) (hi' := hi + 1)
      le_rfl (by linarith) he⟩

/-- **Coverage of the union by two consecutive windows**, for the two-letter weight `tlW p q`
(`a ↦ q`, `b ↦ -p`) and a window of length at least one period.  This is the hypothesis `hE` of
`presentedGroup_union_amalgam` for consecutive band domains. -/
theorem winE_union_shift (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (lo hi : ℤ)
    (hspan : lo + (p : ℤ) * (q : ℤ) ≤ hi) :
    winE (tlW p q) lo hi ∪ winE (tlW p q) (lo + 1) (hi + 1) = winE (tlW p q) lo (hi + 1) := by
  have hq1 : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
  have hp1 : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  have hq0 : (0 : ℤ) ≤ (q : ℤ) := by linarith
  have hp0 : (0 : ℤ) ≤ (p : ℤ) := by linarith
  have hq_le : (q : ℤ) ≤ (p : ℤ) * (q : ℤ) := by nlinarith [hp1, hq0]
  have hp_le : (p : ℤ) ≤ (p : ℤ) * (q : ℤ) := by nlinarith [hq1, hp0]
  have htl0 : tlW p q (0 : Fin 2) = (q : ℤ) := rfl
  have htl1 : tlW p q (1 : Fin 2) = -(p : ℤ) := rfl
  ext e
  obtain ⟨x, i⟩ := e
  have hx : x = (0 : Fin 2) ∨ x = (1 : Fin 2) := by fin_cases x <;> simp
  rcases hx with rfl | rfl
  · -- the `a`-edge, weight `q`
    simp only [Set.mem_union, mem_winE, htl0]
    constructor
    · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
      · exact ⟨h1, by linarith, h3, by linarith⟩
      · exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3, h4⟩
      by_cases hcase : lo + 1 ≤ i
      · exact Or.inr ⟨hcase, h2, by linarith, h4⟩
      · push_neg at hcase
        refine Or.inl ⟨h1, by linarith [hcase, hspan, hq_le, hq1], h3, ?_⟩
        by_contra hcon
        push_neg at hcon
        linarith [hspan, hcase, hcon, h4, hq_le]
  · -- the `b`-edge, weight `-p`
    simp only [Set.mem_union, mem_winE, htl1]
    constructor
    · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
      · exact ⟨h1, by linarith, h3, by linarith⟩
      · exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3, h4⟩
      by_cases hcase : lo + (p : ℤ) + 1 ≤ i
      · exact Or.inr ⟨by linarith, h2, by linarith, h4⟩
      · push_neg at hcase
        exact Or.inl ⟨h1, by linarith [hcase, hp_le, hspan],
          h3, by linarith [hcase, hspan, hq_le, hq1]⟩

/-- The tree-edge relators of a window: the edges of its gauge tree, killed in the presentation. -/
def treeRel (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) :
    Set (FreeGroup ↥(winE c lo hi)) :=
  {w | ∃ e : ↥(winE c lo hi), (e : α × ℤ) ∈ winTree Wt c lo hi ∧ w = FreeGroup.of e}

/-- The tree-edge relators of the gate, as relators over the intersection `E₁ ∩ E₂`.  The predicate
used is "trivial loop class", which is window-independent, so this *is* the gate's gauge tree. -/
def gateTreeRel (Wt : ℤ → FreeGroup α) (c : α → ℤ) (E₁ E₂ : Set (α × ℤ)) :
    Set (FreeGroup ↥(E₁ ∩ E₂)) :=
  {w | ∃ e : ↥(E₁ ∩ E₂), coverClassAt Wt c (e : α × ℤ) = 1 ∧ w = FreeGroup.of e}

/-- **Relator compatibility, first piece** (the hypothesis `h₁` of `presentedGroup_union_amalgam`):
the gate's tree-edge relators map into the first piece's.  This holds because "trivial loop class"
is window-independent and the gate's tree is a subtree of the first piece's (`winTree_gate_subset`),
so no spanning-tree choice is needed. -/
theorem gateTreeRel_map_subset₁ (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) :
    FreeGroup.map (inc₁ (winE c lo hi) (winE c (lo + 1) (hi + 1))) ''
        gateTreeRel Wt c (winE c lo hi) (winE c (lo + 1) (hi + 1))
      ⊆ treeRel Wt c lo hi := by
  rintro w ⟨a, ⟨e, he, rfl⟩, rfl⟩
  exact ⟨inc₁ _ _ e, mem_winTree.mpr ⟨e.2.1, he⟩, FreeGroup.map.of⟩

/-- **Relator compatibility, second piece** (the hypothesis `h₂` of `presentedGroup_union_amalgam`). -/
theorem gateTreeRel_map_subset₂ (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) :
    FreeGroup.map (inc₂ (winE c lo hi) (winE c (lo + 1) (hi + 1))) ''
        gateTreeRel Wt c (winE c lo hi) (winE c (lo + 1) (hi + 1))
      ⊆ treeRel Wt c (lo + 1) (hi + 1) := by
  rintro w ⟨a, ⟨e, he, rfl⟩, rfl⟩
  exact ⟨inc₂ _ _ e, mem_winTree.mpr ⟨e.2.2, he⟩, FreeGroup.map.of⟩

end Work.OROneRel
