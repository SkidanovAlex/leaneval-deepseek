import Mathlib
import Submission.Work.LT.good_base_defs
import Submission.Work.LT.gb_basic
import Submission.Work.LT.gb_extension
import Submission.Work.LT.gb_rank_le
import Submission.Work.LT.gb_matRank_eq_rowRank
import Submission.Work.LT.gb_wt_helpers
import Submission.Work.LT.gb_compl_bound_row
import Submission.Work.LT.gb_compl_bound_col

/-!
# Kalachev--Panteleev Lemma 10 (zero rectangles for `CA ⊞ CB`)

If both codes `CA`, `CB` satisfy property `(*)` with parameter `α` and rank bound `r`, and
`x ∈ CA ⊞ CB` is non-zero of weight `|x| ≤ α² D²/4` and rank `< r`, then `x` vanishes on a
rectangle `A × B` whose complementary rows and columns are at most `2|x| / (α D)` in number.

The proof follows Kalachev--Panteleev, *Two-sided robustly testable codes* (arXiv 2206.09973),
Lemma "on no sparse low-rank codewords".  Let `A` be the rows of `x` of weight at most `α D / 2`
and `B` the columns of weight at most `α D / 2`.  Then `|Aᶜ|, |Bᶜ| ≤ 2|x|/(α D) ≤ α D / 2`.
If `x` did not vanish on `A × B`, KP Lemma 9 (`gb_extension`) would produce `x' ∈ CA ⊞ CB` agreeing
with `x` on `A × B`, whose rows are spanned by the rows indexed by `A` and whose columns by the
columns indexed by `B`; the rows through `A` have weight `≤ α D / 2 + |Bᶜ| ≤ α D`, so the row space
of `x'` is `α`-sparse, and likewise its column space.  Applying property `(*)` to the two sparse
spaces and KP Lemma 8 (`gb_rank_le`) gives
`rk x' ≤ dim(CA ∩ cols x') + dim(CB ∩ rows x') < ½ rk x' + ½ rk x' = rk x'`, a contradiction.
-/

set_option linter.unusedVariables false

namespace Work.LT

/-- Kalachev--Panteleev Lemma 10. If both codes satisfy property `(*)` with parameter `α`, and `x ∈ CA ⊞ CB` is non-zero of weight at most `α² D²/4` and rank `< r`, then `x` has a zero rectangle `A × B` (rows `A`, columns `B`) whose complement sizes are at most `2 |x| / (α D)`. -/
theorem gb_zero_rect_of_star {D : ℕ} (CA CB : Submodule (ZMod 2) (Fin D → ZMod 2))
    (α : ℝ) (r : ℕ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hstarA : GB.HasStar α r CA) (hstarB : GB.HasStar α r CB)
    (x : Fin D × Fin D → ZMod 2) (hx : x ∈ GB.prodSum CA CB) (hx0 : x ≠ 0)
    (hw : (GB.wt x : ℝ) ≤ α ^ 2 * (D : ℝ) ^ 2 / 4) (hr : GB.matRank x < r) :
    ∃ A B : Finset (Fin D), (∀ i ∈ A, ∀ j ∈ B, x (i, j) = 0) ∧
      (((Finset.univ \ A).card : ℕ) : ℝ) ≤ 2 * (GB.wt x : ℝ) / (α * D) ∧
      (((Finset.univ \ B).card : ℕ) : ℝ) ≤ 2 * (GB.wt x : ℝ) / (α * D) := by
  classical
  -- `D ≠ 0`, since otherwise `x = 0`
  have hD : 0 < D := by
    rcases Nat.eq_zero_or_pos D with h | h
    · subst h
      exfalso
      exact hx0 (funext fun q => (Nat.not_lt_zero q.1.val q.1.isLt).elim)
    · exact h
  -- rows and columns of `x` of weight at most `α D / 2`
  set A : Finset (Fin D) :=
    Finset.univ.filter (fun i => (hammingNorm (GB.row x i) : ℝ) ≤ α * (D : ℝ) / 2) with hAdef
  set B : Finset (Fin D) :=
    Finset.univ.filter (fun j => (hammingNorm (GB.col x j) : ℝ) ≤ α * (D : ℝ) / 2) with hBdef
  have hAmem : ∀ i, i ∈ A ↔ (hammingNorm (GB.row x i) : ℝ) ≤ α * (D : ℝ) / 2 := by
    intro i; rw [hAdef]; simp
  have hBmem : ∀ j, j ∈ B ↔ (hammingNorm (GB.col x j) : ℝ) ≤ α * (D : ℝ) / 2 := by
    intro j; rw [hBdef]; simp
  obtain ⟨hAc, hAc2⟩ := gb_compl_bound_row α hα hD x hw A hAmem
  obtain ⟨hBc, hBc2⟩ := gb_compl_bound_col α hα hD x hw B hBmem
  refine ⟨A, B, ?_, hAc, hBc⟩
  -- suppose `x` does not vanish on `A × B`
  by_contra hcon
  push Not at hcon
  obtain ⟨i0, hi0, j0, hj0, hne0⟩ := hcon
  -- extension of `x|_(A × B)` to a codeword `x'` (KP Lemma 9)
  obtain ⟨x', hx'mem, hagree, hrank, hrowsp, hcolsp⟩ := gb_extension CA CB x hx A B
  have hx'pt : x' (i0, j0) ≠ 0 := by
    rw [hagree i0 hi0 j0 hj0]; exact hne0
  -- the column space and row space of `x'` are non-trivial
  have hXpos : 0 < GB.frk (GB.colSpan x') := by
    have hcolne : GB.col x' j0 ≠ 0 := by
      intro hh; exact hx'pt (congr_fun hh i0)
    have hle : Submodule.span (ZMod 2) ({GB.col x' j0} : Set (Fin D → ZMod 2)) ≤ GB.colSpan x' :=
      Submodule.span_le.mpr (by rintro v rfl; exact GB.col_mem_colSpan x' j0)
    have hmono := Submodule.finrank_mono hle
    simp only [GB.frk] at hmono ⊢
    rw [finrank_span_singleton hcolne] at hmono
    omega
  have hYpos : 0 < GB.frk (GB.rowSpan x') := by
    have hrowne : GB.row x' i0 ≠ 0 := by
      intro hh; exact hx'pt (congr_fun hh j0)
    have hle : Submodule.span (ZMod 2) ({GB.row x' i0} : Set (Fin D → ZMod 2)) ≤ GB.rowSpan x' :=
      Submodule.span_le.mpr (by rintro v rfl; exact GB.row_mem_rowSpan x' i0)
    have hmono := Submodule.finrank_mono hle
    simp only [GB.frk] at hmono ⊢
    rw [finrank_span_singleton hrowne] at hmono
    omega
  have hXdim : GB.frk (GB.colSpan x') = GB.matRank x' := rfl
  have hYdim : GB.frk (GB.rowSpan x') = GB.matRank x' := (gb_matRank_eq_rowRank x').symm
  have hXr : GB.frk (GB.colSpan x') ≤ r := by rw [hXdim]; omega
  have hYr : GB.frk (GB.rowSpan x') ≤ r := by rw [hYdim]; omega
  -- the column space of `x'` is `α`-sparse ...
  have hXsparse : GB.IsSparse α (GB.colSpan x') := by
    refine ⟨Set.range (fun j' : {j : Fin D // j ∈ B} => GB.col x' j'.1), ?_, ?_⟩
    · rintro v ⟨j', rfl⟩
      have h1 := hammingNorm_le_add_sdiff (GB.col x' j'.1) (GB.col x j'.1) A
        (fun i hi => hagree i hi j'.1 j'.2)
      have h2 : (hammingNorm (GB.col x j'.1) : ℝ) ≤ α * (D : ℝ) / 2 := (hBmem j'.1).mp j'.2
      have h1' : (hammingNorm (GB.col x' j'.1) : ℝ)
          ≤ (hammingNorm (GB.col x j'.1) : ℝ) + ((Finset.univ \ A).card : ℝ) := by
        exact_mod_cast h1
      have hgoal : (hammingNorm (GB.col x' j'.1) : ℝ) ≤ α * (D : ℝ) := by linarith
      simpa using hgoal
    · apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro v ⟨j', rfl⟩
        exact GB.col_mem_colSpan x' j'.1
      · rw [GB.colSpan_le_iff]; exact hcolsp
  -- ... and the row space of `x'` is `α`-sparse
  have hYsparse : GB.IsSparse α (GB.rowSpan x') := by
    refine ⟨Set.range (fun i' : {i : Fin D // i ∈ A} => GB.row x' i'.1), ?_, ?_⟩
    · rintro v ⟨i', rfl⟩
      have h1 := hammingNorm_le_add_sdiff (GB.row x' i'.1) (GB.row x i'.1) B
        (fun j hj => hagree i'.1 i'.2 j hj)
      have h2 : (hammingNorm (GB.row x i'.1) : ℝ) ≤ α * (D : ℝ) / 2 := (hAmem i'.1).mp i'.2
      have h1' : (hammingNorm (GB.row x' i'.1) : ℝ)
          ≤ (hammingNorm (GB.row x i'.1) : ℝ) + ((Finset.univ \ B).card : ℝ) := by
        exact_mod_cast h1
      have hgoal : (hammingNorm (GB.row x' i'.1) : ℝ) ≤ α * (D : ℝ) := by linarith
      simpa using hgoal
    · apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro v ⟨i', rfl⟩
        exact GB.row_mem_rowSpan x' i'.1
      · rw [GB.rowSpan_le_iff]; exact hrowsp
  -- property `(*)` contradicts the rank inequality of KP Lemma 8
  have hstarX := hstarA (GB.colSpan x') hXsparse hXpos hXr
  have hstarY := hstarB (GB.rowSpan x') hYsparse hYpos hYr
  have hrankle := gb_rank_le CA CB x' hx'mem
  rw [hXdim] at hstarX
  rw [hYdim] at hstarY
  omega

end Work.LT
