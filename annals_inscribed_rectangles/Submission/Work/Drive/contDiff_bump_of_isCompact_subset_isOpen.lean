import Mathlib

namespace Work.Drive

open Set Metric Function

/-- Smooth Urysohn bump: a compact set contained in an open set of a finite-dimensional real
normed space admits a `C^∞` function with values in `[0,1]`, equal to `1` on the compact set and
with compact support contained in the open set. -/
theorem contDiff_bump_of_isCompact_subset_isOpen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ f : E → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧ (∀ x ∈ K, f x = 1) ∧ tsupport f ⊆ U := by
  -- an open set `O` with `K ⊆ O` and `closure O ⊆ U`
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hδ2 : (0 : ℝ) < δ / 2 := half_pos hδ
  set O : Set E := interior (cthickening (δ / 2) K) with hOdef
  have hOopen : IsOpen O := by rw [hOdef]; exact isOpen_interior
  have hKO : K ⊆ O := by
    rw [hOdef]
    exact (self_subset_thickening hδ2 K).trans
      (interior_maximal (thickening_subset_cthickening (δ / 2) K) isOpen_thickening)
  have hclO : closure O ⊆ U := by
    rw [hOdef]
    refine (closure_mono interior_subset).trans ?_
    rw [isClosed_cthickening.closure_eq]
    exact (cthickening_mono (by linarith) K).trans hδU
  -- a smooth nonnegative function supported exactly on `O`, and one supported exactly on `Kᶜ`
  obtain ⟨f, hfs, hfcd, hfr⟩ := hOopen.exists_contDiff_support_eq (n := ⊤)
  obtain ⟨g, hgs, hgcd, hgr⟩ := hK.isClosed.isOpen_compl.exists_contDiff_support_eq (n := ⊤)
  have hfpos : ∀ x, 0 ≤ f x := fun x => (hfr (mem_range_self x)).1
  have hgpos : ∀ x, 0 ≤ g x := fun x => (hgr (mem_range_self x)).1
  -- the denominators are everywhere positive
  have hden : ∀ x, 0 < f x + g x := by
    intro x
    by_cases hx : x ∈ support f
    · have hxf : 0 < f x := lt_of_le_of_ne (hfpos x) (Ne.symm (by simpa [mem_support] using hx))
      linarith [hgpos x]
    · have hxO : x ∉ O := by rw [← hfs]; exact hx
      have hxK : x ∉ K := fun h => hxO (hKO h)
      have hxg : 0 < g x := by
        refine lt_of_le_of_ne (hgpos x) (Ne.symm ?_)
        rw [← mem_support, hgs]
        exact hxK
      linarith [hfpos x]
  refine ⟨fun y => f y / (f y + g y), ?_, ?_, ?_, ?_⟩
  · exact hfcd.div (hfcd.add hgcd) fun y => (hden y).ne'
  · intro y
    refine ⟨div_nonneg (hfpos y) (hden y).le, ?_⟩
    rw [div_le_one (hden y)]
    linarith [hgpos y]
  · intro y hy
    have hgy : g y = 0 := by
      have : y ∉ support g := by rw [hgs]; exact fun h => h hy
      simpa [mem_support] using this
    have hfy : f y ≠ 0 := by
      have : y ∈ support f := by rw [hfs]; exact hKO hy
      simpa [mem_support] using this
    show f y / (f y + g y) = 1
    rw [hgy, add_zero, div_self hfy]
  · refine (closure_mono ?_).trans hclO
    intro y hy
    have hmem : f y / (f y + g y) ≠ 0 := by simpa [mem_support] using hy
    have hfy : f y ≠ 0 := by
      intro h0
      exact hmem (by rw [h0, zero_div])
    rw [← hfs]
    simpa [mem_support] using hfy

end Work.Drive
