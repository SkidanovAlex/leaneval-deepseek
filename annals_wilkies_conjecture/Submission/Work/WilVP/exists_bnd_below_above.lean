import Mathlib
import Submission.Work.WilC2.BndDefs
import Submission.Work.WilC2.gap_subset_of_bnd

namespace Work.WilVP

/-- A nonempty bounded subset `D` of `ℝ` that is not locally "all of `D`" at `x ∈ D` has boundary
points strictly below and strictly above `x`: `sInf D` and `sSup D` are boundary points
(`Work.WilC2.IsBnd`), and they are `< x`, `> x` respectively because `¬ IsBnd D x` with `x ∈ D`
puts an interval around `x` inside `D`. -/
theorem exists_bnd_below_above {D : Set ℝ} {x : ℝ} (hbdd : ∃ R : ℝ, ∀ y ∈ D, |y| ≤ R)
    (hx : x ∈ D) (hint : ¬ Work.WilC2.IsBnd D x) :
    (∃ a : ℝ, Work.WilC2.IsBnd D a ∧ a < x) ∧ (∃ b : ℝ, Work.WilC2.IsBnd D b ∧ x < b) := by
  -- `¬ IsBnd D x` with `x ∈ D` gives an open interval around `x` contained in `D`.
  obtain ⟨ε, hε, hsub⟩ := Work.WilC2.exists_Ioo_subset_of_mem hx hint
  obtain ⟨R, hR⟩ := hbdd
  have hbddBelow : BddBelow D := ⟨-R, fun y hy => neg_le_of_abs_le (hR y hy)⟩
  have hbddAbove : BddAbove D := ⟨R, fun y hy => le_of_abs_le (hR y hy)⟩
  have hne : D.Nonempty := ⟨x, hx⟩
  have hxm : x - ε / 2 ∈ D := hsub (by simp only [Set.mem_Ioo]; constructor <;> linarith)
  have hxp : x + ε / 2 ∈ D := hsub (by simp only [Set.mem_Ioo]; constructor <;> linarith)
  -- `sInf D` is a boundary point of `D`: points just below it are outside `D`, and `D`
  -- accumulates at it from above.
  have hlow : Work.WilC2.IsBnd D (sInf D) := by
    refine ⟨?_, ?_⟩
    · rintro ⟨δ, hδ, hsubδ⟩
      have hy : sInf D - δ / 2 ∈ Set.Ioo (sInf D - δ) (sInf D + δ) := by
        simp only [Set.mem_Ioo]; constructor <;> linarith
      have := csInf_le hbddBelow (hsubδ hy)
      linarith
    · rintro ⟨δ, hδ, hsubδ⟩
      obtain ⟨z, hzD, hzlt⟩ :=
        (csInf_lt_iff hbddBelow hne).mp (by linarith : sInf D < sInf D + δ)
      exact (hsubδ ⟨by linarith [csInf_le hbddBelow hzD], hzlt⟩) hzD
  -- `sSup D` is a boundary point of `D`: points just above it are outside `D`, and `D`
  -- accumulates at it from below.
  have hhigh : Work.WilC2.IsBnd D (sSup D) := by
    refine ⟨?_, ?_⟩
    · rintro ⟨δ, hδ, hsubδ⟩
      have hy : sSup D + δ / 2 ∈ Set.Ioo (sSup D - δ) (sSup D + δ) := by
        simp only [Set.mem_Ioo]; constructor <;> linarith
      have := le_csSup hbddAbove (hsubδ hy)
      linarith
    · rintro ⟨δ, hδ, hsubδ⟩
      obtain ⟨z, hzD, hzgt⟩ :=
        (lt_csSup_iff hbddAbove hne).mp (by linarith : sSup D - δ < sSup D)
      exact (hsubδ ⟨hzgt, by linarith [le_csSup hbddAbove hzD]⟩) hzD
  exact ⟨⟨sInf D, hlow, by linarith [csInf_le hbddBelow hxm]⟩,
    ⟨sSup D, hhigh, by linarith [le_csSup hbddAbove hxp]⟩⟩

end Work.WilVP
