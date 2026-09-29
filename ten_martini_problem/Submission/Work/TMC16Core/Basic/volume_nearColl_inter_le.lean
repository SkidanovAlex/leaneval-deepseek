import Mathlib
import Submission.Work.TMC16Core.Defs

open MeasureTheory Set

namespace Work.TMC16Core.Basic

/-!
# Measure of the `ε`-neighbourhood of a "collision" window

`fracDist (2 * θ + c) < ε` means that `2 * θ + c` lies within `ε` of an integer, i.e.
`θ` lies in one of the open intervals
`I_k = ((k - ε - c) / 2, (k + ε - c) / 2)`, `k ∈ ℤ`, which have length `ε` and are centred
at the numbers `(k - c) / 2`, i.e. on a lattice of mesh `1/2`.

Any half-open window `[a, a + 1/2)` of length `1/2` can therefore meet at most two of these
intervals, so the measure of the part of the set inside the window is at most `2 * ε ≤ 3 * ε`.

The proof below makes this quantitative: the two possibly relevant integers are `⌊u⌋ + 1` and
`⌊u⌋ + 2` where `u = 2 * a + c - ε`.
-/

theorem volume_nearColl_inter_le (c ε a : ℝ) (hε0 : 0 ≤ ε) (hεh : ε ≤ 1 / 2) :
    MeasureTheory.volume
        ({θ : ℝ | Work.TMC16Core.fracDist (2 * θ + c) < ε} ∩ Set.Ico a (a + 1 / 2))
      ≤ ENNReal.ofReal (3 * ε) := by
  -- The set of relevant lattice points `k`: those `k` whose interval `I_k` can meet the window.
  set u : ℝ := 2 * a + c - ε with hu
  -- Step 1 (arithmetic core): if `θ` is in the window and `|2 θ + c - m| < ε` for an integer
  -- `m`, then `m` is one of the only two possible lattice points `⌊u⌋ + 1`, `⌊u⌋ + 2`.
  have hkey : ∀ θ ∈ Set.Ico a (a + 1 / 2), ∀ m : ℤ, |(2 * θ + c) - (m : ℝ)| < ε →
      m = ⌊u⌋ + 1 ∨ m = ⌊u⌋ + 2 := by
    intro θ hθ m hm
    obtain ⟨ha, hb⟩ := hθ
    have h1 : u < (m : ℝ) := by
      have := (abs_lt.mp hm).2
      rw [hu]; linarith
    have h2 : (m : ℝ) < u + 2 := by
      have := (abs_lt.mp hm).1
      rw [hu]; linarith
    have hfl : ⌊u⌋ < m := Int.floor_lt.mpr h1
    have hfu : m < ⌊u⌋ + 3 := by
      have h3 : (m : ℝ) < ((⌊u⌋ + 3 : ℤ) : ℝ) := by
        have := Int.lt_floor_add_one u
        push_cast
        linarith
      exact_mod_cast h3
    omega
  -- Step 2: the whole window part of the set is contained in the union of two intervals of
  -- length `ε`.
  have hsub : {θ : ℝ | Work.TMC16Core.fracDist (2 * θ + c) < ε} ∩ Set.Ico a (a + 1 / 2) ⊆
      Set.Ioo ((((⌊u⌋ : ℝ) + 1) - ε - c) / 2) ((((⌊u⌋ : ℝ) + 1) + ε - c) / 2)
      ∪ Set.Ioo ((((⌊u⌋ : ℝ) + 2) - ε - c) / 2) ((((⌊u⌋ : ℝ) + 2) + ε - c) / 2) := by
    rintro θ ⟨hθS, hθw⟩
    obtain ⟨m, hm⟩ : ∃ m : ℤ, |(2 * θ + c) - (m : ℝ)| < ε :=
      ⟨round (2 * θ + c), by simpa [Work.TMC16Core.fracDist] using hθS⟩
    have hmemb : θ ∈ Set.Ioo (((m : ℝ) - ε - c) / 2) (((m : ℝ) + ε - c) / 2) := by
      rw [Set.mem_Ioo]
      obtain ⟨h1, h2⟩ := abs_lt.mp hm
      constructor <;> linarith
    rcases hkey θ hθw m hm with h | h
    · left
      have hm' : (m : ℝ) = (⌊u⌋ : ℝ) + 1 := by rw [h]; push_cast; ring
      rwa [hm'] at hmemb
    · right
      have hm' : (m : ℝ) = (⌊u⌋ : ℝ) + 2 := by rw [h]; push_cast; ring
      rwa [hm'] at hmemb
  have hvol : ∀ p : ℝ,
      volume (Set.Ioo ((p - ε - c) / 2) ((p + ε - c) / 2)) = ENNReal.ofReal ε := by
    intro p
    rw [Real.volume_Ioo]
    congr 1
    ring_nf
  calc volume ({θ : ℝ | Work.TMC16Core.fracDist (2 * θ + c) < ε} ∩ Set.Ico a (a + 1 / 2))
      ≤ volume (Set.Ioo ((((⌊u⌋ : ℝ) + 1) - ε - c) / 2) ((((⌊u⌋ : ℝ) + 1) + ε - c) / 2)
          ∪ Set.Ioo ((((⌊u⌋ : ℝ) + 2) - ε - c) / 2) ((((⌊u⌋ : ℝ) + 2) + ε - c) / 2)) :=
        measure_mono hsub
    _ ≤ volume (Set.Ioo ((((⌊u⌋ : ℝ) + 1) - ε - c) / 2) ((((⌊u⌋ : ℝ) + 1) + ε - c) / 2))
        + volume (Set.Ioo ((((⌊u⌋ : ℝ) + 2) - ε - c) / 2) ((((⌊u⌋ : ℝ) + 2) + ε - c) / 2)) :=
          measure_union_le _ _
    _ = ENNReal.ofReal ε + ENNReal.ofReal ε := by
          rw [hvol ((⌊u⌋ : ℝ) + 1), hvol ((⌊u⌋ : ℝ) + 2)]
    _ = ENNReal.ofReal (2 * ε) := by
          rw [← ENNReal.ofReal_add hε0 hε0]; ring_nf
    _ ≤ ENNReal.ofReal (3 * ε) := ENNReal.ofReal_le_ofReal (by linarith)

end Work.TMC16Core.Basic
