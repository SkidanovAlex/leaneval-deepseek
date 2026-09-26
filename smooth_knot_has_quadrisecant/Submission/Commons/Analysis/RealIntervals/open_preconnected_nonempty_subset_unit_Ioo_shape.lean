import Mathlib.Topology.Order.IntermediateValue
import Submission.Commons.Analysis.RealIntervals.open_preconnected_untrapped_unit_end_strip

open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

namespace Commons.Analysis.RealIntervals

/-- **Open preconnected subsets of the unit interval are open sub-intervals**:
a nonempty open preconnected subset `S ⊆ (0,1)` of ℝ is exactly an open
interval `Ioo a b` with `a < b`.

Proof: `IsPreconnected.mem_intervals` lists the ten possible shapes of a
preconnected subset of ℝ (`Icc`, `Ico`, `Ioc`, `Ioo`, `Ici`, `Ioi`, `Iic`,
`Iio`, `univ`, `∅`).  Nonempty + open rules out the closed/half-open shapes
(`isOpen_nonempty_not_Icc/Ico/Ioc/Ici/Iic`), the rays `Ioi a`, `Iio b` are
unbounded and hence escape the bounded set `(0,1)` (move one unit outward
from any element), `univ` contains `2 ∉ (0,1)`, and `∅` contradicts
nonemptiness.  The `Ioo (sInf S) (sSup S)` case is the desired conclusion
(`a < b` by nonemptiness of an open interval). -/
theorem open_preconnected_nonempty_subset_unit_Ioo_shape {S : Set ℝ}
    (hS01 : S ⊆ Set.Ioo (0 : ℝ) 1) (hSopen : IsOpen S)
    (hSne : S.Nonempty) (hSpc : IsPreconnected S) :
    ∃ a b : ℝ, a < b ∧ S = Set.Ioo a b := by
  have hgt0 : ∀ x ∈ S, (0 : ℝ) < x := fun x hx => (Set.mem_Ioo.mp (hS01 hx)).1
  have hlt1 : ∀ x ∈ S, x < (1 : ℝ) := fun x hx => (Set.mem_Ioo.mp (hS01 hx)).2
  rcases hSpc.mem_intervals with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10
  · exact False.elim (isOpen_nonempty_not_Icc hSopen hSne h1)
  · exact False.elim (isOpen_nonempty_not_Ico hSopen hSne h2)
  · exact False.elim (isOpen_nonempty_not_Ioc hSopen hSne h3)
  · refine ⟨sInf S, sSup S, ?_, h4⟩
    exact Set.nonempty_Ioo.mp (by rw [← h4]; exact hSne)
  · exact False.elim (isOpen_nonempty_not_Ici hSopen hSne h5)
  · exfalso
    rcases hSne with ⟨y, hy⟩
    have hyI : y ∈ Set.Ioi (sInf S) := by
      rw [← h6]
      exact hy
    have hyplus : y + 1 ∈ S := by
      rw [h6]
      exact Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp hyI])
    have hypluslt1 : y + 1 < (1 : ℝ) := hlt1 (y + 1) hyplus
    have hygt0 : (0 : ℝ) < y := hgt0 y hy
    linarith
  · exact False.elim (isOpen_nonempty_not_Iic hSopen hSne h7)
  · exfalso
    rcases hSne with ⟨y, hy⟩
    have hyI : y ∈ Set.Iio (sSup S) := by
      rw [← h8]
      exact hy
    have hyminus : y - 1 ∈ S := by
      rw [h8]
      exact Set.mem_Iio.mpr (by linarith [Set.mem_Iio.mp hyI])
    have hyminusgt0 : (0 : ℝ) < y - 1 := hgt0 (y - 1) hyminus
    have hylt1 : y < (1 : ℝ) := hlt1 y hy
    linarith
  · exfalso
    have h2S : (2 : ℝ) ∈ S := by rw [h9]; trivial
    have h2lt1 : (2 : ℝ) < (1 : ℝ) := hlt1 2 h2S
    norm_num at h2lt1
  · exfalso
    rw [h10] at hSne
    exact (Set.not_nonempty_empty (α := ℝ) hSne)

end Commons.Analysis.RealIntervals
