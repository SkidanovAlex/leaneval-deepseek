import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLContract.Interfaces

/-!
# `Work.EKLC6Core.dirac_of_mass`

If a measure `m` on `SL₃(ℝ)` is carried on a subgroup `U` (`m Uᶜ = 0`), gives `U` full mass
(`m U = 1`) and gives the identity full mass (`m {1} = 1`), then `m` is the Dirac mass at `1`.

The two mass hypotheses on `U` only serve to identify the total mass of `m`: subadditivity gives
`m univ ≤ m U + m Uᶜ = 1` while monotonicity gives `m univ ≥ m U = 1`.  Since `{1}` is Borel
(`SL₃(ℝ)` carries the Borel σ-algebra, and singletons are closed), `m {1}ᶜ = m univ - m {1} = 0`,
and then every measurable set has the same `m`-mass as its intersection with `{1}`.
-/

open MeasureTheory
open Work.EKLContract

namespace Work.EKLC6Core

theorem dirac_of_mass {U : Subgroup Work.EKLContract.SL3} {m : MeasureTheory.Measure Work.EKLContract.SL3}
    (hcarried : m (U : Set Work.EKLContract.SL3)ᶜ = 0)
    (hmass : m (U : Set Work.EKLContract.SL3) = 1)
    (hone : m ({1} : Set Work.EKLContract.SL3) = 1) :
    m = MeasureTheory.Measure.dirac 1 := by
  have hsing : MeasurableSet ({1} : Set SL3) := measurableSet_singleton 1
  -- the two mass hypotheses force the total mass of `m` to be `1`
  have huniv : m Set.univ = 1 := by
    refine le_antisymm ?_ ?_
    · calc m Set.univ = m ((U : Set SL3) ∪ (U : Set SL3)ᶜ) := by rw [Set.union_compl_self]
        _ ≤ m (U : Set SL3) + m (U : Set SL3)ᶜ := measure_union_le _ _
        _ = 1 := by rw [hmass, hcarried, add_zero]
    · rw [← hmass]; exact measure_mono (Set.subset_univ _)
  -- hence `{1}` already carries all the mass
  have hcompl : m ({1} : Set SL3)ᶜ = 0 := by
    rw [measure_compl hsing (by rw [hone]; exact ENNReal.one_ne_top), huniv, hone]
    simp
  -- every measurable set meets `{1}ᶜ` in a null set
  have hdecomp : ∀ A : Set SL3, A = (A \ {1}) ∪ (A ∩ {1}) := by
    intro A
    ext x; simp only [Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_singleton_iff]
    tauto
  have hmain : ∀ A : Set SL3, MeasurableSet A → m A = m (A ∩ {1}) := by
    intro A hA
    have h1 : m A = m ((A \ {1}) ∪ (A ∩ {1})) := congrArg m (hdecomp A)
    have hdiff : m (A \ {1}) = 0 := measure_mono_null (fun x hx => hx.2) hcompl
    rw [h1, measure_union Set.disjoint_sdiff_inter (hA.inter hsing), hdiff, zero_add]
  refine Measure.ext fun A hA => ?_
  calc m A = m (A ∩ {1}) := hmain A hA
    _ = (Measure.dirac 1) A := by
        by_cases h1A : (1 : SL3) ∈ A
        · rw [Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr h1A), hone,
            Measure.dirac_apply_of_mem h1A]
        · have hA1 : A ∩ {1} = ∅ := by
            rw [Set.eq_empty_iff_forall_notMem]
            rintro x hx
            rw [Set.mem_inter_iff, Set.mem_singleton_iff] at hx
            exact h1A (hx.2 ▸ hx.1)
          rw [hA1, Measure.dirac_apply' 1 hA]
          simp [Set.indicator_of_notMem h1A]

end Work.EKLC6Core
