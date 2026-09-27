import Mathlib
import Submission.Work.EKLRelCross.PeriodDefs
import Submission.Work.EKLRelCross.cc_dense_family
import Submission.Work.EKLRelCross.PeriodFunsDefs
import Submission.Work.EKLRelCross.tent_interval_measure
import Submission.Work.EKLRelCross.measure_eq_map_coeff_map_uij
import Submission.Work.EKLRelCross.finiteOnCompacts_map_coeff

/-!
# A countable separating family of test functions for measures carried by a root subgroup

We prove `Work.EKLRelCross.exists_separating_periodFuns`: for `i ≠ j` there is a sequence
`F : ℕ → C_c(SL₃(ℝ), ℝ)` such that two measures `ν₁, ν₂` on `SL₃(ℝ)` which are finite on
compacts and carried by the one-parameter root subgroup `t ↦ u_ij(t)` are equal as soon as
`∫ F k dν₁ = ∫ F k dν₂` for all `k`.

The functions are obtained by lifting a family of "tent" functions on `ℝ` (which increase
pointwise to the indicator of an interval) along the root subgroup, and the result follows
from the fact that the pushforward of `ν` under the coordinate map `g ↦ g i j` is a
locally finite measure on `ℝ` determined by its values on the intervals `(a,b)`.
-/

namespace Work.EKLRelCross

open MeasureTheory Filter Topology Set
open scoped ENNReal

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

open Work.EKLContract

/-! ## Lifting a compactly supported function on `ℝ` to `SL₃(ℝ)` -/

/-- A choice of lift of a compactly supported continuous function on `ℝ` to `SL₃(ℝ)`
along the root subgroup `t ↦ u_ij(t)`. -/
def liftUij {i j : Fin 3} (hij : i ≠ j) (f : CompactlySupportedContinuousMap ℝ ℝ) :
    CompactlySupportedContinuousMap SL3 ℝ :=
  Classical.choose (exists_lift_uij hij f)

theorem liftUij_spec {i j : Fin 3} (hij : i ≠ j)
    (f : CompactlySupportedContinuousMap ℝ ℝ) :
    ∀ t : ℝ, liftUij hij f (uij hij t) = f t :=
  Classical.choose_spec (exists_lift_uij hij f)

/-! ## A countable enumeration of triples of rationals and naturals -/

theorem exists_surj_rat_triple : ∃ e : ℕ → ℚ × ℚ × ℕ, Function.Surjective e :=
  exists_surjective_nat (ℚ × ℚ × ℕ)

/-- A surjection `ℕ → ℚ × ℚ × ℕ`, used to enumerate all tent functions on all rational
intervals. -/
def idxQuant : ℕ → ℚ × ℚ × ℕ := Classical.choose exists_surj_rat_triple

theorem idxQuant_surj : Function.Surjective idxQuant :=
  Classical.choose_spec exists_surj_rat_triple

/-- The separating family: the `k`-th function is the lift of the tent function on the rational
interval encoded by `idxQuant k`, at the steepness also encoded by `idxQuant k`. -/
def sepFam {i j : Fin 3} (hij : i ≠ j) : ℕ → CompactlySupportedContinuousMap SL3 ℝ :=
  fun k => liftUij hij (tent ((idxQuant k).1 : ℝ) ((idxQuant k).2.1 : ℝ) (idxQuant k).2.2)

theorem exists_separating_periodFuns {i j : Fin 3} (hij : i ≠ j) :
    ∃ F : ℕ → CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ,
      ∀ ν₁ ν₂ : MeasureTheory.Measure Work.EKLContract.SL3,
        MeasureTheory.IsFiniteMeasureOnCompacts ν₁ →
        MeasureTheory.IsFiniteMeasureOnCompacts ν₂ →
        ν₁ (Set.range (fun t : ℝ => Work.EKLContract.uij hij t))ᶜ = 0 →
        ν₂ (Set.range (fun t : ℝ => Work.EKLContract.uij hij t))ᶜ = 0 →
        (∀ k, ∫ g, F k g ∂ν₁ = ∫ g, F k g ∂ν₂) → ν₁ = ν₂ := by
  refine ⟨sepFam hij, ?_⟩
  intro ν₁ ν₂ hfin₁ hfin₂ hR₁ hR₂ hint
  haveI := hfin₁
  haveI := hfin₂
  set c : SL3 → ℝ := fun g => (g : Matrix (Fin 3) (Fin 3) ℝ) i j with hc
  haveI hfl₁ : IsFiniteMeasureOnCompacts (ν₁.map c) := finiteOnCompacts_map_coeff hij ν₁ hR₁
  haveI hfl₂ : IsFiniteMeasureOnCompacts (ν₂.map c) := finiteOnCompacts_map_coeff hij ν₂ hR₂
  haveI hlf₁ : IsLocallyFiniteMeasure (ν₁.map c) := inferInstance
  have hν₁ := measure_eq_map_coeff_map_uij hij ν₁ hR₁
  have hν₂ := measure_eq_map_coeff_map_uij hij ν₂ hR₂
  have hIoo : ∀ a b : ℚ,
      (ν₁.map c) (Ioo (a:ℝ) (b:ℝ)) = (ν₂.map c) (Ioo (a:ℝ) (b:ℝ)) := by
    intro a b
    rcases lt_or_ge a b with hab | hba
    · have hab' : (a:ℝ) < (b:ℝ) := by exact_mod_cast hab
      have hfun : ∀ n : ℕ,
          ∫ t, tentFun (a:ℝ) (b:ℝ) n t ∂(ν₁.map c)
            = ∫ t, tentFun (a:ℝ) (b:ℝ) n t ∂(ν₂.map c) := by
        intro n
        obtain ⟨k, hk⟩ := idxQuant_surj (a, b, n)
        have hF : sepFam hij k = liftUij hij (tent (a:ℝ) (b:ℝ) n) := by
          simp [sepFam, hk]
        have hkey : ∀ ν : Measure SL3, ν (Set.range (fun t : ℝ => uij hij t))ᶜ = 0 →
            ∫ g, sepFam hij k g ∂ν
              = ∫ t, tentFun (a:ℝ) (b:ℝ) n t ∂(ν.map c) := by
          intro ν hR
          conv_lhs => rw [measure_eq_map_coeff_map_uij hij ν hR]
          rw [integral_map]
          · apply integral_congr_ae
            filter_upwards with t
            rw [hF, liftUij_spec hij (tent (a:ℝ) (b:ℝ) n) t, tent_apply]
          · exact (Work.EKLC7.continuous_uij hij).measurable.aemeasurable
          · exact (ContinuousMap.continuous (sepFam hij k).toContinuousMap).aestronglyMeasurable
        rw [← hkey ν₁ hR₁, ← hkey ν₂ hR₂]
        exact hint k
      rw [tent_interval_measure hab' (ν₁.map c), tent_interval_measure hab' (ν₂.map c)]
      exact iSup_congr (fun n => by rw [hfun n])
    · have hba' : (b:ℝ) ≤ (a:ℝ) := by exact_mod_cast hba
      rw [Set.Ioo_eq_empty_of_le hba']
      simp
  have hμ : ν₁.map c = ν₂.map c := Real.measure_ext_Ioo_rat hIoo
  rw [hν₁, hν₂, hμ]

end

end Work.EKLRelCross
