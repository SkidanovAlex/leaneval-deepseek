import Mathlib
import Submission.Work.EKLComp.C8Defs
import Submission.Work.EKLCompSetup.limit_pair

/-!
# The complement indicator integral of a leaf mass

`Work.EKLComp.leafMass ν X₁ R x = ∫⁻ g in ballU h01 R, 1_{X₁} (g • x) ∂(ν x)` is the `ν x`-mass of
the part of the plaque `ballU h01 R` through `x` that the action carries into `X₁`
(`Work.EKLCompSetup.leafMass_eq_measure`).  Its complement inside the plaque therefore has mass
`ν x (ballU h01 R).toReal - (leafMass ν X₁ R x).toReal`, and that is the Bochner integral of the
indicator of the complement:

`∫ g in ballU h01 R, (1 - 1_{X₁} (g • x)) ∂(ν x) = (ν x (ballU h01 R)).toReal
    - (leafMass ν X₁ R x).toReal`.

The point is exactly that `g ↦ 1 - 1_{X₁}(g • x)` is the indicator of
`(ballU h01 R ∩ {g | g • x ∈ X₁})ᶜ`, that the Bochner integral of the indicator of a measurable
set is `(μ s).toReal` (`MeasureTheory.integral_indicator_one` in restricted form), and that
`Measure.real` is additive under `s \ t ⊆ s` (`MeasureTheory.measureReal_sdiff`).
-/

open MeasureTheory
open scoped ENNReal

set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLCompSetup

theorem setIntegral_one_sub_indicator_eq
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    (hν : ∀ x, MeasureTheory.IsFiniteMeasureOnCompacts (ν x))
    {X₁ : Set Work.EKLContract.X3} (hX₁ : MeasurableSet X₁) (R : ℝ) (x : Work.EKLContract.X3) :
    ∫ g in Work.EKLContract.ballU Work.EKLComp.h01 R,
        (1 - X₁.indicator (fun _ => (1 : ℝ)) (g • x)) ∂(ν x)
      = (ν x (Work.EKLContract.ballU Work.EKLComp.h01 R)).toReal
        - (Work.EKLComp.leafMass ν X₁ R x).toReal := by
  classical
  set S : Set Work.EKLContract.SL3 := Work.EKLContract.ballU Work.EKLComp.h01 R with hSdef
  set A : Set Work.EKLContract.SL3 := {g | g • x ∈ X₁} with hAdef
  have hS : MeasurableSet S := by
    rw [hSdef]
    exact (Work.EKLComp.isCompact_ballU R).isClosed.measurableSet
  have hcont : Continuous fun g : Work.EKLContract.SL3 => g • x :=
    continuous_id.smul continuous_const
  have hA : MeasurableSet A := by
    rw [hAdef]
    exact hX₁.preimage hcont.measurable
  have hab : ∀ g : Work.EKLContract.SL3, g ∈ A ↔ g • x ∈ X₁ := fun g => by simp [hAdef]
  have hfin : ν x S ≠ ∞ := by
    haveI := hν x
    rw [hSdef]
    exact (IsFiniteMeasureOnCompacts.lt_top_of_isCompact (Work.EKLComp.isCompact_ballU R)).ne
  -- the leaf mass is the `ν x`-mass of the part of the plaque landing in `X₁`
  have hleaf : Work.EKLComp.leafMass ν X₁ R x = ν x (S ∩ A) :=
    leafMass_eq_measure (S := X₁) hX₁ hcont R
  rw [hleaf]
  -- the integrand is the indicator of the complement
  have hfun : ∀ g : Work.EKLContract.SL3,
      (1 - X₁.indicator (fun _ => (1 : ℝ)) (g • x)) = Aᶜ.indicator (fun _ => (1 : ℝ)) g := by
    intro g
    by_cases hg : g • x ∈ X₁
    · have h1 : g ∈ A := (hab g).mpr hg
      rw [Set.indicator_of_mem hg, Set.indicator_of_notMem (by simpa using h1)]
      ring
    · have h1 : g ∉ A := fun h => hg ((hab g).mp h)
      rw [Set.indicator_of_notMem hg, Set.indicator_of_mem (by simpa using h1)]
      ring
  rw [MeasureTheory.setIntegral_congr_fun hS (fun g _ => hfun g)]
  rw [MeasureTheory.setIntegral_indicator (s := S) (t := Aᶜ) hA.compl]
  rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
  -- `S ∩ Aᶜ = S \ (S ∩ A)`, and `Measure.real` is subtractive there
  have hset : S ∩ Aᶜ = S \ (S ∩ A) := by
    rw [Set.sdiff_eq]
    ext g
    simp only [Set.mem_inter_iff, Set.mem_compl_iff]
    tauto
  rw [hset, MeasureTheory.measureReal_sdiff Set.inter_subset_left (hS.inter hA) hfin]
  simp only [MeasureTheory.measureReal_def]

end Work.EKLCompSetup
