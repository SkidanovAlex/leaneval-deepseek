import Mathlib
import Submission.Work.Drive.EpsFormSphere.Defs
import Submission.Work.Drive.EpsFormSphere.Sideways
import Submission.Work.Drive.EpsFormSphere.span_const_of_sweep_axioms

/-!
# P5: the assembly of the sideways sweep into Pardon's ε-form

This file proves `Work.Drive.EpsFormSphere.thickHalf_of_sideSweepData`: the data of the sideways
sweep (`Work.Drive.EpsSphere.SideSweepData`) convert the *box* statement
`P.ContainsEssentialLoop (boxRegion P s c σ)` into Pardon's ε-form
`Work.Drive.EpsSphere.ThickHalf P s c σ u ε`.

The assembly has three steps.

* **The span is constant along the sweep.**  The abstract argument is
  `Work.Drive.EpsFormSphere.span_const_of_sweep_axioms`: the winding span of the level region is
  constant between critical values (`SideSweepData.regular_span`), changes by at most one across
  each critical value (`SideSweepData.jump`), and at a regular level lies in `{⊥, ⊤}`
  (`SideSweepData.dichotomy`, Pardon's dichotomy `H₁ ∈ {0, 2g}`; here the ambient is `ℚ²`, so
  `2g = 2`).  Since `finrank ⊥ = 0` and `finrank ⊤ = 2`, a jump of at most one across an isolated
  critical value cannot change the span, so the span of the box region equals the span of the end
  region `boxRegion \ slabZ`.

* **The end region is essential.**  The box region contains an essential loop by hypothesis, so its
  span is nonzero; hence so is the span of the end region
  (`WindingSpan_eq_bot_iff`), i.e. `boxRegion \ slabZ` contains an essential loop.

* **Loops of the end region lie in one half.**  A point of the end region misses the slab, so
  `|y (σ 2) - (c (σ 2) + u)| ≥ h > 0`: it is in `upperRegion` or in `lowerRegion`.  As the image of
  a closed curve is connected and the continuous function `y ↦ y (σ 2) - (c (σ 2) + u)` misses
  `0` on it, the whole curve lies in one of the two halves (if it met both, the intermediate value
  theorem would produce a point of the slab).  A loop inside a half-region lies in its
  `ε`-thickening for every `ε > 0`, which is `ThickHalf`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Metric
open Work.Drive.EpsSphere

namespace Work.Drive.EpsFormSphere

noncomputable section

variable {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-- **The winding span of the level `lam` of the sideways sweep** `sideRegion · lam`: the
`H₁`-image of the region of the surface lying in the box behind the wall. -/
def sideSpan (D : SideSweepData P s c σ u) (lam : ℝ) : Submodule ℚ (ℚ × ℚ) :=
  Work.SurgeryInvariance.WindingSpan P (sideRegion P s c σ u D.h D.ℓ lam)

/-- **The regions of the sweep decrease with the level**: a point already behind the wall at the
level `μ` is also behind it at every larger level, so `sideRegion · ν ⊆ sideRegion · μ`. -/
theorem sideRegion_anti (D : SideSweepData P s c σ u) {μ ν : ℝ} (h : μ ≤ ν) :
    sideRegion P s c σ u D.h D.ℓ ν ⊆ sideRegion P s c σ u D.h D.ℓ μ := by
  intro y hy
  obtain ⟨hyc, hyb, hyw⟩ := hy
  exact ⟨hyc, hyb, fun hw => hyw ⟨hw.1, lt_of_lt_of_le hw.2 h⟩⟩

/-- The winding span of the sweep is monotone in the level (contravariantly): `sideSpan · ν` is
contained in `sideSpan · μ` for `μ ≤ ν`. -/
theorem sideSpan_anti (D : SideSweepData P s c σ u) {μ ν : ℝ} (h : μ ≤ ν) :
    sideSpan D ν ≤ sideSpan D μ :=
  Work.SurgeryInvariance.WindingSpan_mono P (sideRegion_anti D h)

/-- **A point of `boxRegion \ slabZ` lies in one of the two half-regions.**  Missing the slab of
half-width `h > 0` means `|y (σ 2) - (c (σ 2) + u)| ≥ h > 0`, so `y (σ 2)` is strictly above or
strictly below the cutting plane. -/
theorem mem_upper_or_lower_of_mem_sdiff_slab (D : SideSweepData P s c σ u) {y : R3}
    (hy : y ∈ Work.BoxShrink.Core.boxRegion P s c σ \ slabZ c σ u D.h) :
    y ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∨
      y ∈ Work.BoxShrink.Core.lowerRegion P s c σ u := by
  obtain ⟨hybox, hyslab⟩ := hy
  obtain ⟨hyc, hyb⟩ := hybox
  have hf : D.h ≤ |y (σ 2) - (c (σ 2) + u)| := not_lt.mp hyslab
  rcases lt_trichotomy (y (σ 2)) (c (σ 2) + u) with hlt | heq | hgt
  · exact Or.inr (Work.BoxShrink.Core.mem_lowerRegion.mpr ⟨hyc, hyb, hlt⟩)
  · exfalso
    rw [heq, sub_self, abs_zero] at hf
    linarith [D.hpos]
  · exact Or.inl (Work.BoxShrink.Core.mem_upperRegion.mpr ⟨hyc, hyb, hgt⟩)

/-- **A closed curve of the end region lies entirely in one of the two halves.**  The image of the
curve is connected and the continuous function `t ↦ γ t (σ 2) - (c (σ 2) + u)` avoids `0` on it
(`|·| ≥ h > 0`), so it cannot take both signs: if it did, the intermediate value theorem would give
a point of the slab. -/
theorem forall_mem_half_of_forall_mem_sdiff_slab (D : SideSweepData P s c σ u)
    {γ : Work.CoreTopology.ClosedCurve P}
    (hmem : ∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.boxRegion P s c σ \ slabZ c σ u D.h) :
    (∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.upperRegion P s c σ u) ∨
      (∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.lowerRegion P s c σ u) := by
  have hcoord : Continuous fun y : R3 => y (σ 2) :=
    PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ 2)
  have hcont : Continuous fun t : ℝ => (γ t) (σ 2) - (c (σ 2) + u) :=
    (hcoord.comp γ.cont).sub continuous_const
  have hne : ∀ t : ℝ, (γ t) (σ 2) - (c (σ 2) + u) ≠ 0 := by
    intro t h0
    have hf : D.h ≤ |(γ t) (σ 2) - (c (σ 2) + u)| := not_lt.mp (hmem t).2
    rw [h0, abs_zero] at hf
    linarith [D.hpos]
  by_cases hup : ∃ t : ℝ, γ t ∈ Work.BoxShrink.Core.upperRegion P s c σ u
  · left
    intro t
    have hpos : 0 < (γ t) (σ 2) - (c (σ 2) + u) := by
      by_contra hcon
      have hlt : (γ t) (σ 2) - (c (σ 2) + u) < 0 :=
        lt_of_le_of_ne (not_lt.mp hcon) (hne t)
      obtain ⟨t₁, ht₁⟩ := hup
      have h₁ : 0 < (γ t₁) (σ 2) - (c (σ 2) + u) := by
        have h := (Work.BoxShrink.Core.mem_upperRegion.mp ht₁).2.2
        linarith
      obtain ⟨τ, hτ⟩ := intermediate_value_univ t t₁ hcont
        (⟨le_of_lt hlt, le_of_lt h₁⟩ : (0 : ℝ) ∈ Set.Icc ((γ t) (σ 2) - (c (σ 2) + u))
          ((γ t₁) (σ 2) - (c (σ 2) + u)))
      exact hne τ hτ
    exact Work.BoxShrink.Core.mem_upperRegion.mpr ⟨γ.mem t, ((hmem t).1).2, by linarith⟩
  · right
    intro t
    have hneg : (γ t) (σ 2) - (c (σ 2) + u) < 0 := by
      by_contra hcon
      have hpos : 0 < (γ t) (σ 2) - (c (σ 2) + u) :=
        lt_of_le_of_ne (not_lt.mp hcon) (Ne.symm (hne t))
      exact hup ⟨t, Work.BoxShrink.Core.mem_upperRegion.mpr ⟨γ.mem t, ((hmem t).1).2, by linarith⟩⟩
    exact Work.BoxShrink.Core.mem_lowerRegion.mpr ⟨γ.mem t, ((hmem t).1).2, by linarith⟩

/-- **The winding span is constant along the sweep**: the box region (the start of the sweep) and
the end region `boxRegion \ slabZ` have the same winding span. -/
theorem span_eq_of_sideSweepData (D : SideSweepData P s c σ u) :
    sideSpan D D.lam0 = sideSpan D D.lam1 := by
  have h := span_const_of_sweep_axioms P
    (fun lam : ℝ => sideRegion P s c σ u D.h D.ℓ lam) D.lam0 D.lam1 D.exc D.hlt D.exc_mem
    (fun μ ν h => sideRegion_anti D h) D.regular_span D.jump D.dichotomy
  simpa only [sideSpan] using h

/-- **The end region of the sweep is essential**, since the box region is. -/
theorem containsEssentialLoop_sdiff_slab (D : SideSweepData P s c σ u)
    (hbox : P.ContainsEssentialLoop (Work.BoxShrink.Core.boxRegion P s c σ)) :
    P.ContainsEssentialLoop
      (Work.BoxShrink.Core.boxRegion P s c σ \ slabZ c σ u D.h) := by
  have h0 : sideSpan D D.lam0 ≠ ⊥ := by
    rw [sideSpan, D.start]
    exact (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mpr hbox
  have h1 : sideSpan D D.lam1 ≠ ⊥ := by
    rw [← span_eq_of_sideSweepData D]; exact h0
  rw [← D.finish]
  exact (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp h1

end

noncomputable section

open LeanEval.KnotTheory.PardonDistortion in
/-- **P5, the assembly**: the data of the sideways sweep give Pardon's ε-form.  The `H₁`-rank of the
region is pinned to `0` or `2g` at the regular levels (Pardon's dichotomy), is constant between
critical values (the isotopy), and changes by at most one across each of the finitely many critical
values, so it is constant along the sweep: the box region is essential, hence so is the end region
`boxRegion \ slabZ`, whose loops lie in the two half-regions (a point of the end region has
`|y (σ 2) - (c (σ 2) + u)| ≥ h > 0`, so it is in `upperRegion` or in `lowerRegion`). -/
theorem thickHalf_of_sideSweepData {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (D : Work.Drive.EpsSphere.SideSweepData P s c σ u)
    (ε : ℝ) (hε : 0 < ε)
    (hbox : P.ContainsEssentialLoop (Work.BoxShrink.Core.boxRegion P s c σ)) :
    Work.Drive.EpsSphere.ThickHalf P s c σ u ε := by
  obtain ⟨γ, hess, hmem⟩ := containsEssentialLoop_sdiff_slab D hbox
  rcases forall_mem_half_of_forall_mem_sdiff_slab D hmem with h | h
  · exact Or.inl ⟨γ, hess, fun t =>
      Metric.mem_thickening_iff.mpr ⟨γ t, h t, by rw [dist_self]; exact hε⟩⟩
  · exact Or.inr ⟨γ, hess, fun t =>
      Metric.mem_thickening_iff.mpr ⟨γ t, h t, by rw [dist_self]; exact hε⟩⟩

end

end Work.Drive.EpsFormSphere
