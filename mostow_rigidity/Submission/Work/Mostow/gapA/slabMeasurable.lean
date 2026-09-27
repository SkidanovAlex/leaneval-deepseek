import Mathlib
import Submission.Work.Mostow.gapA.slabDefs

/-!
# Measurability of a Fermi slab

`Work.Mostow.gapA.sig a b u = (β_b u − β_a u)/2` is built from the two Busemann functions,
and `Work.Mostow.distGeod a b u = arcosh (√(2 e^{β_a u + β_b u}/(1 − ⟪a,b⟫)))` from the same
data.  Since `u ↦ busemann ξ u = log (tpart u − ⟪u,ξ⟫)` is continuous for every `ξ ∈ E 3`
(`tpart u - ⟪u,ξ⟫` is continuous and `Real.log` is measurable), both `sig a b` and `distGeod a b`
are measurable, so the slab `{s ≤ sig a b u < s + L, distGeod a b u ≤ R}` is a Borel set.
The boundary-point hypotheses `ha`, `hb` are not needed for this.
-/

namespace Work.Mostow.gapA

open Submission.Mostow MeasureTheory

/-- The time coordinate `tpart` is continuous. -/
lemma gapA_cont_tpart : Continuous (Submission.Mostow.tpart : Submission.Mostow.E 3 → ℝ) := by
  unfold Submission.Mostow.tpart
  fun_prop

/-- For fixed `ξ`, the function `u ↦ busemann ξ u` is continuous (a composition of `tpart`,
the continuous linear form `⟪·,ξ⟫` and `Real.log`), hence measurable. -/
lemma gapA_measurable_busemann (ξ : Submission.Mostow.E 3) :
    Measurable (fun u : Submission.Mostow.E 3 => Submission.Mostow.busemann ξ u) := by
  have hcont : Continuous
      (fun u : Submission.Mostow.E 3 => Submission.Mostow.tpart u - inner ℝ u ξ) := by
    have h1 := gapA_cont_tpart
    fun_prop
  exact Real.measurable_log.comp hcont.measurable

/-- `Real.arcosh` is measurable, being `Real.log ∘ (x ↦ x + √(x² − 1))`. -/
lemma gapA_measurable_arcosh : Measurable (Real.arcosh : ℝ → ℝ) := by
  unfold Real.arcosh
  have hcont : Continuous (fun x : ℝ => x + Real.sqrt (x ^ 2 - 1)) := by fun_prop
  exact Real.measurable_log.comp hcont.measurable

/-- The coordinate `sig a b` is measurable. -/
lemma gapA_measurable_sig (a b : Submission.Mostow.E 3) :
    Measurable (fun u : Submission.Mostow.E 3 => sig a b u) := by
  unfold sig
  exact ((gapA_measurable_busemann b).sub (gapA_measurable_busemann a)).div_const 2

/-- The distance-to-the-geodesic function `distGeod a b` is measurable. -/
lemma gapA_measurable_distGeod (a b : Submission.Mostow.E 3) :
    Measurable (fun u : Submission.Mostow.E 3 => Work.Mostow.distGeod a b u) := by
  unfold Work.Mostow.distGeod
  have h : Measurable (fun u : Submission.Mostow.E 3 =>
      Real.sqrt (2 * Real.exp (Submission.Mostow.busemann a u + Submission.Mostow.busemann b u) /
        (1 - inner ℝ a b))) := by
    have h1 := gapA_measurable_busemann a
    have h2 := gapA_measurable_busemann b
    fun_prop
  exact gapA_measurable_arcosh.comp h

theorem slabMeasurable (a b : Submission.Mostow.E 3) (ha : a ∈ Submission.Mostow.Sph 3)
    (hb : b ∈ Submission.Mostow.Sph 3) (s L R : ℝ) :
    MeasurableSet {u : Submission.Mostow.E 3 |
      Work.Mostow.gapA.sig a b u ∈ Set.Ico s (s + L) ∧ Work.Mostow.distGeod a b u ≤ R} := by
  have h1 : MeasurableSet {u : Submission.Mostow.E 3 | sig a b u ∈ Set.Ico s (s + L)} :=
    measurableSet_Ico.preimage (gapA_measurable_sig a b)
  have h2 : MeasurableSet {u : Submission.Mostow.E 3 | Work.Mostow.distGeod a b u ≤ R} :=
    measurableSet_Iic.preimage (gapA_measurable_distGeod a b)
  exact h1.inter h2

end Work.Mostow.gapA
