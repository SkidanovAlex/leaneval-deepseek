import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.corrMarg.measurable_and_bound_boxMean
import Submission.Work.BoseFixB1S.oneBodyB1.margAuxAemeasB1
import Submission.Work.BoseFixB1S.oneBodyB1.margAuxBoundSelfB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.MargPiece.integrable_bsW_chiB_sub_holds`

The `u`-marginal integrability of the sliding cut kinetic word with a mean shift:

    `u ↦ bsW (fsKinCoeff c) (fun z ↦ chiB ℓ d u z * (g z − ρ u))`   is `Integrable`

for `0 < ℓ`, `0 < d`, a smooth profile `g` and a measurable, uniformly bounded shift
`ρ : ℝ³ → ℝ`.

The mechanism is exactly the one recorded in
`Submission/Work/BoseFixB1S/corrMarg/NOTE.md`:

* `χ_{B(u)}(z) = chiB ℓ d u z = χ(z/ℓ)·χ(z/(ℓd) − u)` can only be non-zero when the
  sliding centre `u` lies in the *fixed* cube `acube ((1+d)/d)`
  (`Work.BoseFixB1S.chiB_ne_zero_mem_acube_u`, `chiB_mul_eq_zero_of_not_mem_acube_u`) —
  a compact set of finite Lebesgue measure.  Off it the state is identically zero, hence
  so is `bsW` (the `p`-integrand vanishes pointwise);
* on that cube the family of states is smooth, compactly supported in the fixed box
  `acube ℓ`, and its sup-norm and coordinate-derivative bounds are *uniform in* `u`
  (`|χ_B| ≤ chiSup²`, `|g|` bounded on `acube ℓ`, Leibniz + the uniform window-gradient
  bound `Σ_k (∂_k χ_s)² ≤ K/s²`), so `bsW` is uniformly bounded there — this is
  `Work.BoseFixB1S.oneBodyB1.margAuxBoundSelfB1` (built on
  `Work.BSKinetic.bsW_fsKinCoeff_le`);
* a.e. strong measurability of `u ↦ bsW (fsKinCoeff c) (χ_{B(u)}·W u)` for a *jointly
  measurable* kernel `W` is `Work.BoseFixB1S.oneBodyB1.margAuxAemeasB1` (the parametric
  Bochner integral device `StronglyMeasurable.integral_prod_right'`, applied twice).

The assembly is the lemma below: a function that is a.e. strongly measurable, vanishes off
a measurable set of finite measure and is bounded there is integrable
(`MeasureTheory.Integrable.mono'` against the indicator of the cube).
-/

noncomputable section

open MeasureTheory
open scoped Topology Real

namespace Work.BoseFixB1B.MargPiece

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The cut kinetic word of the zero state vanishes. -/
lemma bsW_zero_state (F : ℝ → ℝ) :
    Work.BSKinetic.Decomp.bsW F (0 : E3 → ℝ) = 0 := by
  rw [Work.BSKinetic.Decomp.bsW]
  simp [Work.BSKinetic.Decomp.bsPsi, Submission.BoseGases.kinFT]

/-- A function that is a.e. strongly measurable, vanishes off a measurable set `K` of finite
measure and is bounded there is integrable. -/
lemma integrable_of_support_bound {K : Set E3} {B : ℝ} {f : E3 → ℝ}
    (hK : MeasurableSet K) (hKfin : (MeasureTheory.volume : MeasureTheory.Measure E3) K ≠ ⊤)
    (hf : AEMeasurable f MeasureTheory.volume) (hB : 0 ≤ B)
    (hzero : ∀ u, u ∉ K → f u = 0) (hb : ∀ u, |f u| ≤ B) :
    MeasureTheory.Integrable f MeasureTheory.volume := by
  have hg : MeasureTheory.Integrable (K.indicator (fun _ : E3 => B)) MeasureTheory.volume := by
    rw [MeasureTheory.integrable_indicator_iff hK]
    exact MeasureTheory.integrableOn_const hKfin (by simp)
  refine MeasureTheory.Integrable.mono' hg hf.aestronglyMeasurable ?_
  filter_upwards with u
  by_cases hu : u ∈ K
  · rw [Set.indicator_of_mem hu, Real.norm_eq_abs]
    exact hb u
  · rw [Set.indicator_of_notMem hu, hzero u hu, norm_zero]

theorem integrable_bsW_chiB_sub_holds {ℓ d c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hg : ContDiff ℝ (⊤ : ENat) g)
    {ρ : EuclideanSpace ℝ (Fin 3) → ℝ} (hρ : Measurable ρ)
    (hρbd : ∃ C : ℝ, ∀ u : EuclideanSpace ℝ (Fin 3), |ρ u| ≤ C) :
    MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
        (fun z : EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.chiB ℓ d u z * (g z - ρ u))) := by
  -- ## The `u`-support: the fixed cube of centres
  have hratio : 0 < (1 + d) / d := div_pos (by linarith) hd
  have hKmeas : MeasurableSet (Submission.BoseGases.acube ((1 + d) / d)) :=
    Submission.BoseGases.acube_measurable _
  have hKfin : (MeasureTheory.volume : MeasureTheory.Measure E3)
      (Submission.BoseGases.acube ((1 + d) / d)) ≠ ⊤ :=
    ne_of_lt (Submission.BoseGases.acube_lt_top ((1 + d) / d) hratio.le)
  -- ## a.e. strong measurability (parametric-integral device, jointly measurable kernel)
  have hA : AEMeasurable
      (fun u : E3 => Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
        (fun z : E3 => Submission.BoseGases.chiB ℓ d u z * (g z - ρ u)))
      MeasureTheory.volume := by
    refine Work.BoseFixB1S.oneBodyB1.margAuxAemeasB1 (ℓ := ℓ) (d := d) (c := c)
      (W := fun u z => g z - ρ u) ?_
    have h : Function.uncurry (fun u z : E3 => g z - ρ u)
        = fun q : E3 × E3 => g q.2 - ρ q.1 := by
      funext q
      rfl
    rw [h]
    exact (hg.continuous.measurable.comp measurable_snd).sub (hρ.comp measurable_fst)
  -- ## the uniform bound on the cube
  obtain ⟨C, hρC⟩ := hρbd
  have hC0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  have hρC' : ∀ u : E3, |ρ u| ≤ max C 0 := fun u => le_trans (hρC u) (le_max_left _ _)
  obtain ⟨B, hB0, hBbd⟩ :=
    Work.BoseFixB1S.oneBodyB1.margAuxBoundSelfB1 (ℓ := ℓ) (d := d) (c := c) (C := max C 0)
      hℓ hd hC0 (w := g) hg (c₀ := ρ) hρC'
  -- ## vanishing off the cube, then integrability
  refine integrable_of_support_bound hKmeas hKfin hA hB0 ?_ hBbd
  intro u hu
  have h0 : (fun z : E3 => Submission.BoseGases.chiB ℓ d u z * (g z - ρ u)) = 0 :=
    Work.BoseFixB1S.chiB_mul_eq_zero_of_not_mem_acube_u hℓ hd hu g (ρ u)
  rw [h0]
  exact bsW_zero_state _

end Work.BoseFixB1B.MargPiece
