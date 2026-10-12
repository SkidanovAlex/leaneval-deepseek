import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.oneBodyB1.margAuxAemeasB1
import Submission.Work.BoseFixB1S.oneBodyB1.margAuxBoundSelfB1
import Submission.Work.BoseFixB1S.oneBodyB1.margAuxBoxMeanB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.oneBodyB1.marginalAuxB1`

`MarginalB1` (the `u`-marginal integrability of the two windowed cut words of the mean-mismatch
step of the sliding spectral crux): for `0 < ℓ`, `0 < d`, `c : ℝ` and smooth `w`, both

    u ↦ bsW (fsKinCoeff c) (χ_{B(u)}·w)          and
    u ↦ bsW (fsKinCoeff c) (χ_{B(u)}·(w − ⨍_{B(u)}w))

are integrable on `ℝ³`.

The mechanism is the *fixed* `u`-support of the sliding window: `χ_{B(u)}(x) = χ(x/ℓ)·χ(x/(ℓd) − u)`
can only be non-zero when `u ∈ acube ((1+d)/d)` (`Work.BoseFixB1S.chiB_ne_zero_mem_acube_u`), a
*compact* set of finite volume.  On that set the two states are smooth, compactly supported in the
fixed box `acube ℓ`, and their sup-norm and coordinate-derivative norm are bounded *uniformly in*
`u` — the sup-norm bound uses `|χ_{B(u)}| ≤ chiSup²` and `|c_u| = |⨍_{B(u)}w| ≤ sup_{acube ℓ}|w|`,
the derivative bound the Leibniz rule together with the uniform window-gradient estimate
`Σ_k (∂_k χ_s)² ≤ K/s²`.  So both families are bounded by a constant on a compact set and vanish
outside it, and integrability follows from a.e. strong measurability plus that bound.

Three independent analytic inputs are proved in sibling files:

* `margAuxBoxMeanB1` — `u ↦ (1/boxMass ℓ d u)·∫_{B(u)}w` is measurable and bounded;
* `margAuxBoundB1` — the uniform `bsW`-bound for the state `χ_{B(u)}·(w − c₀ u)` with `|c₀| ≤ C`;
* `margAuxAemeasB1` — a.e. strong measurability of `u ↦ bsW F (χ_{B(u)}·W u)`
  (the parametric-integral argument: `bsW` is a `p`-integral of `F‖p‖·‖kinFT …‖²`, and
  `kinFT` is itself a `z`-integral of a jointly measurable integrand).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1S.oneBodyB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## Elementary helpers -/

private lemma bsPsi_zeroB1 (p : E3) :
    Work.BSKinetic.Decomp.bsPsi (0 : E3 → ℝ) p = 0 := by
  simp [Work.BSKinetic.Decomp.bsPsi, Submission.BoseGases.kinFT]

/-- The cutoff kinetic form of the zero state vanishes. -/
private lemma bsW_zeroB1 (F : ℝ → ℝ) :
    Work.BSKinetic.Decomp.bsW F (0 : E3 → ℝ) = 0 := by
  rw [Work.BSKinetic.Decomp.bsW]
  simp [bsPsi_zeroB1]

/-- A function which is a.e. strongly measurable, vanishes off a measurable set `K` of finite
measure and is bounded by `B` there, is integrable. -/
private lemma integrable_of_boundB1 {K : Set E3} {B : ℝ} {f : E3 → ℝ}
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

/-! ## The marginal -/

theorem marginalAuxB1 : Work.BoseFixB1S.oneBodyB1.MarginalB1 := by
  intro ℓ d hℓ hd c w hw
  -- the sliding box mean is measurable and bounded
  obtain ⟨hmeanMeas, C, hC0, hmeanBd⟩ := margAuxBoxMeanB1 (ℓ := ℓ) (d := d) hℓ hd hw.continuous
  -- the two uniform `bsW`-bounds
  obtain ⟨B₀, hB₀, hbd₀⟩ :=
    margAuxBoundSelfB1 (ℓ := ℓ) (d := d) (c := c) (C := 0) hℓ hd le_rfl (w := w) hw
      (c₀ := fun _ : E3 => 0) (fun _ => by simp)
  obtain ⟨B₁, hB₁, hbd₁⟩ :=
    margAuxBoundSelfB1 (ℓ := ℓ) (d := d) (c := c) (C := C) hℓ hd hC0 (w := w) hw
      (c₀ := fun u : E3 => (1 / Work.SmallBoxSliding.boxMass ℓ d u) *
        ∫ z in Submission.BoseGases.dlBox ℓ d u, w z) hmeanBd
  -- the two a.e. strong measurabilities
  have hA₀ : AEMeasurable
      (fun u : E3 =>
        Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
          (fun z : E3 => Submission.BoseGases.chiB ℓ d u z * w z)) MeasureTheory.volume :=
    margAuxAemeasB1 (W := fun _ z => w z) (hw.continuous.measurable.comp measurable_snd)
  have hA₁ : AEMeasurable
      (fun u : E3 =>
        Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
          (fun z : E3 => Submission.BoseGases.chiB ℓ d u z *
            (w z - (1 / Work.SmallBoxSliding.boxMass ℓ d u) *
              ∫ z' in Submission.BoseGases.dlBox ℓ d u, w z'))) MeasureTheory.volume :=
    margAuxAemeasB1 (W := fun u z => w z - (1 / Work.SmallBoxSliding.boxMass ℓ d u) *
      ∫ z' in Submission.BoseGases.dlBox ℓ d u, w z')
      ((hw.continuous.measurable.comp measurable_snd).sub (hmeanMeas.comp measurable_fst))
  -- the geometry of the `u`-support: everything is supported in the fixed compact cube
  have hratio : 0 < (1 + d) / d := div_pos (by linarith) hd
  have hKmeas : MeasurableSet (Submission.BoseGases.acube ((1 + d) / d)) :=
    Submission.BoseGases.acube_measurable _
  have hKfin : (MeasureTheory.volume : MeasureTheory.Measure E3)
      (Submission.BoseGases.acube ((1 + d) / d)) ≠ ⊤ :=
    ne_of_lt (Submission.BoseGases.acube_lt_top ((1 + d) / d) hratio.le)
  refine ⟨?_, ?_⟩
  · refine integrable_of_boundB1 hKmeas hKfin hA₀ hB₀ ?_ ?_
    · intro u hu
      have h0 : (fun z : E3 => Submission.BoseGases.chiB ℓ d u z * w z) = 0 := by
        simpa using Work.BoseFixB1S.chiB_mul_eq_zero_of_not_mem_acube_u hℓ hd hu w 0
      rw [h0]
      exact bsW_zeroB1 _
    · intro u
      simpa using hbd₀ u
  · refine integrable_of_boundB1 hKmeas hKfin hA₁ hB₁ ?_ ?_
    · intro u hu
      have h0 : (fun z : E3 => Submission.BoseGases.chiB ℓ d u z *
          (w z - (1 / Work.SmallBoxSliding.boxMass ℓ d u) *
            ∫ z' in Submission.BoseGases.dlBox ℓ d u, w z')) = 0 :=
        Work.BoseFixB1S.chiB_mul_eq_zero_of_not_mem_acube_u hℓ hd hu w
          ((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
            ∫ z' in Submission.BoseGases.dlBox ℓ d u, w z')
      rw [h0]
      exact bsW_zeroB1 _
    · intro u
      simpa using hbd₁ u

end Work.BoseFixB1S.oneBodyB1
