import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Order.CompletePartialOrder
import Submission.Work.EllipticEst.Core.i0Aux.setIntegral_Ioo_comp_sub

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Reflection facts on `(0, π/2)`

The map `θ ↦ π/2 - θ` is an involutive, measure preserving bijection of `Ioo 0 (π/2)` onto
itself.  This file records the six consequences used by the endpoint analysis of the `i0`
chapter: invariance of the Lebesgue integral, transfer of integrability, transfer of `C²`,
the first and second chain rules for the global `deriv`, and the transfer of the one-sided
limit at `π/2⁻` for `f` into the one-sided limit at `0⁺` for the reflected function.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Work.EllipticEst.Core.i0Aux.EndpointValues

set_option autoImplicit false

/-- The reflection `θ ↦ π/2 - θ` maps the interval `Ioo 0 (π/2)` onto itself. -/
private lemma reflect_preimage_Ioo :
    (fun θ : ℝ => Real.pi / 2 - θ) ⁻¹' Set.Ioo 0 (Real.pi / 2) = Set.Ioo 0 (Real.pi / 2) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_Ioo]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- The Lebesgue integral on `Ioo 0 (π/2)` is invariant under `θ ↦ π/2 - θ`. -/
private lemma reflect_integral (F : ℝ → ℝ) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2), F (Real.pi / 2 - θ))
      = ∫ θ in Set.Ioo 0 (Real.pi / 2), F θ := by
  have hab : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have h := _root_.Work.EllipticEst.Core.i0Aux.setIntegral_Ioo_comp_sub F (Real.pi / 2) hab
  simpa only [sub_self, sub_zero] using h

/-- Integrability on `Ioo 0 (π/2)` is preserved by `θ ↦ π/2 - θ`. -/
private lemma reflect_integrableOn (F : ℝ → ℝ)
    (hF : MeasureTheory.IntegrableOn F (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => F (Real.pi / 2 - θ))
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hmp : MeasureTheory.MeasurePreserving (fun θ : ℝ => Real.pi / 2 - θ) volume volume :=
    _root_.MeasureTheory.Measure.measurePreserving_sub_left volume (Real.pi / 2)
  have hemb : MeasurableEmbedding (fun θ : ℝ => Real.pi / 2 - θ) :=
    measurableEmbedding_subLeft (Real.pi / 2)
  have h := MeasureTheory.MeasurePreserving.integrableOn_comp_preimage hmp hemb
    (f := F) (s := Set.Ioo 0 (Real.pi / 2))
  rw [reflect_preimage_Ioo] at h
  exact h.mpr hF

/-- `C²` on `Ioo 0 (π/2)` is preserved by `θ ↦ π/2 - θ`. -/
private lemma reflect_contDiffOn (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ 2 (fun θ : ℝ => f (Real.pi / 2 - θ)) (Set.Ioo 0 (Real.pi / 2)) := by
  have hg : ContDiffOn ℝ 2 (fun θ : ℝ => Real.pi / 2 - θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have h : ContDiff ℝ 2 (fun θ : ℝ => Real.pi / 2 - θ) :=
      (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => Real.pi / 2)).sub contDiff_id
    exact h.contDiffOn
  have hmap : MapsTo (fun θ : ℝ => Real.pi / 2 - θ) (Set.Ioo 0 (Real.pi / 2))
      (Set.Ioo 0 (Real.pi / 2)) :=
    fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩
  exact hf.comp hg hmap

/-- The chain rule for the first derivative. -/
private lemma reflect_deriv (f : ℝ → ℝ) (_hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (_hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun θ' : ℝ => f (Real.pi / 2 - θ')) θ = -deriv f (Real.pi / 2 - θ) :=
  deriv_comp_const_sub f (Real.pi / 2) θ

/-- The chain rule for the second derivative (`deriv (deriv ·)`, not `iteratedDeriv`). -/
private lemma reflect_deriv2 (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (deriv (fun θ' : ℝ => f (Real.pi / 2 - θ'))) θ
      = deriv (deriv f) (Real.pi / 2 - θ) := by
  have hso : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hm : Real.pi / 2 - θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  have heq : deriv (fun θ' : ℝ => f (Real.pi / 2 - θ'))
      = fun y : ℝ => -deriv f (Real.pi / 2 - y) :=
    funext fun y => deriv_comp_const_sub f (Real.pi / 2) y
  rw [heq]
  have h2 : HasDerivAt (deriv f) (deriv (deriv f) (Real.pi / 2 - θ)) (Real.pi / 2 - θ) :=
    (((hf.contDiffAt (hso.mem_nhds hm)).derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasDerivAt
  have h3 : HasDerivAt (fun y : ℝ => deriv f (Real.pi / 2 - y))
      (-(deriv (deriv f) (Real.pi / 2 - θ))) θ :=
    HasDerivAt.comp_const_sub (Real.pi / 2) θ h2
  have h4 : deriv (fun y : ℝ => -deriv f (Real.pi / 2 - y)) θ
      = -(-(deriv (deriv f) (Real.pi / 2 - θ))) := by
    simpa only [Pi.neg_def] using h3.neg.deriv
  rw [h4]
  ring

/-- A one-sided limit at `π/2⁻` becomes a one-sided limit at `0⁺` after reflection. -/
private lemma reflect_tendsto (f : ℝ → ℝ) (F : ℝ)
    (hf : Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds F)) :
    Tendsto (fun θ : ℝ => f (Real.pi / 2 - θ)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds F) := by
  have hcont : Continuous fun y : ℝ => Real.pi / 2 - y := continuous_const.sub continuous_id
  have htend : Tendsto (fun y : ℝ => Real.pi / 2 - y) (nhds (0 : ℝ)) (nhds (Real.pi / 2)) :=
    hcont.tendsto' 0 (Real.pi / 2) (by simp)
  have hmem : ∀ᶠ y in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      Real.pi / 2 - y ∈ Set.Iio (Real.pi / 2) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [Set.mem_Ioi] at hy
    simp only [Set.mem_Iio]
    linarith
  have hin : Tendsto (fun y : ℝ => Real.pi / 2 - y) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) :=
    tendsto_nhdsWithin_iff.mpr ⟨htend.mono_left nhdsWithin_le_nhds, hmem⟩
  exact hf.comp hin

theorem reflectFacts :
    (∀ F : ℝ → ℝ, (∫ θ in Set.Ioo 0 (Real.pi / 2), F (Real.pi / 2 - θ))
        = ∫ θ in Set.Ioo 0 (Real.pi / 2), F θ) ∧
    (∀ F : ℝ → ℝ, MeasureTheory.IntegrableOn F (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn (fun θ : ℝ => F (Real.pi / 2 - θ))
        (Set.Ioo 0 (Real.pi / 2))) ∧
    (∀ f : ℝ → ℝ, ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
      ContDiffOn ℝ 2 (fun θ : ℝ => f (Real.pi / 2 - θ)) (Set.Ioo 0 (Real.pi / 2))) ∧
    (∀ f : ℝ → ℝ, ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (fun θ' : ℝ => f (Real.pi / 2 - θ')) θ = -deriv f (Real.pi / 2 - θ)) ∧
    (∀ f : ℝ → ℝ, ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (deriv (fun θ' : ℝ => f (Real.pi / 2 - θ'))) θ
        = deriv (deriv f) (Real.pi / 2 - θ)) ∧
    (∀ (f : ℝ → ℝ) (F : ℝ),
      Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds F) →
      Filter.Tendsto (fun θ : ℝ => f (Real.pi / 2 - θ)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds F)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact reflect_integral
  · intro F hF
    exact reflect_integrableOn F hF
  · intro f hf
    exact reflect_contDiffOn f hf
  · intro f hf θ hθ
    exact reflect_deriv f hf hθ
  · intro f hf θ hθ
    exact reflect_deriv2 f hf hθ
  · intro f F hf
    exact reflect_tendsto f F hf

end Work.EllipticEst.Core.i0Aux.EndpointValues
