import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Have

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert.GsingSmooth

open MeasureTheory Set
open scoped ContDiff Topology
open intervalIntegral

/-- The tail integral `z ↦ ∫ r in Ioi z, g r` of a function `g` which is `C^m` and integrable
on `(0, ∞)` is `C^m` on `(0, ∞)`.

This is the standard "differentiate under the integral sign" statement for a tail integral,
which is really the fundamental theorem of calculus: the tail integral differs from the
primitive `z ↦ ∫₀^z g` by a constant on `(0, ∞)`, and the derivative of the tail integral is
`-g`. -/
theorem contDiffOn_tailIntegral_Ioi0 (g : ℝ → ℝ)
    (hg : ∀ m : ℕ, ContDiffOn ℝ m g (Set.Ioi 0))
    (hint : MeasureTheory.IntegrableOn g (Set.Ioi 0)) :
    ∀ m : ℕ, ContDiffOn ℝ m (fun z : ℝ => ∫ r in Set.Ioi z, g r) (Set.Ioi 0) := by
  have hcont : ContinuousOn g (Set.Ioi (0 : ℝ)) := (hg 0).continuousOn
  have hmeas : ∀ z ∈ Set.Ioi (0 : ℝ), StronglyMeasurableAtFilter g (𝓝 z) volume :=
    fun z hz => hcont.stronglyMeasurableAtFilter isOpen_Ioi z hz
  -- The fundamental theorem of calculus: the derivative of the tail integral is `-g`.
  have hderiv : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z : ℝ => ∫ r in Set.Ioi z, g r) (-(g z)) z := by
    intro z hz
    have hz0 : (0 : ℝ) < z := hz
    -- On `(0, ∞)` the tail integral is a constant minus the primitive.
    have hEq : (fun z : ℝ => ∫ r in Set.Ioi z, g r) =ᶠ[𝓝 z]
        ((fun _ : ℝ => ∫ r in Set.Ioi (0 : ℝ), g r) -
          fun w : ℝ => ∫ x in (0 : ℝ)..w, g x) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz0] with w hw
      have hw0 : (0 : ℝ) < w := hw
      have hIoi : IntegrableOn g (Set.Ioi w) := hint.mono_set (Ioi_subset_Ioi hw0.le)
      have h := integral_interval_add_Ioi (f := g) (a := (0 : ℝ)) (b := w) hint hIoi
      simp only [Pi.sub_apply]
      linarith
    have hInt : IntervalIntegrable g volume (0 : ℝ) z := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hz0.le]
      exact hint.mono_set fun x hx => hx.1
    have hprim : HasDerivAt (fun w : ℝ => ∫ x in (0 : ℝ)..w, g x) (g z) z :=
      integral_hasDerivAt_right hInt (hmeas z hz)
        (hcont.continuousAt (isOpen_Ioi.mem_nhds hz0))
    have hmain : HasDerivAt
        ((fun _ : ℝ => ∫ r in Set.Ioi (0 : ℝ), g r) -
          fun w : ℝ => ∫ x in (0 : ℝ)..w, g x) (0 - g z) z :=
      (hasDerivAt_const (x := z) (c := ∫ r in Set.Ioi (0 : ℝ), g r)).sub hprim
    exact (hmain.congr_of_eventuallyEq hEq).congr_deriv (zero_sub (g z))
  have hdiff : DifferentiableOn ℝ (fun z : ℝ => ∫ r in Set.Ioi z, g r) (Set.Ioi 0) :=
    fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt
  -- The derivative is `-g`, which is smooth on `(0, ∞)`.
  have hderivC : ContDiffOn ℝ ∞ (deriv (fun z : ℝ => ∫ r in Set.Ioi z, g r)) (Set.Ioi 0) := by
    have hgInfty : ContDiffOn ℝ ∞ g (Set.Ioi (0 : ℝ)) := contDiffOn_infty.2 hg
    exact (hgInfty.neg).congr fun z hz => (hderiv z hz).deriv
  have hFInfty : ContDiffOn ℝ ∞ (fun z : ℝ => ∫ r in Set.Ioi z, g r) (Set.Ioi 0) :=
    (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).2 ⟨hdiff, hderivC⟩
  intro m
  exact (contDiffOn_infty.1 hFInfty) m

end Work.FTS.EllipticEst.Cert.GsingSmooth
