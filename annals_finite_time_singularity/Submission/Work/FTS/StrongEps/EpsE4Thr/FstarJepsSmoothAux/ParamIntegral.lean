import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Filter
open scoped Topology

namespace Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

theorem ParamIntegral {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    [MeasureTheory.IsFiniteMeasure μ] {Φ : ℕ → ℝ → X → ℝ}
    (hmeas : ∀ k s, MeasureTheory.AEStronglyMeasurable (Φ k s) μ)
    (hderiv : ∀ k, ∀ᵐ x ∂μ, ∀ s : ℝ, HasDerivAt (fun s' => Φ k s' x) (Φ (k + 1) s x) s)
    (hbound : ∀ k s₀, ∃ B : X → ℝ, MeasureTheory.Integrable B μ ∧
      ∀ᵐ x ∂μ, ∀ s ∈ Set.Ioo (s₀ - 1) (s₀ + 1), |Φ k s x| ≤ B x)
    (m : ℕ) : ContDiff ℝ m (fun s => ∫ x, Φ 0 s x ∂μ) := by
  -- Each `Φ k s` is integrable, since it is dominated by the integrable `B` on a neighbourhood
  -- of `s` itself.
  have hInt : ∀ k s, MeasureTheory.Integrable (Φ k s) μ := by
    intro k s
    obtain ⟨B, hBint, hB⟩ := hbound k s
    refine hBint.mono' (hmeas k s) ?_
    filter_upwards [hB] with x hx
    simpa only [Real.norm_eq_abs] using hx s ⟨by linarith, by linarith⟩
  -- Differentiation under the integral sign: the derivative of `s ↦ ∫ x, Φ k s x ∂μ` is the
  -- integral of `Φ (k+1)`.
  have hd : ∀ k s, HasDerivAt (fun s => ∫ x, Φ k s x ∂μ) (∫ x, Φ (k + 1) s x ∂μ) s := by
    intro k s
    obtain ⟨B, hBint, hB⟩ := hbound (k + 1) s
    have hs : Set.Ioo (s - 1) (s + 1) ∈ 𝓝 s := Ioo_mem_nhds (by linarith) (by linarith)
    have hbnd : ∀ᵐ x ∂μ, ∀ y ∈ Set.Ioo (s - 1) (s + 1), ‖Φ (k + 1) y x‖ ≤ B x := by
      filter_upwards [hB] with x hx y hy
      simpa only [Real.norm_eq_abs] using hx y hy
    have hdiff : ∀ᵐ x ∂μ, ∀ y ∈ Set.Ioo (s - 1) (s + 1),
        HasDerivAt (fun y' => Φ k y' x) (Φ (k + 1) y x) y :=
      (hderiv k).mono fun x hx y _ => hx y
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℝ) (E := ℝ)
      hs (Filter.Eventually.of_forall fun y => hmeas k y) (hInt k s) (hmeas (k + 1) s)
      hbnd hBint hdiff).2
  -- Identification of all iterated derivatives of the integral.
  have hiter : ∀ k, iteratedDeriv k (fun s => ∫ x, Φ 0 s x ∂μ) = fun s => ∫ x, Φ k s x ∂μ := by
    intro k
    induction k with
    | zero => rw [iteratedDeriv_zero]
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext s
      exact (hd n s).deriv
  rw [contDiff_nat_iff_iteratedDeriv]
  refine ⟨fun m' _ => ?_, fun m' _ => ?_⟩
  · rw [hiter m']
    exact Differentiable.continuous (f := fun s => ∫ x, Φ m' s x ∂μ)
      fun s => (hd m' s).differentiableAt
  · rw [hiter m']
    exact fun s => (hd m' s).differentiableAt

end Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux
