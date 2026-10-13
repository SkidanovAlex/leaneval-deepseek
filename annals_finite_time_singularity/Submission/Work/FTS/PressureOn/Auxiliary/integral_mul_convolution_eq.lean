import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.PressureOn.Auxiliary

/-- **Duality identity for a convolution against a multiplication.**

For scalar functions `q`, `b`, `ρ` on `ℝ³` with `ρ` even (and `b`, `ρ` compactly supported),
the pairing `∫ q · (ρ ⋆ b)` equals `∫ (ρ ⋆ q) · b`.

The proof is the standard one: unfold both convolutions with `convolution_lsmul`, distribute
the pointwise factor into the integral (`integral_const_mul` / `integral_mul_const`), apply
Fubini (`integral_integral_swap`, the two integrability hypotheses are exactly the Fubini
hypotheses), and then observe that the two double integrals agree after the change of
variables `t ↦ -t` in the outer variable (using `heven`) and `x ↦ x + t` in the inner one
(`integral_sub_right_eq_self`). -/
theorem integral_mul_convolution_eq
    (q b : EuclideanSpace ℝ (Fin 3) → ℝ)
    (ρ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hq : Continuous q) (hb : Continuous b) (hbc : HasCompactSupport b)
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (heven : ∀ z, ρ (-z) = ρ z)
    (hγ : MeasureTheory.Integrable (Function.uncurry fun (x t : EuclideanSpace ℝ (Fin 3)) =>
        q x * (ρ t * b (x - t))) (MeasureTheory.volume.prod MeasureTheory.volume))
    (hδ : MeasureTheory.Integrable (Function.uncurry fun (x t : EuclideanSpace ℝ (Fin 3)) =>
        (ρ t * q (x - t)) * b x) (MeasureTheory.volume.prod MeasureTheory.volume)) :
    ∫ x, q x * (MeasureTheory.convolution ρ b (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x)
      = ∫ x, (MeasureTheory.convolution ρ q (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x)
          * b x := by
  have hconvb : ∀ x,
      MeasureTheory.convolution ρ b (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x
        = ∫ t, ρ t * b (x - t) := by
    intro x
    rw [MeasureTheory.convolution_lsmul]
    simp
  have hconvq : ∀ x,
      MeasureTheory.convolution ρ q (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x
        = ∫ t, ρ t * q (x - t) := by
    intro x
    rw [MeasureTheory.convolution_lsmul]
    simp
  have hL : ∫ x, q x *
        (MeasureTheory.convolution ρ b (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x)
      = ∫ t, ∫ x, q x * (ρ t * b (x - t)) := by
    have h1 : (fun x => q x * (∫ t, ρ t * b (x - t)))
        = fun x => ∫ t, q x * (ρ t * b (x - t)) := by
      funext x
      exact (MeasureTheory.integral_const_mul (q x) (fun t => ρ t * b (x - t))).symm
    simp only [hconvb, h1]
    exact MeasureTheory.integral_integral_swap hγ
  have hR : ∫ x,
        (MeasureTheory.convolution ρ q (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x) * b x
      = ∫ t, ∫ x, (ρ t * q (x - t)) * b x := by
    have h1 : (fun x => (∫ t, ρ t * q (x - t)) * b x)
        = fun x => ∫ t, (ρ t * q (x - t)) * b x := by
      funext x
      exact (MeasureTheory.integral_mul_const (b x) (fun t => ρ t * q (x - t))).symm
    simp only [hconvq, h1]
    exact MeasureTheory.integral_integral_swap hδ
  rw [hL, hR]
  -- The two double integrals agree: for every `t` the inner integral of the right-hand side
  -- is the inner integral of the left-hand side at `-t` (change of variables `x ↦ x + t` in
  -- the inner integral, plus evenness of `ρ`).
  have hGF : ∀ t, (∫ x, (ρ t * q (x - t)) * b x)
      = ∫ x, q x * (ρ (-t) * b (x - (-t))) := by
    intro t
    have hstep : ∫ x, (ρ t * q (x - t)) * b x
        = ∫ u, (ρ t * q u) * b (u + t) := by
      have h := MeasureTheory.integral_sub_right_eq_self (μ := volume)
        (fun u : EuclideanSpace ℝ (Fin 3) => (ρ t * q u) * b (u + t)) t
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
    rw [hstep]
    have h2 : ∫ u, (ρ t * q u) * b (u + t) = ∫ u, q u * (ρ t * b (u + t)) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      ring
    rw [h2]
    have h3 : ∫ u, q u * (ρ t * b (u + t)) = ∫ u, q u * (ρ (-t) * b (u + t)) := by
      rw [heven t]
    rw [h3]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [sub_neg_eq_add]
  calc ∫ t, ∫ x, q x * (ρ t * b (x - t))
      = ∫ t, (fun s => ∫ x, q x * (ρ s * b (x - s))) t := rfl
    _ = ∫ t, (fun s => ∫ x, q x * (ρ s * b (x - s))) (-t) :=
        (MeasureTheory.integral_neg_eq_self (fun s => ∫ x, q x * (ρ s * b (x - s))) volume).symm
    _ = ∫ t, ∫ x, (ρ t * q (x - t)) * b x := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        exact (hGF t).symm

end Work.FTS.PressureOn.Auxiliary
