import Mathlib

namespace Work.C17g

theorem segment_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {z₀ z : ℂ} {t : ℝ}
    (hf : DifferentiableAt ℂ f (z₀ + t • (z - z₀))) :
    HasDerivAt (fun x : ℂ => (x - z₀) • f (z₀ + t • (x - z₀)))
      (f (z₀ + t • (z - z₀)) + (z - z₀) • (t • deriv f (z₀ + t • (z - z₀)))) z := by
  -- The affine reparametrisation `x ↦ z₀ + t • (x - z₀)`.
  have hφ : HasDerivAt (fun x : ℂ => z₀ + t • (x - z₀)) (t : ℂ) z := by
    have h1 : HasDerivAt (fun x : ℂ => x - z₀) (1:ℂ) z := (hasDerivAt_id z).sub_const z₀
    have h2 : HasDerivAt (fun x : ℂ => (t:ℂ) * (x - z₀)) ((t:ℂ) * 1) z := h1.const_mul (t:ℂ)
    have h3 : HasDerivAt (fun x : ℂ => z₀ + (t:ℂ) * (x - z₀)) ((t:ℂ)*1) z := h2.const_add z₀
    simpa using h3
  -- Chain rule for `x ↦ f (z₀ + t • (x - z₀))`.
  have hd : HasDerivAt f (deriv f (z₀ + t • (z - z₀))) (z₀ + t • (z - z₀)) := hf.hasDerivAt
  have hF : HasDerivAt (fun x : ℂ => f (z₀ + t • (x - z₀))) (t • deriv f (z₀ + t • (z - z₀))) z :=
    hd.scomp z hφ
  -- Leibniz rule against the scalar factor `x ↦ x - z₀`.
  have hc : HasDerivAt (fun x : ℂ => x - z₀) (1:ℂ) z := (hasDerivAt_id z).sub_const z₀
  have hprod := hc.smul hF
  have hderiv : (z - z₀) • (t • deriv f (z₀ + t • (z - z₀))) + (1:ℂ) • f (z₀ + t • (z - z₀))
      = f (z₀ + t • (z - z₀)) + (z - z₀) • (t • deriv f (z₀ + t • (z - z₀))) := by
    rw [one_smul, add_comm]
  exact hprod.congr_deriv hderiv

end Work.C17g
