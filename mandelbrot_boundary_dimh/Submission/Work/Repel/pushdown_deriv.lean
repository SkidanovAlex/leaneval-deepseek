import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.basic

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology
open scoped Topology

noncomputable section

/-- `π(a + b) = π(a) · π(b)` for `π(w) = exp(2πiw)`. -/
theorem piExp_add (a b : ℂ) : piExp (a + b) = piExp a * piExp b := by
  rw [piExp, piExp, piExp, ← Complex.exp_add]
  congr 1
  ring

/-- `π a = π(a + b) · π(-b)`. -/
theorem piExp_eq_mul_piExp_neg (a b : ℂ) : piExp a = piExp (a + b) * piExp (-b) := by
  rw [← piExp_add, show a + b + -b = a by ring]

/-- The pushdown of a `T`-equivariant map with `E w = w - c + o(1)` at the upper end is
differentiable at `0` with derivative `π(-c) = exp(-2πi c)`.

The lift `ζ ↦ log ζ/(2πi)` of `ζ → 0` runs to the upper end (`Im → +∞`), so the asymptotic
expansion of `E` at that end controls the germ of `pushdown E` at `0`. -/
theorem pushdown_deriv {E : ℂ → ℂ} {DR : Set ℂ} {y : ℝ} {c : ℂ}
    (hopen : IsOpen DR) (heq : IsTEquivariantOn E DR) (hdiff : DifferentiableOn ℂ E DR)
    (hy : ∀ w : ℂ, y ≤ |w.im| → w ∈ DR)
    (hup : Tendsto (fun w => E w - w + c) upperEnd (𝓝 0)) :
    HasDerivAt (pushdown E) (piExp (-c)) 0 := by
  -- the lift tends to the upper end as `ζ → 0`
  have hlog : Tendsto (fun ζ : ℂ => Complex.log ζ / (2 * Real.pi * Complex.I))
      (𝓝[≠] (0 : ℂ)) upperEnd := Work.Horn.MandelDim.tendsto_log_div_upperEnd
  -- therefore `E w - w + c → 0` along `ζ → 0`
  have hξ : Tendsto (fun ζ : ℂ => E (Complex.log ζ / (2 * Real.pi * Complex.I)) -
      Complex.log ζ / (2 * Real.pi * Complex.I) + c) (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
    hup.comp hlog
  -- and exponentiation of it tends to `1`
  have hpi : Tendsto (fun z : ℂ => piExp z) (𝓝 (0 : ℂ)) (𝓝 1) := by
    have hc : Continuous piExp := by unfold piExp; fun_prop
    have h0 : piExp 0 = 1 := by simp [piExp]
    simpa [h0] using hc.tendsto 0
  have hcomp : Tendsto (fun ζ : ℂ => piExp (E (Complex.log ζ / (2 * Real.pi * Complex.I)) -
      Complex.log ζ / (2 * Real.pi * Complex.I) + c)) (𝓝[≠] (0 : ℂ)) (𝓝 1) :=
    hpi.comp hξ
  have hlim : Tendsto (fun ζ : ℂ => piExp (E (Complex.log ζ / (2 * Real.pi * Complex.I)) -
      Complex.log ζ / (2 * Real.pi * Complex.I) + c) * piExp (-c))
      (𝓝[≠] (0 : ℂ)) (𝓝 (piExp (-c))) := by
    have h := hcomp.mul_const (piExp (-c))
    simpa using h
  -- identify the slope with `π(E w) / π w`
  rw [hasDerivAt_iff_tendsto_slope]
  have hsl : slope (pushdown E) 0 = fun ζ : ℂ => ζ⁻¹ * pushdown E ζ := by
    funext ζ
    simp [slope, Work.Horn.MandelDim.pushdown_zero, smul_eq_mul]
  rw [hsl]
  refine Filter.Tendsto.congr' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with ζ hζ
  set w : ℂ := Complex.log ζ / (2 * Real.pi * Complex.I) with hwdef
  have hpush : pushdown E ζ = piExp (E w) := by
    rw [Work.Horn.MandelDim.pushdown_of_ne E hζ, hwdef]
  have hzeta : ζ = piExp w := by
    rw [hwdef]
    exact (Work.Horn.MandelDim.piExp_log_div ζ hζ).symm
  rw [hpush, hzeta, ← div_eq_inv_mul, ← Work.Horn.MandelDim.piExp_sub]
  exact (piExp_eq_mul_piExp_neg (E w - w) c).symm

end

end Work.Repel
