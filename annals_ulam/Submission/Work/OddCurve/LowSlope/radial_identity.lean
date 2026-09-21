import Mathlib
import Submission.Work.OddCurve.LowSlope.sphereArea_eq_ballVol

/-!
# The pointwise identity of the radial function: `ρ³ = f (f - t f') (ρ + u ρ')`

If `ρ` is the radial function of a body of revolution with profile `f` in the parametrisation
`f (ρ u · u) = ρ u · √(1-u²)` (`|u| < 1`), and `t = ρ u · u`, then on `(-1,1)`

`f t · (f t - t f' t) · (ρ u + u ρ' u) = ρ u ^ 3`.

Equivalently `f (f - t f') = ρ³ / (ρ + u ρ')`: the factor `(ρ + u ρ') = dt/du` is exactly the
Jacobian of the substitution `u ↦ t = ρ u · u`, so this identity is what turns the spherical-Radon
integral into the section integral of `Work.OddCurve.LowSlope.section_ibp`.

Proof: differentiate `f (ρ u)² = ρ u² (1-u²)` in `u`:
`f f' (ρ + u ρ') = ρ ρ' (1-u²) - ρ² u`, then
`f (f - t f')(ρ + u ρ') = f²(ρ+uρ') - t f f'(ρ+uρ')
 = ρ²(1-u²)(ρ+uρ') - ρu(ρρ'(1-u²) - ρ²u) = ρ³(1-u²) + ρ³u² = ρ³`.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- **The pointwise identity of the radial function.** -/
theorem radial_identity {f ρ : ℝ → ℝ} {u : ℝ} (hu : u ∈ Set.Ioo (-1 : ℝ) 1)
    (hρpos : 0 < ρ u)
    (hρd : HasDerivAt ρ (deriv ρ u) u)
    (hfd : HasDerivAt f (deriv f (ρ u * u)) (ρ u * u))
    (hρ : ∀ v ∈ Set.Ioo (-1 : ℝ) 1, ρ v * Real.sqrt (1 - v ^ 2) = f (ρ v * v)) :
    f (ρ u * u) * (f (ρ u * u) - (ρ u * u) * deriv f (ρ u * u)) *
        (ρ u + u * deriv ρ u) = ρ u ^ 3 := by
  have h1u : 0 < 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
  have hsne : Real.sqrt (1 - u ^ 2) ≠ 0 := by positivity
  have hsq : Real.sqrt (1 - u ^ 2) * Real.sqrt (1 - u ^ 2) = 1 - u ^ 2 := by
    rw [← sq, Real.sq_sqrt h1u.le]
  have h21 : (2 : ℕ) - 1 = 1 := by norm_num
  -- the derivative of `v ↦ √(1-v²)`
  have hsqrt : HasDerivAt (fun v : ℝ => Real.sqrt (1 - v ^ 2))
      ((-u) / Real.sqrt (1 - u ^ 2)) u := by
    have hinner : HasDerivAt (fun v : ℝ => 1 - v ^ 2) (-(2 * u)) u := by
      have hh := (hasDerivAt_const (x := u) (c := (1 : ℝ))).sub ((hasDerivAt_id u).pow 2)
      have hfun : ((fun _ : ℝ => (1 : ℝ)) - id ^ 2) = fun v : ℝ => 1 - v ^ 2 := by
        funext v; simp
      rw [hfun] at hh
      refine hh.congr_deriv ?_
      rw [id_eq]
      norm_num
    have hsq' := (Real.hasDerivAt_sqrt (x := 1 - u ^ 2) (ne_of_gt h1u)).comp u hinner
    have hval : (1 / (2 * Real.sqrt (1 - u ^ 2))) * (-(2 * u)) = (-u) / Real.sqrt (1 - u ^ 2) := by
      field_simp [hsne]
    rwa [hval] at hsq'
  -- the two derivatives in play
  have hprod : HasDerivAt (fun v : ℝ => ρ v * Real.sqrt (1 - v ^ 2))
      (deriv ρ u * Real.sqrt (1 - u ^ 2) + ρ u * ((-u) / Real.sqrt (1 - u ^ 2))) u :=
    hρd.mul hsqrt
  have heq : (fun v : ℝ => ρ v * Real.sqrt (1 - v ^ 2)) =ᶠ[𝓝 u]
      (fun v : ℝ => f (ρ v * v)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
    exact hρ v hv
  have hcomp : HasDerivAt (fun v : ℝ => f (ρ v * v))
      (deriv ρ u * Real.sqrt (1 - u ^ 2) + ρ u * ((-u) / Real.sqrt (1 - u ^ 2))) u :=
    hprod.congr_of_eventuallyEq heq.symm
  have hinner : HasDerivAt (fun v : ℝ => ρ v * v) (deriv ρ u * u + ρ u) u := by
    have hh := hρd.mul (hasDerivAt_id u)
    have hfun : (ρ * id : ℝ → ℝ) = fun v : ℝ => ρ v * v := by
      funext v; simp
    rw [hfun] at hh
    refine hh.congr_deriv ?_
    rw [id_eq]
    ring
  have hchain : HasDerivAt (fun v : ℝ => f (ρ v * v))
      (deriv f (ρ u * u) * (deriv ρ u * u + ρ u)) u :=
    HasDerivAt.comp u hfd hinner
  -- the derivative identity
  have hderiv_eq : deriv f (ρ u * u) * (deriv ρ u * u + ρ u)
      = deriv ρ u * Real.sqrt (1 - u ^ 2) + ρ u * ((-u) / Real.sqrt (1 - u ^ 2)) :=
    hchain.unique hcomp
  have hf_eq : f (ρ u * u) = ρ u * Real.sqrt (1 - u ^ 2) := (hρ u hu).symm
  rw [hf_eq]
  have hA : deriv f (ρ u * u) * (ρ u + u * deriv ρ u)
      = deriv ρ u * Real.sqrt (1 - u ^ 2) - ρ u * u / Real.sqrt (1 - u ^ 2) := by
    have hcomm : deriv f (ρ u * u) * (ρ u + u * deriv ρ u)
        = deriv f (ρ u * u) * (deriv ρ u * u + ρ u) := by ring
    rw [hcomm, hderiv_eq]
    field_simp
    ring
  have hexp : ρ u * Real.sqrt (1 - u ^ 2) *
        (ρ u * Real.sqrt (1 - u ^ 2) - ρ u * u * deriv f (ρ u * u)) *
        (ρ u + u * deriv ρ u)
      = (ρ u * Real.sqrt (1 - u ^ 2)) ^ 2 * (ρ u + u * deriv ρ u)
        - (ρ u * u) * (ρ u * Real.sqrt (1 - u ^ 2)) *
            (deriv f (ρ u * u) * (ρ u + u * deriv ρ u)) := by ring
  rw [hexp, hA]
  have hsq2 : (ρ u * Real.sqrt (1 - u ^ 2)) ^ 2 = ρ u ^ 2 * (1 - u ^ 2) := by
    rw [mul_pow]
    congr 1
    rw [sq]
    exact hsq
  rw [hsq2]
  field_simp
  rw [Real.sq_sqrt h1u.le]
  ring

end

end Work.OddCurve.LowSlope
