import Mathlib
import Submission.Work.BoxShrink.PinchOff.RefuteDrop.Config
import Submission.Work.BoxShrink.PinchOff.RefuteDrop.omega_rank_two
import Submission.Work.BoxShrink.PinchOff.TangentData.Basic

/-!
# The box-sphere trace of the `RefuteDrop` configuration carries no essential loop

At the configuration of `RefuteDrop/Config.lean` — the linear diffeomorphism `ψ = dropDiffeo`,
the box centre `dropC = 0`, the coordinate permutation `dropCyc = swap 0 2` and the box size
`dropS = 7/5` — the trace of the boundary sphere `∂PBox dropS dropC dropCyc` on the surface
carries **no** essential loop (`Work.BoxShrink.PinchOff.RefuteDrop.sphereTrace_inessential_drop`).

The argument is the "confining grid line" one.  The parametrised trace
`T = {(u, v) | boxNorm dropC dropCyc (dropVec (torusMap u v)) = dropS} ⊆ ℝ²/2πℤ²` misses two
whole grid circles in the parameter torus:

* the **longitude** `{θ = dropTheta}` with `dropTheta = arccos(-12/13)`: for every `φ` the point
  `dropVec (torusMap dropTheta φ)` has all three coordinates `< dropS = 7/5` in absolute value,
  hence lies *strictly inside* the box and off the sphere (`drop_boxNorm_longitude_lt`);
* the **meridian** `{φ = π}`: for every `θ` the point `dropVec (torusMap θ π)` again has all three
  coordinates `< dropS` (`drop_boxNorm_meridian_lt`).

A closed curve `γ` of the surface whose image lies in `∂PBox dropS dropC dropCyc` lifts to a pair
of continuous functions `(Θ, Φ)` with `dropVec (torusMap (Θ t) (Φ t)) = γ t`; since the trace is
exactly the set of parameter pairs whose image is on the sphere, `Θ` avoids the lattice
`dropTheta + 2πℤ` and `Φ` avoids `π + 2πℤ`.  Both avoidances force the corresponding winding
increment to vanish (`Work.BoxShrink.PinchOff.int_eq_zero_of_notMem_lattice`), so the winding
vector of `γ` is `0` and `γ` is inessential.

The two bounds are elementary: writing `ρ = 2 + cos φ ∈ [1,3]` and `z = sin φ ∈ [-1,1]`, the
coordinates of `dropVec (torusMap dropTheta φ)` are the affine expressions

* `w₀ = -(99/1300) ρ + (97/100) z`,
* `w₁ = -(221/650) ρ - (3/25) z`,
* `w₂ = (8/325) ρ + (59/100) z`,

each bounded by `|A|·3 + |B|`; all three bounds are `< 7/5`.  For the meridian `φ = π` one has
`ρ = 1` and the coordinates are `A cos θ + B sin θ`, whose amplitude `√(A² + B²)` is `< 7/5`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff.RefuteDrop

noncomputable section

/-! ## Periodicity of the parametrisation in integer multiples of `2π` -/

theorem torusMap_add_int_mul_two_pi_left (θ φ : ℝ) (k : ℤ) :
    Work.Core.torusMap (θ + (k : ℝ) * (2 * Real.pi)) φ = Work.Core.torusMap θ φ := by
  ext i
  fin_cases i <;>
    simp [Work.Core.torusMap, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

theorem torusMap_add_int_mul_two_pi_right (θ φ : ℝ) (k : ℤ) :
    Work.Core.torusMap θ (φ + (k : ℝ) * (2 * Real.pi)) = Work.Core.torusMap θ φ := by
  ext i
  fin_cases i <;>
    simp [Work.Core.torusMap, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

/-! ## The box norm of the configuration in coordinates -/

/-- **The box norm of the counterexample in coordinates**: `z` (index `2`) carries the side
`dropS`, `y` (index `1`) the side `2^{1/3} · dropS` and `x` (index `0`) the side
`2^{2/3} · dropS`. -/
theorem boxNorm_drop (y : R3) :
    Submission.boxNorm dropC dropCyc y =
      max (max |y 2| (|y 1| / (2 : ℝ) ^ (1 / 3 : ℝ))) (|y 0| / (2 : ℝ) ^ (2 / 3 : ℝ)) := by
  rw [Submission.boxNorm, dropCyc_zero, dropCyc_one, dropCyc_two, dropC_zero, dropC_one,
    dropC_two, Submission.boxSide_zero, Submission.boxSide_one, Submission.boxSide_two]
  simp

/-! ## A chosen longitude and a chosen meridian lie strictly inside the box -/

/-- The three coordinates of `dropVec (torusMap dropTheta φ)` are affine in
`(2 + cos φ, sin φ)` with the coefficients displayed in the module docstring. -/
theorem dropVec_dropTheta_coord_zero (φ : ℝ) :
    (dropVec (Work.Core.torusMap dropTheta φ)).ofLp 0 =
      (-(99 / 1300) : ℝ) * (2 + Real.cos φ) + (97 / 100) * Real.sin φ := by
  rw [dropVec_coord_zero, Work.CoreTopology.torusMap_apply_zero,
    Work.CoreTopology.torusMap_apply_one, Work.CoreTopology.torusMap_apply_two,
    dropTheta_cos, dropTheta_sin]
  ring

theorem dropVec_dropTheta_coord_one (φ : ℝ) :
    (dropVec (Work.Core.torusMap dropTheta φ)).ofLp 1 =
      (-(221 / 650) : ℝ) * (2 + Real.cos φ) + (-(3 / 25)) * Real.sin φ := by
  rw [dropVec_coord_one, Work.CoreTopology.torusMap_apply_zero,
    Work.CoreTopology.torusMap_apply_one, Work.CoreTopology.torusMap_apply_two,
    dropTheta_cos, dropTheta_sin]
  ring

theorem dropVec_dropTheta_coord_two (φ : ℝ) :
    (dropVec (Work.Core.torusMap dropTheta φ)).ofLp 2 =
      (8 / 325 : ℝ) * (2 + Real.cos φ) + (59 / 100) * Real.sin φ := by
  rw [dropVec_coord_two, Work.CoreTopology.torusMap_apply_zero,
    Work.CoreTopology.torusMap_apply_one, Work.CoreTopology.torusMap_apply_two,
    dropTheta_cos, dropTheta_sin]
  ring

/-- **The longitude `{θ = dropTheta}` lies strictly inside the box**: every point of the
longitude circle `φ ↦ dropVec (torusMap dropTheta φ)` has box norm `< dropS`, so the box sphere
meets the surface in no point of that longitude. -/
theorem drop_boxNorm_longitude_lt (φ : ℝ) :
    Submission.boxNorm dropC dropCyc (dropVec (Work.Core.torusMap dropTheta φ)) < dropS := by
  have hw2 : |(dropVec (Work.Core.torusMap dropTheta φ)) 2| < dropS := by
    rw [dropVec_dropTheta_coord_two φ]
    exact abs_mul_add_bound (by linarith [Real.neg_one_le_cos φ])
      (by linarith [Real.cos_le_one φ]) (Real.abs_sin_le_one φ) (by norm_num [dropS])
  have hw1 : |(dropVec (Work.Core.torusMap dropTheta φ)) 1| < dropS := by
    rw [dropVec_dropTheta_coord_one φ]
    exact abs_mul_add_bound (by linarith [Real.neg_one_le_cos φ])
      (by linarith [Real.cos_le_one φ]) (Real.abs_sin_le_one φ) (by norm_num [dropS])
  have hw0 : |(dropVec (Work.Core.torusMap dropTheta φ)) 0| < dropS := by
    rw [dropVec_dropTheta_coord_zero φ]
    exact abs_mul_add_bound (by linarith [Real.neg_one_le_cos φ])
      (by linarith [Real.cos_le_one φ]) (Real.abs_sin_le_one φ) (by norm_num [dropS])
  have ha1 : (1 : ℝ) ≤ (2 : ℝ) ^ (1 / 3 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
  have hb1 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 / 3 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
  rw [boxNorm_drop]
  exact max_lt (max_lt hw2 (lt_of_le_of_lt (div_le_self (abs_nonneg _) ha1) hw1))
    (lt_of_le_of_lt (div_le_self (abs_nonneg _) hb1) hw0)

/-- The three coordinates of `dropVec (torusMap θ π)`, where the meridian circle has horizontal
radius `1`. -/
theorem dropVec_meridian_coord_zero (θ : ℝ) :
    (dropVec (Work.Core.torusMap θ Real.pi)).ofLp 0 =
      (-(2 / 25) : ℝ) * Real.cos θ + (-(39 / 100)) * Real.sin θ := by
  rw [dropVec_coord_zero, Work.CoreTopology.torusMap_apply_zero,
    Work.CoreTopology.torusMap_apply_one, Work.CoreTopology.torusMap_apply_two,
    Real.cos_pi, Real.sin_pi]
  ring

theorem dropVec_meridian_coord_one (θ : ℝ) :
    (dropVec (Work.Core.torusMap θ Real.pi)).ofLp 1 =
      (81 / 100 : ℝ) * Real.cos θ + (53 / 50) * Real.sin θ := by
  rw [dropVec_coord_one, Work.CoreTopology.torusMap_apply_zero,
    Work.CoreTopology.torusMap_apply_one, Work.CoreTopology.torusMap_apply_two,
    Real.cos_pi, Real.sin_pi]
  ring

theorem dropVec_meridian_coord_two (θ : ℝ) :
    (dropVec (Work.Core.torusMap θ Real.pi)).ofLp 2 =
      (49 / 100 : ℝ) * Real.cos θ + (31 / 25) * Real.sin θ := by
  rw [dropVec_coord_two, Work.CoreTopology.torusMap_apply_zero,
    Work.CoreTopology.torusMap_apply_one, Work.CoreTopology.torusMap_apply_two,
    Real.cos_pi, Real.sin_pi]
  ring

/-- **The meridian `{φ = π}` lies strictly inside the box**: every point of the meridian circle
`θ ↦ dropVec (torusMap θ π)` has box norm `< dropS`, so the box sphere meets the surface in no
point of that meridian. -/
theorem drop_boxNorm_meridian_lt (θ : ℝ) :
    Submission.boxNorm dropC dropCyc (dropVec (Work.Core.torusMap θ Real.pi)) < dropS := by
  have hw2 : |(dropVec (Work.Core.torusMap θ Real.pi)) 2| < dropS := by
    rw [dropVec_meridian_coord_two θ]
    exact abs_cos_sin_lt (49 / 100) (31 / 25) dropS θ (by norm_num [dropS]) (by norm_num [dropS])
  have hw1 : |(dropVec (Work.Core.torusMap θ Real.pi)) 1| < dropS := by
    rw [dropVec_meridian_coord_one θ]
    exact abs_cos_sin_lt (81 / 100) (53 / 50) dropS θ (by norm_num [dropS]) (by norm_num [dropS])
  have hw0 : |(dropVec (Work.Core.torusMap θ Real.pi)) 0| < dropS := by
    rw [dropVec_meridian_coord_zero θ]
    exact abs_cos_sin_lt (-(2 / 25)) (-(39 / 100)) dropS θ (by norm_num [dropS])
      (by norm_num [dropS])
  have ha1 : (1 : ℝ) ≤ (2 : ℝ) ^ (1 / 3 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
  have hb1 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 / 3 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
  rw [boxNorm_drop]
  exact max_lt (max_lt hw2 (lt_of_le_of_lt (div_le_self (abs_nonneg _) ha1) hw1))
    (lt_of_le_of_lt (div_le_self (abs_nonneg _) hb1) hw0)

/-! ## The box-sphere trace carries no essential loop -/

theorem sphereTrace_inessential_drop :
    ¬ (Work.Smooth.Morse.torus Work.BoxShrink.PinchOff.RefuteDrop.dropDiffeo).ContainsEssentialLoop
      (Work.BoxShrink.Core.sphereSet Work.BoxShrink.PinchOff.RefuteDrop.dropC
        Work.BoxShrink.PinchOff.RefuteDrop.dropCyc
        Work.BoxShrink.PinchOff.RefuteDrop.dropS) := by
  rintro ⟨γ, ⟨L, hL⟩, hmem⟩
  -- A lift of a curve of the sphere trace has image on the box sphere.
  have hbn : ∀ t : ℝ, Submission.boxNorm dropC dropCyc
      (dropVec (Work.Core.torusMap (L.Θ t) (L.Φ t))) = dropS := by
    intro t
    have h := hmem t
    rw [Work.BoxShrink.Core.mem_sphereSet] at h
    have heq : dropVec (Work.Core.torusMap (L.Θ t) (L.Φ t)) = γ.γ t := by
      rw [← L.lifts t, Work.Smooth.Morse.torus_psi, param_dropDiffeo]
    rwa [← heq] at h
  -- Hence neither parameter hits its forbidden grid line.
  have hTheta : ∀ t : ℝ, ∀ k : ℤ, L.Θ t ≠ dropTheta + (k : ℝ) * (2 * Real.pi) := by
    intro t k hk
    have h1 := hbn t
    rw [hk, torusMap_add_int_mul_two_pi_left] at h1
    exact absurd h1 (ne_of_lt (drop_boxNorm_longitude_lt (L.Φ t)))
  have hPhi : ∀ t : ℝ, ∀ k : ℤ, L.Φ t ≠ Real.pi + (k : ℝ) * (2 * Real.pi) := by
    intro t k hk
    have h1 := hbn t
    rw [hk, torusMap_add_int_mul_two_pi_right] at h1
    exact absurd h1 (ne_of_lt (drop_boxNorm_meridian_lt (L.Θ t)))
  have h1 : (L.winding).1 = 0 :=
    Work.BoxShrink.PinchOff.int_eq_zero_of_notMem_lattice L.contΘ hTheta
      (by linarith [(L.winding_spec).1])
  have h2 : (L.winding).2 = 0 :=
    Work.BoxShrink.PinchOff.int_eq_zero_of_notMem_lattice L.contΦ hPhi
      (by linarith [(L.winding_spec).2])
  exact hL (Prod.ext h1 h2)

end

end Work.BoxShrink.PinchOff.RefuteDrop
