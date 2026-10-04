import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The trigonometric model function of the differentiable sphere theorem (area C)

This module introduces the one-variable **model function**

`modelF a u κ s = arccos (cos a * cos (u * s) + sin a * sin (u * s) * κ)`

together with its "cosine" `modelG`, the closed form `modelD` of `deriv modelG`, and the
closed form `modelW` of `deriv modelF` on the open set where `modelG` avoids `±1`.

The point of the model is a Jacobi/Hessian comparison in the model space of curvature `κ`:
the second derivative of the model angle at `0` is `cot a * (u ^ 2 - (u * κ) ^ 2)`
(see `Work.Diff.C.model_deriv`).

Nothing here is a `sorry`.
-/

namespace Work.Diff.C

noncomputable section

/-- The cosine of the model angle: `cos a * cos (u * s) + sin a * sin (u * s) * κ`. -/
def modelG (a u κ : ℝ) : ℝ → ℝ :=
  fun s => Real.cos a * Real.cos (u * s) + Real.sin a * Real.sin (u * s) * κ

/-- The derivative of `modelG`, in closed form. -/
def modelD (a u κ : ℝ) : ℝ → ℝ :=
  fun s => u * (-(Real.cos a) * Real.sin (u * s) + Real.sin a * κ * Real.cos (u * s))

/-- The model angle `arccos (modelG a u κ s)`. -/
def modelF (a u κ : ℝ) : ℝ → ℝ :=
  fun s => Real.arccos (modelG a u κ s)

/-- The closed form of `deriv (modelF a u κ)` on the set where `modelG` avoids `±1`. -/
def modelW (a u κ : ℝ) : ℝ → ℝ :=
  fun s => -(modelD a u κ s) / Real.sqrt (1 - (modelG a u κ s) ^ 2)

lemma modelG_apply (a u κ s : ℝ) :
    modelG a u κ s = Real.cos a * Real.cos (u * s) + Real.sin a * Real.sin (u * s) * κ := rfl

lemma modelD_apply (a u κ s : ℝ) :
    modelD a u κ s = u * (-(Real.cos a) * Real.sin (u * s) + Real.sin a * κ * Real.cos (u * s)) :=
  rfl

lemma modelF_apply (a u κ s : ℝ) :
    modelF a u κ s = Real.arccos (Real.cos a * Real.cos (u * s) + Real.sin a * Real.sin (u * s) * κ) :=
  rfl

/-- `modelG a u κ` is differentiable everywhere, with derivative `modelD a u κ`. -/
lemma modelG_hasDerivAt (a u κ s : ℝ) : HasDerivAt (modelG a u κ) (modelD a u κ s) s := by
  have hlin : HasDerivAt (fun x : ℝ => u * x) u s := by
    simpa using (hasDerivAt_id s).const_mul u
  have hcos : HasDerivAt (fun x : ℝ => Real.cos (u * x)) (-Real.sin (u * s) * u) s := hlin.cos
  have hsin : HasDerivAt (fun x : ℝ => Real.sin (u * x)) (Real.cos (u * s) * u) s := hlin.sin
  have h1 : HasDerivAt (fun x : ℝ => Real.cos a * Real.cos (u * x))
      (Real.cos a * (-Real.sin (u * s) * u)) s := hcos.const_mul _
  have h2 : HasDerivAt (fun x : ℝ => Real.sin a * Real.sin (u * x))
      (Real.sin a * (Real.cos (u * s) * u)) s := hsin.const_mul _
  have h3 : HasDerivAt (fun x : ℝ => Real.sin a * Real.sin (u * x) * κ)
      ((Real.sin a * (Real.cos (u * s) * u)) * κ) s := h2.mul_const κ
  have h := h1.add h3
  have hv : Real.cos a * (-Real.sin (u * s) * u) + Real.sin a * (Real.cos (u * s) * u) * κ
      = modelD a u κ s := by
    simp only [modelD]; ring
  rw [hv] at h
  convert h using 1
  ext x; simp only [modelG, Pi.add_apply]

/-- `deriv (modelG a u κ) = modelD a u κ`. -/
lemma deriv_modelG (a u κ : ℝ) : deriv (modelG a u κ) = modelD a u κ := by
  funext s
  exact (modelG_hasDerivAt a u κ s).deriv

/-- The derivative of `modelD a u κ` at `0` is `-(u ^ 2 * cos a)`. -/
lemma modelD_hasDerivAt_zero (a u κ : ℝ) : HasDerivAt (modelD a u κ) (-(u ^ 2 * Real.cos a)) 0 := by
  have hlin : HasDerivAt (fun x : ℝ => u * x) u 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).const_mul u
  have hcos : HasDerivAt (fun x : ℝ => Real.cos (u * x)) (-Real.sin (u * 0) * u) 0 := hlin.cos
  have hsin : HasDerivAt (fun x : ℝ => Real.sin (u * x)) (Real.cos (u * 0) * u) 0 := hlin.sin
  have hA : HasDerivAt (fun x : ℝ => -(Real.cos a) * Real.sin (u * x))
      (-(Real.cos a) * (Real.cos (u * 0) * u)) 0 := hsin.const_mul _
  have hB : HasDerivAt (fun x : ℝ => Real.sin a * κ * Real.cos (u * x))
      ((Real.sin a * κ) * (-Real.sin (u * 0) * u)) 0 := hcos.const_mul _
  have hinner := hA.add hB
  have h := hinner.const_mul u
  have hv : u * (-(Real.cos a) * (Real.cos (u * 0) * u) + (Real.sin a * κ) * (-Real.sin (u * 0) * u))
      = -(u ^ 2 * Real.cos a) := by
    rw [mul_zero, Real.cos_zero, Real.sin_zero]; ring
  rw [hv] at h
  convert h using 1
  ext y; simp only [modelD, Pi.add_apply]

lemma modelG_zero (a u κ : ℝ) : modelG a u κ 0 = Real.cos a := by
  simp [modelG]

lemma modelD_zero (a u κ : ℝ) : modelD a u κ 0 = u * (Real.sin a * κ) := by
  simp [modelD]

end

end Work.Diff.C
