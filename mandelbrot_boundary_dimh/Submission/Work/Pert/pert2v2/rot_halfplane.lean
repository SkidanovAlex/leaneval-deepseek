import Mathlib

namespace Work.Pert.pert2v2

open Set Metric Filter Topology

/-- Imaginary part of the affine map `z ↦ -i z - i y₁`. -/
private lemma im_rot_affine (z : ℂ) (y₁ : ℝ) :
    (-(Complex.I * z) - (y₁ : ℂ) * Complex.I).im = -z.re - y₁ := by simp

/-- The affine map `rot y₁ : z ↦ -i z - i y₁` maps the closed right half plane exactly onto the
closed half plane `{w | w.im ≤ -y₁}`; in particular the open right half plane lands in the open
half plane `{w | w.im < -y₁}`, where (by hypothesis) `h` is holomorphic. -/
private lemma rot_affine_image (y₁ : ℝ) :
    (∀ z : ℂ, 0 < z.re → (-(Complex.I * z) - (y₁ : ℂ) * Complex.I).im < -y₁) ∧
      (∀ w : ℂ, w.im ≤ -y₁ →
        ∃ z : ℂ, 0 ≤ z.re ∧ -(Complex.I * z) - (y₁ : ℂ) * Complex.I = w) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    rw [im_rot_affine]; linarith
  · intro w hw
    refine ⟨-(w.im + y₁) + w.re * Complex.I, ?_, ?_⟩
    · have hre : (-(w.im + y₁) + w.re * Complex.I).re = -(w.im + y₁) := by simp
      rw [hre]; linarith
    · refine Complex.ext ?_ ?_ <;> simp

/-- **Rotation to the right half plane.**  A function `h` holomorphic and bounded by `M` on the
closed half plane `{w | w.im ≤ -y₁}` can be rotated to a function `F` on the closed right half
plane `{z | 0 ≤ z.re}` with the same bound on the open half plane, the boundary values
`F (i x) = h (x - i y₁)`, and such that `F` still takes every value of `h` on the closed half
plane (attained at `z = -(w.im + y₁) + i w.re`, i.e. `w = -i z - i y₁`).

This is the elementary "the two half planes are the same half plane up to a rotation" step used
in the perturbation argument. -/
theorem rot_halfplane {h : ℂ → ℂ} {y₁ M : ℝ}
    (hd : ∀ w : ℂ, w.im ≤ -y₁ → DifferentiableAt ℂ h w)
    (hbdd : ∀ w : ℂ, w.im ≤ -y₁ → ‖h w‖ ≤ M) :
    ∃ F : ℂ → ℂ, DiffContOnCl ℂ F {z : ℂ | 0 < z.re} ∧ (∀ z : ℂ, 0 < z.re → ‖F z‖ ≤ M) ∧
      (∀ x : ℝ, F ((x : ℂ) * Complex.I) = h ((x : ℂ) - (y₁ : ℂ) * Complex.I)) ∧
      (∀ w : ℂ, w.im ≤ -y₁ → ∃ z : ℂ, 0 ≤ z.re ∧ F z = h w) := by
  obtain ⟨hopen, hsurj⟩ := rot_affine_image y₁
  refine ⟨fun z => h (-(Complex.I * z) - (y₁ : ℂ) * Complex.I), ?_, ?_, ?_, ?_⟩
  · -- differentiability on the open right half plane and continuity on its closure
    refine ⟨?_, ?_⟩
    · intro z hz
      have hzr : 0 < z.re := hz
      have hle : (-(Complex.I * z) - (y₁ : ℂ) * Complex.I).im ≤ -y₁ :=
        le_of_lt (hopen z hzr)
      exact ((hd _ hle).comp z (by fun_prop :
        DifferentiableAt ℂ (fun z : ℂ => -(Complex.I * z) - (y₁ : ℂ) * Complex.I) z)).differentiableWithinAt
    · -- `closure {Re z > 0} ⊆ {Re z ≥ 0}`, on which `F` is even continuous everywhere
      have hsub : {z : ℂ | 0 < z.re} ⊆ {z : ℂ | 0 ≤ z.re} :=
        fun z hz => le_of_lt (show (0 : ℝ) < z.re from hz)
      have hclosed : IsClosed {z : ℂ | 0 ≤ z.re} :=
        isClosed_le continuous_const Complex.continuous_re
      refine ContinuousOn.mono ?_ (closure_minimal hsub hclosed)
      intro z hz
      have hzr : 0 ≤ z.re := hz
      have hle : (-(Complex.I * z) - (y₁ : ℂ) * Complex.I).im ≤ -y₁ := by
        rw [im_rot_affine]; linarith
      have h1 : ContinuousAt (fun z : ℂ => -(Complex.I * z) - (y₁ : ℂ) * Complex.I) z := by
        fun_prop
      have h2 : ContinuousAt h ((fun z : ℂ => -(Complex.I * z) - (y₁ : ℂ) * Complex.I) z) :=
        (hd _ hle).continuousAt
      exact (ContinuousAt.comp (f := fun z : ℂ => -(Complex.I * z) - (y₁ : ℂ) * Complex.I)
        (x := z) h2 h1).continuousWithinAt
  · -- the bound `M` transfers along the rotation
    intro z hz
    exact hbdd _ (le_of_lt (hopen z hz))
  · -- boundary values on the imaginary axis
    intro x
    refine congrArg h ?_
    refine Complex.ext ?_ ?_ <;> simp
  · -- surjectivity onto the values of `h` on the closed half plane
    intro w hw
    obtain ⟨z, hz, hzw⟩ := hsurj w hw
    exact ⟨z, hz, congrArg h hzw⟩

end Work.Pert.pert2v2
