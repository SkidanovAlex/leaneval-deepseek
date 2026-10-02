import Mathlib
import Submission.Work.Implosion.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Topology

namespace Work.Implosion.Cylinder

/-- If `g` is differentiable at `0` with derivative `lam` and `g 0 = 0`, and `lam` is not real,
then for all sufficiently small positive real `x`, the imaginary part of `g x` is nonzero.
Indeed `g x = lam * x + o(x)`, so its imaginary part is `(im lam) * x + o(x)`, which is
dominated by `(im lam) * x` since `im lam ≠ 0`. -/
theorem exists_im_ne_zero_near_zero (g : ℂ → ℂ) (lam : ℂ)
    (hlam : lam ∉ Set.range ((↑) : ℝ → ℂ)) (hg0 : g 0 = 0) (hg : HasDerivAt g lam 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, x ∈ Set.Ioc 0 r → (g (x : ℂ)).im ≠ 0 := by
  -- `lam` is non-real, so its imaginary part is nonzero
  have hlamim : lam.im ≠ 0 := by
    intro h
    exact hlam ⟨lam.re, Complex.ext rfl h.symm⟩
  -- differentiability gives `g z - g 0 - z * lam = o(z)` at `z = 0`
  have hlittle : (fun z : ℂ => g z - g 0 - (z - 0) • lam) =o[𝓝 0] (fun z : ℂ => z - 0) :=
    hg.isLittleO
  -- restrict to the real axis
  have hcomp : (fun x : ℝ => g (x : ℂ) - g 0 - ((x : ℂ) - 0) • lam) =o[𝓝 (0 : ℝ)]
      (fun x : ℝ => ((x : ℂ) - 0)) :=
    hlittle.comp_tendsto (Complex.continuous_ofReal.tendsto 0)
  have hcomp' : (fun x : ℝ => g (x : ℂ) - g 0 - (x : ℂ) * lam) =o[𝓝 (0 : ℝ)]
      (fun x : ℝ => (x : ℂ)) := by
    simpa using hcomp
  -- extract the quantitative bound: eventually `‖g x - x*lam‖ ≤ (|im lam|/2) * |x|`
  have hev := Asymptotics.IsLittleO.def (c := |lam.im| / 2) hcomp' (by positivity)
  obtain ⟨r0, hr0pos, hr0⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨r0 / 2, by positivity, ?_⟩
  intro x hx him
  have hx0 : 0 < x := hx.1
  have hxr : x ≤ r0 / 2 := hx.2
  have hdist : dist x 0 < r0 := by
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hx0]; linarith
  have hb := hr0 hdist
  have hnorm : ‖(x : ℂ)‖ = |x| := RCLike.norm_ofReal x
  rw [hnorm] at hb
  -- the imaginary part of `g x - x*lam` equals `-(x * im lam)` because `im (g x) = 0`
  have him2 : (g (x : ℂ) - g 0 - (x : ℂ) * lam).im = -(x * lam.im) := by
    rw [Complex.sub_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hg0]
    simp [him]
  have hle : |x * lam.im| ≤ |lam.im| / 2 * |x| := by
    calc |x * lam.im| = |(g (x : ℂ) - g 0 - (x : ℂ) * lam).im| := by rw [him2]; simp
      _ ≤ ‖g (x : ℂ) - g 0 - (x : ℂ) * lam‖ := Complex.abs_im_le_norm _
      _ ≤ |lam.im| / 2 * |x| := hb
  rw [abs_mul] at hle
  nlinarith [abs_pos.mpr hx0.ne', abs_pos.mpr hlamim]

end Work.Implosion.Cylinder
