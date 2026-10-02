import Mathlib
import Submission.Work.FQC.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.FQC.ell_homeo` — the MNS twist `ℓ_t` is a homeomorphism of `ℂ`

The twist `ℓ t (x + iy) = x + i (y + t · saw x)` of `Submission/Work/FQC/Defs.lean` fixes the
real part and adds to the imaginary part a continuous function of the real part.  Hence it is a
bijection, with the explicit two-sided inverse

`ellInv t (u + iv) = u + i (v - t · saw u)`,

and both `ell t` and `ellInv t` are continuous; so `ell t` is a homeomorphism of `ℂ`.

The only point that needs care is the continuity of the triangle wave `saw`, which is defined
through `Int.fract` (discontinuous at the integers).  The composition `|fract y - 1/2|` is
nevertheless continuous, because at a jump of `fract` (from `1` to `0`) the two one-sided limits
of `|· - 1/2|` agree; this is exactly Mathlib's `ContinuousOn.comp_fract''`.
-/

noncomputable section

namespace Work.FQC

/-! ## Continuity of the triangle wave `saw` -/

/-- The triangle wave `saw` is continuous: it is the composition of the `1`-periodic extension
of `y ↦ 1/2 - 2 |y - 1/2|` with `x ↦ x + 1/4`. -/
theorem continuous_saw : Continuous saw := by
  have hg : ContinuousOn (fun y : ℝ => (1:ℝ)/2 - 2 * |y - 1/2|) (Set.Icc 0 1) := by
    apply Continuous.continuousOn
    continuity
  have hc := ContinuousOn.comp_fract'' (α := ℝ) (β := ℝ) hg (by norm_num)
  have heq : saw =
      ((fun y : ℝ => (1:ℝ)/2 - 2 * |y - 1/2|) ∘ Int.fract) ∘ (fun x : ℝ => x + 1/4) := by
    funext x
    simp [saw, Function.comp]
  rw [heq]
  exact hc.comp (continuous_id.add continuous_const)

/-! ## The explicit inverse of `ell t` -/

/-- The inverse of the twist `ℓ_t`: it fixes the real part and subtracts `t · saw` of it from
the imaginary part. -/
def ellInv (t : ℝ) (w : ℂ) : ℂ :=
  (w.re : ℂ) + ((w.im - t * saw w.re : ℝ) : ℂ) * Complex.I

theorem ell_ellInv (t : ℝ) (w : ℂ) : ell t (ellInv t w) = w := by
  apply Complex.ext <;> simp [ell, ellInv]

theorem ellInv_ell (t : ℝ) (z : ℂ) : ellInv t (ell t z) = z := by
  apply Complex.ext <;> simp [ell, ellInv]

/-! ## Continuity of `ell t` and of its inverse -/

theorem continuous_ell (t : ℝ) : Continuous (ell t) := by
  have hs : Continuous (fun w : ℂ => saw w.re) := continuous_saw.comp Complex.continuous_re
  have h2 : Continuous (fun w : ℂ => ((t * saw w.re : ℝ) : ℂ) * Complex.I) :=
    (Complex.continuous_ofReal.comp (continuous_const.mul hs)).mul continuous_const
  exact continuous_id.add h2

theorem continuous_ellInv (t : ℝ) : Continuous (ellInv t) := by
  have hs : Continuous (fun w : ℂ => saw w.re) := continuous_saw.comp Complex.continuous_re
  have him : Continuous (fun w : ℂ => (w.im - t * saw w.re : ℝ)) :=
    Complex.continuous_im.sub (continuous_const.mul hs)
  have h2 : Continuous (fun w : ℂ => ((w.im - t * saw w.re : ℝ) : ℂ) * Complex.I) :=
    (Complex.continuous_ofReal.comp him).mul continuous_const
  have h1 : Continuous (fun w : ℂ => (w.re : ℂ)) :=
    Complex.continuous_ofReal.comp Complex.continuous_re
  exact h1.add h2

/-! ## The homeomorphism -/

/-- The twist `ℓ_t` as a homeomorphism of `ℂ`, with inverse `ellInv t`. -/
def ellHomeo (t : ℝ) : ℂ ≃ₜ ℂ :=
  Homeomorph.mk
    { toFun := ell t
      invFun := ellInv t
      left_inv := fun z => ellInv_ell t z
      right_inv := fun w => ell_ellInv t w }
    (continuous_ell t) (continuous_ellInv t)

theorem ell_homeo (t : ℝ) : ∃ e : ℂ ≃ₜ ℂ, ⇑e = Work.FQC.ell t := ⟨ellHomeo t, rfl⟩

end Work.FQC

end
