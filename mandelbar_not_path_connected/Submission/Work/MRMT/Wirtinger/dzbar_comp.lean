import Mathlib
import Submission.Work.MRMT.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Wirtinger `∂̄` chain rule

`Work.MRMT.dz` and `Work.MRMT.dzbar` are computed from the *real* Fréchet derivative
(`Submission/Work/MRMT/Basic.lean`).  The point of this file is the chain rule for `dzbar`
along a composition of merely real-differentiable maps, which is the algebraic engine behind
the composition rule for complex dilatations used in the Ahlfors–Bers theory of the
Mandelbar subproject.

The mathematical content is the standard decomposition of an `ℝ`-linear map `A : ℂ → ℂ` in
terms of its values on the real basis `{1, I}`:

`A v = ((A 1 - I * A I)/2) * v + ((A 1 + I * A I)/2) * star v`   (`fderiv_apply_eq`)

(the two coefficients being precisely `dz` and `dzbar` of the map), together with the
chain rule `fderiv ℝ (g ∘ f) z = (fderiv ℝ g (f z)).comp (fderiv ℝ f z)`.
-/

namespace Work.MRMT.Wirtinger

open Complex

/-- Decomposition of an `ℝ`-linear map `A : ℂ → ℂ` in the basis `{1, I}` of `ℂ` over `ℝ`:
the two coefficients are the "Wirtinger derivatives" `dz` and `dzbar` of `A`. -/
lemma fderiv_apply_eq (A : ℂ →L[ℝ] ℂ) (v : ℂ) :
    A v = ((A 1 - Complex.I * A Complex.I) / 2) * v
        + ((A 1 + Complex.I * A Complex.I) / 2) * star v := by
  rw [Complex.star_def]
  have hv : v = (v.re : ℂ) + (v.im : ℂ) * Complex.I := (Complex.re_add_im v).symm
  have hs : ((v.re : ℝ) : ℂ) = (v.re : ℝ) • (1 : ℂ) := by rw [Complex.real_smul, mul_one]
  have hs2 : ((v.im : ℝ) : ℂ) * Complex.I = (v.im : ℝ) • Complex.I := by rw [Complex.real_smul]
  have h1 : A ((v.re : ℂ)) = (v.re : ℂ) * A 1 := by
    conv_lhs => rw [hs]
    rw [map_smul, Complex.real_smul]
  have h2 : A ((v.im : ℂ) * Complex.I) = (v.im : ℂ) * A Complex.I := by
    conv_lhs => rw [hs2]
    rw [map_smul, Complex.real_smul]
  rw [hv, map_add, h1, h2]
  rw [map_add, map_mul]
  simp only [Complex.conj_ofReal, Complex.conj_I]
  ring_nf
  rw [show Complex.I ^ 2 = -1 by rw [pow_two, Complex.I_mul_I]]
  ring

/-- The Wirtinger `∂̄`-chain rule: for `ℝ`-differentiable `f`, `g`,
`∂̄(g ∘ f) = (∂g ∘ f) · ∂̄f + (∂̄g ∘ f) · conj(∂f)`. -/
theorem dzbar_comp {f g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℝ g (f z))
    (hf : DifferentiableAt ℝ f z) :
    dzbar (g ∘ f) z = dz g (f z) * dzbar f z + dzbar g (f z) * star (dz f z) := by
  have hinner : fderiv ℝ (g ∘ f) z = (fderiv ℝ g (f z)).comp (fderiv ℝ f z) :=
    fderiv_comp z hg hf
  unfold dzbar dz
  rw [hinner, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [fderiv_apply_eq (fderiv ℝ g (f z)) ((fderiv ℝ f z) 1),
      fderiv_apply_eq (fderiv ℝ g (f z)) ((fderiv ℝ f z) Complex.I),
      fderiv_apply_eq (fderiv ℝ f z) 1,
      fderiv_apply_eq (fderiv ℝ f z) Complex.I]
  rw [Complex.star_def]
  simp only [map_add, map_mul, map_sub, map_neg, map_div₀, map_ofNat, map_one, Complex.conj_I]
  ring_nf

end Work.MRMT.Wirtinger
