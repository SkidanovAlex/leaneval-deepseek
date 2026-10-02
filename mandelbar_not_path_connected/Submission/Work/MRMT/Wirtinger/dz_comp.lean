import Mathlib
import Submission.Work.MRMT.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Chain rule for the Wirtinger derivative `∂/∂z`

`Work.MRMT.dz` and `Work.MRMT.dzbar` are computed from the *real* Fréchet derivative,
so the chain rule for `fderiv ℝ` reduces the composition formula to a purely linear
algebraic statement about `ℝ`-linear maps `ℂ → ℂ`: such a map `A` is determined by its
values on `1` and on `i`, and

`A w = ((A 1 - i A i)/2) * w + ((A 1 + i A i)/2) * star w`  for every `w : ℂ`

(`star` is complex conjugation).  Applying this to `A = Dg(f z)` and to the two arguments
`Df(z)(1)`, `Df(z)(i)` yields the chain rule

`∂(g ∘ f)(z) = ∂g(f z) · ∂f(z) + ∂̄g(f z) · conj (∂̄f(z))`.
-/

namespace Work.MRMT.Wirtinger

open Complex

/-! ## The linear algebra of the Wirtinger decomposition -/

/-- Secondary (algebraic) form of `realLinearMap_apply_eq`: the right-hand side of the
decomposition formula, written in coordinates `x = re w`, `y = im w`. -/
theorem lin_decomp (x y p q : ℂ) :
    x * p + y * q =
      ((p - Complex.I * q) / 2) * (x + y * Complex.I)
        + ((p + Complex.I * q) / 2) * (x - y * Complex.I) := by
  ring_nf
  rw [pow_two, Complex.I_mul_I]
  ring

/-- For a real-linear `A : ℂ →L[ℝ] ℂ` and real `x y`,
`A (x + i y) = ((A 1 - i A i)/2) * (x + i y) + ((A 1 + i A i)/2) * (x - i y)`. -/
theorem realLinearMap_apply_eq_coord (A : ℂ →L[ℝ] ℂ) (x y : ℝ) :
    A ((x : ℂ) + (y : ℂ) * Complex.I) =
      ((A 1 - Complex.I * A Complex.I) / 2) * ((x : ℂ) + (y : ℂ) * Complex.I)
        + ((A 1 + Complex.I * A Complex.I) / 2) * ((x : ℂ) - (y : ℂ) * Complex.I) := by
  have hA : A ((x : ℂ) + (y : ℂ) * Complex.I) =
      (x : ℝ) • A 1 + (y : ℝ) • A (Complex.I : ℂ) := by
    have h1 : ((x : ℂ) + (y : ℂ) * Complex.I) =
        (x : ℝ) • (1 : ℂ) + (y : ℝ) • (Complex.I : ℂ) := by
      rw [Complex.real_smul, Complex.real_smul, mul_one]
    rw [h1, map_add, map_smul, map_smul]
  rw [hA, Complex.real_smul, Complex.real_smul]
  exact lin_decomp (x : ℂ) (y : ℂ) (A 1) (A Complex.I)

/-- Same as `realLinearMap_apply_eq_coord`, with the conjugation left in place (note
`conj (x + i y) = x - i y`). -/
theorem realLinearMap_apply_eq_coord_star (A : ℂ →L[ℝ] ℂ) (x y : ℝ) :
    A ((x : ℂ) + (y : ℂ) * Complex.I) =
      ((A 1 - Complex.I * A Complex.I) / 2) * ((x : ℂ) + (y : ℂ) * Complex.I)
        + ((A 1 + Complex.I * A Complex.I) / 2) * star ((x : ℂ) + (y : ℂ) * Complex.I) := by
  have hstar : star ((x : ℂ) + (y : ℂ) * Complex.I) = (x : ℂ) - (y : ℂ) * Complex.I := by
    simp [sub_eq_add_neg]
  rw [hstar]
  exact realLinearMap_apply_eq_coord A x y

/-- **A real-linear map `ℂ → ℂ` is determined by its values on `1` and `i`**, in Wirtinger
form: for every `A : ℂ →L[ℝ] ℂ` and every `w : ℂ`,

`A w = ((A 1 - i A i)/2) * w + ((A 1 + i A i)/2) * conj w`.

The two coefficients are exactly the Wirtinger derivatives `dz`/`dzbar` of `A` read as a
map `ℂ → ℂ`. -/
theorem realLinearMap_apply_eq (A : ℂ →L[ℝ] ℂ) (w : ℂ) :
    A w = ((A 1 - Complex.I * A Complex.I) / 2) * w
      + ((A 1 + Complex.I * A Complex.I) / 2) * star w := by
  have hw : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := (Complex.re_add_im w).symm
  rw [hw]
  exact realLinearMap_apply_eq_coord_star A w.re w.im

/-- The chain rule for `dz`, in the form in which it follows directly from the chain rule
for the real Fréchet derivative: for two `ℝ`-linear maps `D E : ℂ →L[ℝ] ℂ`,

`∂(E ∘ D) = ∂E · ∂D + ∂̄E · conj (∂̄D)`,

where `∂A  = (A 1 - i A i)/2` and `∂̄A = (A 1 + i A i)/2`. -/
theorem linearMap_dz_comp (D E : ℂ →L[ℝ] ℂ) :
    (E (D 1) - Complex.I * E (D Complex.I)) / 2 =
      ((E 1 - Complex.I * E Complex.I) / 2) * ((D 1 - Complex.I * D Complex.I) / 2)
        + ((E 1 + Complex.I * E Complex.I) / 2)
            * star ((D 1 + Complex.I * D Complex.I) / 2) := by
  set u : ℂ := (E 1 - Complex.I * E Complex.I) / 2 with hu
  set v : ℂ := (E 1 + Complex.I * E Complex.I) / 2 with hv
  set a : ℂ := (D 1 - Complex.I * D Complex.I) / 2 with ha
  set b : ℂ := (D 1 + Complex.I * D Complex.I) / 2 with hb
  have h1 : E (D 1) = u * D 1 + v * star (D 1) := by
    rw [hu, hv]; exact realLinearMap_apply_eq E (D 1)
  have h2 : E (D Complex.I) = u * (D Complex.I) + v * star (D Complex.I) := by
    rw [hu, hv]; exact realLinearMap_apply_eq E (D Complex.I)
  have hD1 : D 1 = a + b := by rw [ha, hb]; ring
  have hDI : D Complex.I = Complex.I * (a - b) := by
    rw [ha, hb]; ring_nf; rw [pow_two, Complex.I_mul_I]; ring
  have hs1 : star (D 1) = star a + star b := by rw [hD1]; simp
  have hs2 : star (D Complex.I) = -Complex.I * star a + Complex.I * star b := by
    rw [hDI, star_mul]; simp [Complex.conj_I, sub_eq_add_neg]; ring
  rw [h1, h2, hs1, hs2, hD1, hDI]
  ring_nf
  rw [pow_two, Complex.I_mul_I]
  ring

/-! ## The chain rule for `dz` -/

theorem dz_comp {f g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℝ g (f z))
    (hf : DifferentiableAt ℝ f z) :
    dz (g ∘ f) z = dz g (f z) * dz f z + dzbar g (f z) * star (dzbar f z) := by
  have hD : fderiv ℝ (g ∘ f) z = (fderiv ℝ g (f z)).comp (fderiv ℝ f z) :=
    fderiv_comp z hg hf
  rw [dz, dz, dz, dzbar, hD]
  simp only [ContinuousLinearMap.comp_apply]
  exact linearMap_dz_comp (fderiv ℝ f z) (fderiv ℝ g (f z))

end Work.MRMT.Wirtinger
