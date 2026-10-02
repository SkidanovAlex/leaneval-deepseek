import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Wirtinger.dz_comp
import Submission.Work.MRMT.Wirtinger.dzbar_comp

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The composition rule for the complex dilatation along an *anti*-holomorphic map

`Work.MRMT.beltramiOf g z = ∂̄g(z) / ∂g(z)` is the pointwise complex dilatation
(`Submission/Work/MRMT/Basic.lean`).  Along a composite `g ∘ f` the Wirtinger chain rules
(`Submission/Work/MRMT/Wirtinger/dz_comp.lean`, `.../dzbar_comp.lean`) give

`∂(g ∘ f) z = ∂g(f z) · ∂f(z) + ∂̄g(f z) · conj (∂̄f(z))`,
`∂̄(g ∘ f) z = ∂g(f z) · ∂̄f(z) + ∂̄g(f z) · conj (∂f(z))`.

When `f` is **anti-holomorphic** at `z` — that is, `star ∘ f` is complex differentiable
at `z` — its `∂`-derivative vanishes while its `∂̄`-derivative is the complex conjugate of
the derivative of `star ∘ f` (this file proves the vanishing part, which is all the
computation needs).  Both chain-rule expressions then become single products, and the
resulting identity

`μ_{g∘f}(z) = μ_g(f z)⁻¹ · (conj (∂̄f z) / ∂̄f z)⁻¹`

is the usual transformation rule for the `∂̄`-equation when the coordinate change is
orientation reversing.  The identity holds *unconditionally* with the junk-value
convention `0⁻¹ = 0` used by `beltramiOf`; the hypotheses `h0`, `h1` of the requested
statement are therefore not needed by the algebraic rearrangement.

The case in which `f` is holomorphic (`beltramiOf_comp_holo`) is obtained by the same
two chain rules with `∂̄f = 0` instead.
-/

open Complex Function

namespace Work.MRMT.Wirtinger

/-! ## The conjugation `star` as a smooth real map -/

/-- The real Fréchet derivative of `star : ℂ → ℂ` (complex conjugation) at any point is
the conjugation `ℝ`-linear isometry `Complex.conjCLE` itself. -/
lemma fderiv_star (w : ℂ) : fderiv ℝ (star : ℂ → ℂ) w = (↑Complex.conjCLE : ℂ →L[ℝ] ℂ) := by
  have hfun : (star : ℂ → ℂ) = ⇑Complex.conjCLE := by funext z; simp
  rw [hfun, Complex.conjCLE.fderiv]

/-- Conjugation `star : ℂ → ℂ` is real differentiable everywhere. -/
lemma differentiableAt_star (w : ℂ) : DifferentiableAt ℝ (star : ℂ → ℂ) w := by
  have hfun : (star : ℂ → ℂ) = ⇑Complex.conjCLE := by funext z; simp
  rw [hfun]; exact Complex.conjCLE.differentiableAt

/-- `∂ star = 0`: conjugation is anti-holomorphic. -/
lemma dz_star (w : ℂ) : dz (star : ℂ → ℂ) w = 0 := by
  simp only [dz]
  rw [fderiv_star]
  simp

/-- `∂̄ star = 1`. -/
lemma dzbar_star (w : ℂ) : dzbar (star : ℂ → ℂ) w = 1 := by
  simp only [dzbar]
  rw [fderiv_star]
  simp

/-! ## The Wirtinger derivatives of a holomorphic / anti-holomorphic map -/

/-- A map that is complex differentiable at `z` has vanishing `∂̄`: `∂̄ h z = 0`. -/
lemma dzbar_of_holo {h : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ h z) : dzbar h z = 0 := by
  have hd : HasDerivAt h (deriv h z) z := by simpa using hf.hasFDerivAt.hasDerivAt
  have hf' : fderiv ℝ h z = deriv h z • (1 : ℂ →L[ℝ] ℂ) := hd.complexToReal_fderiv.fderiv
  simp only [dzbar, hf', smul_apply, one_apply_eq_self, smul_eq_mul, mul_one]
  ring_nf
  rw [pow_two, Complex.I_mul_I]
  ring

/-- An anti-holomorphic map (`star ∘ f` complex differentiable at `z`) is real
differentiable at `z`. -/
lemma differentiableAt_of_antiholo {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ (star ∘ f) z) : DifferentiableAt ℝ f z := by
  have h1 : DifferentiableAt ℝ (star ∘ f) z := hf.restrictScalars ℝ
  have h2 : DifferentiableAt ℝ (star ∘ (star ∘ f)) z :=
    (differentiableAt_star ((star ∘ f) z)).comp z h1
  have hfeq : star ∘ (star ∘ f) = f := by funext x; simp
  rwa [hfeq] at h2

/-- An anti-holomorphic map has vanishing `∂`: `∂ f z = 0`. -/
lemma dz_of_antiholo {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ (star ∘ f) z) :
    dz f z = 0 := by
  have hcomp : DifferentiableAt ℝ (star ∘ f) z := hf.restrictScalars ℝ
  have hcr := dz_comp (f := star ∘ f) (g := (star : ℂ → ℂ))
      (differentiableAt_star ((star ∘ f) z)) hcomp
  rw [dz_star, dzbar_star, dzbar_of_holo hf, star_zero] at hcr
  simp only [zero_mul, mul_zero, add_zero] at hcr
  have hfeq : star ∘ (star ∘ f) = f := by funext x; simp
  rwa [hfeq] at hcr

/-! ## The composition rule -/

set_option linter.unusedVariables false in
theorem beltramiOf_comp_antiholo {f g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℝ g (f z))
    (hf : DifferentiableAt ℂ (star ∘ f) z) (h0 : beltramiOf g (f z) ≠ 0)
    (h1 : dzbar f z ≠ 0) :
    beltramiOf (g ∘ f) z = (beltramiOf g (f z))⁻¹ * (star (dzbar f z) / dzbar f z)⁻¹ := by
  have hfr : DifferentiableAt ℝ f z := differentiableAt_of_antiholo hf
  have hb : dz f z = 0 := dz_of_antiholo hf
  simp only [beltramiOf]
  rw [dzbar_comp hg hfr, dz_comp hg hfr, hb, star_zero]
  simp only [mul_zero, zero_add, add_zero]
  rw [inv_div, inv_div, div_mul_div_comm]

end Work.MRMT.Wirtinger
