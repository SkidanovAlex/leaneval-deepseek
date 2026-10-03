import Mathlib
import Submission.Work.KMTPlan.A6.SymToolbox

/-!
# The second partial derivative loses exactly one order of smoothness

`dp2 1 Φ x y = ∂₂Φ(x,y) = deriv (fun t => Φ x t) y` is the first partial derivative of `Φ` in the
**second** variable.  If `Φ`, viewed as a function on `ℝ × ℝ`, is `C^{m+1}`, then
`p ↦ ∂₂Φ(p.1, p.2)` is `C^m`: differentiation in one variable of a `C^{m+1}` function of two
variables costs one order of smoothness.

The formalisation keeps the two variables *separate* rather than bundling `ℝ × ℝ` into one
variable: the auxiliary function

  `F := Function.uncurry (fun p : ℝ × ℝ => fun y : ℝ => Φ p.1 y) : (ℝ × ℝ) × ℝ → ℂ`

is `C^{m+1}` (it is `Φ` composed with the linear map `(p, y) ↦ (p.1, y)`), so that Mathlib's
`ContDiff.fderiv_apply` with `E = ℝ × ℝ`, `F = G = ℝ`(the target being `ℂ`), `g p = p.2` and
`k ≡ 1` gives `ContDiff ℝ m (fun p => (fderiv ℝ (fun y => Φ p.1 y) p.2) 1)`.  Since the domain is
one-dimensional, `fderiv ... 1 = deriv ...` (`fderiv_apply_one_eq_deriv`, which holds by `rfl`),
and `deriv = iteratedDeriv 1` (`iteratedDeriv_one`).
-/

namespace Work.KMTPlan.A6

/-- `∂₂` of a `C^{m+1}` function on `ℝ × ℝ` is `C^m`. -/
theorem SymToolbox_dp2_one_contDiff (Φ : ℝ → ℝ → ℂ) (m : ℕ)
    (hsm : ContDiff ℝ (m + 1) (fun p : ℝ × ℝ => Φ p.1 p.2)) :
    ContDiff ℝ m (fun p : ℝ × ℝ => Work.KMTPlan.A6.dp2 1 Φ p.1 p.2) := by
  -- The map `(p, y) ↦ (p.1, y)` is linear (hence smooth).
  have hL : ContDiff ℝ (m + 1)
      (fun z : (ℝ × ℝ) × ℝ => ((z.1.1, z.2) : ℝ × ℝ)) :=
    (contDiff_fst.comp contDiff_fst).prodMk contDiff_snd
  -- Hence `Φ` composed with it, i.e. `(p, y) ↦ Φ p.1 y`, is `C^{m+1}`.
  have hf : ContDiff ℝ (m + 1)
      (Function.uncurry (fun p : ℝ × ℝ => fun y : ℝ => Φ p.1 y)) :=
    hsm.comp hL
  have hg : ContDiff ℝ m (fun p : ℝ × ℝ => p.2) := contDiff_snd
  have hk : ContDiff ℝ m (fun _ : ℝ × ℝ => (1 : ℝ)) := contDiff_const
  -- Differentiate the second variable: `p ↦ (fderiv ℝ (fun y => Φ p.1 y) p.2) 1`.
  have hmain := ContDiff.fderiv_apply
    (f := fun p : ℝ × ℝ => fun y : ℝ => Φ p.1 y) hf hg hk (le_refl ((m : WithTop ℕ∞) + 1))
  simpa [Work.KMTPlan.A6.dp2, iteratedDeriv_one, fderiv_apply_one_eq_deriv] using hmain

end Work.KMTPlan.A6
