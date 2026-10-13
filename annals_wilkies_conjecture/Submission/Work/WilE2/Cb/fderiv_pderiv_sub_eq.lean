import Mathlib

/-!
# The quotient rule for the logarithmic derivative of a `C²` function

The main statement rewrites the derivative of
`y ↦ ∂_j F y - (∂_j F x / ∂_i F x) * ∂_i F y`
as `∂_i F x` times the derivative of the quotient `y ↦ ∂_j F y / ∂_i F y`.

The key input is the general lemma `fderiv_sub_const_mul_eq_smul_fderiv_div`, which holds for
arbitrary real normed spaces and real valued functions: for differentiable `g` and `h` with
`h x ≠ 0`,
`fderiv ℝ (fun y => g y - (g x / h x) * h y) x = h x • fderiv ℝ (fun y => g y / h y) x`.
It is proved by applying the product rule to `(g / h) * h`, which agrees with `g` near `x`
because `h` is nonzero there.
-/

namespace Work.WilE2.Cb

open Filter
open scoped Topology

/-- For differentiable real-valued functions `g`, `h` on a real normed space, with `h x ≠ 0`,
the derivative of `y ↦ g y - (g x / h x) * h y` at `x` equals `h x` times the derivative of
`y ↦ g y / h y` at `x`. -/
lemma fderiv_sub_const_mul_eq_smul_fderiv_div {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g h : E → ℝ} {x : E} (hg : DifferentiableAt ℝ g x)
    (hh : DifferentiableAt ℝ h x) (hhx : h x ≠ 0) :
    fderiv ℝ (fun y => g y - (g x / h x) * h y) x
      = (h x) • fderiv ℝ (fun y => g y / h y) x := by
  -- The quotient `g / h` is differentiable at `x`, being the product of `g` and the
  -- reciprocal of `h`.
  have hd : DifferentiableAt ℝ (fun y => g y / h y) x := hg.mul (hh.inv hhx)
  -- Product rule for `(g / h) * h`.
  have hprod : fderiv ℝ (fun y => g y / h y * h y) x
      = (g x / h x) • fderiv ℝ h x + (h x) • fderiv ℝ (fun y => g y / h y) x :=
    fderiv_mul hd hh
  -- Near `x` the function `h` does not vanish.
  have hcont : ∀ᶠ y in 𝓝 x, h y ≠ 0 := hh.continuousAt.eventually_ne hhx
  -- Hence `(g / h) * h` agrees with `g` near `x`.
  have heq : (fun y => g y / h y * h y) =ᶠ[𝓝 x] g := by
    filter_upwards [hcont] with y hy
    exact div_mul_cancel₀ (g y) hy
  have hgf : fderiv ℝ g x
      = (g x / h x) • fderiv ℝ h x + (h x) • fderiv ℝ (fun y => g y / h y) x :=
    heq.fderiv_eq.symm.trans hprod
  -- Rearranging gives the derivative of the quotient.
  have hkey : (h x) • fderiv ℝ (fun y => g y / h y) x
      = fderiv ℝ g x - (g x / h x) • fderiv ℝ h x := by
    rw [hgf, add_sub_cancel_left]
  -- The derivative of the affine-in-`h` expression.
  have hL : fderiv ℝ (fun y => g y - (g x / h x) * h y) x
      = fderiv ℝ g x - (g x / h x) • fderiv ℝ h x := by
    rw [show (fun y => g y - (g x / h x) * h y)
          = (g - fun y => (g x / h x) * h y) from rfl]
    rw [fderiv_sub hg (hh.const_mul (g x / h x)), fderiv_const_mul hh (g x / h x)]
  rw [hL, hkey]

theorem fderiv_pderiv_sub_eq {m : ℕ} (F : (Fin (m+1) → ℝ) → ℝ) (hF : ContDiff ℝ 2 F)
    (i j : Fin (m+1)) {x : Fin (m+1) → ℝ} (hx : fderiv ℝ F x (Pi.single i 1) ≠ 0) :
    fderiv ℝ (fun y => fderiv ℝ F y (Pi.single j 1)
        - (fderiv ℝ F x (Pi.single j 1) / fderiv ℝ F x (Pi.single i 1))
          * fderiv ℝ F y (Pi.single i 1)) x
      = (fderiv ℝ F x (Pi.single i 1)) •
        fderiv ℝ (fun y => fderiv ℝ F y (Pi.single j 1) / fderiv ℝ F y (Pi.single i 1)) x := by
  -- `F` is `C²`, so the first partial derivatives `y ↦ ∂_k F y` are differentiable.
  have hg : DifferentiableAt ℝ (fun y => fderiv ℝ F y (Pi.single j 1)) x := by fun_prop
  have hh : DifferentiableAt ℝ (fun y => fderiv ℝ F y (Pi.single i 1)) x := by fun_prop
  exact fderiv_sub_const_mul_eq_smul_fderiv_div hg hh hx

end Work.WilE2.Cb
