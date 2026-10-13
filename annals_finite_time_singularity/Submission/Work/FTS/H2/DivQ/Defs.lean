/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `x = sin(2θ)` coordinate and the operator `G` behind `DivisionBySin` in the interior class

`Work.FTS.H2.DivSinQ` needs Elgindi's Proposition `DivisionBySin` for the *interior* class
`Work.FTS.Nonlin.RegQ` (smooth on the open quadrant), where the per-slice regularity facts of the
`SmoothNbhd` world (`Work.Elliptic.DivSinSliceBdd` and friends: `|D_θ^i(Φ/sin 2θ)| ≤ C s²`,
etc.) are simply false -- a slice may behave like `s^{δ}` with `δ` just above `(γ-1)/2`, so
`D_θ^i(Φ/sin 2θ)` blows up like `s^{δ-1}`.  The intended route is the paper's own: *substitute*

  `x = sin(2θ)`,   `θ = arcsin(x)/2 = thetaOf x`,

so that the angular operator becomes the *Euler operator*:

  `D_θ = sin(2θ) ∂_θ ↦ G = 2 κ(x) · (x ∂_x)`,   `κ x = cos(2 θ(x)) = √(1-x²)`,

and the division `Φ/sin(2θ)` becomes `Φ/x` -- exactly the shape of the paper's Lemma 2 of
tex 1301 (`∫ x^{2k-γ}(∂_x^k(f/x))² ≤ ∫ x^{2k-γ}(∂_x^{k+1}f)²`), whose constant is sharp.  Since
`κ` vanishes at `x = 1` (i.e. `θ = π/4`), the substitution is only used on the *near* region
`x ≤ x₁ = 1/√2` (`θ ≤ π/8`), where `κ ≥ 1/√2`; the far region is its mirror image under
`θ ↦ π/2 - θ` and the middle `[π/8, 3π/8]` is handled by a crude pointwise recursion.

This file contains only the resulting vocabulary:

* `thetaOf`, `xOf`, `kappa`, `xNear`;
* `sliceX h`, the `x`-coordinate version of a slice `h : ℝ → ℝ`;
* `Gop`, the transport of `D_θ` to the `x`-variable;
* `bCoeff` and `aCoeff`, the coefficients of the two expansions
  `G^i u = Σ_j b i j · x^j ∂_x^j u` and `G^i (2κ ∂_x f) = Σ_l a i l · x^l ∂_x^{l+1} f`.

The key properties proved in the sibling files are

* `DthIter i h (thetaOf x) = Gop^[i] (sliceX h) x` (`DthIter_sliceX`), which transports every
  angular derivative of a slice to the `x`-variable;
* the two expansions above (`bCoeff_expansion`, `aCoeff_expansion`), which turn the *left* side
  `D_θ^i(Φ/sin 2θ)` into `Σ_j b i j x^j ∂_x^j (Φ/x)` and the *right* side `D_θ^i(∂_θΦ)` into
  `Σ_l a i l x^l ∂_x^{l+1}(Φ∘thetaOf)`;
* the *vanishing order* `x² ∣ aCoeff i 0` (`aCoeff_zero_dvd`), the only structural fact about the
  coefficients that is not merely boundedness: it makes the `l = 0` correction in the inversion
  harmless, its effective weight `x^{4-γ}` being controlled by the `η`-weighted data
  (`x^{4-γ} ≤ x^{-η}` for `x ≤ 1`, `η = 99/100`, `γ = 1+α/10 ≤ 1.1`).
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.DivQ

set_option autoImplicit false

/-- The right end `x₁ = sin(π/4) = 1/√2` of the *near* region `(0,x₁]` (`θ ∈ (0,π/8]`), where the
substitution `x = sin(2θ)` has `κ x = √(1-x²) ≥ 1/√2`. -/
def xNear : ℝ := Real.sin (Real.pi / 4)

/-- The angular substitution `θ ↦ x = sin(2θ)`. -/
def xOf (θ : ℝ) : ℝ := Real.sin (2 * θ)

/-- Its inverse `x ↦ θ = arcsin(x)/2` on `(-1,1)`. -/
def thetaOf (x : ℝ) : ℝ := Real.arcsin x / 2

/-- The `x`-coordinate version of a slice `h`: `x ↦ h (arcsin(x)/2)`. -/
def sliceX (h : ℝ → ℝ) : ℝ → ℝ := fun x => h (thetaOf x)

/-- `κ x = cos(2 θ(x))`, the factor relating `D_θ = sin(2θ)∂_θ` to `x ∂_x`; on `(-1,1)` it is
`√(1-x²)`. -/
def kappa (x : ℝ) : ℝ := Real.cos (2 * thetaOf x)

/-- The operator `G u = 2κ · x ∂_x u`: the transport of `D_θ` to the `x`-variable. -/
def Gop (u : ℝ → ℝ) : ℝ → ℝ := fun x => 2 * kappa x * (x * deriv u x)

/-- The coefficients of the expansion `G^i u = Σ_{j} b i j · x^j ∂_x^j u`:
`b 0 0 = 1`, `b 0 j = 0` for `j ≠ 0`, and

  `b (i+1) j = 2κ · (x · (b i j)' + j · b i j) + (if j = 0 then 0 else 2κ · b i (j-1))`,

the first term coming from `2κ x ∂_x` acting on the coefficient and the `x^j ∂_x^j` factor, the
second from `∂_x` falling on `∂_x^j u`. -/
def bCoeff : ℕ → ℕ → ℝ → ℝ
  | 0, j => fun _ => if j = 0 then 1 else 0
  | (i + 1), j => fun x =>
      2 * kappa x * (x * deriv (bCoeff i j) x + (j : ℝ) * bCoeff i j x)
        + (if j = 0 then 0 else 2 * kappa x * bCoeff i (j - 1) x)

/-- The coefficients of the expansion `G^i (2κ ∂_x f) = Σ_{l} a i l · x^l ∂_x^{l+1} f`; the
recursion is the same as for `bCoeff` but with the initial datum `a 0 0 = 2κ`, which is the
`x`-form of `∂_θ h = 2 cos(2θ) ∂_x (h∘thetaOf)`. -/
def aCoeff : ℕ → ℕ → ℝ → ℝ
  | 0, j => fun x => if j = 0 then 2 * kappa x else 0
  | (i + 1), j => fun x =>
      2 * kappa x * (x * deriv (aCoeff i j) x + (j : ℝ) * aCoeff i j x)
        + (if j = 0 then 0 else 2 * kappa x * aCoeff i (j - 1) x)

@[simp] theorem bCoeff_zero_zero : bCoeff 0 0 = fun _ => (1 : ℝ) := rfl
@[simp] theorem aCoeff_zero_zero : aCoeff 0 0 = fun x => 2 * kappa x := rfl

end Work.FTS.H2.DivQ
