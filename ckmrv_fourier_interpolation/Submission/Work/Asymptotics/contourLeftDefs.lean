/-
# The left-detour (corrected sign) and the assembled continuation `H`

## Why this module exists

`Work.Asymptotics.detourLeft` (in `continuationDefs.lean`) is *sign-wrong* on its two horizontal
edges.  The path of the left detour replacing the axis interval `I₂ = (c-A, c+A)` (`c = 1/t₀`) is

  `(0, c-A) → (-ξ, c-A) → (-ξ, c+A) → (0, c+A)`

(going up), and the `1`-form is `K(τ,z)e^{iπr²z} dz/i`; on the first edge `dz = -du` and on the
third edge `dz = +du`, so the correct combination of the three edge integrals is

  `- ∫_{0}^{ξ} edgeH(-u, c-A) du  +  ∫_{c-A}^{c+A} edgeV(-ξ, v) dv  +  ∫_{0}^{ξ} edgeH(-u, c+A) du`,

whereas `detourLeft` has the first integral with a `+` and the third with a `-`.  This was
verified numerically: for the entire `1`-form coefficient `g(z) = e^z` and `c = 2, A = 1, ξ = 2`,
the correct combination equals `∫_{c-A}^{c+A} g(it) i dt` (the Cauchy–Goursat statement for a
pole-free rectangle), while `detourLeft`'s combination does not.

`contourLeftC` below is the corrected left detour (with the height `c` of the rectangle as an
explicit argument, which the `t₀⁻¹`-normalisation of `detourLeft` hid), and `contourHC` is the
resulting indented contour: the imaginary axis with `I₁ = (t₀-A₁, t₀+A₁)` and
`I₂ = (t₀⁻¹-A₂, t₀⁻¹+A₂)` removed and replaced by the two **left** detours; because both detours
sweep the half-plane `Re ≤ 0`, they avoid the *removable* coincidence `z = ST⁻¹τ = -1/(τ-1)`
(which has `Re z > 0` when `Re τ < 1`) — the price is that the left detour at height `t₀`
contains the *genuine* pole `z = τ-1` (residue `1/(2π)`), which is compensated by adding the
explicit holomorphic correction `sinSqC r * e^{iπr²(τ-1)}` (`Hleft`).

For `Re τ < 1` the pole is inside the first rectangle, so Cauchy–Goursat with the residue gives
`detourLeftC(c=t₀) = ∫_{I₁} - e^{iπr²(τ-1)}` and (no pole in the second rectangle)
`detourLeftC(c=t₀⁻¹) = ∫_{I₂}`, whence `Hleft = kernelTransform`.
-/
import Mathlib
import Submission.Work.Asymptotics.continuationDefs

noncomputable section

namespace Work.Asymptotics

open UpperHalfPlane MeasureTheory

/-- **The corrected left detour.**  The three sides of the rectangle `[-ξ,0] × [c-A, c+A]`,
traversed upwards (from `(0,c-A)` to `(0,c+A)`), as the `1`-form `K(τ,z)e^{iπr²z} dz/i`.  Note
the signs: `-∫ edgeH(-·, c-A)` (bottom, `dz = -du`) and `+∫ edgeH(-·, c+A)` (top). -/
def detourLeftC (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r c A ξ : ℝ)
    (τ : UpperHalfPlane) : ℂ :=
  - (∫ u in Set.Ioo (0 : ℝ) ξ, edgeH ℓ d r τ (-u) (c - A))
  + (∫ v in Set.Ioo (c - A) (c + A), edgeV ℓ d r τ (-ξ) v)
  + (∫ u in Set.Ioo (0 : ℝ) ξ, edgeH ℓ d r τ (-u) (c + A))

/-- **The corrected indented contour.**  The positive imaginary axis with the two intervals
`I₁ = (t₀-A₁, t₀+A₁)`, `I₂ = (t₀⁻¹-A₂, t₀⁻¹+A₂)` removed and replaced by the left detours
`detourLeftC` at heights `t₀` and `t₀⁻¹`. -/
def contourHC (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r t₀ A₁ ξ₁ A₂ ξ₂ : ℝ)
    (τ : UpperHalfPlane) : ℂ :=
  sinSqC r * (straightPart ℓ d r t₀ A₁ A₂ τ + detourLeftC ℓ d r t₀ A₁ ξ₁ τ
    + detourLeftC ℓ d r t₀⁻¹ A₂ ξ₂ τ)

/-- The residue correction `e^{iπr²(τ-1)} = 2πi·Res_{z=τ-1}(K(τ,z)e^{iπr²z}/i)`. -/
def resCorr (r : ℝ) (τ : UpperHalfPlane) : ℂ :=
  Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2 * ((τ : ℂ) - 1))

/-- **The candidate continuation.**  `contourHC` plus the residue correction; this is the function
that agrees with `kernelTransform` on `{Re τ < 1}` and is holomorphic on the ball. -/
def Hleft (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r t₀ A₁ ξ₁ A₂ ξ₂ : ℝ)
    (τ : UpperHalfPlane) : ℂ :=
  contourHC ℓ d r t₀ A₁ ξ₁ A₂ ξ₂ τ + sinSqC r * resCorr r τ

/-- The closed left rectangle at height `c` and half-widths `A` (vertical) and `ξ` (horizontal,
`Re ≤ 0`). -/
def leftRect (c A ξ : ℝ) (z : UpperHalfPlane) : Prop :=
  -ξ ≤ z.re ∧ z.re ≤ 0 ∧ c - A ≤ z.im ∧ z.im ≤ c + A

/-- The point `τ - 1` of `ℍ`. -/
abbrev tauSubOne (τ : UpperHalfPlane) : UpperHalfPlane := (-1 : ℝ) +ᵥ τ

lemma tauSubOne_coe (τ : UpperHalfPlane) : ((tauSubOne τ : UpperHalfPlane) : ℂ) = (τ : ℂ) - 1 := by
  rw [tauSubOne, UpperHalfPlane.coe_vadd]
  push_cast
  ring

end Work.Asymptotics

namespace Work.Asymptotics

open UpperHalfPlane MeasureTheory

/-- The *removable coincidence* `ST⁻¹ τ = -1/(τ-1)`: for `Re τ < 1` it is the unique point of the
`SL(2,ℤ)`-orbit of `τ` with strictly positive real part near the height `1/Im τ`; the residue of
`z ↦ K(τ,z)` there vanishes (`φ(TS) = 0`), which is why the contour may sweep the half-plane
`Re ≤ 0` around that height. -/
def tauCoinc (τ : UpperHalfPlane) : UpperHalfPlane :=
  (ModularGroup.S * ModularGroup.T⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ

lemma tauCoinc_coe (τ : UpperHalfPlane) :
    ((tauCoinc τ : UpperHalfPlane) : ℂ) = -1 / ((τ : ℂ) - 1) := by
  rw [tauCoinc, UpperHalfPlane.coe_specialLinearGroup_apply]
  norm_num
  ring_nf

/-- **For `Re τ < 1` the removable coincidence lies strictly to the right of the axis.**  Hence it
is not in either of the two (left) rectangles swept by `contourHC`. -/
lemma tauCoinc_re_pos (τ : UpperHalfPlane) (h : τ.re < 1) : 0 < (tauCoinc τ).re := by
  have hne : (τ : ℂ) - 1 ≠ 0 := by
    intro h0
    have h1 : (τ : ℂ) = 1 := sub_eq_zero.mp h0
    have h2 : τ.im = 0 := by rw [← UpperHalfPlane.coe_im, h1]; simp
    exact absurd h2 (ne_of_gt τ.im_pos)
  have hb : ((τ : ℂ) - 1).re = τ.re - 1 := by simp
  rw [← UpperHalfPlane.coe_re, tauCoinc_coe,
    show (-1 : ℂ) / ((τ : ℂ) - 1) = -(((τ : ℂ) - 1)⁻¹) by rw [inv_eq_one_div, neg_div],
    Complex.neg_re, Complex.inv_re, hb, ← Complex.sq_norm,
    show -((τ.re - 1) / ‖(τ : ℂ) - 1‖ ^ 2) = (1 - τ.re) / ‖(τ : ℂ) - 1‖ ^ 2 by ring]
  exact div_pos (by linarith) (pow_pos (norm_pos_iff.mpr hne) 2)

end Work.Asymptotics
