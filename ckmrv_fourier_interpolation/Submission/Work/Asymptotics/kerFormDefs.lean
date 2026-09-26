/-
# The contour `1`-form integrand `z ↦ K(τ,z)e^{iπr²z}/i` on `ℂ`

The left detour `Work.Asymptotics.detourLeftC` is assembled from the edge integrands
`edgeH`/`edgeV` of `Work.Asymptotics.contourLeftDefs`, which are parametrised by real
coordinates.  In order to apply the residue theorem for a rectangle
(`Work.Asymptotics.rectInt_eq_residue`) one needs the *same* quantity as a function of the
complex variable `z`, namely the coefficient

  `kerForm ℓ d r τ z = K^{(d)}(τ,z) e^{iπr²z} / i`

of the `1`-form `K e^{iπr²z} dz/i`.  This file defines that function (it is total on `ℂ`, with a
junk value outside the upper half plane; only `0 < z.im` is ever used) together with the two
rectangles of the left detour and the elementary conversions between the real parametrisations
`edgeH`, `edgeV` and `kerForm`.
-/
import Mathlib
import Submission.Work.Asymptotics.contourLeftDefs

noncomputable section

namespace Work.Asymptotics

open UpperHalfPlane MeasureTheory

/-- The exponential factor `e^{iπr²z}` of the contour integrand. -/
def kerExp (r : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2 * z)

/-- **The contour `1`-form integrand** `K^{(d)}(τ,z) e^{iπr²z}/i` as a function of `z : ℂ`.
Outside the upper half plane the value is junk; only `z` with `0 < z.im` are used. -/
def kerForm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r : ℝ) (τ : UpperHalfPlane)
    (z : ℂ) : ℂ :=
  Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex z) * kerExp r z / Complex.I

/-- The closed left rectangle `[-ξ,0] × [c-A, c+A]` of the complex plane. -/
def leftRectℂ (c A ξ : ℝ) : Set ℂ :=
  {z : ℂ | -ξ ≤ z.re ∧ z.re ≤ 0 ∧ c - A ≤ z.im ∧ z.im ≤ c + A}

/-- The open left rectangle `(-ξ,0) × (c-A, c+A)` of the complex plane. -/
def openLeftRectℂ (c A ξ : ℝ) : Set ℂ :=
  {z : ℂ | -ξ < z.re ∧ z.re < 0 ∧ c - A < z.im ∧ z.im < c + A}

/-- The pole `τ - 1` of `z ↦ K(τ,z)`, as a complex number. -/
def poleℂ (τ : UpperHalfPlane) : ℂ := ((tauSubOne τ : UpperHalfPlane) : ℂ)

lemma poleℂ_eq (τ : UpperHalfPlane) : poleℂ τ = (τ : ℂ) - 1 := by
  rw [poleℂ, tauSubOne_coe]

lemma kerForm_eq (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r : ℝ) (τ : UpperHalfPlane)
    (z : ℂ) :
    kerForm ℓ d r τ z
      = Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex z) * kerExp r z / Complex.I := rfl

/-- On the upper half plane, `ofReImT u v` and `ofComplex (u + i v)` agree. -/
lemma ofReImT_eq_ofComplex (u v : ℝ) (hv : 0 < v) :
    ofReImT u v = UpperHalfPlane.ofComplex ((u : ℂ) + (v : ℂ) * Complex.I) := by
  apply UpperHalfPlane.ext
  rw [ofReImT_coe u v hv, UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using hv)]

/-- `ofComplex` is continuous on the upper half plane. -/
lemma continuousOn_ofComplex_of_im_pos :
    ContinuousOn (fun z : ℂ => UpperHalfPlane.ofComplex z) {z : ℂ | 0 < z.im} := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h : ({z : ℂ | 0 < z.im}.domRestrict (fun z : ℂ => UpperHalfPlane.ofComplex z))
      = fun z : {z : ℂ | 0 < z.im} => (⟨(z : ℂ), z.2⟩ : UpperHalfPlane) := by
    funext z
    exact UpperHalfPlane.ofComplex_apply_of_im_pos z.2
  rw [h]
  exact continuous_subtype_val.upperHalfPlaneMk (fun z => z.2)

lemma leftRectℂ_subset_im_pos {c A ξ : ℝ} (hcA : 0 < c - A) :
    leftRectℂ c A ξ ⊆ {z : ℂ | 0 < z.im} := by
  intro z hz
  simp only [leftRectℂ, Set.mem_ofPred_eq] at hz
  simp only [Set.mem_ofPred_eq]
  linarith [hz.2.2.1]

lemma openLeftRectℂ_subset_leftRectℂ (c A ξ : ℝ) :
    openLeftRectℂ c A ξ ⊆ leftRectℂ c A ξ := by
  intro z hz
  simp only [openLeftRectℂ, Set.mem_ofPred_eq] at hz
  simp only [leftRectℂ, Set.mem_ofPred_eq]
  exact ⟨le_of_lt hz.1, le_of_lt hz.2.1, le_of_lt hz.2.2.1, le_of_lt hz.2.2.2⟩

end Work.Asymptotics
