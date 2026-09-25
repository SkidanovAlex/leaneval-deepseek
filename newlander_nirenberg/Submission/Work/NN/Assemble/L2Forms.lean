/-
The weighted `L²` formalism for the **perturbed** flat `∂̄`-operator, in the flat model `ℂⁿ`.

This file provides the definitions used by the route of `NOTES_gauge_l2.md`: the perturbed
`(0,1) → (0,2)` operator `∂̄_J f = π^J_{0,2}(df)` for `J = JstdCn n + A` (defined through the
already available `Work.NN.Final.proj02`/`dOne`, exactly as the integrability hypothesis of the
target is phrased), together with the weighted `L²` norms and pairings of `(0,1)`- and `(0,2)`-forms
in the *coefficient* convention of `Work.Hormander.Weights` (the coefficients being the values on
the standard basis `e_j`).
-/
import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.NN.Assemble.Setup
import Submission.Work.NN.Core.CnPert
import Submission.Work.Hormander.Weights.Estimate

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace Work.NN.Assemble

/-- The standard basis vector of `ℂⁿ`. -/
noncomputable def eb (n : ℕ) (j : Fin n) : Cn n := Pi.single j 1

/-- The `L²_φ` square norm of a `(0,1)`-form in the flat model, in the coefficient convention:
`Σ_j ∫ ‖f z (e_j)‖² e^{-φ z}`. -/
noncomputable def wN1 {n : ℕ} (φ : Cn n → ℝ) (f : Cn n → Cn n →L[ℝ] ℂ) : ℝ :=
  ∫ z, (∑ j, ‖f z (eb n j)‖ ^ 2) * Real.exp (-(φ z))

/-- The `L²_φ` square norm of a `(0,2)`-form in the flat model, in the coefficient convention. -/
noncomputable def wN2 {n : ℕ} (φ : Cn n → ℝ) (F : Cn n → Cn n → Cn n → ℂ) : ℝ :=
  ∫ z, ((1 / 2) * ∑ j, ∑ k, ‖F z (eb n j) (eb n k)‖ ^ 2) * Real.exp (-(φ z))

/-- The weighted pairing of two `(0,1)`-forms in the flat model. -/
noncomputable def wP1 {n : ℕ} (φ : Cn n → ℝ) (f g : Cn n → Cn n →L[ℝ] ℂ) : ℂ :=
  ∫ z, (∑ j, f z (eb n j) * star (g z (eb n j))) * (Real.exp (-(φ z)) : ℂ)

/-- **The perturbed `∂̄` on `(0,1)`-forms.**  For `J = JstdCn n + A` and a `(0,1)`-form `f`
(given as a map into the dual of `ℂⁿ`), `∂̄_J f = π^J_{0,2}(df)`, evaluated through the exterior
derivative `dOne` and the `(0,2)`-projection `proj02` (the same objects that occur in the
integrability hypothesis of the target). -/
noncomputable def dbarJ {n : ℕ} (A : Cn n → Cn n →L[ℝ] Cn n) (f : Cn n → Cn n →L[ℝ] ℂ) :
    Cn n → Cn n → Cn n → ℂ :=
  fun z V W => Work.NN.Final.proj02 (Work.NN.Core.JstdCn n + A) (Work.NN.Final.dOne f) z V W

/-- The `(0,1)`-operator of the perturbed structure applied to a **function** (landing in the
`(0,1)`-forms); this is `∂̄_J` in the sense of `Work.NN.Core.dbarCn`. -/
noncomputable def dbarJ_fun {n : ℕ} (A : Cn n → Cn n →L[ℝ] Cn n) (u : Cn n → ℂ) :
    Cn n → Cn n →L[ℝ] ℂ :=
  Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u

/-- **The co-closedness (gauge) condition** for the perturbed operator: `f` is orthogonal, in the
weighted `L²_φ` pairing, to the range of `∂̄_J` (tested against compactly supported smooth
functions). -/
def IsPertCoclosed {n : ℕ} (A : Cn n → Cn n →L[ℝ] Cn n) (φ : Cn n → ℝ)
    (f : Cn n → Cn n →L[ℝ] ℂ) : Prop :=
  ∀ h : Cn n → ℂ, (∀ m : ℕ, ContDiff ℝ m h) → HasCompactSupport h →
    wP1 φ f (dbarJ_fun A h) = 0

/-! ## The weighted `L²` layer in the flat vocabulary `ℂⁿ = Fin n → ℂ`

The weighted chapter `Work.Hormander.Weights` lives on `EuclideanSpace ℂ (Fin n) = PiLp 2 _`, which
is *not* definitionally the flat model `Fin n → ℂ` used by the `J`-chapters.  The definitions below
mirror the chapter's (`dbarCoord`, `dCoord`, `dbarStar`, the three weighted norms) directly in the
flat vocabulary, so that estimates can be stated and used where the almost complex structure lives. -/

/-- The `(1,0)`-derivative of a real weight, `∂_j φ` (flat model). -/
noncomputable def dPh {n : ℕ} (j : Fin n) (φ : (Fin n → ℂ) → ℝ) (z : Fin n → ℂ) : ℂ :=
  (1 / 2 : ℂ) * ((fderiv ℝ φ z (Pi.single j 1) : ℂ)
    - Complex.I * (fderiv ℝ φ z (Pi.single j Complex.I) : ℂ))

/-- The formal weight-adjoint `∂̄*_φ f = -Σ_j (∂_j f_j - f_j · ∂_j φ)`, mirrored from
`Work.Hormander.Weights.dbarStar`. -/
noncomputable def dbarSt {n : ℕ} (φ : (Fin n → ℂ) → ℝ) (f : Fin n → (Fin n → ℂ) → ℂ) :
    (Fin n → ℂ) → ℂ :=
  fun z => -∑ j, (Work.CR.Flat.dCoord j (f j) z - f j z * dPh j φ z)

/-- The `(0,2)`-form `∂̄f` of a `(0,1)`-form `f`, mirrored from `Work.Hormander.Weights.dbarForm`. -/
noncomputable def dbarFo {n : ℕ} (f : Fin n → (Fin n → ℂ) → ℂ) :
    Fin n → Fin n → (Fin n → ℂ) → ℂ :=
  fun j k z => Work.CR.Flat.dbarCoord k (f j) z - Work.CR.Flat.dbarCoord j (f k) z

/-- The weighted `L²` square norm of a function. -/
noncomputable def wnSq0 {n : ℕ} (φ : (Fin n → ℂ) → ℝ) (u : (Fin n → ℂ) → ℂ) : ℝ :=
  ∫ z, ‖u z‖ ^ 2 * Real.exp (-(φ z))

/-- The weighted `L²` square norm of a `(0,1)`-form (coefficient convention). -/
noncomputable def wnSq1 {n : ℕ} (φ : (Fin n → ℂ) → ℝ) (f : Fin n → (Fin n → ℂ) → ℂ) : ℝ :=
  ∫ z, (∑ j, ‖f j z‖ ^ 2) * Real.exp (-(φ z))

/-- The weighted `L²` square norm of a `(0,2)`-form (antisymmetric convention). -/
noncomputable def wnSq2 {n : ℕ} (φ : (Fin n → ℂ) → ℝ)
    (F : Fin n → Fin n → (Fin n → ℂ) → ℂ) : ℝ :=
  ∫ z, ((1 / 2) * ∑ j, ∑ k, ‖F j k z‖ ^ 2) * Real.exp (-(φ z))

end Work.NN.Assemble

