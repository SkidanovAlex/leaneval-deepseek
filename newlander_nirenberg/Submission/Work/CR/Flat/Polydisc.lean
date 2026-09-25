/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Polydiscs in `ℂⁿ` and the flat `∂̄`-operator

This file sets up the geometry used by the flat `∂̄`-Poincaré lemma: polydiscs in
`ℂⁿ = Fin n → ℂ` (with the sup norm, which is the natural norm for the
componentwise estimates), and the `j`-th `∂̄`-operator

  `dbarCoord j u z = (1/2)(∂_{x_j} u z + i ∂_{y_j} u z)`,

i.e. the derivative of `u` in the `(0,1)` direction of the `j`-th coordinate.
A `∂̄`-equation for a `(0,1)`-form `f = Σ_j f_j dz̄_j` is the system
`dbarCoord j u = f j`, and the form is *closed* when
`dbarCoord k (f j) = dbarCoord j (f k)` for all `j`, `k`.

The polydisc is open, so `holderNorm_mono_set` applies to smaller polydiscs.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder

noncomputable section

open scoped NNReal ENNReal
open Set

namespace Work.CR.Flat

/-- The polydisc with centre `c` and multi-radius `r` in `ℂⁿ = Fin n → ℂ`. -/
def polydisc {n : ℕ} (c : Fin n → ℂ) (r : Fin n → ℝ) : Set (Fin n → ℂ) :=
  {z | ∀ j, ‖z j - c j‖ < r j}

@[simp] lemma mem_polydisc {n : ℕ} {c : Fin n → ℂ} {r : Fin n → ℝ} {z : Fin n → ℂ} :
    z ∈ polydisc c r ↔ ∀ j, ‖z j - c j‖ < r j := Iff.rfl

lemma polydisc_mono {n : ℕ} {c : Fin n → ℂ} {r r' : Fin n → ℝ} (h : ∀ j, r' j ≤ r j) :
    polydisc c r' ⊆ polydisc c r :=
  fun _ hz j => lt_of_lt_of_le (hz j) (h j)

lemma isOpen_polydisc {n : ℕ} (c : Fin n → ℂ) (r : Fin n → ℝ) : IsOpen (polydisc c r) := by
  have h : polydisc c r = ⋂ j, {z : Fin n → ℂ | ‖z j - c j‖ < r j} := by
    ext z; simp [polydisc]
  rw [h]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt ((continuous_apply j).sub continuous_const |>.norm) continuous_const

/-- The `j`-th `(0,1)`-derivative: `∂̄_j u = (1/2)(∂_{x_j} + i ∂_{y_j})u`.
`Pi.single j 1` is the unit vector in the `j`-th coordinate direction and
`Pi.single j Complex.I` is multiplication by `i` in that coordinate. -/
noncomputable def dbarCoord {n : ℕ} (j : Fin n) (u : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ u z (Pi.single j 1) + Complex.I * fderiv ℝ u z (Pi.single j Complex.I))

/-- The `(1,0)`-derivative `∂_j u = (1/2)(∂_{x_j} - i ∂_{y_j})u`. -/
noncomputable def dCoord {n : ℕ} (j : Fin n) (u : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ u z (Pi.single j 1) - Complex.I * fderiv ℝ u z (Pi.single j Complex.I))

/-- The slice of `f` in the `j`-th coordinate: `w ↦ f (z with z_j replaced by w)`. -/
def slice {n : ℕ} (j : Fin n) (f : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) : ℂ → ℂ :=
  fun w => f (Function.update z j w)

@[simp] lemma slice_apply {n : ℕ} (j : Fin n) (f : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) (w : ℂ) :
    slice j f z w = f (Function.update z j w) := rfl

lemma slice_update_self {n : ℕ} (j : Fin n) (f : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    slice j f z (z j) = f z := by
  simp [slice]

/-- A `(0,1)`-form `f = Σ_j f_j dz̄_j` is closed when
`∂̄_k f_j = ∂̄_j f_k` for all `j`, `k`.  (This is the `(0,2)`-part of `∂̄f`.) -/
def IsClosedForm {n : ℕ} (f : Fin n → (Fin n → ℂ) → ℂ) : Prop :=
  ∀ j k, ∀ z : Fin n → ℂ, dbarCoord k (f j) z = dbarCoord j (f k) z

/-- Reduction to the one-variable case: for `n = 1` every form is closed, since
there is no `(0,2)`-part. -/
theorem isClosedForm_one {f : Fin 1 → (Fin 1 → ℂ) → ℂ} : IsClosedForm f := by
  intro j k z
  fin_cases j; fin_cases k; rfl

end Work.CR.Flat
