/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The weighted `L²` theory of `∂̄` on `ℂⁿ`: definitions

This is the vocabulary of the subproject `Submission/Work/Hormander/Weights`, the
chapter that formalises the technique behind Hörmander's proof of the
Newlander–Nirenberg theorem: the `L²` theory of the `∂̄` operator with weights on
a polydisc.

Everything is in namespace `Work.Hormander.Weights`.

## The setting

* `Cn n = EuclideanSpace ℂ (Fin n)` is the flat model `ℂⁿ` (the same type as
  `Submission.F n`); it is a `ℂ`-vector space, hence carries the standard
  complex structure `J v = I • v`.  Points are written `z`, and the `j`-th
  complex coordinate is `coord n j z : ℂ`.
* `evec n j` is the `j`-th basis vector and `ivec n j = I • evec n j`; these are
  the two real directions of the `j`-th complex coordinate.
* `polydisc c r = {z | ∀ j, ‖coord n j (z - c)‖ < r}`.

## The operators

* `dbarCoord n j u z = (1/2)(∂_{x_j} + i ∂_{y_j})u(z)` and
  `dCoord n j u z = (1/2)(∂_{x_j} - i ∂_{y_j})u(z)`, the `(0,1)`- and
  `(1,0)`-derivatives in the `j`-th coordinate (this is
  `Submission.dbar Submission.Jstd u z (evec n j)` for `dbarCoord`, see
  `dbarCoord_eq_dbar_Jstd`).
* `dbarPhi n j φ`, `dPhi n j φ` are the same operators applied to a real weight
  `φ` (viewed as a complex valued function), and
  `hessPhi n i j φ z = ∂_i ∂̄_j φ` is the complex Hessian of `φ`.
* `Form0 n = Cn n → ℂ`, `Form1 n = Fin n → Cn n → ℂ` and
  `Form2 n = Fin n → Fin n → Cn n → ℂ` are the coefficient families of
  `(0,0)`-, `(0,1)`- and `(0,2)`-forms: a `(0,1)`-form `f` is
  `z ↦ Σ_j f j z dz̄_j` and a `(0,2)`-form `F` is `z ↦ Σ_{j<k} F j k z dz̄_j ∧ dz̄_k`
  (the convention is that the coefficient family is antisymmetric in `j`, `k`:
  see `IsAlt2`).  The reason for the antisymmetric convention is that for such a
  family
  `Σ_{j<k} ‖F j k z‖² = (1/2) Σ_{j,k} ‖F j k z‖²`,
  which is the identity used in the norm `normSq2` below.
* `dbarFun u = Σ_j ∂̄_j u · dz̄_j` and
  `dbarForm f = Σ_{j<k} (∂̄_k f_j − ∂̄_j f_k) dz̄_j ∧ dz̄_k`;
  `dbarFun_dbarFun` is `∂̄² = 0` (for `C²` functions).
* `dbarStar φ f = -Σ_j (∂_j f_j − f_j ∂_j φ)` is the formal adjoint of `∂̄`
  with respect to the weighted inner product `e^{-φ}`, characterised by
  `pairing1 φ (dbarFun u) f = pairing0 φ u (dbarStar φ f)`.

## The weighted inner products

With `wn φ z = e^{-φ z}`:

* `normSq0 φ u = ∫ ‖u z‖² e^{-φ z}`, `normSq1 φ f = ∫ (Σ_j ‖f j z‖²) e^{-φ z}`,
  `normSq2 φ F = ∫ ((1/2) Σ_{j,k} ‖F j k z‖²) e^{-φ z}` — the squares of the
  `L²_φ` norms of `(0,0)`-, `(0,1)`- and `(0,2)`-forms;
* `pairing0 φ u v = ∫ u z * conj (v z) * e^{-φ z}` and
  `pairing1 φ f g = ∫ (Σ_j f j z * conj (g j z)) * e^{-φ z}` — the `L²_φ`
  Hermitian pairings (linear in the first argument).

The basic estimate (Hörmander, *An introduction to complex analysis in several
variables*, Ch. 4; Kohn–Morrey formula) is

  `‖∂̄f‖²_φ + ‖∂̄*_φf‖²_φ = Σ_{j,k} ∫ ‖∂̄_k f_j‖² e^{-φ} + Σ_{j,k} ∫ (∂_j∂̄_kφ) f_j f̄_k e^{-φ}`

for compactly supported smooth `(0,1)`-forms `f`; see
`kohnMorrey_identity` and `basicEstimate_general`/`basicEstimate_quad`.

## Conventions

* `∂̄` on a `(0,1)`-form is *defined* to be the antisymmetrisation
  `(∂̄f)_{jk} = ∂̄_k f_j - ∂̄_j f_k`; signs are immaterial for the estimates.
* All the weighted norms are Bochner integrals.  For compactly supported smooth
  data every integrand below is continuous with compact support, hence
  integrable; the statements that need this carry `HasCompactSupport`
  hypotheses.
-/

import Mathlib
import Submission.Work.Core.Defs

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace Work.Hormander.Weights

variable {n : ℕ}

/-- The flat model `ℂⁿ` as a real Euclidean space; definitionally the same type as
`Submission.F n`. -/
abbrev Cn (n : ℕ) : Type := EuclideanSpace ℂ (Fin n)

/-- The `j`-th standard basis vector of `ℂⁿ`. -/
def evec (n : ℕ) (j : Fin n) : Cn n := EuclideanSpace.single j 1

/-- `i` times the `j`-th basis vector: the second real direction of the `j`-th
complex coordinate. -/
def ivec (n : ℕ) (j : Fin n) : Cn n := Complex.I • evec n j

/-- The `j`-th complex coordinate, as a `ℂ`-linear continuous map. -/
noncomputable def coord (n : ℕ) (j : Fin n) : Cn n →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj j).comp (EuclideanSpace.equiv (Fin n) ℂ).toContinuousLinearMap

@[simp] lemma coord_apply (n : ℕ) (j : Fin n) (z : Cn n) : coord n j z = z.ofLp j := rfl

lemma coord_add (n : ℕ) (j : Fin n) (z w : Cn n) : coord n j (z + w) = coord n j z + coord n j w :=
  map_add _ _ _

lemma coord_sub (n : ℕ) (j : Fin n) (z w : Cn n) : coord n j (z - w) = coord n j z - coord n j w :=
  map_sub _ _ _

/-- The polydisc of centre `c` and radius `r`. -/
def polydisc (c : Cn n) (r : ℝ) : Set (Cn n) := {z | ∀ j, ‖coord n j (z - c)‖ < r}

@[simp] lemma mem_polydisc {c : Cn n} {r : ℝ} {z : Cn n} :
    z ∈ polydisc c r ↔ ∀ j, ‖coord n j (z - c)‖ < r := Iff.rfl

lemma polydisc_zero (r : ℝ) : polydisc (0 : Cn n) r = {z | ∀ j, ‖coord n j z‖ < r} := by
  ext z; simp

lemma polydisc_mono {c : Cn n} {r r' : ℝ} (h : r' ≤ r) : polydisc c r' ⊆ polydisc c r :=
  fun _ hz j => lt_of_lt_of_le (hz j) h

lemma isOpen_polydisc (c : Cn n) (r : ℝ) : IsOpen (polydisc c r) := by
  have h : polydisc c r = ⋂ j, {z : Cn n | ‖coord n j (z - c)‖ < r} := by
    ext z; simp [polydisc]
  rw [h]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt (((coord n j).continuous.sub continuous_const).norm) continuous_const

/-- The norm bound for points of a polydisc. -/
lemma norm_le_of_mem_polydisc_zero [Nonempty (Fin n)] {z : Cn n} {r : ℝ} (hr : 0 ≤ r)
    (hz : z ∈ polydisc 0 r) : ‖z‖ ≤ Real.sqrt n * r := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i, ‖z.ofLp i‖ ^ 2 ≤ ∑ _i : Fin n, r ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    have hi : ‖coord n i z‖ < r := by simpa using hz i
    simpa [coord_apply] using pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hi) 2
  calc Real.sqrt (∑ i, ‖z.ofLp i‖ ^ 2) ≤ Real.sqrt (∑ _i : Fin n, r ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt n * r := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq hr]

/-! ### The `∂̄` and `∂` operators -/

/-- The `j`-th `(0,1)`-derivative: `∂̄_j u = (1/2)(∂_{x_j} + i ∂_{y_j})u`. -/
noncomputable def dbarCoord (n : ℕ) (j : Fin n) (u : Cn n → ℂ) (z : Cn n) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ u z (evec n j) + Complex.I * fderiv ℝ u z (ivec n j))

/-- The `j`-th `(1,0)`-derivative: `∂_j u = (1/2)(∂_{x_j} - i ∂_{y_j})u`. -/
noncomputable def dCoord (n : ℕ) (j : Fin n) (u : Cn n → ℂ) (z : Cn n) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ u z (evec n j) - Complex.I * fderiv ℝ u z (ivec n j))

@[simp] lemma evec_ofLp (j : Fin n) : (evec n j).ofLp = Pi.single j (1 : ℂ) := rfl

@[simp] lemma ivec_ofLp (j : Fin n) : (ivec n j).ofLp = Pi.single j Complex.I := by
  funext i
  by_cases h : i = j <;> simp [ivec, evec, h]

/-- `∂̄_j φ` for a real valued weight `φ`. -/
noncomputable def dbarPhi (n : ℕ) (j : Fin n) (φ : Cn n → ℝ) (z : Cn n) : ℂ :=
  dbarCoord n j (fun w => (φ w : ℂ)) z

/-- `∂_j φ` for a real valued weight `φ`. -/
noncomputable def dPhi (n : ℕ) (j : Fin n) (φ : Cn n → ℝ) (z : Cn n) : ℂ :=
  dCoord n j (fun w => (φ w : ℂ)) z

/-- The complex Hessian `∂_i ∂̄_j φ` of a real valued weight. -/
noncomputable def hessPhi (n : ℕ) (i j : Fin n) (φ : Cn n → ℝ) (z : Cn n) : ℂ :=
  dCoord n i (dbarPhi n j φ) z

/-- The weight function `z ↦ e^{-φ z}`, the density of `L²_φ`. -/
def wn (n : ℕ) (φ : Cn n → ℝ) : Cn n → ℝ := fun z => Real.exp (-(φ z))

lemma wn_pos (φ : Cn n → ℝ) (z : Cn n) : 0 < wn n φ z := Real.exp_pos _

@[simp] lemma wn_apply (φ : Cn n → ℝ) (z : Cn n) : wn n φ z = Real.exp (-(φ z)) := rfl

/-- The quadratic weight `φ(z) = K‖z‖²`.  For this weight the complex Hessian is
`K·δ_{ij}`, so the basic estimate gives a gain of `K` in the `L²` estimate. -/
noncomputable def quadWeight (n : ℕ) (K : ℝ) : Cn n → ℝ := fun z => K * ‖z‖ ^ 2

/-! ### Forms -/

/-- `(0,0)`-forms: complex valued functions. -/
abbrev Form0 (n : ℕ) : Type := Cn n → ℂ

/-- `(0,1)`-forms, given by their coefficients `f j` in `dz̄_j`. -/
abbrev Form1 (n : ℕ) : Type := Fin n → Cn n → ℂ

/-- `(0,2)`-forms, given by their coefficients `F j k` in `dz̄_j ∧ dz̄_k`; the natural
condition on such a coefficient family is `IsAlt2`. -/
abbrev Form2 (n : ℕ) : Type := Fin n → Fin n → Cn n → ℂ

/-- The antisymmetry convention for `(0,2)`-forms. -/
def IsAlt2 (F : Form2 n) : Prop := ∀ j k, ∀ z, F j k z = -F k j z

/-- `∂̄` on functions: `∂̄u = Σ_j ∂̄_j u dz̄_j`. -/
noncomputable def dbarFun (u : Form0 n) : Form1 n := fun j z => dbarCoord n j u z

/-- `∂̄` on `(0,1)`-forms: `(∂̄f)_{jk} = ∂̄_k f_j - ∂̄_j f_k`, the coefficient of
`dz̄_j ∧ dz̄_k` in `∂̄f`. -/
noncomputable def dbarForm (f : Form1 n) : Form2 n :=
  fun j k z => dbarCoord n k (f j) z - dbarCoord n j (f k) z

/-- The formal adjoint `∂̄*_φ` of `∂̄` with respect to the weight `e^{-φ}`:
`∂̄*_φ f = -Σ_j (∂_j f_j - f_j ∂_j φ)`. -/
noncomputable def dbarStar (φ : Cn n → ℝ) (f : Form1 n) : Form0 n :=
  fun z => -∑ j, (dCoord n j (f j) z - f j z * dPhi n j φ z)

/-- The `L²_φ` square norm of a `(0,0)`-form. -/
noncomputable def normSq0 (φ : Cn n → ℝ) (u : Form0 n) : ℝ :=
  ∫ z, ‖u z‖ ^ 2 * wn n φ z

/-- The `L²_φ` square norm of a `(0,1)`-form. -/
noncomputable def normSq1 (φ : Cn n → ℝ) (f : Form1 n) : ℝ :=
  ∫ z, (∑ j, ‖f j z‖ ^ 2) * wn n φ z

/-- The `L²_φ` square norm of a `(0,2)`-form, with the antisymmetric (orthonormal
basis) convention `Σ_{j<k} ‖F j k‖² = (1/2) Σ_{j,k} ‖F j k‖²`. -/
noncomputable def normSq2 (φ : Cn n → ℝ) (F : Form2 n) : ℝ :=
  ∫ z, ((1 / 2 : ℝ) * ∑ j, ∑ k, ‖F j k z‖ ^ 2) * wn n φ z

/-- The `L²_φ` Hermitian pairing of `(0,0)`-forms. -/
noncomputable def pairing0 (φ : Cn n → ℝ) (u v : Form0 n) : ℂ :=
  ∫ z, u z * star (v z) * wn n φ z

/-- The `L²_φ` Hermitian pairing of `(0,1)`-forms. -/
noncomputable def pairing1 (φ : Cn n → ℝ) (f g : Form1 n) : ℂ :=
  ∫ z, (∑ j, f j z * star (g j z)) * wn n φ z

/-- The real weighted integral `∫ U e^{-φ}`, the basic functional out of which the
`L²_φ` pairings are built. -/
noncomputable def rint (φ : Cn n → ℝ) (U : Cn n → ℝ) : ℝ :=
  ∫ z, U z * wn n φ z

/-- The *real* `L²_φ` inner product `Re ∫ u conj v e^{-φ}` of `(0,0)`-forms.  It is a
symmetric `ℝ`-bilinear form and satisfies `rpair0 φ u u = normSq0 φ u`, which makes it
the convenient pairing for the Kohn–Morrey identity (everything in the identity is
real after taking `Re`, and the antisymmetrisation of `(0,2)`-forms is then
conjugation-free). -/
noncomputable def rpair0 (φ : Cn n → ℝ) (u v : Form0 n) : ℝ :=
  rint φ (fun z => (u z * star (v z)).re)

/-- The pointwise squared length of a `(0,1)`-form. -/
def normSqPt (f : Form1 n) (z : Cn n) : ℝ := ∑ j, ‖f j z‖ ^ 2

/-- The pointwise squared length of a `(0,2)`-form. -/
def normSqPt2 (F : Form2 n) (z : Cn n) : ℝ := (1 / 2 : ℝ) * ∑ j, ∑ k, ‖F j k z‖ ^ 2

/-- A lower bound `κ` for the complex Hessian of the weight `φ`, in the sense of
Hermitian forms: `Σ_{i,j} ∂_i∂̄_jφ(z) v_i conj v_j ≥ κ ‖v‖²` for all `v`. -/
def HessLowerBound (φ : Cn n → ℝ) (κ : ℝ) : Prop :=
  ∀ z (v : Fin n → ℂ), κ * ∑ j, ‖v j‖ ^ 2
    ≤ (∑ i, ∑ j, hessPhi n i j φ z * (v i * star (v j))).re

/-- The weight `φ` is (strictly, with constant `κ`) plurisubharmonic for the flat
structure. -/
def IsPSH (φ : Cn n → ℝ) (κ : ℝ) : Prop := HessLowerBound φ κ

end Work.Hormander.Weights
