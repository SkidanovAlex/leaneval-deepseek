/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The *exact* defect identity of the `∂̄`-perturbation, at the level of forms

Let `J = JstdCn n + A` be an almost complex structure on (an open set of) `ℂⁿ`, `w : ℂⁿ → ℂ`
smooth and `ρ := ∂̄_J w = dbarCn (JstdCn n + A) w` the `(0,1)`-form which is the defect of
`w`.  Write `ξ := Lzero A w` for the *form-valued* first-order perturbation

  `ξ(z)(V) = (i/2)·dw_z(A_zV)`,      so that     `∂̄_J w = ∂̄_{Jstd} w + ξ`      (pointwise).

The content of this file is the identity

  `proj02 Jstd (dOne ξ) z = - (proj02 (Jstd + A) (dOne ρ) z - proj02 Jstd (dOne ρ) z)`,

i.e. `∂̄₀ξ = -(∂̄_J ρ - ∂̄₀ρ) = -L¹_A ρ`, where `L¹_A ρ` is the *algebraic* (first-order, but with
coefficients depending only on the *values* of `A`) perturbation of `∂̄` at the level of `(0,1)`-forms.

**Why this matters, and why the operator is the one above and not `L_A`.**

* `∂̄_J = ∂̄₀ + L⁰_A` on functions and `∂̄_J = ∂̄₀ + L¹_A` on `(0,1)`-forms, where `L¹_A α` is
  *algebraic* in `(dα_z, A_z)`: it involves no derivative of `A`.  Consequently

    `‖L¹_A ρ(z)‖ ≤ C ‖A_z‖ · ‖dρ_z‖ ≤ C ε ‖dρ_z‖`

  — the *sharp* defect bound, with the operator norm of `fderiv ρ` on the right (`proj02_diff_bound`).
* On the other hand `∂̄₀ ∘ L⁰_A = -L¹_A ∘ ∂̄_J` (both sides are first-order operators with
  coefficients in `A`; the identity is obtained by expanding `∂̄_J ∘ ∂̄_J = 0`).  The identity proved
  here is its evaluation at `w`:
  `∂̄₀(L⁰_A w) = -L¹_A(∂̄_J w)`, i.e. `∂̄₀ξ = -L¹_Aρ`.

*The pitfall.*  The analogue with the *slotwise* operator `L_A` (i.e. `(L_Aα)(V) = (i/2)α(A_zV)`
applied to a `(0,1)`-form `α`) is **false**: that operator contains `∂A` (`L_A` applied to a form
differentiates only through `α`, but its "second variation" `L_A²` picks up `d(L⁰_Aw) = dw(∂A) +
d²w`), and the hypotheses of the assembly bound only `‖A z‖` and the `α`-Hölder seminorm of `A`,
not `fderiv A`.  This is the precise reason why the coefficient-level ("array") defect estimates of
`Work.NN.Assemble.defectFive*` fail, while the form-level statement above — which is an identity of
forms, not of coefficient arrays — is sharp.

*Reduction of the proof.*  `∂̄_J(dbarCn J w) = 0` is the integrability hypothesis (`∂̄_J² = 0`) and
`∂̄₀(dbarCn Jstd w) = 0` is the standard-structure case `∂̄₀² = 0`.  Splitting `dbarCn J w =
dbarCn Jstd w + ξ` (see `dbarCn_eq_std_add_Lzero`) and expanding both `(0,2)`-projections, the
difference is *algebraically* equal to `-proj02 Jstd (dOne ξ)`: the mixed terms cancel using the two
vanishing facts.  Nothing analytic enters: the proof is the linearity of `proj02` and of `dOne`
together with the two closedness statements.
-/
import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Final.proj02_diff_bound
import Submission.Work.NN.PertApriori.proj02_JstdCn_dbarCn_zero

noncomputable section

namespace Work.NN.Final

open Work.NN.Core

/-- **The form-valued first-order perturbation of `∂̄`.**  `Lzero A w` is the `1`-form
`V ↦ (i/2)·dw_z(A_zV)`; it is the difference `∂̄_{Jstd+A}w - ∂̄_{Jstd}w` at every point
(`dbarCn_eq_std_add_Lzero`). -/
def Lzero {n : ℕ} (A : Cn n → Cn n →L[ℝ] Cn n) (w : Cn n → ℂ) : Cn n → Cn n →L[ℝ] ℂ :=
  fun z => (Complex.I / 2) • ((fderiv ℝ w z).comp (A z))

@[simp] lemma Lzero_apply {n : ℕ} (A : Cn n → Cn n →L[ℝ] Cn n) (w : Cn n → ℂ) (z V : Cn n) :
    Lzero A w z V = (Complex.I / 2) * fderiv ℝ w z (A z V) := by
  simp only [Lzero, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul]

/-- **Pointwise splitting of `∂̄_{Jstd+A}`.**  As forms, `∂̄_{Jstd+A}w = ∂̄_{Jstd}w + Lzero A w`. -/
lemma dbarCn_eq_std_add_Lzero {n : ℕ} (A : Cn n → Cn n →L[ℝ] Cn n) (w : Cn n → ℂ) :
    dbarCn (JstdCn n + A) w = fun z => dbarCn (JstdCn n) w z + Lzero A w z := by
  funext z
  apply ContinuousLinearMap.ext
  intro V
  rw [add_apply, dbarCn_apply, dbarCn_apply, Lzero_apply]
  have h : (JstdCn n + A) z V = JstdCn n z V + A z V := by
    rw [Pi.add_apply]; rfl
  rw [h, map_add]
  ring

/-- **Additivity of `dOne` in the form.**  `dOne (α + β) = dOne α + dOne β` (pointwise), under the
differentiability hypotheses which make `fderiv_add` applicable. -/
lemma dOne_add {n : ℕ} {α β : Cn n → Cn n →L[ℝ] ℂ} {z : Cn n}
    (hα : ∀ W : Cn n, DifferentiableAt ℝ (fun z' => α z' W) z)
    (hβ : ∀ W : Cn n, DifferentiableAt ℝ (fun z' => β z' W) z) (V W : Cn n) :
    dOne (fun z' => α z' + β z') z V W = dOne α z V W + dOne β z V W := by
  simp only [dOne, add_apply]
  have h1 : (fun z' : Cn n => α z' W + β z' W) = (fun z' => α z' W) + (fun z' => β z' W) := rfl
  have h2 : (fun z' : Cn n => α z' V + β z' V) = (fun z' => α z' V) + (fun z' => β z' V) := rfl
  rw [h1, h2, fderiv_add (hα W) (hβ W), fderiv_add (hα V) (hβ V)]
  simp only [add_apply]
  ring

/-- **Additivity of `proj02` in the `2`-form.** -/
lemma proj02_add {n : ℕ} (J : Cn n → Cn n →L[ℝ] Cn n)
    (Ω Ω' : Cn n → Cn n → Cn n → ℂ) (z V W : Cn n) :
    proj02 J (fun z' a b => Ω z' a b + Ω' z' a b) z V W
      = proj02 J Ω z V W + proj02 J Ω' z V W := by
  simp only [proj02]
  ring

/-- **The `(1,0)`-part of a `1`-form** (for the standard structure `JstdCn n`).  In the
array/form dictionary `∇(Arr α) = Arr (∂̄₀α) + ∇(Arr (Pi10 α))` this is the "junk" term: it is
the difference between the array-level `∂̄₀` of the array of `α` and the form-level `∂̄₀` of `α`.
It is *pointwise* in `α` (it does not differentiate `A`), which is why it can be estimated by the
values of `α` only. -/
def Pi10 {n : ℕ} (α : Cn n → Cn n →L[ℝ] ℂ) : Cn n → Cn n →L[ℝ] ℂ :=
  fun z => (1 / 2 : ℂ) • (α z - Complex.I • ((α z).comp (JstdCn n z)))

@[simp] lemma Pi10_apply {n : ℕ} (α : Cn n → Cn n →L[ℝ] ℂ) (z V : Cn n) :
    Pi10 α z V = (1 / 2 : ℂ) * (α z V - Complex.I * α z (Complex.I • V)) := by
  simp only [Pi10, smul_apply, sub_apply, ContinuousLinearMap.comp_apply,
    JstdCn_apply, smul_eq_mul]

/-- **The junk term for a `J`-antilinear `(0,1)`-form.**  If `q` is `JstdCn n + A`-antilinear then
the `(1,0)`-part of `q` on the standard basis vectors is `(i/2)·q(z)(A_ze_m)`: it is *linear in the
values of* `q` and *linear in* `A`, and in particular `O(ε‖q z‖)`. -/
lemma Pi10_apply_basis {n : ℕ} {A : Cn n → Cn n →L[ℝ] Cn n} {q : Cn n → Cn n →L[ℝ] ℂ}
    (hq : ∀ z V, q z ((JstdCn n + A) z V) = -Complex.I * q z V) (z : Cn n) (m : Fin n) :
    Pi10 q z (Pi.single m 1) = (Complex.I / 2) * q z (A z (Pi.single m 1)) := by
  have h2 := hq z (Pi.single m 1)
  have hsplit : (JstdCn n + A) z (Pi.single m 1)
      = Complex.I • Pi.single m (1 : ℂ) + A z (Pi.single m 1) := by
    simp only [Pi.add_apply, add_apply, JstdCn_apply]
  rw [hsplit, map_add] at h2
  rw [Pi10_apply]
  have hq' : q z (Complex.I • Pi.single m (1 : ℂ))
      = -Complex.I * q z (Pi.single m 1) - q z (A z (Pi.single m 1)) := by
    linear_combination h2
  rw [hq']
  linear_combination (1 / 2 * (q z (Pi.single m 1))) * Complex.I_mul_I

/-- Norm form of `Pi10_apply_basis`: if `A z` is small on the basis vector `e_m`, the junk term is
`≤ ε‖q z‖`. -/
lemma Pi10_apply_basis_bound {n : ℕ} {A : Cn n → Cn n →L[ℝ] Cn n} {q : Cn n → Cn n →L[ℝ] ℂ}
    (hq : ∀ z V, q z ((JstdCn n + A) z V) = -Complex.I * q z V) (z : Cn n) (m : Fin n) {ε : ℝ}
    (hA : ‖A z (Pi.single m 1)‖ ≤ ε) :
    ‖Pi10 q z (Pi.single m 1)‖ ≤ ε * ‖q z‖ := by
  rw [Pi10_apply_basis hq z m, norm_mul]
  have hI : ‖(Complex.I / 2 : ℂ)‖ = 1 / 2 := by rw [norm_div]; simp
  have hq' : ‖q z (A z (Pi.single m 1))‖ ≤ ‖q z‖ * ε :=
    le_trans (ContinuousLinearMap.le_opNorm _ _)
      (mul_le_mul_of_nonneg_left hA (norm_nonneg _))
  calc ‖(Complex.I / 2 : ℂ)‖ * ‖q z (A z (Pi.single m 1))‖
      = (1 / 2) * ‖q z (A z (Pi.single m 1))‖ := by rw [hI]
    _ ≤ (1 / 2) * (‖q z‖ * ε) := mul_le_mul_of_nonneg_left hq' (by norm_num)
    _ ≤ ε * ‖q z‖ := by
        nlinarith [hA, norm_nonneg (A z (Pi.single m 1)), norm_nonneg (q z)]

/-- **The junk term of `Lzero A u`.**  The `(1,0)`-part of the perturbation form
`Lzero A u = (i/2)d u(A·)` on the basis vectors is `(1/4)(i·du(A_ze_m) + du(A_z(ie_m)))`; hence it
is `O(ε‖fderiv u z‖)` (see `Pi10_Lzero_bound`). -/
lemma Pi10_Lzero {n : ℕ} (A : Cn n → Cn n →L[ℝ] Cn n) (u : Cn n → ℂ) (z : Cn n) (m : Fin n) :
    Pi10 (Lzero A u) z (Pi.single m 1)
      = (1 / 4 : ℂ) * (Complex.I * fderiv ℝ u z (A z (Pi.single m 1))
          + fderiv ℝ u z (A z (Complex.I • Pi.single m (1 : ℂ)))) := by
  rw [Pi10_apply, Lzero_apply, Lzero_apply]
  linear_combination
    (-(1 / 4) * fderiv ℝ u z (A z (Complex.I • Pi.single m (1 : ℂ)))) * Complex.I_mul_I

/-- Norm form of `Pi10_Lzero`: if `A z` is small on the two vectors `e_m` and `i·e_m`, then the
junk term of the perturbation form `Lzero A u` is `≤ ε‖fderiv u z‖`. -/
lemma Pi10_Lzero_bound {n : ℕ} (A : Cn n → Cn n →L[ℝ] Cn n) (u : Cn n → ℂ) (z : Cn n)
    (m : Fin n) {ε : ℝ} (hA : ‖A z (Pi.single m 1)‖ ≤ ε)
    (hA' : ‖A z (Pi.single m (Complex.I : ℂ))‖ ≤ ε) (hε : 0 ≤ ε) :
    ‖Pi10 (Lzero A u) z (Pi.single m 1)‖ ≤ ε * ‖fderiv ℝ u z‖ := by
  rw [Pi10_Lzero, smul_single_I, norm_mul, show ‖(1 / 4 : ℂ)‖ = (1 / 4 : ℝ) by norm_num]
  have h1 : ‖fderiv ℝ u z (A z (Pi.single m 1))‖ ≤ ‖fderiv ℝ u z‖ * ε :=
    le_trans (ContinuousLinearMap.le_opNorm _ _)
      (mul_le_mul_of_nonneg_left hA (norm_nonneg _))
  have h2 : ‖fderiv ℝ u z (A z (Pi.single m (Complex.I : ℂ)))‖ ≤ ‖fderiv ℝ u z‖ * ε :=
    le_trans (ContinuousLinearMap.le_opNorm _ _)
      (mul_le_mul_of_nonneg_left hA' (norm_nonneg _))
  have hI : ‖Complex.I * fderiv ℝ u z (A z (Pi.single m 1))‖
      = ‖fderiv ℝ u z (A z (Pi.single m 1))‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
  calc (1 / 4) * ‖Complex.I * fderiv ℝ u z (A z (Pi.single m 1))
        + fderiv ℝ u z (A z (Pi.single m (Complex.I : ℂ)))‖
      ≤ (1 / 4) * (‖Complex.I * fderiv ℝ u z (A z (Pi.single m 1))‖
          + ‖fderiv ℝ u z (A z (Pi.single m (Complex.I : ℂ)))‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ ≤ (1 / 4) * (‖fderiv ℝ u z‖ * ε + ‖fderiv ℝ u z‖ * ε) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        rw [hI]
        exact add_le_add h1 h2
    _ ≤ ε * ‖fderiv ℝ u z‖ := by
        nlinarith [hε, norm_nonneg (fderiv ℝ u z)]

/-- **The exact form-level defect identity.**  Let `A` be a field on `ℂⁿ`, `w` a function, and
suppose

* `dOne (∂̄_{Jstd+A}w) = dOne (∂̄_{Jstd}w) + dOne (Lzero A w)` (the splitting of
  `dbarCn_eq_std_add_Lzero`, which one obtains from `dOne_add` under differentiability hypotheses),
* `proj02 (Jstd+A) (dOne (∂̄_{Jstd+A}w)) = 0` (integrability `∂̄_J² = 0`),
* `proj02 Jstd (dOne (∂̄_{Jstd}w)) = 0` (the standard case `∂̄₀² = 0`).

Then, at every point `z` and for all `V W`,

  `∂̄₀(Lzero A w) z V W = -((∂̄_J - ∂̄₀)(∂̄_J w)) z V W`.

Here `∂̄_J = proj02 (Jstd+A) (dOne ·)` and `∂̄₀ = proj02 Jstd (dOne ·)` are the *form-level*
operators (the object `(∂̄_J - ∂̄₀)` applied to a `(0,1)`-form is `L¹_A`, algebraic in `(d·, A)`;
see `proj02_diff_bound` for the resulting `O(ε·‖fderiv‖)` bound). -/
theorem defect_form_identity {n : ℕ} {A : Cn n → Cn n →L[ℝ] Cn n} {w : Cn n → ℂ}
    (hadd : dOne (fun z' => dbarCn (JstdCn n + A) w z')
      = fun z V W => dOne (fun z' => dbarCn (JstdCn n) w z') z V W
          + dOne (Lzero A w) z V W)
    (hint : ∀ z V W, proj02 (JstdCn n + A)
        (fun z' => dOne (fun z'' => dbarCn (JstdCn n + A) w z'') z') z V W = 0)
    (hstd : ∀ z V W, proj02 (JstdCn n)
        (fun z' => dOne (fun z'' => dbarCn (JstdCn n) w z'') z') z V W = 0)
    (z V W : Cn n) :
    proj02 (JstdCn n) (fun z' => dOne (Lzero A w) z') z V W
      = -(proj02 (JstdCn n + A)
            (fun z' => dOne (fun z'' => dbarCn (JstdCn n + A) w z'') z') z V W
          - proj02 (JstdCn n)
            (fun z' => dOne (fun z'' => dbarCn (JstdCn n + A) w z'') z') z V W) := by
  -- the pointwise splitting of the integrand
  have hfun : (fun z' => dOne (fun z'' => dbarCn (JstdCn n + A) w z'') z')
      = fun z' a b => dOne (fun z'' => dbarCn (JstdCn n) w z'') z' a b
          + dOne (Lzero A w) z' a b := by
    funext z' a b
    exact congrFun (congrFun (congrFun hadd z') a) b
  -- the splitting of the `∂̄₀`-projection of the defect: `∂̄₀(dbarCn Jstd w) = 0`
  have hsplitS : proj02 (JstdCn n)
        (fun z' => dOne (fun z'' => dbarCn (JstdCn n + A) w z'') z') z V W
      = proj02 (JstdCn n) (fun z' => dOne (fun z'' => dbarCn (JstdCn n) w z'') z') z V W
        + proj02 (JstdCn n) (fun z' => dOne (Lzero A w) z') z V W := by
    rw [hfun, proj02_add]
  have hS : proj02 (JstdCn n)
      (fun z' => dOne (fun z'' => dbarCn (JstdCn n + A) w z'') z') z V W
      = proj02 (JstdCn n) (fun z' => dOne (Lzero A w) z') z V W := by
    rw [hsplitS, hstd z V W, zero_add]
  rw [hint z V W, hS]
  ring

/-- **The exact form-level defect identity, with the standard case discharged.**  This is
`defect_form_identity` with the hypothesis `proj02 Jstd (dOne (∂̄₀w)) = 0` supplied by
`Work.NN.PertApriori.proj02_JstdCn_dbarCn_zero` (the standard structure satisfies `∂̄₀² = 0`). -/
theorem defect_form_identity_std {n : ℕ} {A : Cn n → Cn n →L[ℝ] Cn n} {w : Cn n → ℂ}
    (hw : ∀ m : ℕ, ContDiff ℝ m w)
    (hadd : dOne (fun z' => dbarCn (JstdCn n + A) w z')
      = fun z V W => dOne (fun z' => dbarCn (JstdCn n) w z') z V W
          + dOne (Lzero A w) z V W)
    (hint : ∀ z V W, proj02 (JstdCn n + A)
        (fun z' => dOne (fun z'' => dbarCn (JstdCn n + A) w z'') z') z V W = 0)
    (z V W : Cn n) :
    proj02 (JstdCn n) (fun z' => dOne (Lzero A w) z') z V W
      = -(proj02 (JstdCn n + A)
            (fun z' => dOne (fun z'' => dbarCn (JstdCn n + A) w z'') z') z V W
          - proj02 (JstdCn n)
            (fun z' => dOne (fun z'' => dbarCn (JstdCn n + A) w z'') z') z V W) :=
  defect_form_identity hadd hint
    (fun z V W => Work.NN.PertApriori.proj02_JstdCn_dbarCn_zero w hw z V W) z V W

/-- The `(0,2)`-form `z ↦ ((V,W) ↦ dOne ρ z V W)`, exhibited as a curried
`ContinuousLinearMap`-valued `2`-form (the shape in which `proj02_diff_bound` estimates the
difference of the two `(0,2)`-projections). -/
def dTwoLambda {n : ℕ} (ρ : Cn n → Cn n →L[ℝ] ℂ) : Cn n → Cn n →L[ℝ] Cn n →L[ℝ] ℂ :=
  fun z => ((fderiv ℝ ρ z).flip).flip - (fderiv ℝ ρ z).flip

/-- The curried `2`-form `dTwoLambda ρ` evaluates to `dOne ρ`. -/
lemma dTwoLambda_apply {n : ℕ} {ρ : Cn n → Cn n →L[ℝ] ℂ} {z : Cn n}
    (hρ : DifferentiableAt ℝ ρ z) (V W : Cn n) : dTwoLambda ρ z V W = dOne ρ z V W := by
  have h1 : fderiv ℝ (fun z' : Cn n => ρ z' W) z = (fderiv ℝ ρ z).flip W := by
    rw [fderiv_clm_apply hρ (differentiableAt_const W)]
    simp
  have h2 : fderiv ℝ (fun z' : Cn n => ρ z' V) z = (fderiv ℝ ρ z).flip V := by
    rw [fderiv_clm_apply hρ (differentiableAt_const V)]
    simp
  rw [dOne, h1, h2, dTwoLambda]
  simp only [sub_apply, ContinuousLinearMap.flip_apply]

/-- **The sharp form-level defect bound for an arbitrary `(0,1)`-form `ρ`.**  The difference of the
`(0,2)`-projections of `dOne ρ` for `Jstd + A` and `Jstd` is `O(ε·‖dTwoLambda ρ z‖)` with no
derivative of `A`: this is `proj02_diff_bound` transported to the `dOne`-shaped `2`-form (whose
values are the exterior derivative of the `1`-form `ρ`; `‖dTwoLambda ρ z‖ ≍ ‖fderiv ℝ ρ z‖`). -/
theorem defect_form_bound {n : ℕ} : ∃ C : ℝ, 0 < C ∧
    ∀ (A : Cn n → Cn n →L[ℝ] Cn n) (ε : ℝ), 0 ≤ ε → ε ≤ 1 → (∀ z, ‖A z‖ ≤ ε) →
    ∀ (ρ : Cn n → Cn n →L[ℝ] ℂ), (∀ z, DifferentiableAt ℝ ρ z) → ∀ (z V W : Cn n),
      ‖proj02 (JstdCn n + A) (fun z' => dOne ρ z') z V W
          - proj02 (JstdCn n) (fun z' => dOne ρ z') z V W‖
        ≤ C * ε * ‖dTwoLambda ρ z‖ * ((‖V‖ + 1) * (‖W‖ + 1)) := by
  obtain ⟨C, hC, hbound⟩ := proj02_diff_bound (n := n)
  refine ⟨C, hC, ?_⟩
  intro A ε hε0 hε1 hA ρ hρ z V W
  have hfun : (fun z' : Cn n => dOne ρ z') = fun z' a b => (dTwoLambda ρ z') a b := by
    funext z' a b
    exact (dTwoLambda_apply (hρ z') a b).symm
  rw [hfun]
  exact hbound A ε hε0 hε1 hA (dTwoLambda ρ) z V W

/-- **The sharp form-level defect bound in the form used by the defect step.**  For `w` smooth with
`ρ := ∂̄_{Jstd+A}w` and `ξ := Lzero A w`, the identity `∂̄₀ξ = -L¹_Aρ` (`defect_form_identity`)
upgrades the boundary above to a bound on `∂̄₀ξ` itself:
`‖(∂̄₀ξ)(z)(V,W)‖ ≤ C ε ‖dTwoLambda ρ z‖ (‖V‖+1)(‖W‖+1)`. -/
theorem defect_Lzero_bound {n : ℕ} : ∃ C : ℝ, 0 < C ∧
    ∀ (A : Cn n → Cn n →L[ℝ] Cn n) (ε : ℝ), 0 ≤ ε → ε ≤ 1 → (∀ z, ‖A z‖ ≤ ε) →
    ∀ (w : Cn n → ℂ)
      (hadd : dOne (fun z' => dbarCn (JstdCn n + A) w z')
        = fun z V W => dOne (fun z' => dbarCn (JstdCn n) w z') z V W
            + dOne (Lzero A w) z V W)
      (hint : ∀ z V W, proj02 (JstdCn n + A)
        (fun z' => dOne (fun z'' => dbarCn (JstdCn n + A) w z'') z') z V W = 0)
      (hstd : ∀ z V W, proj02 (JstdCn n)
        (fun z' => dOne (fun z'' => dbarCn (JstdCn n) w z'') z') z V W = 0),
      (∀ z, DifferentiableAt ℝ (fun z' => dbarCn (JstdCn n + A) w z') z) →
      ∀ (z V W : Cn n),
      ‖proj02 (JstdCn n) (fun z' => dOne (Lzero A w) z') z V W‖
        ≤ C * ε * ‖dTwoLambda (fun z' => dbarCn (JstdCn n + A) w z') z‖
            * ((‖V‖ + 1) * (‖W‖ + 1)) := by
  obtain ⟨C, hC, hbound⟩ := defect_form_bound (n := n)
  refine ⟨C, hC, ?_⟩
  intro A ε hε0 hε1 hA w hadd hint hstd hρ z V W
  rw [defect_form_identity hadd hint hstd z V W, norm_neg]
  exact hbound A ε hε0 hε1 hA (fun z' => dbarCn (JstdCn n + A) w z') hρ z V W

end Work.NN.Final
