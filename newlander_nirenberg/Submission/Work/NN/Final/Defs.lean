/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# `Submission/Work/NN/Final`: the assembly chapter for the general `n` case

This directory is the **assembly chapter** of the general-`n` case of Newlander–Nirenberg.  It
works in the flat model `ℂⁿ = Fin n → ℂ` and turns

* the **open flat `∂̄`-Poincaré lemmas on nested polydiscs** — right inverses of `∂̄₀` on
  `(0,1)`-forms and of `∂̄₀` on `(0,2)`-forms, for data which is closed *on the polydisc* (not
  only globally), with a gain of one derivative in the `C^{k,α}` scale and mapping smooth data to
  smooth solutions (the classical content; the supported versions are in `Work/CR/Flat`), and

* the **integrability identity** `∂̄₀ L_A = -L^{(2)}_A ∘ ∂̄_J` read off from `∂̄_J² = 0`
  (`Work.NN.Core.dbar_sq_zero`),

into a **right inverse of `∂̄_J` on `∂̄_J`-closed data on a polydisc** with the per-level
`C^{m,α}` estimates, and hence into `Submission.DbarSolvable` for every `n`.

## The interfaces

* `FlatOne n α ρ`: the `(0,1)`-level Poincaré datum.  Its `T1` is a *linear* operator such that a
  form which is `∂̄`-closed on the polydisc of radii `4ρ` has a primitive, computed by `T1`, on the
  polydisc of radii `2ρ`, with
  `‖T1 f‖_{C^{k+1,α}(2ρ)} ≤ C k · Σ_j ‖f_j‖_{C^{k,α}(4ρ)}`.
* `FlatTwo n α ρ`: the same at the `(0,2)`-level (the potential of a `∂̄`-closed `(0,2)`-form).
* `FlatDbar n α ρ`: the pair.

## The assembly

`Perturb.lean` derives from `FlatDbar` a right inverse of `∂̄_{Jstd+A}` on `∂̄_{Jstd+A}`-closed
data, with the estimates of `Work.NN.Core.DbarSolverH`; `Main.lean` transports it to `E n` and
derives `Submission.DbarSolvable` for every `n`.
-/
import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Polydisc.dbarCoord_comm

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Final

open Work.CR.Flat

variable {n : ℕ}

/-! ## Polydiscs of the scaled family -/

/-- The polydisc of centre `0` and radii `c * ρ`. -/
def pd (n : ℕ) (ρ : Fin n → ℝ) (c : ℝ) : Set (Fin n → ℂ) :=
  polydisc 0 (fun j => c * ρ j)

lemma mem_pd {ρ : Fin n → ℝ} {c : ℝ} {z : Fin n → ℂ} :
    z ∈ pd n ρ c ↔ ∀ j, ‖z j‖ < c * ρ j := by
  simp [pd, polydisc]

lemma isOpen_pd (ρ : Fin n → ℝ) (c : ℝ) : IsOpen (pd n ρ c) := isOpen_polydisc 0 _

lemma pd_mono {ρ : Fin n → ℝ} {c c' : ℝ} (hρ : ∀ j, 0 < ρ j) (h : c ≤ c') :
    pd n ρ c ⊆ pd n ρ c' :=
  polydisc_mono fun j => mul_le_mul_of_nonneg_right h (le_of_lt (hρ j))

lemma pd_one_subset_two {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) : pd n ρ 1 ⊆ pd n ρ 2 :=
  pd_mono hρ (by norm_num)

lemma pd_two_subset_four {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) : pd n ρ 2 ⊆ pd n ρ 4 :=
  pd_mono hρ (by norm_num)

lemma pd_one_subset_four {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) : pd n ρ 1 ⊆ pd n ρ 4 :=
  (pd_one_subset_two hρ).trans (pd_two_subset_four hρ)

/-! ## Closedness of forms on a polydisc -/

/-- A `(0,1)`-form is closed on the polydisc `pd n ρ c` when `∂̄_j f_l = ∂̄_l f_j` there. -/
def Clos1 (n : ℕ) (ρ : Fin n → ℝ) (c : ℝ) (f : Fin n → (Fin n → ℂ) → ℂ) : Prop :=
  ∀ j l z, z ∈ pd n ρ c → dbarCoord j (f l) z = dbarCoord l (f j) z

/-- A `(0,2)`-form `η` is closed on `pd n ρ c` when its `∂̄` (a `(0,3)`-form) vanishes there. -/
def Clos2 (n : ℕ) (ρ : Fin n → ℝ) (c : ℝ)
    (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) : Prop :=
  ∀ j l m z, z ∈ pd n ρ c →
    dbarCoord j (η l m) z - dbarCoord l (η j m) z + dbarCoord m (η j l) z = 0

/-! ## The `∂̄`-operators at the level of coefficient families

`dbarOne J u j z` is the `j`-th coefficient of `∂̄_J u` and `ddbar J a j l z` the `(j,l)`-coefficient
of the `(0,2)`-form `∂̄_J a` for a `(0,1)`-form with coefficients `a`.  The two agree with
`Work.CR.Flat.dbarCoord` when `J` is the standard structure (`dbarOne_std`, `ddbar_std`). -/

/-- The `j`-th coefficient of `∂̄_J u` at `z`. -/
def dbarOne {n : ℕ} (J : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ))
    (u : (Fin n → ℂ) → ℂ) (j : Fin n) (z : Fin n → ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ u z (Pi.single j 1)
    + Complex.I * fderiv ℝ u z (J z (Pi.single j 1)))

/-- The `(j,l)`-coefficient of the `(0,2)`-form `∂̄_J a`, for a `(0,1)`-form with coefficients
`a`. -/
def ddbar {n : ℕ} (J : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ))
    (a : Fin n → (Fin n → ℂ) → ℂ) (j l : Fin n) (z : Fin n → ℂ) : ℂ :=
  dbarOne J (a l) j z - dbarOne J (a j) l z

@[simp] lemma dbarOne_std {n : ℕ} (u : (Fin n → ℂ) → ℂ) (j : Fin n) (z : Fin n → ℂ) :
    dbarOne (Work.NN.Core.JstdCn n) u j z = dbarCoord j u z := by
  simp only [dbarOne, dbarCoord, Work.NN.Core.JstdCn_apply,
    Work.NN.Core.smul_single_I]

lemma ddbar_std {n : ℕ} (a : Fin n → (Fin n → ℂ) → ℂ) (j l : Fin n) (z : Fin n → ℂ) :
    ddbar (Work.NN.Core.JstdCn n) a j l z = dbarCoord j (a l) z - dbarCoord l (a j) z := by
  simp [ddbar]

lemma Clos1_iff_ddbar_std {ρ : Fin n → ℝ} {c : ℝ} {f : Fin n → (Fin n → ℂ) → ℂ} :
    Clos1 n ρ c f ↔ ∀ j l z, z ∈ pd n ρ c → ddbar (Work.NN.Core.JstdCn n) f j l z = 0 := by
  simp only [Clos1, ddbar_std, sub_eq_zero]

/-- The `(0,2)`-level perturbation operator: `(L^{(2)}_A a)_{jl} = (L_A a_l)_j - (L_A a_j)_l`. -/
def L2 {n : ℕ} (A : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ))
    (a : Fin n → (Fin n → ℂ) → ℂ) (j l : Fin n) (z : Fin n → ℂ) : ℂ :=
  Work.NN.Core.Lcoef A (a l) j z - Work.NN.Core.Lcoef A (a j) l z

/-- The linearisation of `∂̄` at the level of coefficients. -/
lemma dbarOne_pert {n : ℕ} (A : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ))
    (w : (Fin n → ℂ) → ℂ) (m : Fin n) (z : Fin n → ℂ) :
    dbarOne (Work.NN.Core.JstdCn n + A) w m z
      = dbarOne (Work.NN.Core.JstdCn n) w m z + Work.NN.Core.Lcoef A w m z := by
  simp only [dbarOne, Work.NN.Core.Lcoef, Pi.add_apply, add_apply, map_add]
  ring

/-- The decomposition `∂̄_{Jstd+A} = ∂̄₀ + L^{(2)}_A` at the `(0,2)`-level. -/
lemma ddbar_pert_decomp {n : ℕ} (A : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ))
    (a : Fin n → (Fin n → ℂ) → ℂ) (j l : Fin n) (z : Fin n → ℂ) :
    ddbar (Work.NN.Core.JstdCn n + A) a j l z
      = ddbar (Work.NN.Core.JstdCn n) a j l z + L2 A a j l z := by
  simp only [ddbar, L2, dbarOne_pert]
  ring

/-- Differentiability of `y ↦ dbarOne J w m y`, with the hypotheses in the form in which the
callers of the additivity lemmas of this file have them. -/
lemma diffAt_dbarOne {n : ℕ} {J : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)}
    {w : (Fin n → ℂ) → ℂ} {m : Fin n} {z : Fin n → ℂ}
    (hw : ContDiffAt ℝ 2 w z) (hJ : DifferentiableAt ℝ J z) :
    DifferentiableAt ℝ (fun y => dbarOne J w m y) z := by
  have hdw : DifferentiableAt ℝ (fun y => fderiv ℝ w y) z :=
    (hw.fderiv_right (m := (1 : ℕ∞)) (by norm_num)).differentiableAt (by norm_num)
  have hJv : DifferentiableAt ℝ (fun y => J y (Pi.single m 1)) z :=
    hJ.clm_apply (differentiableAt_const _)
  have hterm : DifferentiableAt ℝ
      (fun y => (fderiv ℝ w y) (J y (Pi.single m 1))) z :=
    hdw.clm_apply hJv
  have h1 : DifferentiableAt ℝ (fun y => (fderiv ℝ w y) (Pi.single m 1)) z :=
    hdw.clm_apply (differentiableAt_const _)
  have h : (fun y => dbarOne J w m y) = fun y =>
      (1 / 2 : ℂ) * ((fderiv ℝ w y) (Pi.single m 1)
        + Complex.I * (fderiv ℝ w y) (J y (Pi.single m 1))) := rfl
  rw [h]
  exact (differentiableAt_const (1 / 2 : ℂ)).mul
    (h1.add ((differentiableAt_const Complex.I).mul hterm))

/-- Differentiability of `y ↦ Lcoef A w m y`. -/
lemma diffAt_Lcoef {n : ℕ} {A : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)}
    {w : (Fin n → ℂ) → ℂ} {m : Fin n} {z : Fin n → ℂ}
    (hw : ContDiffAt ℝ 2 w z) (hA : DifferentiableAt ℝ A z) :
    DifferentiableAt ℝ (fun y => Work.NN.Core.Lcoef A w m y) z := by
  have hdw : DifferentiableAt ℝ (fun y => fderiv ℝ w y) z :=
    (hw.fderiv_right (m := (1 : ℕ∞)) (by norm_num)).differentiableAt (by norm_num)
  have hAv : DifferentiableAt ℝ (fun y => A y (Pi.single m 1)) z :=
    hA.clm_apply (differentiableAt_const _)
  have hterm : DifferentiableAt ℝ (fun y => (fderiv ℝ w y) (A y (Pi.single m 1))) z :=
    hdw.clm_apply hAv
  have h : (fun y => Work.NN.Core.Lcoef A w m y) = fun y =>
      (Complex.I / 2) * ((fderiv ℝ w y) (A y (Pi.single m 1))) := rfl
  rw [h]
  exact (differentiableAt_const (Complex.I / 2)).mul hterm

/-- Additivity of the coefficient of `∂̄` in the function (differentiability is needed because
`fderiv` is defined to be `0` at non-differentiable points). -/
lemma dbarOne_add {n : ℕ} (J : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ))
    {a b : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ} (ha : DifferentiableAt ℝ a z)
    (hb : DifferentiableAt ℝ b z) (m : Fin n) :
    dbarOne J (fun y => a y + b y) m z = dbarOne J a m z + dbarOne J b m z := by
  have hfd : fderiv ℝ (fun y => a y + b y) z = fderiv ℝ a z + fderiv ℝ b z := fderiv_add ha hb
  simp only [dbarOne, hfd, add_apply, map_add]
  ring

/-- Subadditivity of the coefficient of `∂̄` in the function. -/
lemma dbarOne_sub {n : ℕ} (J : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ))
    {a b : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ} (ha : DifferentiableAt ℝ a z)
    (hb : DifferentiableAt ℝ b z) (m : Fin n) :
    dbarOne J (fun y => a y - b y) m z = dbarOne J a m z - dbarOne J b m z := by
  have hfd : fderiv ℝ (fun y => a y - b y) z = fderiv ℝ a z - fderiv ℝ b z := fderiv_sub ha hb
  simp only [dbarOne, hfd, sub_apply, map_sub]
  ring

/-- Linearity of the perturbation `L_A` in its argument. -/
lemma Lcoef_sub {n : ℕ} (A : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ))
    {a b : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ} (ha : DifferentiableAt ℝ a z)
    (hb : DifferentiableAt ℝ b z) (j : Fin n) :
    Work.NN.Core.Lcoef A (fun y => a y - b y) j z
      = Work.NN.Core.Lcoef A a j z - Work.NN.Core.Lcoef A b j z := by
  have hfd : fderiv ℝ (fun y => a y - b y) z = fderiv ℝ a z - fderiv ℝ b z := fderiv_sub ha hb
  simp only [Work.NN.Core.Lcoef, hfd, sub_apply]
  ring

/-- Additivity of the `(0,2)`-form `∂̄_J` in the coefficient family. -/
lemma ddbar_add {n : ℕ} (J : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ))
    {a b : Fin n → (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (ha : ∀ m, DifferentiableAt ℝ (a m) z) (hb : ∀ m, DifferentiableAt ℝ (b m) z)
    (j l : Fin n) :
    ddbar J (fun m y => a m y + b m y) j l z = ddbar J a j l z + ddbar J b j l z := by
  simp only [ddbar, dbarOne_add J (ha _) (hb _)]
  ring

/-- Subadditivity of the `(0,2)`-form `∂̄_J` in the coefficient family. -/
lemma ddbar_sub {n : ℕ} (J : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ))
    {a b : Fin n → (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (ha : ∀ m, DifferentiableAt ℝ (a m) z) (hb : ∀ m, DifferentiableAt ℝ (b m) z)
    (j l : Fin n) :
    ddbar J (fun m y => a m y - b m y) j l z = ddbar J a j l z - ddbar J b j l z := by
  simp only [ddbar, dbarOne_sub J (ha _) (hb _)]
  ring

/-- Subadditivity of `L^{(2)}_A`. -/
lemma L2_sub {n : ℕ} (A : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ))
    {a b : Fin n → (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (ha : ∀ m, DifferentiableAt ℝ (a m) z) (hb : ∀ m, DifferentiableAt ℝ (b m) z)
    (j l : Fin n) :
    L2 A (fun m y => a m y - b m y) j l z = L2 A a j l z - L2 A b j l z := by
  simp only [L2, Lcoef_sub _ (ha _) (hb _)]
  ring

/-- `∂̄₀² = 0` at the level of coefficients: the `(0,2)`-form `∂̄₀(∂̄₀w)` vanishes. -/
lemma ddbar_std_self {n : ℕ} {w : (Fin n → ℂ) → ℂ} (hw : ContDiff ℝ 2 w)
    (j l : Fin n) (z : Fin n → ℂ) :
    ddbar (Work.NN.Core.JstdCn n) (fun m y => dbarOne (Work.NN.Core.JstdCn n) w m y) j l z
      = 0 := by
  have hd : (fun m y => dbarOne (Work.NN.Core.JstdCn n) w m y)
      = fun m y => dbarCoord m w y := by
    funext m y; exact dbarOne_std w m y
  rw [hd]
  simp only [ddbar, dbarOne_std]
  rw [Work.CR.Flat.Polydisc.dbarCoord_comm l j w z (hw.contDiffAt)]
  ring

/-- `ddbar J a` is antisymmetric in its two form indices. -/
lemma ddbar_antisymm {J : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)}
    (a : Fin n → (Fin n → ℂ) → ℂ) (j l : Fin n) (z : Fin n → ℂ) :
    ddbar J a j l z = - ddbar J a l j z := by
  simp only [ddbar]
  ring

/-! ## The `(0,2)`-projection of a form (the *correct* operator)

`dOne α z V W` is the exterior derivative of the `1`-form `α` at `z`, evaluated on the fixed
vectors `(V,W)`, and `proj02 J Ω z V W` is the `J`-`(0,2)`-projection of the `2`-form `Ω` at `z`,
evaluated on `(V,W)` — the formula of `Work.NN.Core.dbarSq` / `Work.AlmostComplex.Types.proj02`.
These are the *form-level* operators: `proj02 J (dOne (dbarCn J v)) = 0` is integrability
(`Work.NN.Core.dbar_sq_zero`), and they are **not** the coefficient-level operators of the flat
chapter (`dbarOne`, `ddbar`) once `J` is non-constant; see `README.md` §4. -/

/-- The exterior derivative of a `1`-form at `z`, evaluated on `(V,W)`. -/
def dOne {n : ℕ} (α : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] ℂ) (z V W : Fin n → ℂ) : ℂ :=
  fderiv ℝ (fun z' : Fin n → ℂ => α z' W) z V - fderiv ℝ (fun z' : Fin n → ℂ => α z' V) z W

/-- The `J`-`(0,2)`-projection of a `2`-form (given by its values) at `z`, evaluated on `(V,W)`. -/
def proj02 {n : ℕ} (J : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ))
    (Ω : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ) (z V W : Fin n → ℂ) : ℂ :=
  (1 / 4 : ℂ) * (Ω z V W + Complex.I * Ω z (J z V) W + Complex.I * Ω z V (J z W)
    - Ω z (J z V) (J z W))

/-- A `C^{0,α}`-bound (supremum **and** Hölder seminorm) for a *vector-valued* function, with
constant `ε` — the form in which the estimates below consume the smallness of the perturbation
(the workspace's `holderNorm` is only defined for `ℂ`-valued functions). -/
def VecHolder {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : (Fin n → ℂ) → E) (α ε : ℝ) (Ω : Set (Fin n → ℂ)) : Prop :=
  (∀ z ∈ Ω, ‖φ z‖ ≤ ε) ∧ (∀ z ∈ Ω, ∀ z' ∈ Ω, ‖φ z - φ z'‖ ≤ ε * ‖z - z'‖ ^ α)

/-! ## The interfaces -/

/-- **The `(0,1)`-level open flat `∂̄`-Poincaré on nested polydiscs.**

`T1` is a linear primitive operator: on the polydisc `pd n ρ 4` (where the data are closed) it
produces, on `pd n ρ 2`, a solution of `∂̄_j u = f_j`, with a gain of one derivative in the
`C^{k,α}` scale and mapping smooth data to smooth primitives. -/
structure FlatOne (n : ℕ) (α : ℝ) (ρ : Fin n → ℝ) where
  /-- the radii are positive -/
  hρ : ∀ j, 0 < ρ j
  /-- `0 < α < 1` -/
  hα0 : 0 < α
  hα1 : α < 1
  /-- the constants in the `C^{k,α}` estimates -/
  C1 : ℕ → ℝ
  hC1 : ∀ k, 0 < C1 k
  /-- the primitive operator -/
  T1 : (Fin n → (Fin n → ℂ) → ℂ) →ₗ[ℝ] ((Fin n → ℂ) → ℂ)
  /-- `T1 f` solves `∂̄ u = f` on `pd n ρ 2` when `f` is closed on `pd n ρ 4` -/
  T1_solves : ∀ f : Fin n → (Fin n → ℂ) → ℂ,
    (∀ j : Fin n, ContDiffOn ℝ (1 : ℕ∞) (f j) (pd n ρ 4)) → Clos1 n ρ 4 f →
      ∀ (j : Fin n) (z : Fin n → ℂ), z ∈ pd n ρ 2 → dbarCoord j (T1 f) z = f j z
  /-- the gain of one derivative in the `C^{k,α}` scale -/
  T1_est : ∀ (k : ℕ) (f : Fin n → (Fin n → ℂ) → ℂ),
    (∀ j : Fin n, ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞) (f j) (pd n ρ 4)) → Clos1 n ρ 4 f →
      holderNorm (k + 1) α (T1 f) (pd n ρ 2)
        ≤ ENNReal.ofReal (C1 k) * ∑ j, holderNorm k α (f j) (pd n ρ 4)
  /-- smooth data give a smooth primitive -/
  T1_smooth : ∀ f : Fin n → (Fin n → ℂ) → ℂ,
    (∀ j : Fin n, ContDiffOn ℝ ∞ (f j) (pd n ρ 4)) → Clos1 n ρ 4 f →
      ContDiffOn ℝ ∞ (T1 f) (pd n ρ 2)

/-- **The `(0,2)`-level open flat `∂̄`-Poincaré on nested polydiscs.**

`T2` is a linear potential operator: a `(0,2)`-form `η` which is closed (as a `(0,2)`-form) on
`pd n ρ 4` has, on `pd n ρ 2`, a `(0,1)`-form potential `T2 η` with
`∂̄_j (T2 η)_l - ∂̄_l (T2 η)_j = η_{jl}`, again with a gain of one derivative and mapping smooth data
to smooth potentials. -/
structure FlatTwo (n : ℕ) (α : ℝ) (ρ : Fin n → ℝ) where
  /-- the radii are positive -/
  hρ : ∀ j, 0 < ρ j
  /-- `0 < α < 1` -/
  hα0 : 0 < α
  hα1 : α < 1
  /-- the constants in the `C^{k,α}` estimates -/
  C2 : ℕ → ℝ
  hC2 : ∀ k, 0 < C2 k
  /-- the potential operator -/
  T2 : (Fin n → Fin n → (Fin n → ℂ) → ℂ) →ₗ[ℝ] (Fin n → (Fin n → ℂ) → ℂ)
  /-- `T2 η` solves `∂̄_j ψ_l - ∂̄_l ψ_j = η_{jl}` on `pd n ρ 2` when `η` is closed on `pd n ρ 4` -/
  T2_solves : ∀ η : Fin n → Fin n → (Fin n → ℂ) → ℂ,
    (∀ j l : Fin n, ContDiffOn ℝ (1 : ℕ∞) (η j l) (pd n ρ 4)) →
    (∀ j l : Fin n, ∀ z : Fin n → ℂ, η j l z = - η l j z) → Clos2 n ρ 4 η →
      ∀ j l : Fin n, ∀ z : Fin n → ℂ, z ∈ pd n ρ 2 →
        dbarCoord j (T2 η l) z - dbarCoord l (T2 η j) z = η j l z
  /-- the gain of one derivative in the `C^{k,α}` scale -/
  T2_est : ∀ (k : ℕ) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ),
    (∀ j l : Fin n, ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞) (η j l) (pd n ρ 4)) →
    (∀ j l : Fin n, ∀ z : Fin n → ℂ, η j l z = - η l j z) → Clos2 n ρ 4 η → ∀ j : Fin n,
      holderNorm (k + 1) α (T2 η j) (pd n ρ 2)
        ≤ ENNReal.ofReal (C2 k) * ∑ j, ∑ l, holderNorm k α (η j l) (pd n ρ 4)
  /-- smooth data give a smooth potential -/
  T2_smooth : ∀ η : Fin n → Fin n → (Fin n → ℂ) → ℂ,
    (∀ j l : Fin n, ContDiffOn ℝ ∞ (η j l) (pd n ρ 4)) →
    (∀ j l : Fin n, ∀ z : Fin n → ℂ, η j l z = - η l j z) → Clos2 n ρ 4 η →
      ∀ j : Fin n, ContDiffOn ℝ ∞ (T2 η j) (pd n ρ 2)

/-- The pair of flat Poincaré operators needed by the perturbation argument. -/
structure FlatDbar (n : ℕ) (α : ℝ) (ρ : Fin n → ℝ) where
  /-- the `(0,1)`-level operator -/
  one : FlatOne n α ρ
  /-- the `(0,2)`-level operator -/
  two : FlatTwo n α ρ

/-! ## The Calderón–Zygmund projection `Π₀ = 1 - T₂∂̄₀`

`proj F η := η - T₂ (∂̄₀ η)` is the projection of a `(0,1)`-form onto the closed forms along the
range of the `(0,2)`-potential operator: it kills `range T₂` and its image consists of closed
forms (`proj_closed`), which is exactly what is needed to apply `T1`. -/

/-- The defect-corrected projection `Π₀ = 1 - T₂∂̄₀`. -/
def proj {n : ℕ} {α : ℝ} {ρ : Fin n → ℝ} (F : FlatTwo n α ρ) :
    (Fin n → (Fin n → ℂ) → ℂ) → (Fin n → (Fin n → ℂ) → ℂ) :=
  fun f => f - F.T2 (fun j l z => ddbar (Work.NN.Core.JstdCn n) f j l z)

@[simp] lemma proj_apply {n : ℕ} {α : ℝ} {ρ : Fin n → ℝ} (F : FlatTwo n α ρ)
    (f : Fin n → (Fin n → ℂ) → ℂ) (j : Fin n) (z : Fin n → ℂ) :
    proj F f j z = f j z - F.T2 (fun j l z => ddbar (Work.NN.Core.JstdCn n) f j l z) j z := rfl

end Work.NN.Final
