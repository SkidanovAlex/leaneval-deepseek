/-
# Propagation of the functional equations: definitions

The CKMRV generating function `F` is defined on the `Γ(2)`-fundamental domain `𝒟` by the
contour integral (5.2), and is extended to the whole upper half plane by *analytic
continuation*: CKMRV Proposition 3.2 ("Propagation and extension", Section 3.1).  The two
functional equations of Theorem 3.1 constrain `F` only through its defects

  `(T-I)²`  and  `S(T-I)²`,

so the continuation only has to be compatible with those two defects; the propagation
proposition says that this pins the extension down on all of `ℍ`.

The slash operator is a *right* action (`Work.Kernels.slash_mul`), so the CKMRV defect
`f|_k S(T-I)²` is the slash by the group algebra element `S·(T-I)²`, i.e. it acts by `S` first
and by `(T-I)²` afterwards, and it evaluates `f` at the three points `S·τ`, `S·(τ+1)`,
`S·(τ+2)`.  This is `Work.Asymptotics.S2op` below.  The `(T-I)²`-defect is weight-independent
(`j(T,τ) = 1`), so it is just `Work.Kernels.T2op`.

## Main definitions

* `Work.Asymptotics.S2op k f` : the `S(T-I)²`-defect `Work.Kernels.slash k (R_S*(R_T-1)²) f`.
* `Work.Asymptotics.Propagates k O f h₁ h₂` : the hypotheses of CKMRV Proposition 3.2(1) for the
  holomorphic function `f` on the open set `O`, with defects `h₁`, `h₂`.

The two propagation theorems themselves (**CKMRV Proposition 3.2(1)** and **(2)**) are developed
in the companion modules `Submission.Work.Asymptotics.exists_extension_of_propagates`,
`Submission.Work.Asymptotics.inP_of_propagates` and
`Submission.Work.Asymptotics.bound_of_propagates`; this file only sets up the interface.
-/
import Mathlib
import Submission.Work.Kernels.All
import Submission.Work.Asymptotics.DomainD

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels

/-- The `S(T-I)²`-defect `f|_k S(T-I)²`, i.e. the weight-`k` slash of `f` by the group algebra
element `S·(T-I)²` of `Work.Kernels.R`.  Since the slash action is a right action this is
`(f|_k S)|_k (T-I)² = T2op (f|_k S)`, which evaluates `f` at `S·τ`, `S·(τ+1)` and `S·(τ+2)`
(the two are genuinely different operators: `(T-I)²` does not commute with `S`). -/
def S2op (k : ℤ) (f : ℍ → ℂ) : ℍ → ℂ :=
  Work.Kernels.slash k (Work.Kernels.R_S * (Work.Kernels.R_T - 1) ^ 2) f

/-- **CKMRV Proposition 3.2, hypotheses.**  `Propagates k O f h₁ h₂` says: `O` is an open subset
of `ℍ`, `f` is holomorphic on `O`, `h₁` and `h₂` are holomorphic on `ℍ`, and the two defects of
`f` agree with `h₁` and `h₂` wherever both sides are defined:

* `(T-I)²f = h₁` on `O ∩ T⁻¹O ∩ T⁻²O`;
* `S(T-I)²f = h₂` on `SO ∩ T⁻¹SO ∩ T⁻²SO`. -/
def Propagates (k : ℤ) (O : Set ℍ) (f h₁ h₂ : ℍ → ℂ) : Prop :=
  IsOpen O ∧ MDiff h₁ ∧ MDiff h₂ ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f O ∧
  (∀ τ : ℍ, τ ∈ O → (1 : ℝ) +ᵥ τ ∈ O → (2 : ℝ) +ᵥ τ ∈ O → T2op f τ = h₁ τ) ∧
  (∀ τ : ℍ, ModularGroup.S • τ ∈ O → ModularGroup.S • ((1 : ℝ) +ᵥ τ) ∈ O →
    ModularGroup.S • ((2 : ℝ) +ᵥ τ) ∈ O → S2op k f τ = h₂ τ)

/-- The hypotheses of `Propagates` are monotone in the open set. -/
lemma Propagates.mono {k : ℤ} {O O' : Set ℍ} {f h₁ h₂ : ℍ → ℂ} (h : Propagates k O f h₁ h₂)
    (hsub : O' ⊆ O) (hopen : IsOpen O') : Propagates k O' f h₁ h₂ :=
  ⟨hopen, h.2.1, h.2.2.1, h.2.2.2.1.mono hsub,
   fun τ h1 h2 h3 => h.2.2.2.2.1 τ (hsub h1) (hsub h2) (hsub h3),
   fun τ h1 h2 h3 => h.2.2.2.2.2 τ (hsub h1) (hsub h2) (hsub h3)⟩


/-- The first defect of `Propagates` is the slash by `(T-I)²`: the definition above is
weight-independent. -/
lemma T2op_eq_slash_T2 (k : ℤ) (f : ℍ → ℂ) :
    T2op f = Work.Kernels.slash k ((Work.Kernels.R_T - 1) ^ 2) f :=
  (Work.Kernels.slash_T2 k f).symm

/-- `S(T-I)²` acts by `S` first: `S2op k f = T2op (f|_k S)`. -/
lemma S2op_eq_T2op_slash (k : ℤ) (f : ℍ → ℂ) :
    S2op k f = T2op (Work.Kernels.slash k Work.Kernels.R_S f) := by
  rw [S2op, Work.Kernels.AlgebraFacts.slash_mul, Work.Kernels.slash_T2]

/-- Pointwise form of `S2op`: `(f|_k S(T-I)²) τ` evaluates `f|_k S` at `τ`, `τ+1`, `τ+2`. -/
lemma S2op_apply_eq (k : ℤ) (f : ℍ → ℂ) (τ : ℍ) :
    S2op k f τ = (f ∣[k] ModularGroup.S) ((2 : ℝ) +ᵥ τ)
      - 2 * (f ∣[k] ModularGroup.S) ((1 : ℝ) +ᵥ τ) + (f ∣[k] ModularGroup.S) τ := by
  rw [S2op_eq_T2op_slash]
  simp only [T2op, Work.Kernels.slash_R_S]

end Work.Asymptotics
