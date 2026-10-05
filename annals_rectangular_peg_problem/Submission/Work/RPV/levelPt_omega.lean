import Mathlib
import Submission.Work.RPV.Defs
import Submission.Work.RPV.hasDerivAt_levelPt_fst
import Submission.Work.RPV.hasDerivAt_levelPt_snd
import Submission.Work.RPV.symp_levelPt_algebra

/-!
# `Work.RPV.levelPt_omega`

The level-curve symplectic identity of the rectangular-peg generating-function route.

`levelPt u σ a` is the point of the level `K₀ = -1 - σ` with reduced coordinate `u` and phase
`q₂ = a`:

`levelPt u σ a = (((e^{-ia} u).im, a), ((e^{-ia} u).re, ‖u‖²/2 - σ - 1))`.

For a two-parameter family of level curves, written in reduced coordinates as
`P(σ, t) = levelPt (Γ σ t) σ (A σ t)`, the symplectic form of the two partial derivatives is

`ω(∂_σ P, ∂_t P) = ω_ℂ(∂_σ Γ, ∂_t Γ) - ∂_t A`,

i.e. *the family is Lagrangian iff `∂_t A = ω_ℂ(∂_σ Γ, ∂_t Γ)`* (the "area law" of the route).

The proof is a straight computation, and is assembled here from three independent pieces
(delegated to sibling modules of this directory):

* `Work.RPV.hasDerivAt_levelPt_fst` — the partial derivative in `σ` of
  `s ↦ levelPt (Γ s t) s (A s t)`;
* `Work.RPV.hasDerivAt_levelPt_snd` — the partial derivative in `t` of
  `s ↦ levelPt (Γ σ s) σ (A σ s)`;
* `Work.RPV.symp_levelPt_algebra` — the pure complex algebra: after substituting the two
  partial derivatives (writing `e = exp (-(A σ t) i)`, `z = Γ σ t`, which has `|e| = 1`), the
  pairing `symp` collapses to `ωC Γσ Γt - At`.

What is left here is the modulus-one fact `conj e * e = 1` for `e = exp (-(a i))` and the
assembly.
-/

set_option autoImplicit false

noncomputable section

namespace Work.RPV

/-- `exp (-(a i))` has modulus one. -/
private lemma conj_exp_neg_mul_I_mul_self (a : ℝ) :
    (starRingEnd ℂ) (Complex.exp (-(a : ℂ) * Complex.I)) * Complex.exp (-(a : ℂ) * Complex.I)
      = 1 := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  have h : (starRingEnd ℂ) (-(a : ℂ) * Complex.I) + (-(a : ℂ) * Complex.I) = 0 := by
    simp [Complex.conj_I]
  rw [h, Complex.exp_zero]

theorem levelPt_omega (Γ : ℝ → ℝ → ℂ) (A : ℝ → ℝ → ℝ) (σ t : ℝ) (Γσ Γt : ℂ) (Aσ At : ℝ)
    (hΓσ : HasDerivAt (fun s => Γ s t) Γσ σ) (hΓt : HasDerivAt (fun s => Γ σ s) Γt t)
    (hAσ : HasDerivAt (fun s => A s t) Aσ σ) (hAt : HasDerivAt (fun s => A σ s) At t) :
    Work.RPV.symp (deriv (fun s => Work.RPV.levelPt (Γ s t) s (A s t)) σ)
        (deriv (fun s => Work.RPV.levelPt (Γ σ s) σ (A σ s)) t)
      = Work.RPV.ωC Γσ Γt - At := by
  have h1 := hasDerivAt_levelPt_fst Γ A σ t Γσ Aσ hΓσ hAσ
  have h2 := hasDerivAt_levelPt_snd Γ A σ t Γt At hΓt hAt
  rw [h1.deriv, h2.deriv]
  exact symp_levelPt_algebra (Γ σ t) Γσ Γt Aσ At _
    (conj_exp_neg_mul_I_mul_self (A σ t))

end Work.RPV
