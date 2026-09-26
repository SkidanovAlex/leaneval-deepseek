import Mathlib
import Submission.Work.Modular.Basic

/-!
# The slash defect of a quasi-modular form

A quasi-modular form of weight `k` and depth at most `1` is, by definition
(`IsQuasiModularForm`), a function of the shape

  `f = E₂ ^ 0 * m₀ + E₂ ^ 1 * m₁ = m₀ + E₂ * m₁`

with `m₀` a holomorphic modular form of weight `k` and `m₁` a holomorphic modular form
of weight `k - 2` for `SL(2, ℤ)`.

This file proves the *intrinsic* (cocycle) form of that statement
(`IsQuasiModularSlash k f`): for every `γ ∈ SL(2, ℤ)` the slash defect of `f` is `m₁`
times the `E₂`-defect,

  `f ∣[k] γ - f = (E₂ ∣[2] γ - E₂) * m₁`.

This is the form in which quasi-modularity is used in the CKMRV interpolation problem:
the failure of `f` to be modular is entirely accounted for by the failure of `E₂`.

The proof is the multiplicative behaviour of the slash action
(`ModularForm.mul_slash_SL2`) together with slash invariance of `m₀` and `m₁`.  The one
formal point of care is that the `j`-th summand of `IsQuasiModularFormDepth 1 k` has
weight `k - 2 * (j : ℤ)`, so the summands `m 0` and `m 1` carry the weights
`k - 2 * ↑(0 : Fin 2)` and `k - 2 * ↑(1 : Fin 2)`; the second is definitionally `k - 2`,
while the first is only *propositionally* `k`, and needs the transport below.
-/

namespace Work.Modular

open UpperHalfPlane ModularForm
open scoped Manifold MatrixGroups ModularForm

/-- A modular form of weight `k` for `SL(2, ℤ)` is invariant under the weight-`k` slash
action of every `γ ∈ SL(2, ℤ)`: `⇑g ∣[k] γ = ⇑g`.

This is `SlashInvariantForm.slash_action_eq'` for the image of `SL(2, ℤ)` in
`GL(2, ℝ)`, transported back along the definitional equality `ModularForm.SL_slash`. -/
theorem modularForm_slash_eq_self {k : ℤ} (g : ModularForm 𝒮ℒ k) (γ : SL(2, ℤ)) :
    ⇑g ∣[k] γ = ⇑g :=
  g.slash_action_eq' (γ : GL (Fin 2) ℝ) (MonoidHom.mem_range.mpr ⟨γ, rfl⟩)

/-- If `f` is a quasi-modular form of weight `k` and depth at most `1`, then its slash
defect is a modular form of weight `k - 2` times the `E₂`-defect; i.e. the intrinsic
cocycle formulation `IsQuasiModularSlash k f` holds. -/
theorem slash_defect {k : ℤ} {f : ℍ → ℂ} (hf : IsQuasiModularForm k f) :
    IsQuasiModularSlash k f := by
  obtain ⟨m, hm⟩ := hf
  intro γ
  have hmem : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := MonoidHom.mem_range.mpr ⟨γ, rfl⟩
  -- `f` is the sum of its two depth-one summands: `f = m₀ + E₂ * m₁`.
  have hd : f = ⇑(m 0) + E2 * ⇑(m 1) := by
    rw [hm, Fin.sum_univ_two]
    simp
  -- `m 0` has weight `k - 2 * ↑(0 : Fin 2)`, which is `k` only propositionally.
  have hw0 : k - 2 * ((0 : Fin 2) : ℤ) = k := by norm_num
  -- The weight-`k` summand `m₀` is slash-invariant.
  have h0 : ⇑(m 0) ∣[k] γ = ⇑(m 0) := by
    have h := (m 0).slash_action_eq' (γ : GL (Fin 2) ℝ) hmem
    have hc := congrArg (fun w : ℤ => (m 0).toFun ∣[w] (γ : GL (Fin 2) ℝ)) hw0
    rwa [hc] at h
  -- The weight-`(k - 2)` summand `m₁` is slash-invariant.
  have h1 : ⇑(m 1) ∣[k - 2] γ = ⇑(m 1) := modularForm_slash_eq_self (m 1) γ
  -- Hence the second summand acquires the `E₂`-defect: `(E₂ * m₁) ∣[k] γ = (E₂ ∣[2] γ) * m₁`.
  have h2 : (E2 * ⇑(m 1)) ∣[k] γ = (E2 ∣[(2 : ℤ)] γ) * ⇑(m 1) := by
    have h := ModularForm.mul_slash_SL2 (2 : ℤ) (k - 2) γ E2 (⇑(m 1))
    rw [show (2 : ℤ) + (k - 2) = k from by ring] at h
    rw [h, h1]
  refine ⟨m 1, ?_⟩
  rw [hd, SlashAction.add_slash, h0, h2]
  ext τ
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  ring

end Work.Modular
