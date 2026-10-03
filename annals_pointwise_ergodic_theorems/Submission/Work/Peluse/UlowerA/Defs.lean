import Mathlib
import Submission.Work.Peluse.UlowerA.Basic
import Submission.Work.Peluse.Ulower.StepLe.blindInterchangeDefs

/-!
# The unbalanced scale relation with a single constant

The target `Work.Peluse.Ulower.degree_lowering_A` replaces the *balanced* scale relation
`Scaled Ns N d` (`N^d/2 ≤ Ns ≤ 2 N^d`) of `Work.Peluse.Ulower.degree_lowering_v2` by the
*unbalanced* two-sided relation, with a natural number `A ≥ 1`:

  `(N : ℝ) ^ d ≤ A · Ns`  and  `(Ns : ℝ) ≤ A · N^d`.

Both halves are needed by the middle step (`StepLe/blindConvertK`): the lower half is what makes the
support box `dSup P Ns N` comparable to `Ns`, and the upper half `Ns ≲ N^d` is what makes the
loss of the major-arc pinning data-independent (without it the middle step is *false*, see
`Submission/Work/Peluse/UlowerA/blindConvertKA.lean`).

At the point where the numerical information is consumed, both halves can be stated with the *same*
constant `C`:

* the lower half `N^d ≤ A · Ns` gives `dSup P Ns N + 1 ≤ (2 + coeffSum P * A) · Ns`
  (`Work.Peluse.UlowerA.dSup_add_one_le_of_unbal`), and
* the upper half `Ns ≤ A · N^d` gives `Ns ≤ (2 + coeffSum P * A) · N^d` because
  `A ≤ 2 + coeffSum P * A`.

This is the relation `UnbalScale P C Ns N` below, and it is the only scale hypothesis of the
`A`-versions of the chain pieces.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.UlowerA

open Polynomial

/-- **The unbalanced scale relation, with a single constant.**

`UnbalScale P C Ns N` is the pair of inequalities
`dSup P Ns N + 1 ≤ C · Ns` (the support box is comparable to `Ns`) and
`Ns ≤ C · N^{deg P}` (the support is not much larger than the polynomial scale).  It is what the
`A`-rounded relation `N^d ≤ A · Ns`, `Ns ≤ A · N^d` yields at `C = 2 + coeffSum P * A`. -/
def UnbalScale (P : Polynomial ℤ) (C : ℕ) (Ns N : ℕ) : Prop :=
  Work.Peluse.dSup P Ns N + 1 ≤ C * Ns ∧ (Ns : ℝ) ≤ (C : ℝ) * (N : ℝ) ^ P.natDegree

/-- **The lossy dual--difference interchange, with the unbalanced scale relation.**

This is `Work.Peluse.Ulower.StepLe.HasInterchangeL` with the balanced hypothesis
`Scaled Ns N P.natDegree` replaced by `UnbalScale P C Ns N` (at the price of the extra parameter
`C`, which the constants of the conclusion may depend on).  The proof does not use the scale
hypothesis at all, so this is a faithful generalisation. -/
def HasInterchangeLU (P : Polynomial ℤ) (C₀ : ℕ) : Prop :=
  ∀ σ : ℕ, 1 ≤ σ → ∀ K₀ : ℝ, 1 ≤ K₀ →
  ∃ c : ℝ, 0 < c ∧ ∃ Ki : ℕ, 1 ≤ Ki ∧
    ∀ (B Ns N D : ℕ) (f₀ f₁ : ℤ → ℂ)
      (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ)
      (H₁ : Finset ((Fin σ → ℤ) × (Fin σ → ℤ))) {γ η : ℝ},
      1 ≤ N → 1 ≤ Ns → UnbalScale P C₀ Ns N → N ≤ Ns →
      1 ≤ D → (D : ℝ) ≤ K₀ * (Ns : ℝ) →
      Work.Peluse.SupportIn f₀ Ns → Work.Peluse.SupportIn f₁ Ns →
      (∀ x : ℤ, ‖f₀ x‖ ≤ 1) → (∀ x : ℤ, ‖f₁ x‖ ≤ 1) →
      Work.Peluse.dSup P Ns N + 2 * σ * D ≤ B →
      0 < γ → 0 < η → η ≤ 1 →
      H₁ ⊆ Work.Peluse.Ulower.StepLe.pairBox σ D →
      γ * (D : ℝ) ^ (2 * σ) ≤ (H₁.card : ℝ) →
      (∀ p ∈ H₁, η ≤ Work.Peluse.Ulower.StepLe.cubeAmp B (Work.Peluse.dualFn N P f₀ f₁) β
        p.1 p.2) →
      ∃ H₂ ⊆ Work.Peluse.Ulower.ThetaSet σ D H₁,
        c * (η * γ * ((D : ℝ) / (B : ℝ))) ^ Ki *
            ((Work.Peluse.Ulower.ThetaSet σ D H₁).card : ℝ) ≤ (H₂.card : ℝ) ∧
        ∀ k ∈ H₂, c * (η * γ * ((D : ℝ) / (B : ℝ))) ^ Ki ≤
          ‖((B : ℂ))⁻¹ * ∑' x : ℤ,
            Work.Peluse.Ulower.StepLe.sliceDual σ N P f₀ f₁ (fun i => (k.2.1 i, k.2.2 i)) x *
              Complex.exp (2 * Real.pi * Complex.I *
                (Work.Peluse.Ulower.StepLe.mixedPhase β k : ℂ) * (x : ℂ))‖

end Work.Peluse.UlowerA
