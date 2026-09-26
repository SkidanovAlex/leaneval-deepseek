/-
# Section 5: assembling the hypotheses of Theorem 3.1

CKMRV Corollary 5.2 (`corin4.1`) and Proposition 5.1 (`prop:extendF2`) reduce the verification
of the hypotheses of Theorem 3.1 for `F = Fgen K`, `F̃ = Ftgen K̂` to two identities satisfied by
the kernel transform `F₂ = kernelTransform K` together with the definitional relation
`K̂ = -K|^τ_{d/2}S` of Theorem 4.9.

This file records that reduction:

* `Work.Kernels.Section5Facts.kernelTransform_slash_S` : `Ftgen K̂ = -F₂|^τ_{d/2}S`;
* `Work.Kernels.Fgen_T2` : `F₂|(T-I)² = -F₁|(T-I)²` gives `F(τ+2)-2F(τ+1)+F(τ) = 0`;
* `Work.Kernels.Section5Facts.Ftgen_T2` : `F₂|S(T-I)² = 0` gives `F̃(τ+2)-2F̃(τ+1)+F̃(τ) = 0`;
* `Work.Kernels.Section5Facts.Fgen_third` : the third functional equation is automatic from
  `F̃ = -F₂|S` and `(-i)^{d/2} = 1`.

The two remaining inputs are purely analytic: holomorphy in `τ` and the growth/strip bounds.
They are isolated as explicit hypotheses in `Work.Kernels.satisfiesThm31_of_analysis`.
-/
import Mathlib
import Submission.Work.Kernels.Section5
import Submission.Work.Kernels.Section5Facts.kernelTransform_slash_S
import Submission.Work.Kernels.Section5Facts.Ftgen_T2
import Submission.Work.Kernels.Section5Facts.Fgen_third

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix MeasureTheory
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels

/-- **Corollary 5.2, clause (5) of Theorem 3.1.**  Given the two identities satisfied by the
kernel transform and the relation `K̂ = -K|^τ_{d/2}S`, the constructed
`F = Fgen K`, `F̃ = Ftgen K̂` satisfy the three functional equations of `SatisfiesThm31`. -/
theorem satisfiesThm31_clause5 {d : ℕ} (hdI : (-Complex.I) ^ (d / 2) = 1)
    {K Khat : ℍ → ℍ → ℂ}
    (hKhat : ∀ τ z : ℍ, Khat τ z = - (τ : ℂ) ^ (-((d : ℤ) / 2)) * K (ModularGroup.S • τ) z)
    (h5a : ∀ r : ℝ, T2op (fun τ : ℍ => kernelTransform K τ r)
      = - T2op (fun τ : ℍ => gaussTerm τ r))
    (h5b : ∀ r : ℝ, slash ((d : ℤ) / 2) (R_S * (R_T - 1) ^ 2)
      (fun τ : ℍ => kernelTransform K τ r) = 0) :
    (∀ r : ℝ, T2op (fun τ : ℍ => Fgen K τ r) = 0) ∧
    (∀ r : ℝ, T2op (fun τ : ℍ => Ftgen Khat τ r) = 0) ∧
    (∀ (τ : ℍ) (r : ℝ), Fgen K τ r + (Complex.I / (τ : ℂ)) ^ (d / 2)
      * Ftgen Khat (ModularGroup.S • τ) r = gaussTerm τ r) :=
  ⟨Fgen_T2 h5a, Section5Facts.Ftgen_T2 hKhat h5b, Section5Facts.Fgen_third hdI hKhat⟩

/-- **Reduction of Theorem 3.1 to the two analytic inputs.**  If the kernel transform has the
two identities of Corollary 5.2, is holomorphic in `τ` together with `F̃`, and satisfies the
growth bounds (3) and the strip bound (4), then `(Fgen K, Ftgen K̂)` satisfies `SatisfiesThm31`. -/
theorem satisfiesThm31_of_analysis {d k₀ : ℕ} (hdI : (-Complex.I) ^ (d / 2) = 1)
    {K Khat : ℍ → ℍ → ℂ}
    (hKhat : ∀ τ z : ℍ, Khat τ z = - (τ : ℂ) ^ (-((d : ℤ) / 2)) * K (ModularGroup.S • τ) z)
    (h5a : ∀ r : ℝ, T2op (fun τ : ℍ => kernelTransform K τ r)
      = - T2op (fun τ : ℍ => gaussTerm τ r))
    (h5b : ∀ r : ℝ, slash ((d : ℤ) / 2) (R_S * (R_T - 1) ^ 2)
      (fun τ : ℍ => kernelTransform K τ r) = 0)
    (h1 : (∀ r : ℝ, MDiff (fun τ : ℍ => Fgen K τ r)) ∧
      (∀ r : ℝ, MDiff (fun τ : ℍ => Ftgen Khat τ r)))
    (h3 : (∀ k l : ℕ, ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧
        ∀ (τ : ℍ) (r : ℝ), (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Fgen K τ s) r‖
          ≤ α * (τ.im) ^ (-β) + γ * ‖(τ : ℂ)‖ ^ δ) ∧
      (∀ k l : ℕ, ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧
        ∀ (τ : ℍ) (r : ℝ), (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Ftgen Khat τ s) r‖
          ≤ α * (τ.im) ^ (-β) + γ * ‖(τ : ℂ)‖ ^ δ))
    (h4 : ∃ α β : ℝ, 0 ≤ α ∧ 0 < β ∧ ∀ (τ : ℍ) (r : ℝ), -1 ≤ τ.re → τ.re ≤ 1 →
      max ‖Fgen K τ r‖ ‖Ftgen Khat τ r‖ ≤ α * (τ.im) ^ (-β)) :
    SatisfiesThm31 d k₀ (Fgen K) (Ftgen Khat) := by
  obtain ⟨hc5a, hc5b, hc5c⟩ := satisfiesThm31_clause5 hdI hKhat h5a h5b
  refine ⟨h1.1, h1.2, h3.1, h3.2, h4, ?_, ?_, ?_⟩
  · intro τ r
    have h := congr_fun (hc5a r) τ
    simpa [T2op, vadd_one_add_one] using h
  · intro τ r
    have h := congr_fun (hc5b r) τ
    simpa [T2op, vadd_one_add_one] using h
  · exact hc5c

end Work.Kernels
