import Mathlib
import Submission.Commons.LorentzianPolynomials.hessian_aeval_eq
import Submission.Commons.LorentzianPolynomials.strict_lorentzian_quadratic_stable
import Submission.Commons.LorentzianPolynomials.S_closed
import Submission.Commons.LorentzianPolynomials.strict_subset_L
import Submission.Commons.LorentzianPolynomials.closure_strict_eq_L_of_degree_le_two
import Submission.Commons.LorentzianPolynomials.flow_substS_mem_L

namespace Commons.LorentzianPolynomials

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- The substitution polynomial `(1−θ)·X_j + θ·(Σᵢ Xᵢ)` is homogeneous of degree 1. -/
private lemma substS_linearForm_homogeneous (n : ℕ) (θ : ℝ) (j : Fin n) :
    (MvPolynomial.C (1 - θ) * MvPolynomial.X j +
        MvPolynomial.C θ * (∑ i : Fin n, MvPolynomial.X i)).IsHomogeneous 1 := by
  have hXj : (MvPolynomial.X j : MvPolynomial (Fin n) ℝ).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X (σ := Fin n) (R := ℝ) j
  have hC1 : (MvPolynomial.C (1 - θ) : MvPolynomial (Fin n) ℝ).IsHomogeneous 0 :=
    MvPolynomial.isHomogeneous_C (σ := Fin n) (R := ℝ) (1 - θ)
  have hsum : ((∑ i : Fin n, MvPolynomial.X i) : MvPolynomial (Fin n) ℝ).IsHomogeneous 1 := by
    exact MvPolynomial.IsHomogeneous.sum Finset.univ (fun i : Fin n => MvPolynomial.X i) 1
      (fun i hi => MvPolynomial.isHomogeneous_X (σ := Fin n) (R := ℝ) i)
  have hC2 : (MvPolynomial.C θ : MvPolynomial (Fin n) ℝ).IsHomogeneous 0 :=
    MvPolynomial.isHomogeneous_C (σ := Fin n) (R := ℝ) θ
  exact (MvPolynomial.IsHomogeneous.mul (φ := MvPolynomial.C (1 - θ)) hC1 (ψ := MvPolynomial.X j) hXj).add
    (MvPolynomial.IsHomogeneous.mul (φ := MvPolynomial.C θ) hC2 (ψ := ∑ i : Fin n, MvPolynomial.X i) hsum)

/-- `S(θ,f) = f((1−θ)·X + θ·(Σᵢ Xᵢ))`, the substitution with matrix `(1−θ)I + θJ`. -/
noncomputable def substS {n d : ℕ} (θ : ℝ) (f : H n d) : H n d :=
  ⟨MvPolynomial.aeval (fun j : Fin n =>
      MvPolynomial.C (1 - θ) * MvPolynomial.X j +
        MvPolynomial.C θ * (∑ i : Fin n, MvPolynomial.X i)) f.1, by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    -- substitution by homogeneous linear forms preserves homogeneity
    have hhom := MvPolynomial.IsHomogeneous.aeval (hφ := f.2)
      (g := fun j : Fin n =>
        MvPolynomial.C (1 - θ) * MvPolynomial.X j +
          MvPolynomial.C θ * (∑ i : Fin n, MvPolynomial.X i))
      (substS_linearForm_homogeneous n θ)
    simpa [mul_comm] using hhom⟩

/-- `S(0, f) = f`. -/
lemma substS_zero (n d : ℕ) (f : H n d) : substS (n := n) (d := d) 0 f = f := by
  apply Subtype.ext
  simp [substS, MvPolynomial.aeval_X_left_apply]

/-- Brändén–Huh Theorem (flow): for `f ∈ L n d` and `0 ≤ θ ≤ 1`, the substituted polynomial
`S(θ,f) = f((1−θ)·X + θ·(Σᵢ Xᵢ))` is again Lorentzian. -/
theorem substS_flow_mem_L (n d : ℕ) (hn : 0 < n) (f : H n d) (hf : f ∈ L n d) :
    ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → substS (n := n) (d := d) θ f ∈ L n d := by
  intro θ hθ0 hθ1
  by_cases hθ : θ = 0
  · subst θ
    rw [substS_zero]
    exact hf
  · rcases (flow_substS_mem_L n d hn f hf θ hθ0 hθ1) with ⟨g, hgL, hgeq⟩
    have hsub : substS θ f = g := by
      apply Subtype.ext
      change (MvPolynomial.aeval (fun j : Fin n =>
        MvPolynomial.C (1 - θ) * MvPolynomial.X j +
          MvPolynomial.C θ * (∑ i : Fin n, MvPolynomial.X i)) f.1) = g.1
      exact hgeq.symm
    rw [hsub]
    exact hgL

end Commons.LorentzianPolynomials
