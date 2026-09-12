import Mathlib
import Submission.Commons.LorentzianPolynomials.hessian_aeval_eq
import Submission.Commons.LorentzianPolynomials.strict_lorentzian_quadratic_stable
import Submission.Commons.Algebra.MvPolynomial.subst_coeff_pos
import Submission.Commons.LorentzianPolynomials.substS_at_zero

namespace Commons.LorentzianPolynomials

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set
open scoped BigOperators
set_option autoImplicit false

/-- The substituted variable: `(1−θ)·X j + θ·(∑ i, X i)`. -/
private noncomputable def flowVar (n : ℕ) (θ : ℝ) (j : Fin n) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.C (1 - θ) * MvPolynomial.X j +
    MvPolynomial.C θ * (∑ i : Fin n, MvPolynomial.X i)

/-- `flowVar n θ j` is homogeneous of degree 1. -/
private lemma flowVar_isHomogeneous_one (n : ℕ) (θ : ℝ) (j : Fin n) :
    (flowVar n θ j).IsHomogeneous 1 := by
  have hXj : (MvPolynomial.X j : MvPolynomial (Fin n) ℝ).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X (σ := Fin n) (R := ℝ) j
  have hC1 : (MvPolynomial.C (1 - θ) : MvPolynomial (Fin n) ℝ).IsHomogeneous 0 :=
    MvPolynomial.isHomogeneous_C (σ := Fin n) (R := ℝ) (1 - θ)
  have hsum : ((∑ i : Fin n, MvPolynomial.X i) : MvPolynomial (Fin n) ℝ).IsHomogeneous 1 := by
    exact MvPolynomial.IsHomogeneous.sum Finset.univ (fun i : Fin n => MvPolynomial.X i) 1
      (fun i hi => MvPolynomial.isHomogeneous_X (σ := Fin n) (R := ℝ) i)
  have hC2 : (MvPolynomial.C θ : MvPolynomial (Fin n) ℝ).IsHomogeneous 0 :=
    MvPolynomial.isHomogeneous_C (σ := Fin n) (R := ℝ) θ
  unfold flowVar
  exact (MvPolynomial.IsHomogeneous.mul (φ := MvPolynomial.C (1 - θ)) hC1 (ψ := MvPolynomial.X j) hXj).add
    (MvPolynomial.IsHomogeneous.mul (φ := MvPolynomial.C θ) hC2 (ψ := ∑ i : Fin n, MvPolynomial.X i) hsum)

/-- `S_θ f := f((1−θ)·X + θ·(ΣᵢXᵢ))` as an element of `H n d`. -/
private noncomputable def flowSubst {n d : ℕ} (θ : ℝ) (f : H n d) : H n d :=
  ⟨MvPolynomial.aeval (fun j : Fin n =>
      MvPolynomial.C (1 - θ) * MvPolynomial.X j +
        MvPolynomial.C θ * (∑ i : Fin n, MvPolynomial.X i)) f.1, by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    have hg : ∀ j : Fin n, (MvPolynomial.C (1 - θ) * MvPolynomial.X j +
        MvPolynomial.C θ * (∑ i : Fin n, MvPolynomial.X i)).IsHomogeneous 1 := by
      intro j
      simpa [flowVar] using (flowVar_isHomogeneous_one n θ j)
    have hhom := MvPolynomial.IsHomogeneous.aeval (hφ := f.2)
      (g := fun j : Fin n =>
        MvPolynomial.C (1 - θ) * MvPolynomial.X j +
          MvPolynomial.C θ * (∑ i : Fin n, MvPolynomial.X i)) hg
    simpa [mul_comm] using hhom⟩

/-- Coefficients of a member of `P n d` are nonnegative. -/
private lemma P_nonneg_coeff (n d : ℕ) (f : H n d) (hf : f ∈ P n d) :
    ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m := by
  intro m
  by_cases hw : Finsupp.weight (1 : Fin n → ℕ) m = d
  · exact le_of_lt (hf m hw)
  · have hhom : f.1.IsHomogeneous d :=
      (MvPolynomial.mem_homogeneousSubmodule (σ := Fin n) (R := ℝ) d f.1).mp f.2
    have hwh : f.1.IsWeightedHomogeneous (1 : Fin n → ℕ) d := by
      simpa [MvPolynomial.IsHomogeneous] using hhom
    have hc : f.1.coeff m = 0 :=
      MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero (w := (1 : Fin n → ℕ)) (φ := f.1) (n := d)
        hwh m hw
    rw [hc]

/-- Substituting `X ⱼ ↦ (1−θ)·X ⱼ + θ·(Σᵢ Xᵢ)` keeps positive coefficients positive,
for `0 ≤ θ ≤ 1`. -/
theorem substS_mem_P (n d : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (f : Commons.LorentzianPolynomials.H n d) (hf : f ∈ Commons.LorentzianPolynomials.P n d) :
    ∃ g : Commons.LorentzianPolynomials.H n d,
      g ∈ Commons.LorentzianPolynomials.P n d ∧
      g.1 = MvPolynomial.aeval (fun j : Fin n =>
        MvPolynomial.C (1 - θ) * MvPolynomial.X j +
          MvPolynomial.C θ * (∑ i : Fin n, MvPolynomial.X i)) f.1 := by
  classical
  refine ⟨flowSubst (n := n) (d := d) θ f, ?_mem, ?_eq⟩
  · -- membership in P
    intro m hm
    change 0 < (MvPolynomial.aeval (fun j : Fin n =>
        MvPolynomial.C (1 - θ) * MvPolynomial.X j +
          MvPolynomial.C θ * (∑ i : Fin n, MvPolynomial.X i)) f.1).coeff m
    rcases lt_or_eq_of_le hθ0 with hθpos | hθzero
    · -- 0 < θ : use the coefficientwise positivity lemma
      have hhom : f.1.IsHomogeneous d :=
        (MvPolynomial.mem_homogeneousSubmodule (σ := Fin n) (R := ℝ) d f.1).mp f.2
      have hp : ∀ m' : Fin n →₀ ℕ, 0 ≤ f.1.coeff m' := P_nonneg_coeff n d f hf
      have hp0 : f.1 ≠ 0 := by
        intro hz
        have hcoeff : f.1.coeff m = 0 := by simp [hz]
        have hpos : 0 < f.1.coeff m := hf m hm
        linarith
      have hpos := Commons.Algebra.MvPolynomial.subst_coeff_pos n d f.1 hp hp0 hhom hθpos hθ1 m hm
      simpa using hpos
    · -- θ = 0 : the substitution is the identity
      rw [hθzero.symm]
      rw [substS_at_zero n d f]
      exact hf m hm
  · -- the value of the constructed element
    rfl

end Commons.LorentzianPolynomials
