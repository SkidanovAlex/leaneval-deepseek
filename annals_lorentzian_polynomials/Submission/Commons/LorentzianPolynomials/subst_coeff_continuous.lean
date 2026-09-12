import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Topology.Algebra.Polynomial
import Submission.Commons.LorentzianPolynomials.hessian_aeval_eq

namespace Commons.LorentzianPolynomials

open Finsupp MvPolynomial BigOperators

set_option autoImplicit false

/-- Substitute each variable `X j` by `(1 - θ) X j + θ (∑ i, X i)` with `θ` kept as a
formal polynomial variable; coefficients in `X` then become polynomials in `θ`. -/
private noncomputable def substPoly (n : ℕ) (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) (Polynomial ℝ) :=
  MvPolynomial.aeval (R := ℝ) (fun j : Fin n =>
    MvPolynomial.C (Polynomial.C 1 - Polynomial.X) * MvPolynomial.X j +
    MvPolynomial.C Polynomial.X * (∑ i : Fin n, MvPolynomial.X i)) p

private lemma map_algebraMap_comp (n : ℕ) (θ : ℝ) :
    ((MvPolynomial.map (σ := Fin n) (Polynomial.evalRingHom θ)) : MvPolynomial (Fin n) (Polynomial ℝ) →+* MvPolynomial (Fin n) ℝ).comp
        (algebraMap ℝ (MvPolynomial (Fin n) (Polynomial ℝ))) =
      algebraMap ℝ (MvPolynomial (Fin n) ℝ) := by
  ext r m
  rw [RingHom.comp_apply]
  rw [MvPolynomial.coeff_map]
  by_cases h : (0 : Fin n →₀ ℕ) = m
  · subst m
    simp
  · simp [h]

private lemma map_substVar (n : ℕ) (θ : ℝ) (j : Fin n) :
    (MvPolynomial.map (σ := Fin n) (Polynomial.evalRingHom θ))
        (MvPolynomial.C (Polynomial.C 1 - Polynomial.X) * MvPolynomial.X j +
          MvPolynomial.C Polynomial.X * (∑ i : Fin n, MvPolynomial.X i)) =
      MvPolynomial.C (1 - θ) * MvPolynomial.X j +
        MvPolynomial.C θ * (∑ i : Fin n, MvPolynomial.X i) := by
  rw [map_add, map_mul, map_mul]
  simp [map_sum]

private lemma substPoly_map (n : ℕ) (θ : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.map (σ := Fin n) (Polynomial.evalRingHom θ) (substPoly n p) =
      MvPolynomial.aeval (R := ℝ) (fun j : Fin n =>
        MvPolynomial.C (1 - θ) * MvPolynomial.X j +
        MvPolynomial.C θ * (∑ i : Fin n, MvPolynomial.X i)) p := by
  unfold substPoly
  let ψ : Polynomial ℝ →+* ℝ := Polynomial.evalRingHom θ
  let Φ : MvPolynomial (Fin n) (Polynomial ℝ) →+* MvPolynomial (Fin n) ℝ := MvPolynomial.map (σ := Fin n) ψ
  let g : Fin n → MvPolynomial (Fin n) (Polynomial ℝ) := fun j =>
    MvPolynomial.C (Polynomial.C 1 - Polynomial.X) * MvPolynomial.X j +
    MvPolynomial.C Polynomial.X * (∑ i : Fin n, MvPolynomial.X i)
  let h : Fin n → MvPolynomial (Fin n) ℝ := fun j =>
    MvPolynomial.C (1 - θ) * MvPolynomial.X j + MvPolynomial.C θ * (∑ i : Fin n, MvPolynomial.X i)
  have hmapC : ∀ r : ℝ, Φ (MvPolynomial.aeval (R := ℝ) g (MvPolynomial.C r)) =
      MvPolynomial.aeval (R := ℝ) h (MvPolynomial.C r) := by
    intro r
    rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C]
    have hc := RingHom.congr_fun (map_algebraMap_comp n θ) r
    dsimp [Φ, ψ]
    rw [← RingHom.comp_apply]
    exact hc
  have hmapX : ∀ j : Fin n, Φ (MvPolynomial.aeval (R := ℝ) g (MvPolynomial.X j)) =
      MvPolynomial.aeval (R := ℝ) h (MvPolynomial.X j) := by
    intro j
    rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    rw [map_substVar n θ j]
  change Φ (MvPolynomial.aeval (R := ℝ) g p) = MvPolynomial.aeval (R := ℝ) h p
  induction p using MvPolynomial.induction_on with
  | C r => exact hmapC r
  | add p q ihp ihq =>
      rw [map_add, map_add, map_add]
      rw [ihp, ihq]
  | mul_X p j ih =>
      rw [map_mul, map_mul, map_mul]
      rw [ih, hmapX j]

private lemma coeff_subst_eq_eval (n : ℕ) (θ : ℝ) (p : MvPolynomial (Fin n) ℝ) (m : Fin n →₀ ℕ) :
    (MvPolynomial.aeval (R := ℝ) (fun j : Fin n =>
        MvPolynomial.C (1 - θ) * MvPolynomial.X j +
        MvPolynomial.C θ * (∑ i : Fin n, MvPolynomial.X i)) p).coeff m =
      Polynomial.eval θ ((substPoly n p).coeff m) := by
  rw [← substPoly_map n θ p]
  rw [MvPolynomial.coeff_map]
  rfl

private lemma coeff_subst_continuous (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (m : Fin n →₀ ℕ) :
    Continuous (fun θ : ℝ =>
      (MvPolynomial.aeval (fun j : Fin n =>
        MvPolynomial.C (1 - θ) * MvPolynomial.X j +
          MvPolynomial.C θ * (∑ i : Fin n, MvPolynomial.X i)) p).coeff m) := by
  have h : (fun θ : ℝ =>
      (MvPolynomial.aeval (fun j : Fin n =>
        MvPolynomial.C (1 - θ) * MvPolynomial.X j +
          MvPolynomial.C θ * (∑ i : Fin n, MvPolynomial.X i)) p).coeff m) =
      fun θ : ℝ => Polynomial.eval θ ((substPoly n p).coeff m) := by
    funext θ
    exact coeff_subst_eq_eval n θ p m
  rw [h]
  exact Polynomial.continuous ((substPoly n p).coeff m)

theorem subst_coeff_continuous (n d : ℕ) (f : Commons.LorentzianPolynomials.H n d)
    (m : Fin n →₀ ℕ) :
    Continuous (fun θ : ℝ =>
      (MvPolynomial.aeval (fun j : Fin n =>
        MvPolynomial.C (1 - θ) * MvPolynomial.X j +
          MvPolynomial.C θ * (∑ i : Fin n, MvPolynomial.X i)) f.1).coeff m) := by
  exact coeff_subst_continuous n f.1 m

end Commons.LorentzianPolynomials