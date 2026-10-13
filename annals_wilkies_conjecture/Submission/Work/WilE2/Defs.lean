/-
  Work.WilE2 — area E2 of the `annals_wilkies_conjecture` development:
  Khovanskii bounds for exp-affine chains, and components of EA semi-Pfaffian sets.

  This module: VOCABULARY for the Khovanskii–Rolle elimination.
  Everything here is proved from the frozen `Submission.Work.Wilkies.E.Spec` vocabulary.
-/
import Submission.Work.Wilkies.E.Spec
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Algebra.MvPolynomial.Degrees

set_option autoImplicit false

noncomputable section
open Classical
namespace Work.WilE2

open WilkiesDesign WilkiesDesign.E WilkiesConjecture

variable {n r k : ℕ}

/-! ## §1. Exp-affine systems in `n` ambient variables

The frozen `WilkiesDesign.E.EAChain k r` describes `r` chain functions
`x ↦ exp (∑ i, a j i * x i + b j)` on `ℝᵏ`.  The Khovanskii elimination lifts an `n × n`
system to an `(n+1) × (n+1)` system, so we need the same notion in `ℝⁿ` for any `n ≥ r`.
`ESys n r` is that notion (the lifted chain simply has a zero coefficient in the new
coordinate). -/

/-- An exp-affine system: `n` ambient coordinates, `r` chain functions,
the `j`-th being `ψ_j x = exp (∑ i, a j i * x i + b j)`. -/
structure ESys (n r : ℕ) where
  a : Fin r → Fin n → ℝ
  b : Fin r → ℝ

/-- The affine exponent `ℓ_j x = ∑ i, a j i * x i + b j`. -/
def ESys.ell (S : ESys n r) (j : Fin r) (x : Fin n → ℝ) : ℝ :=
  ∑ i, S.a j i * x i + S.b j

/-- The chain functions `ψ_j`. -/
def ESys.psi (S : ESys n r) (j : Fin r) (x : Fin n → ℝ) : ℝ :=
  Real.exp (S.ell j x)

/-- Polynomials in the `n` coordinates and the `r` chain functions. -/
abbrev EPoly (n r : ℕ) := MvPolynomial (Fin n ⊕ Fin r) ℝ

/-- Evaluation of an EA polynomial along the chain. -/
def ESys.ev (S : ESys n r) (P : EPoly n r) : (Fin n → ℝ) → ℝ :=
  fun x => MvPolynomial.eval (Sum.elim x (fun j => S.psi j x)) P

/-- The symbolic partial derivative `∂ᵢ = ∂/∂xᵢ + ∑ⱼ a j i * ψ_j * ∂/∂ψ_j`.
It does not raise the total degree. -/
def ESys.d (S : ESys n r) (i : Fin n) (Q : EPoly n r) : EPoly n r :=
  MvPolynomial.pderiv (Sum.inl i) Q +
    ∑ j : Fin r, MvPolynomial.C (S.a j i) * MvPolynomial.X (Sum.inr j) *
      MvPolynomial.pderiv (Sum.inr j) Q

/-- Ordered mixed derivative `∂_{n-1}^{m (n-1)} ⋯ ∂_0^{m 0} Q`. -/
def ESys.dmulti (S : ESys n r) (m : Fin n → ℕ) (Q : EPoly n r) : EPoly n r :=
  (List.finRange n).foldr (fun i g => (S.d i)^[m i] g) Q

/-- A system of `n` equations given by `n` EA polynomials, and its nondegenerate
(regular) zeros. -/
def ESys.Nondegen (S : ESys n r) (F : Fin n → EPoly n r) (x : Fin n → ℝ) : Prop :=
  (∀ i, S.ev (F i) x = 0) ∧ (Matrix.of fun i j => S.ev (S.d j (F i)) x).det ≠ 0

/-! ## §2. Bridge to the frozen vocabulary -/

/-- The frozen `EAChain k r` as an `ESys k r`. -/
def ESys.ofChain (c : EAChain k r) : ESys k r := ⟨c.a, c.b⟩

@[simp] theorem ESys.ofChain_a (c : EAChain k r) : (ESys.ofChain c).a = c.a := rfl
@[simp] theorem ESys.ofChain_b (c : EAChain k r) : (ESys.ofChain c).b = c.b := rfl

theorem ESys.ofChain_ell (c : EAChain k r) (j : Fin r) (x : Fin k → ℝ) :
    (ESys.ofChain c).ell j x = c.ell j x := rfl

theorem ESys.ofChain_ev (c : EAChain k r) (P : EPoly k r) (x : Fin k → ℝ) :
    (ESys.ofChain c).ev P x = eaEval c P x := rfl

theorem ESys.ofChain_d (c : EAChain k r) (i : Fin k) (Q : EPoly k r) :
    (ESys.ofChain c).d i Q = eaD c i Q := rfl

theorem ESys.ofChain_dmulti (c : EAChain k r) (m : Fin k → ℕ) (Q : EPoly k r) :
    (ESys.ofChain c).dmulti m Q = eaDmulti c m Q := rfl

theorem ESys.ofChain_nondeg (c : EAChain k r) (F : Fin k → EPoly k r) (x : Fin k → ℝ) :
    (ESys.ofChain c).Nondegen F x ↔
      ((∀ i, eaEval c (F i) x = 0) ∧
        (Matrix.of fun i j => eaEval c (eaD c j (F i)) x).det ≠ 0) := Iff.rfl

/-- The `atomDeg` of the frozen vocabulary is `totalDegree + 1`. -/
theorem atomDeg_eq (Q : EPoly k r) : atomDeg Q = Q.totalDegree + 1 := rfl

end Work.WilE2
