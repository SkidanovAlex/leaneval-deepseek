/-
  annals_wilkies_conjecture, hole `C4a_puiseux` (`PuiseuxReal`): core vocabulary.

  Route: analytic curve selection; the Puiseux statement is proved by
    * complexifying the real-analytic coefficients,
    * the (complex) Puiseux theorem for a monic polynomial with holomorphic coefficients:
      the roots become single-valued holomorphic functions of `u` after the ramification
      `s = u ^ (deg !)`, proved via local factorization (implicit function theorem), the
      monodromy of the root covering, and Riemann's removable singularity theorem,
    * a perturbation + compactness argument to remove the square-freeness hypothesis,
    * extraction of the real branches.

  This file: the vocabulary shared by all the modules of the area, plus elementary lemmas.
-/
import Submission.Work.Wilkies.CG.C4a.Spec
import Mathlib.Analysis.Analytic.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped BigOperators

namespace Work.WilC4aP

open Polynomial

/-- Evaluation of a function at a point, as a ring homomorphism (functions carry the
pointwise ring structure). -/
def evAt (z : ℂ) : (ℂ → ℂ) →+* ℂ where
  toFun f := f z
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] lemma evAt_apply (z : ℂ) (f : ℂ → ℂ) : evAt z f = f z := rfl

/-- The embedding of the constants. -/
def cstHom : ℂ →+* (ℂ → ℂ) where
  toFun c := Function.const ℂ c
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] lemma cstHom_apply (c : ℂ) (z : ℂ) : cstHom c z = c := rfl

/-- The fibre of a polynomial with function coefficients at a point of the base. -/
def Pz (P : Polynomial (ℂ → ℂ)) (z : ℂ) : Polynomial ℂ := P.map (evAt z)

/-- All coefficients of `P` are holomorphic at `z`. -/
def HolCoeffs (P : Polynomial (ℂ → ℂ)) (z : ℂ) : Prop := ∀ i, AnalyticAt ℂ (P.coeff i) z

/-- `P` has only simple roots over the set `S` of the base. -/
def SimpleRootsOn (P : Polynomial (ℂ → ℂ)) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, ∀ w : ℂ, (Pz P z).eval w = 0 → (Pz P z).derivative.eval w ≠ 0

/-- The roots of `P` over the ramification `s = u ^ N` are the values of the functions
`η j`. -/
def FactoredOn {m : ℕ} (P : Polynomial (ℂ → ℂ)) (N : ℕ) (η : Fin m → ℂ → ℂ) (ρ : ℝ) : Prop :=
  ∀ u ∈ Metric.ball (0 : ℂ) ρ,
    Pz P (u ^ N) = ∏ j, (X - C (η j u))

/-- Monicity of `P` transfers to each fibre. -/
lemma monic_Pz {P : Polynomial (ℂ → ℂ)} (h : P.Monic) (z : ℂ) : (Pz P z).Monic :=
  h.map _

lemma natDegree_Pz {P : Polynomial (ℂ → ℂ)} (h : P.Monic) (z : ℂ) :
    (Pz P z).natDegree = P.natDegree := h.natDegree_map _

@[simp] lemma Pz_zero : Pz (0 : Polynomial (ℂ → ℂ)) 0 = 0 := by simp [Pz]
@[simp] lemma Pz_one : Pz (1 : Polynomial (ℂ → ℂ)) 0 = 1 := by simp [Pz]

lemma Pz_add (P Q : Polynomial (ℂ → ℂ)) (z : ℂ) : Pz (P + Q) z = Pz P z + Pz Q z := by
  simp [Pz]

lemma Pz_mul (P Q : Polynomial (ℂ → ℂ)) (z : ℂ) : Pz (P * Q) z = Pz P z * Pz Q z := by
  simp [Pz]

lemma Pz_derivative (P : Polynomial (ℂ → ℂ)) (z : ℂ) :
    (Pz P z).derivative = Pz P.derivative z := by
  rw [Pz, Pz, Polynomial.derivative_map]

lemma Pz_C (c : ℂ) (z : ℂ) : Pz (C (cstHom c)) z = C c := by
  rw [Pz, Polynomial.map_C]; rfl

/-- A permutation of a finite type satisfies `σ ^ (card !) = 1`. -/
lemma perm_pow_factorial {α : Type*} [DecidableEq α] [Fintype α] (σ : Equiv.Perm α) :
    σ ^ (Fintype.card α).factorial = 1 := by
  rw [← Fintype.card_perm (α := α)]
  exact pow_card_eq_one

/-- The cardinality of the root multiset of a split monic polynomial is its degree. -/
lemma card_roots_of_monic {p : Polynomial ℂ} (hmon : p.Monic) :
    p.roots.card = p.natDegree := by
  obtain ⟨s, hs⟩ := (Polynomial.splits_iff_exists_multiset (f := p)).mp (IsAlgClosed.splits p)
  have h : p.roots = s := by
    conv_lhs => rw [hs, hmon.leadingCoeff, map_one, one_mul]
    exact Polynomial.roots_multiset_prod_X_sub_C s
  rw [h, hs, hmon.leadingCoeff, map_one, one_mul]
  simp

/-- A monic polynomial over `ℂ` is the product of its linear factors, with multiplicity. -/
lemma prod_roots_eq_of_monic {p : Polynomial ℂ} (hmon : p.Monic) :
    (p.roots.map (fun a => X - C a)).prod = p :=
  Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon (card_roots_of_monic hmon)

end Work.WilC4aP
