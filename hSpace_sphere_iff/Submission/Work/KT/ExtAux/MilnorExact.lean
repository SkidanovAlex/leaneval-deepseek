import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.k0_basic
import Submission.Work.KT.k0_exact

/-!
# Thin wrappers around the `k0_basic` / `k0_exact` nodes

`Work.KT.ext_product` only uses the following consequences of the two K₀ nodes.  Factoring them
here means that a small adjustment of this file suffices if the nodes' statements are rephrased.
-/

namespace Work.KT.ExtAux

open Matrix

noncomputable section

/-! ## From `k0_basic` -/

/-- Existence of the product on `K₀` of a commutative ring. -/
lemma k0Mul_exists (A : Type) [Ring A] (hcomm : ∀ x y : A, x * y = y * x) :
    ∃ μ : K0 A →+ K0 A →+ K0 A, IsK0Mul μ :=
  (k0_basic.1 A hcomm).imp fun _ h => h.1

/-- Naturality of the product on `K₀`. -/
lemma k0Mul_natural (A B : Type) [Ring A] [Ring B] (hcomm : ∀ x y : A, x * y = y * x)
    (φ : A →+* B) (μA : K0 A →+ K0 A →+ K0 A) (μB : K0 B →+ K0 B →+ K0 B)
    (hA : IsK0Mul μA) (hB : IsK0Mul μB) (a b : K0 A) :
    K0.map φ (μA a b) = μB (K0.map φ a) (K0.map φ b) :=
  k0_basic.2.1 A B hcomm φ μA μB hA hB a b

/-- Functoriality of `K₀`. -/
lemma k0map_comp (A B C : Type) [Ring A] [Ring B] [Ring C] (φ : A →+* B) (ψ : B →+* C) :
    K0.map (ψ.comp φ) = (K0.map ψ).comp (K0.map φ) :=
  k0_basic.2.2.1 A B C φ ψ

/-- `K₀` of the identity. -/
lemma k0map_id (A : Type) [Ring A] : K0.map (RingHom.id A) = AddMonoidHom.id (K0 A) :=
  k0_basic.2.2.2.1 A

/-- `K₀(ℂ) ≅ ℤ` by the rank. -/
lemma k0C_iso : ∃ e : K0 ℂ ≃+ ℤ, e (cls (Mat.one ℂ 1)) = 1 :=
  k0_basic.2.2.2.2

/-! ## From `k0_exact` -/

/-- Middle exactness of `K₀` for a surjection. -/
lemma k0_exact_middle (A B : Type) [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] [Nontrivial B]
    (π : A →ₐ[ℂ] B) (hπ : Function.Surjective π) (U : Subalgebra ℂ A)
    (hU : ∀ r : A, r ∈ U ↔ ∃ c : ℂ, π r = algebraMap ℂ B c)
    (ε : U →ₐ[ℂ] ℂ) (hε : ∀ u : U, π u = algebraMap ℂ B (ε u)) :
    ∀ z : K0 A, K0.mapA π z = 0 →
      ∃ w : K0 U, K0.mapA ε w = 0 ∧ K0.mapA U.val w = z :=
  (k0_exact.1 A B π hπ U hU ε hε).1

/-- Injectivity of `K₀(U) → K₀(A)` given stable lifting of invertibles. -/
lemma k0_exact_injective (A B : Type) [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
    [Nontrivial B] (π : A →ₐ[ℂ] B) (hπ : Function.Surjective π) (U : Subalgebra ℂ A)
    (hU : ∀ r : A, r ∈ U ↔ ∃ c : ℂ, π r = algebraMap ℂ B c)
    (ε : U →ₐ[ℂ] ℂ) (hε : ∀ u : U, π u = algebraMap ℂ B (ε u))
    (hlift : ∀ (n : ℕ) (u : Matrix (Fin n) (Fin n) B), IsUnit u →
        ∃ (k : ℕ) (v : Matrix (Fin (n + k)) (Fin (n + k)) A), IsUnit v ∧
          v.map π = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks u 0 0 1)) :
    ∀ w : K0 U, K0.mapA ε w = 0 → K0.mapA U.val w = 0 → w = 0 :=
  (k0_exact.1 A B π hπ U hU ε hε).2 hlift

end

end Work.KT.ExtAux
