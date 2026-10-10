import Mathlib.Basic.Real.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Submission.NK.GlobalCFTdeep.FundamentalClassReduction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Artin reciprocity, ideal-theoretic form (orchestrator-owned; do not edit)

The reciprocity law in the form that needs NO local class field theory (Lang, *Algebraic Number Theory*, X §1–2;
Artin–Tate V; Janusz V): for abelian `L/K` there is `m` (divisible by every ramified prime) such that for every
totally positive `a ≡ 1 mod m`, the product of the Frobenius elements of the prime factors of `(a)`, with
multiplicity, is trivial.
-/

namespace NK.CFTLib

open NumberField

def ArtinReciprocityIdeal : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L], (∀ a b : L ≃ₐ[K] L, a * b = b * a) →
    ∃ m : ℕ, 0 < m ∧
      (∀ p : NK.Chebotarev.PrimeIdeal K, (m : 𝓞 K) ∉ p.asIdeal →
        Ideal.ramificationIdxIn p.asIdeal (𝓞 L) = 1) ∧
      ∀ (a : 𝓞 K), a - 1 ∈ Ideal.span {(m : 𝓞 K)} → (∀ φ : K →+* ℝ, 0 < φ (a : K)) →
      ∀ (s : Finset (NK.Chebotarev.PrimeIdeal K)) (e : NK.Chebotarev.PrimeIdeal K → ℕ)
        (σ : NK.Chebotarev.PrimeIdeal K → (L ≃ₐ[K] L)),
        (∀ p ∈ s, (m : 𝓞 K) ∉ p.asIdeal) →
        Ideal.span {a} = ∏ p ∈ s, p.asIdeal ^ e p →
        (∀ p ∈ s, NK.Chebotarev.IsFrobAtPrime (L := L) p (σ p)) →
        (s.toList.map (fun p => σ p ^ e p)).prod = 1

end NK.CFTLib
