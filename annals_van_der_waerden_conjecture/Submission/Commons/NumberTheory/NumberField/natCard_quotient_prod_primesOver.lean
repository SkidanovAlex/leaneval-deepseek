import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients

open scoped BigOperators
open scoped NumberField

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField

/-- Cardinality of the quotient of a commutative ring by the product of finitely many pairwise
coprime ideals is the product of the cardinalities of the individual quotients
(Chinese remainder theorem). -/
lemma natCard_quotient_prod_pairwiseCoprime (R : Type*) [CommRing R]
    (s : Finset (Ideal R))
    (hcop : ∀ ⦃I : Ideal R⦄, I ∈ s → ∀ ⦃J : Ideal R⦄, J ∈ s → I ≠ J → IsCoprime I J) :
    Nat.card (R ⧸ ∏ I ∈ s, I) = ∏ I ∈ s, Nat.card (R ⧸ I) := by
  classical
  let P : Finset (Ideal R) → Prop := fun t =>
    (∀ ⦃I : Ideal R⦄, I ∈ t → ∀ ⦃J : Ideal R⦄, J ∈ t → I ≠ J → IsCoprime I J) →
      Nat.card (R ⧸ ∏ I ∈ t, I) = ∏ I ∈ t, Nat.card (R ⧸ I)
  have main : P s := by
    refine Finset.induction_on s ?base ?step
    · intro h
      simp
    · intro a t hat ih hc
      rw [Finset.prod_insert hat, Finset.prod_insert hat]
      have ih' := ih (fun I hI J hJ hne =>
        hc (Finset.mem_insert_of_mem hI) (Finset.mem_insert_of_mem hJ) hne)
      have hcprod : IsCoprime a (∏ I ∈ t, I) := by
        rw [Ideal.isCoprime_iff_sup_eq]
        refine Ideal.sup_prod_eq_top ?_
        intro I hI
        have hne : a ≠ I := by
          intro h
          exact hat (h.symm ▸ hI)
        exact (Ideal.isCoprime_iff_sup_eq.mp
          (hc (Finset.mem_insert_self a t) (Finset.mem_insert_of_mem hI) hne))
      calc
        Nat.card (R ⧸ a * ∏ I ∈ t, I) =
            Nat.card ((R ⧸ a) × (R ⧸ ∏ I ∈ t, I)) :=
              Nat.card_congr (Ideal.quotientMulEquivQuotientProd a (∏ I ∈ t, I) hcprod).toEquiv
        _ = Nat.card (R ⧸ a) * Nat.card (R ⧸ ∏ I ∈ t, I) := Nat.card_prod _ _
        _ = Nat.card (R ⧸ a) * ∏ I ∈ t, Nat.card (R ⧸ I) := by rw [ih']
  exact main hcop

/-- Every prime ideal of the ring of integers of a number field that lies over a nonzero prime
ideal of `ℤ` is maximal. -/
theorem natCard_quotient_prod_primesOver {K : Type*} [Field K] [NumberField K] (p : ℕ)
    [Fact (Nat.Prime p)] :
    Nat.card ((𝓞 K) ⧸ ∏ P ∈
        IsDedekindDomain.primesOverFinset (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 K), P) =
      ∏ P ∈ IsDedekindDomain.primesOverFinset (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 K),
        Nat.card ((𝓞 K) ⧸ P) := by
  classical
  let pZ : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  let S : Finset (Ideal (𝓞 K)) := IsDedekindDomain.primesOverFinset pZ (𝓞 K)
  have hpℤ : (p : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))
  have hpZ_ne : pZ ≠ ⊥ := by
    dsimp [pZ]
    rw [Ideal.span_singleton_eq_bot]
    exact hpℤ
  have hcop : ∀ ⦃P : Ideal (𝓞 K)⦄, P ∈ S → ∀ ⦃Q : Ideal (𝓞 K)⦄, Q ∈ S → P ≠ Q →
      IsCoprime P Q := by
    intro P hP Q hQ hPQ
    have hP' : P ∈ pZ.primesOver (𝓞 K) :=
      (IsDedekindDomain.mem_primesOverFinset_iff (p := pZ) (B := 𝓞 K) hpZ_ne).mp hP
    have hQ' : Q ∈ pZ.primesOver (𝓞 K) :=
      (IsDedekindDomain.mem_primesOverFinset_iff (p := pZ) (B := 𝓞 K) hpZ_ne).mp hQ
    haveI : P.IsMaximal := hP'.1.isMaximal (Ideal.ne_bot_of_mem_primesOver hpZ_ne hP')
    haveI : Q.IsMaximal := hQ'.1.isMaximal (Ideal.ne_bot_of_mem_primesOver hpZ_ne hQ')
    exact Ideal.isCoprime_of_isMaximal hPQ
  change Nat.card ((𝓞 K) ⧸ ∏ P ∈ S, P) = ∏ P ∈ S, Nat.card ((𝓞 K) ⧸ P)
  exact natCard_quotient_prod_pairwiseCoprime (𝓞 K) S hcop

end Commons.NumberTheory.NumberField