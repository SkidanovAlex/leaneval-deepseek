import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

namespace Commons.RingTheory.Ideal

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- For the standard `ℕ`-grading of a multivariate polynomial ring, the decomposition map
is the homogeneous component projection. -/
private lemma decompose_eq_homogeneousComponent {k : Type} [CommSemiring k] {m : ℕ}
    (x : MvPolynomial (Fin m) k) (j : ℕ) :
    (DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin m) k) x j :
        MvPolynomial (Fin m) k) = MvPolynomial.homogeneousComponent j x := by
  rw [← DirectSum.Decomposition.decompose'_eq]
  exact MvPolynomial.decomposition.decompose'_apply x j

theorem minimalPrimes_homogeneous {k : Type} [Field k] {m : ℕ}
    (J : Ideal (MvPolynomial (Fin m) k))
    (hJ : ∀ x ∈ J, ∀ j, MvPolynomial.homogeneousComponent j x ∈ J)
    {q : Ideal (MvPolynomial (Fin m) k)} (hq : q ∈ J.minimalPrimes) :
    ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q := by
  classical
  have hJhom : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin m) k) := by
    intro i x hx
    rw [decompose_eq_homogeneousComponent]
    exact hJ x hx i
  have hqprime : q.IsPrime := hq.1.1
  have hcoreprime :
      (q.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k)).toIdeal.IsPrime :=
    hqprime.homogeneousCore
  have hJ_le_core :
      J ≤ (q.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k)).toIdeal := by
    have hmono : J.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k) ≤
        q.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k) :=
      Ideal.homogeneousCore_mono _ hq.1.2
    have hto : (J.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k)).toIdeal ≤
        (q.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k)).toIdeal :=
      hmono
    rwa [Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_self hJhom] at hto
  have hcore_le_q :
      (q.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k)).toIdeal ≤ q :=
    Ideal.toIdeal_homogeneousCore_le _ q
  have hq_le_core :
      q ≤ (q.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k)).toIdeal :=
    hq.2 ⟨hcoreprime, hJ_le_core⟩ hcore_le_q
  have hqhom : q.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin m) k) :=
    (Ideal.IsHomogeneous.iff_eq _ q).mpr (le_antisymm hcore_le_q hq_le_core)
  intro x hx j
  exact (MvPolynomial.mem_iff_homogeneousComponent_mem hqhom x).mp hx j

end

end Commons.RingTheory.Ideal