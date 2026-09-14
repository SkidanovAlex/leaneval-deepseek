import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open MvPolynomial

set_option linter.style.haveILetI false

namespace Commons.Algebra.MvPolynomial

theorem finite_zeroLocus_of_moduleFinite {F : Type*} [Field F] [IsAlgClosed F] {r : ℕ}
    (I : Ideal (MvPolynomial (Fin r) F)) (h : Module.Finite F (MvPolynomial (Fin r) F ⧸ I)) :
    (MvPolynomial.zeroLocus F I).Finite := by
  classical
  haveI : Module.Finite F (MvPolynomial (Fin r) F ⧸ I) := h
  -- Each variable, viewed in the finite-dimensional quotient, is integral over `F`.
  choose p hp_monic hp_zero using fun i : Fin r =>
    IsIntegral.of_finite F (Ideal.Quotient.mkₐ F I (MvPolynomial.X i))
  have hp_eval : ∀ i,
      Polynomial.aeval (Ideal.Quotient.mkₐ F I (MvPolynomial.X i)) (p i) = 0 := by
    intro i
    rw [Polynomial.aeval_def]
    exact hp_zero i
  -- Hence the one-variable polynomial `p i` evaluated at `X i` lies in `I`.
  have hmem : ∀ i, Polynomial.aeval (MvPolynomial.X i) (p i) ∈ I := by
    intro i
    have h1 := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ F I) (MvPolynomial.X i) (p i)
    have h0 : (Ideal.Quotient.mkₐ F I) (Polynomial.aeval (MvPolynomial.X i) (p i)) = 0 := by
      rw [← h1]
      exact hp_eval i
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact h0
  -- A point of the zero locus has each coordinate among the roots of `p i`.
  have hsub : MvPolynomial.zeroLocus F I ⊆
      {a : Fin r → F | ∀ i, a i ∈ ((p i).roots.toFinset : Set F)} := by
    intro a ha i
    have hroot : (p i).IsRoot (a i) := by
      rw [Polynomial.IsRoot.def]
      have h2 : Polynomial.aeval (a i) (p i)
          = (MvPolynomial.aeval (R := F) a) (Polynomial.aeval (R := F) (MvPolynomial.X i) (p i)) := by
        have h3 := Polynomial.aeval_algHom_apply (MvPolynomial.aeval (R := F) a) (MvPolynomial.X i) (p i)
        rwa [MvPolynomial.aeval_X] at h3
      rw [show Polynomial.eval (a i) (p i) = Polynomial.aeval (a i) (p i) by
        rw [Polynomial.aeval_def]; simp]
      rw [h2]
      exact ha _ (hmem i)
    rw [Finset.mem_coe]
    rw [Multiset.mem_toFinset]
    rw [Polynomial.mem_roots (hp_monic i).ne_zero]
    exact hroot
  exact (Set.Finite.pi' (κ := fun _ => F)
    (fun i => Finset.finite_toSet ((p i).roots.toFinset))).subset hsub

end Commons.Algebra.MvPolynomial