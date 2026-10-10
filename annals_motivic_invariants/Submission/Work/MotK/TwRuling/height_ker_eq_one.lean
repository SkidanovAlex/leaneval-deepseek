import Mathlib
import Submission.Work.MotK.CensusBridge.height_eq_one_of_trdeg_eq_two
import Submission.Work.MotV.trdeg_fractionRing_mvPolynomial

set_option linter.unusedVariables false -- v435-speed

/-!
# The kernel of a `K`-algebra map `K[X₀,X₁,X₂] → F` has height one

If `φ : K[X₀,X₁,X₂] →ₐ[K] F` is a `K`-algebra map into a field whose image has transcendence
degree `2` over `K`, then `ker φ` is a height-one prime of `K[X₀,X₁,X₂]`.

This is the codimension-one case of the dimension formula for the three-dimensional polynomial
ring: `height p + dim(R ⧸ p) = dim R = 3`, and `dim(R ⧸ p) = trdeg_K (R ⧸ p) = 2`.

The work is delegated to `Work.MotK.CensusBridge.height_eq_one_of_trdeg_eq_two`, which needs the
hypothesis in the form `trdeg_K (Frac (R ⧸ p)) = 2`.  The bridges here are
* `R ⧸ ker φ ≃ₐ[K] φ.range` (first isomorphism theorem, `Ideal.quotientKerAlgEquivOfSurjective`
  applied to the surjective `φ.rangeRestrict`), so the residue ring has transcendence degree `2`;
* passing to the fraction field does not change the transcendence degree, since
  `Frac A` is algebraic over `A` (`Work.MotV.isAlgebraic_fractionRing_self`), so that
  `Algebra.trdeg K (Frac A) = Algebra.trdeg K A` by additivity of `trdeg` in towers.
-/

set_option linter.style.haveILetI false

namespace Work.MotK.TwRuling

theorem height_ker_eq_one (K : Type) [Field K] {F : Type} [Field F] [Algebra K F]
    (φ : MvPolynomial (Fin 3) K →ₐ[K] F) (h : Algebra.trdeg K ↥(φ.range) = 2) :
    (RingHom.ker φ).height = 1 := by
  classical
  -- `ker φ` is prime, so the quotient is a domain.
  haveI hp : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  -- The quotient `K[X₀,X₁,X₂] ⧸ ker φ` is the range of `φ`.
  have htrA : Algebra.trdeg K (MvPolynomial (Fin 3) K ⧸ RingHom.ker φ) = 2 := by
    have h1 : Algebra.trdeg K
        (MvPolynomial (Fin 3) K ⧸ RingHom.ker φ.rangeRestrict) = 2 := by
      rw [AlgEquiv.trdeg_eq
        (Ideal.quotientKerAlgEquivOfSurjective φ.rangeRestrict_surjective)]
      exact h
    rwa [AlgHom.ker_rangeRestrict φ] at h1
  -- The fraction field is algebraic over the quotient, so the transcendence degree is unchanged.
  have htrF : Algebra.trdeg K (FractionRing (MvPolynomial (Fin 3) K ⧸ RingHom.ker φ)) = 2 := by
    haveI : Algebra.IsAlgebraic (MvPolynomial (Fin 3) K ⧸ RingHom.ker φ)
        (FractionRing (MvPolynomial (Fin 3) K ⧸ RingHom.ker φ)) :=
      Work.MotV.isAlgebraic_fractionRing_self _
    have ht := trdeg_add_eq K (MvPolynomial (Fin 3) K ⧸ RingHom.ker φ)
      (A := FractionRing (MvPolynomial (Fin 3) K ⧸ RingHom.ker φ))
    have h0 : Algebra.trdeg (MvPolynomial (Fin 3) K ⧸ RingHom.ker φ)
        (FractionRing (MvPolynomial (Fin 3) K ⧸ RingHom.ker φ)) = 0 := trdeg_eq_zero
    rw [h0, add_zero] at ht
    rw [← ht, htrA]
  exact Work.MotK.CensusBridge.height_eq_one_of_trdeg_eq_two K (RingHom.ker φ) htrF

end Work.MotK.TwRuling
