import Submission.Work.Whitney.tcmRelCup_assoc_prep

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Whitney

open Work.Cohomology
open CategoryTheory AlgebraicTopology CategoryTheory.Limits

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# Associativity of the canonical relative–relative cup product

The canonical relative–relative cup product `Work.Whitney.tcmRelCup` is the Alexander–Whitney
product on the `A+B` complex `C^*(X,A) ∩ C^*(X,B)`, transported along the inverse of the
quasi-isomorphism `C^*(X,A∪B) → C^*(X,A+B)`.  This module proves its associativity.

Both bracketings of the triple product are compared inside the three-fold intersection complex
`C^*(X,A+B+C)` (`Work.Whitney.pd3CohR`), where the comparison is the proved lemma
`Work.Whitney.tcmRelCup_tripleImage_agreeA`; the injectivity of `C^*(X,A∪B∪C) → C^*(X,A+B+C)`
(`Work.Whitney.pd3InclRelR_quasiIso`) then gives the result.  The `Set.union_assoc` transport
between `(A∪B)∪C` and `A∪(B∪C)` is handled through the *generalised* inclusion
`pd3InclRelROf`, whose target set is a variable so that the transport lemma
`pd3InclRelROf_transport` applies.  All the auxiliary material lives in
`Submission.Work.Whitney.tcmRelCup_assoc_prep`.
-/

/-- **Associativity of the canonical relative–relative cup product.** -/
theorem tcmRelCup_assoc : Work.Whitney.tcmRelCupAssoc := by
  intro X _ A B C hA hB hC p q r a b c
  set L₀ : Work.Thom.RelCoh ℤ ((p + q) + r) X ((A ∪ B) ∪ C) :=
    tcmRelCup (A ∪ B) C (hA.union hB) hC (p + q) r (tcmRelCup A B hA hB p q a b) c with hL₀
  set R₀ : Work.Thom.RelCoh ℤ (p + (q + r)) X (A ∪ (B ∪ C)) :=
    tcmRelCup A (B ∪ C) hA (hB.union hC) p (q + r) a (tcmRelCup B C hB hC q r b c) with hR₀
  -- Move the `Nat.add_assoc` transport outside the `Set.union_assoc` transport, so that the
  -- degree transport of the left-hand side can be moved through the structural inclusion.
  refine (eqRec_swapRel (Set.union_assoc A B C) (Nat.add_assoc p q r) L₀).trans ?_
  -- It now suffices to prove the equation after transporting back along `Set.union_assoc`.
  refine eqRec_symm_inj (Set.union_assoc A B C) (p + (q + r)) ?_
  show (Set.union_assoc A B C).symm ▸ ((Set.union_assoc A B C) ▸ ((Nat.add_assoc p q r) ▸ L₀))
      = (Set.union_assoc A B C).symm ▸ R₀
  rw [eqRec_self_symm (Set.union_assoc A B C) (p + (q + r)) ((Nat.add_assoc p q r) ▸ L₀)]
  -- The structural inclusion `C^*(X,A∪B∪C) → C^*(X,A+B+C)` is injective in cohomology.
  apply pd3InclRelR_injective A B C hA hB hC (p + (q + r))
  show (HomologicalComplex.homologyMap (pd3InclRelR (TopCat.of X) A B C) (p + (q + r))).hom
        ((Nat.add_assoc p q r) ▸ L₀)
      = (HomologicalComplex.homologyMap (pd3InclRelR (TopCat.of X) A B C) (p + (q + r))).hom
        ((Set.union_assoc A B C).symm ▸ R₀)
  -- The image of the left-hand side, factorised through the pair `(A∪B, C)`.
  have hleft := pd3InclRelR_image_left A B C (Nat.add_assoc p q r) L₀
  -- The image of the right-hand side, factorised through the pair `(A, B∪C)`.
  have hright := pd3InclRelR_image_right A B C p q r (Set.union_assoc A B C).symm R₀
  -- The two factorised images agree, by the comparison lemma for the triple product.
  have hmid : (Nat.add_assoc p q r) ▸ ((HomologicalComplex.homologyMap
            (pdABCOhR_to_pd3CohR_left (TopCat.of X) A B C) (p + q + r)).hom
          ((HomologicalComplex.homologyMap
            (pdABInclRelR (R := ℤ) (TopCat.of X) (A ∪ B) C) (p + q + r)).hom L₀))
      = (HomologicalComplex.homologyMap (pdABCOhR_to_pd3CohR_right (TopCat.of X) A B C)
          (p + (q + r))).hom
        ((HomologicalComplex.homologyMap (pdABInclRelR (R := ℤ) (TopCat.of X) A (B ∪ C))
          (p + (q + r))).hom R₀) := by
    rw [hL₀, hR₀]
    exact tcmRelCup_tripleImage_agreeA A B C hA hB hC p q r a b c
  exact hleft.trans (hmid.trans hright.symm)

end Work.Whitney
