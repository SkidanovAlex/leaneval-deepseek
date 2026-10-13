import Mathlib
import Submission.Work.DSG4b.Defs
import Submission.Work.DSG4b.RootLift
import Submission.Work.DSG4b.rootLocal_flat

/-!
# DSG4b, G4b residue enlargement: the "U-part" (`Work.DSG4b.uRing`)

Vocabulary for the second half of the residue enlargement (`gonf_residue_enlargement`): over a
*perfectified* ring `S` (a local ring whose residue field `L` is perfect) we adjoin, for every
`α` in `K = AlgebraicClosure L`, a root of the lift `uPoly S α` of the minimal polynomial
`minpoly L α`, lifted coefficientwise along the set-theoretic residue section
`Work.DSG4b.coeffLift`.

The key point is that `uPoly S α` is *monic* (because `minpoly L α` is monic and `coeffLift 1 = 1`),
so that `uRing S` is flat over `S` by the monic-quotient brick `Work.DSG4b.RFAux.flat_quotient_monic`,
and that its `𝔪`-fibre is the "tensor product of all minimal polynomial quotients"
`L[X_α : α ∈ K] ⧸ (minpoly L α)(X_α)`, whose localisation at the canonical maximal ideal is `K`.
-/

namespace Work.DSG4b

universe a

open MvPolynomial Polynomial

section Eval

variable {R S₁ : Type*} [CommSemiring R] [CommSemiring S₁] {σ : Type*}

/-- Applying a ring homomorphism out of `MvPolynomial σ R` to the evaluation at a variable of a
univariate polynomial over `R`. -/
lemma eval₂Hom_aeval_X (f : R →+* S₁) (g : σ → S₁) (i : σ) (p : Polynomial R) :
    MvPolynomial.eval₂Hom f g (Polynomial.aeval (MvPolynomial.X i : MvPolynomial σ R) p)
      = p.eval₂ f (g i) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, Polynomial.aeval_add, Polynomial.eval₂_add, hp, hq]
  | monomial n r =>
      rw [Polynomial.aeval_def]
      simp only [Polynomial.eval₂_monomial, MvPolynomial.algebraMap_eq, MvPolynomial.eval₂Hom_C,
        MvPolynomial.eval₂Hom_X', map_mul, map_pow]

end Eval

section Main

variable (S : Type a) [CommRing S] [IsLocalRing S]

/-- The monic lift, along the set-theoretic coefficient section `Work.DSG4b.coeffLift`, of the
minimal polynomial over the residue field of `S` of an element `α` of an algebraic closure. -/
noncomputable def uPoly (α : AlgebraicClosure (IsLocalRing.ResidueField S)) : Polynomial S :=
  polyLift (minpoly (IsLocalRing.ResidueField S) α)

lemma uPoly_monic (α : AlgebraicClosure (IsLocalRing.ResidueField S)) : (uPoly S α).Monic :=
  polyLift_monic (minpoly.monic (Algebra.IsIntegral.isIntegral α))

lemma uPoly_map (α : AlgebraicClosure (IsLocalRing.ResidueField S)) :
    (uPoly S α).map (IsLocalRing.residue S) = minpoly (IsLocalRing.ResidueField S) α :=
  map_polyLift _

/-- The "separable closure over a perfectified ring": `S[X_α : α ∈ K]` modulo the root relations
for the lifted minimal polynomials. -/
noncomputable abbrev uRing : Type a :=
  MvPolynomial (AlgebraicClosure (IsLocalRing.ResidueField S)) S ⧸ RFAux.qI (uPoly S)

lemma uRing_flat : Module.Flat S (uRing S) :=
  RFAux.flat_quotient_monic (uPoly S) (uPoly_monic S)

/-- The canonical `S`-algebra structure map of `uRing S`. -/
noncomputable def uRingAlg : S →+* uRing S :=
  (Ideal.Quotient.mk (RFAux.qI (uPoly S))).comp
    (MvPolynomial.C : S →+* MvPolynomial (AlgebraicClosure (IsLocalRing.ResidueField S)) S)

/-- The canonical `S`-algebra structure map of `uRing S` is the algebra structure map. -/
lemma uRingAlg_eq_algebraMap : uRingAlg S = algebraMap S (uRing S) := by
  ext s
  simp only [uRingAlg, RingHom.comp_apply, MvPolynomial.algebraMap_eq]
  exact congrFun (congrArg DFunLike.coe (Ideal.Quotient.algebraMap_eq (RFAux.qI (uPoly S))))
    (MvPolynomial.C s)

/-- The variable `X_α` of `uRing S`. -/
noncomputable def uVar (α : AlgebraicClosure (IsLocalRing.ResidueField S)) : uRing S :=
  Ideal.Quotient.mk (RFAux.qI (uPoly S))
    (MvPolynomial.X α : MvPolynomial (AlgebraicClosure (IsLocalRing.ResidueField S)) S)

/-- The canonical evaluation `uRing S →+* K`, `X_α ↦ α`, which exists because the lifted minimal
polynomials vanish at the corresponding elements of the algebraic closure. -/
noncomputable def uEv : uRing S →+* AlgebraicClosure (IsLocalRing.ResidueField S) :=
  Ideal.Quotient.lift (RFAux.qI (uPoly S))
    (MvPolynomial.eval₂Hom
      ((algebraMap (IsLocalRing.ResidueField S) (AlgebraicClosure (IsLocalRing.ResidueField S))).comp
        (IsLocalRing.residue S)) (fun α => α))
    (by
      show RFAux.qI (uPoly S) ≤ RingHom.ker
        (MvPolynomial.eval₂Hom
          ((algebraMap (IsLocalRing.ResidueField S) (AlgebraicClosure (IsLocalRing.ResidueField S))).comp
            (IsLocalRing.residue S)) (fun α : AlgebraicClosure (IsLocalRing.ResidueField S) => α))
      rw [RFAux.qI]
      refine Ideal.span_le.mpr ?_
      rintro x ⟨α, rfl⟩
      refine RingHom.mem_ker.mpr ?_
      rw [eval₂Hom_aeval_X]
      have h1 : (polyLift (minpoly (IsLocalRing.ResidueField S) α)).eval₂
          ((algebraMap (IsLocalRing.ResidueField S) (AlgebraicClosure (IsLocalRing.ResidueField S))).comp
            (IsLocalRing.residue S)) α
          = (minpoly (IsLocalRing.ResidueField S) α).eval₂
            (algebraMap (IsLocalRing.ResidueField S)
              (AlgebraicClosure (IsLocalRing.ResidueField S))) α := by
        rw [← Polynomial.eval₂_map]
        exact congrArg (fun q : Polynomial (IsLocalRing.ResidueField S) =>
          q.eval₂ (algebraMap (IsLocalRing.ResidueField S)
            (AlgebraicClosure (IsLocalRing.ResidueField S))) α) (uPoly_map S α)
      rw [show (uPoly S α) = polyLift (minpoly (IsLocalRing.ResidueField S) α) from rfl]
      rw [h1]
      exact minpoly.aeval _ α)

lemma uEv_uVar (α : AlgebraicClosure (IsLocalRing.ResidueField S)) : uEv S (uVar S α) = α := by
  simp only [uEv, uVar, Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_X']

lemma uEv_surjective : Function.Surjective (uEv S) := by
  intro x
  exact ⟨uVar S x, uEv_uVar S x⟩

/-- The evaluation restricts to the residue map on the coefficient ring. -/
lemma uEv_uRingAlg (s : S) : uEv S (uRingAlg S s) =
    algebraMap (IsLocalRing.ResidueField S) (AlgebraicClosure (IsLocalRing.ResidueField S))
      (IsLocalRing.residue S s) := by
  simp only [uEv, uRingAlg, RingHom.comp_apply, Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_C]

lemma uEv_eq_zero_of_mem_maximalIdeal {s : S} (hs : s ∈ IsLocalRing.maximalIdeal S) :
    uEv S (uRingAlg S s) = 0 := by
  rw [uEv_uRingAlg, (IsLocalRing.residue_eq_zero_iff s).mpr hs, map_zero]

end Main

end Work.DSG4b
