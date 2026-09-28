import Mathlib
import Submission.Work.StemsB.sphRatHomology
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.localHomology

/-!
# Tools for the sphere loop-space computation (Step I)

General tools used by the sphere-specific route to the crux (`CONTRACTS.md` §F, Step I):

* `Work.StemsB.isZero_homology_rat_of_isZero_homology_int` — vanishing of integral singular
  homology implies vanishing of rational singular homology (change of rings `⊗[ℤ] ℚ`);
* `Work.StemsB.isIso_hPairδ_of_isZero` — if the total space of a pair is acyclic in degrees `m`
  and `m-1`, then the connecting homomorphism `H_m(X,A) → H_{m-1}(A)` of the long exact sequence
  of the pair is an isomorphism (so that `H_m(X,A) ≅ H_{m-1}(A)`).
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

namespace Work.StemsB

noncomputable section

/-- **Vanishing of integral singular homology implies vanishing of rational singular homology.**

The rational singular chains are the integral ones with coefficients extended along `ℤ → ℚ`
(`Work.StemsB.SphRat.chainComplexBaseChange`), and extension of scalars along the flat ring
homomorphism `ℤ → ℚ` preserves homology. -/
theorem isZero_homology_rat_of_isZero_homology_int (X : TopCat) (m : ℕ)
    (h : IsZero ((Work.Cohomology.singularChains ℤ X).homology m)) :
    IsZero ((Work.Cohomology.singularChains ℚ X).homology m) := by
  haveI : PreservesFiniteLimits (ModuleCat.extendScalars (Int.castRingHom ℚ)) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (by rw [RingHom.Flat]; infer_instance)
  haveI : PreservesFiniteColimits (ModuleCat.extendScalars (Int.castRingHom ℚ)) := inferInstance
  haveI : ∀ (S : Type), PreservesColimitsOfShape (Discrete S)
      (ModuleCat.extendScalars (Int.castRingHom ℚ)) := fun _ => inferInstance
  let F : ModuleCat ℤ ⥤ ModuleCat ℚ := ModuleCat.extendScalars (Int.castRingHom ℚ)
  haveI : F.PreservesHomology := inferInstance
  let K : ChainComplex (ModuleCat ℤ) ℕ := Work.Cohomology.singularChains ℤ X
  let L : ChainComplex (ModuleCat ℚ) ℕ := Work.Cohomology.singularChains ℚ X
  have hΦ : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ≅ L :=
    SphRat.chainComplexBaseChange F (TopCat.toSSet.obj X) (ModuleCat.of ℤ ℤ) ≪≫
      SphRat.chainComplexCoeffIso (TopCat.toSSet.obj X) SphRat.extendScalarsIntRatIso
  have hΨ : L.homology m ≅ F.obj (K.homology m) :=
    (HomologicalComplex.homologyMapIso hΦ m).symm ≪≫ (SphRat.homologyMapBaseChange F K m).some
  exact IsZero.of_iso (Functor.map_isZero F h) hΨ

/-- **The connecting homomorphism of the long exact sequence of a pair is an isomorphism in a
degree where the total space is acyclic (in this degree and the previous one).** -/
theorem isIso_hPairδ_of_isZero (X : TopCat) (A : Set X) (m : ℕ) (hm : 1 ≤ m)
    (hX : IsZero ((Work.Cohomology.singularChains ℤ X).homology m))
    (hX' : IsZero ((Work.Cohomology.singularChains ℤ X).homology (m - 1))) :
    IsIso (Work.Cohomology.hPairδ X A (m - 1)) := by
  -- monomorphism: exactness at `H_m(X,A)`, with `H_m(X) = 0`
  have hmono : Mono (Work.Cohomology.hPairδ X A (m - 1)) := by
    have hX'' : IsZero ((Work.Cohomology.singularChains ℤ X).homology ((m - 1) + 1)) := by
      rw [Nat.sub_add_cancel hm]; exact hX
    have hex : (ShortComplex.mk (HomologicalComplex.homologyMap
        (cokernel.π (Work.Cohomology.inclChains X A)) ((m - 1) + 1))
        (Work.Cohomology.hPairδ X A (m - 1))
        (Work.Cohomology.hPair_comp_δ X A (m - 1))).Exact :=
      Work.Cohomology.hPair_exact₃ X A (m - 1)
    exact (ShortComplex.exact_iff_mono _ (hX''.eq_zero_of_src _)).mp hex
  -- epimorphism: exactness at `H_{m-1}(A)`, with `H_{m-1}(X) = 0`
  have hepi : Epi (Work.Cohomology.hPairδ X A (m - 1)) := by
    have hex : (ShortComplex.mk (Work.Cohomology.hPairδ X A (m - 1))
        (HomologicalComplex.homologyMap (Work.Cohomology.inclChains X A) (m - 1))
        (Work.Cohomology.hPairδ_comp X A (m - 1))).Exact :=
      Work.Cohomology.hPair_exact₁ X A (m - 1)
    exact (ShortComplex.exact_iff_epi _ (hX'.eq_zero_of_tgt _)).mp hex
  exact isIso_of_mono_of_epi _

end

end Work.StemsB
