import Mathlib
import Submission.Work.Whitney.TCMProdDefs
import Submission.Work.Sph3Disc.pairDelta_mixedCup_general
import Submission.Work.Thom.Pair
import Submission.Work.Whitney.Cutoff
import Submission.Work.Whitney.CocycleSmul

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The cut-off class of a relative cup (the class-level Leibniz step)

This module proves `Work.Whitney.cutoff_class_formula`: the relative--relative cup of a class
`a : H^m(X,A)` with the transgression `pairδC C 0 γ` of a `0`-cocycle `γ` on `C` is `(-1)^m` times
the class in the `A+C` complex of `d (cup alpha gamma_t)`, where `alpha` is a cocycle
representative of `a` and `gamma_t` an absolute lift of `γ`.

This is the *class-level* form of the atomic Leibniz identity
`cup α (d γt) = (-1)^m • d (cup α γt)`
(`Work.Cohomology.cup_cochainDiff_leibniz`, in `Submission/Work/Whitney/Cutoff.lean`), which is the
origin of the Koszul sign `(-1)^n` in the rank-one case of the model product formula
`Work.Whitney.rankOne_cup_model`.

The module also contains the auxiliary
`Work.Cohomology.homologyPi_cocycleOfK_congr` (the congruence of `cocycleOfK` for equal cochains).

See `rankOne_cup_model_NOTES.md` §24 for the exact final proof script and for the remaining pieces
of the rank-one case.
-/

namespace Work.Cohomology
open CategoryTheory CategoryTheory.Limits

/-- `cocycleOfK` is congruent for equal cochains (both cocycle proofs). -/
theorem homologyPi_cocycleOfK_congr (K : CochainComplex (ModuleCat ℤ) ℕ) {n : ℕ}
    (c c' : ↑(K.X n)) (h : c = c')
    (hc : (ModuleCat.Hom.hom (K.d n (n + 1))) c = 0)
    (hc' : (ModuleCat.Hom.hom (K.d n (n + 1))) c' = 0) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyπ K n)) (cocycleOfK K c hc)
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyπ K n)) (cocycleOfK K c' hc') := by
  subst h
  exact congrArg (fun hh => (ModuleCat.Hom.hom (HomologicalComplex.homologyπ K n))
    (cocycleOfK K c hh)) (Subsingleton.elim hc hc')

end Work.Cohomology

namespace Work.Whitney

open Work.Thom
open Work.Cohomology
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

noncomputable section

/-- **Piece (2), the class-level cut-off formula**: the relative cup of a class `a` with the
transgression of a `0`-cocycle `γ` on `C` is `(-1)^m` times the class in the `A+C` complex of
`d (cup alpha gamma_t)`, where `alpha` is a cocycle representative of `a` and `gamma_t` an absolute
lift of `γ`.  This is the "cut-off class" formula of `rankOne_cup_model_NOTES.md` §2. -/
theorem cutoff_class_formula {X : Type} [TopologicalSpace X] (A C : Set X) (hA : IsOpen A)
    (hC : IsOpen C) (m : ℕ)
    (α : (relComplex ℤ (TopCat.of X) A).X m)
    (hα : (relComplex ℤ (TopCat.of X) A).d m (m + 1) α = 0)
    (hα' : relDiffLM ℤ (TopCat.of X) A m α = 0)
    (γ : Cochain ℤ (ssB ↥C) 0) (hγ : cochainDiff ℤ (ssB ↥C) γ = 0)
    (γt : Cochain ℤ (ssB X) 0)
    (hγt : (ModuleCat.Hom.hom ((restr ℤ (TopCat.of X) C).f 0)) γt = γ)
    (hmem : ((singularCochainComplex ℤ (TopCat.of X)).d m (m + 1)).hom
        (cup ℤ (ssB X) α.1 γt) ∈ pdABKernR (TopCat.of X) A C (m + 1))
    (hcoc : (pdABCohR (TopCat.of X) A C).d (m + 1) (m + 1 + 1)
        ⟨((singularCochainComplex ℤ (TopCat.of X)).d m (m + 1)).hom (cup ℤ (ssB X) α.1 γt),
          hmem⟩ = 0) :
    (HomologicalComplex.homologyMap (pdABInclRelR (TopCat.of X) A C) (m + 1)).hom
      ((tcmRelCup A C hA hC m 1)
        (relClassOf ℤ (TopCat.of X) A α hα')
        ((pairδC C 0).hom (cohomologyClassOf ℤ (ssB ↥C) γ hγ)))
    = ((-1 : ℤ) ^ m) •
      ((pdABCohR (TopCat.of X) A C).homologyπ (m + 1)).hom
        (cocycleOfK (pdABCohR (TopCat.of X) A C)
          ⟨((singularCochainComplex ℤ (TopCat.of X)).d m (m + 1)).hom (cup ℤ (ssB X) α.1 γt),
            hmem⟩ hcoc) := by
  -- Step 1: the gauge
  rw [tcmRelCup, tcmRelCupG_apply, tcmRelCupInv_spec]
  -- Step 2: the transgression representative (piece (2i))
  obtain ⟨hmemC, hcocC, hpair⟩ := Work.Whitney.pairδC_class_of_lift C γ hγ γt hγt
  rw [hpair]
  -- Step 3: pass to the `homologyπ ∘ cocycleOfK` form
  rw [Work.Cohomology.relClassOf_eq_homologyπ_cocycleOfK ℤ (TopCat.of X) A α hα' hα]
  -- Item 1: the *second* argument, in the `homologyπ ∘ cocycleOfK` form
  have hcocC' : (Work.Cohomology.relComplex ℤ (TopCat.of X) C).d 1 (1 + 1)
      ⟨((Work.Cohomology.singularCochainComplex ℤ (TopCat.of X)).d 0 1).hom γt, hmemC⟩ = 0 := by
    rw [Work.Cohomology.relComplex_d]
    exact hcocC
  rw [Work.Cohomology.relClassOf_eq_homologyπ_cocycleOfK ℤ (TopCat.of X) C
    ⟨((Work.Cohomology.singularCochainComplex ℤ (TopCat.of X)).d 0 1).hom γt, hmemC⟩ hcocC hcocC']
  -- Residual item 1: `starAB X A C m 1 α ⟨d γt, hmemC⟩` is a cocycle in the `A+C` complex
  have hstar : (Work.Whitney.pdABCohR (TopCat.of X) A C).d (m + 1) (m + 1 + 1)
      ((Work.Whitney.starAB (TopCat.of X) A C m 1) α
        ⟨((Work.Cohomology.singularCochainComplex ℤ (TopCat.of X)).d 0 1).hom γt, hmemC⟩) = 0 := by
    have h := Work.Whitney.Leibniz3_starAB (R := ℤ) (TopCat.of X) A C (m := m) (n := 1) α
      ⟨((Work.Cohomology.singularCochainComplex ℤ (TopCat.of X)).d 0 1).hom γt, hmemC⟩
    rwa [hα, hcocC', map_zero, map_zero, smul_zero, add_zero] at h
  -- Residual item 2: read off the class of `starAB ...` via `relRelCupHMap_apply`
  rw [Work.Whitney.relRelCupHMap_apply (TopCat.of X) A C m 1 α
    ⟨((Work.Cohomology.singularCochainComplex ℤ (TopCat.of X)).d 0 1).hom γt, hmemC⟩ hα hcocC' hstar]
  -- The `starAB α ⟨d γt⟩` is a cocycle in the `A+C` complex, of the form `(-1)^m • d (cup α γt)`
  have hαX : Work.Cohomology.cochainDiff ℤ (Work.Whitney.ssB X) α.1 = 0 :=
    Work.Cohomology.relClassOf_cochainDiff ℤ (TopCat.of X) A α hα'
  have hslide : ((Work.Whitney.starAB (TopCat.of X) A C m 1) α
        ⟨((Work.Cohomology.singularCochainComplex ℤ (TopCat.of X)).d 0 1).hom γt, hmemC⟩)
      = ((-1 : ℤ) ^ m) •
        (⟨((Work.Cohomology.singularCochainComplex ℤ (TopCat.of X)).d m (m + 1)).hom
            (Work.Cohomology.cup ℤ (Work.Whitney.ssB X) α.1 γt), hmem⟩ :
          (Work.Whitney.pdABCohR (TopCat.of X) A C).X (m + 1)) := by
    apply Subtype.ext
    rw [Submodule.coe_smul, Work.Whitney.starAB_coe]
    simp only [Subtype.coe_mk, Submodule.coe_mk]
    have h1 : (ModuleCat.Hom.hom
        ((Work.Cohomology.singularCochainComplex ℤ (TopCat.of X)).d 0 1)) γt
        = Work.Cohomology.cochainDiff ℤ (Work.Whitney.ssB X) γt :=
      Work.Cohomology.singularCochain_d_apply ℤ (TopCat.of X) γt
    have h2 : (ModuleCat.Hom.hom
          ((Work.Cohomology.singularCochainComplex ℤ (TopCat.of X)).d m (m + 1)))
          (Work.Cohomology.cup ℤ (Work.Whitney.ssB X) α.1 γt)
        = Work.Cohomology.cochainDiff ℤ (Work.Whitney.ssB X)
            (Work.Cohomology.cup ℤ (Work.Whitney.ssB X) α.1 γt) :=
      Work.Cohomology.singularCochain_d_apply ℤ (TopCat.of X)
        (show Work.Cohomology.Cochain ℤ (Work.Whitney.ssB X) m from
          Work.Cohomology.cup ℤ (Work.Whitney.ssB X) α.1 γt)
    rw [h1, h2]
    exact Work.Cohomology.cup_cochainDiff_leibniz (R := ℤ) (Work.Whitney.ssB X) α.1 hαX γt
  have hcyc : (Work.Whitney.pdABCohR (TopCat.of X) A C).d (m + 1) (m + 1 + 1)
      (((-1 : ℤ) ^ m) •
        (⟨((Work.Cohomology.singularCochainComplex ℤ (TopCat.of X)).d m (m + 1)).hom
            (Work.Cohomology.cup ℤ (Work.Whitney.ssB X) α.1 γt), hmem⟩ :
          (Work.Whitney.pdABCohR (TopCat.of X) A C).X (m + 1))) = 0 := by
    rw [map_zsmul, hcoc, smul_zero]
  rw [← Work.Cohomology.homologyPi_cocycleOfK_smul (Work.Whitney.pdABCohR (TopCat.of X) A C)
    ⟨((Work.Cohomology.singularCochainComplex ℤ (TopCat.of X)).d m (m + 1)).hom
      (Work.Cohomology.cup ℤ (Work.Whitney.ssB X) α.1 γt), hmem⟩ hcoc ((-1 : ℤ) ^ m) hcyc]
  exact Work.Cohomology.homologyPi_cocycleOfK_congr (Work.Whitney.pdABCohR (TopCat.of X) A C)
    _ _ hslide hstar hcyc

end

end Work.Whitney
