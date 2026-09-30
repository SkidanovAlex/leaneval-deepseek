import Mathlib
import Submission.Work.Charts.Step3Defs
import Submission.Work.Charts.exists_V_of_landsIn_Wp
import Submission.Work.Charts.landsIn_Wp_of_linEquiv
import Submission.Work.Charts.exists_sepPt_landsIn
import Submission.Work.Charts.genericPoint_notMem_image_bcFst
import Submission.Work.Charts.finiteDimensional_resField_of_isClosed
import Submission.Work.Charts.surjective_quotMap
import Submission.Work.Charts.isProper_quotMap
import Submission.Work.Charts.exists_lift_bcSch
import Submission.Work.Charts.step3Z_ne_univ
import Submission.Work.Charts.mem_omegaOpen_of_landsIn_step3U
import Submission.Work.SymQuot.Sym.isIntegral_sym
import Submission.Work.SymQuot.Sym.geometricallyIrreducible_sym

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.Charts

universe u

/-- **Every closed point of `Sym^g C` lies in `Ω_E` for a centre `E` over a finite separable
extension of `K`.**

This is step 3 (SEP-PT + `x ∈ Ω_E`) of route B of
`Submission/Work/NOTES_LEAD_jacobian_charts3.md` §1(S), the last ingredient of the cover
COV′: fix the closed point `x` of `S = Sym^g C`, so that its residue field `κ(x)` is finite
over `K` (`finiteDimensional_resField_of_isClosed`) and the projection
`fst : S_{κ(x)} ⟶ S` of the base change is finite, hence closed.

* `step3Z_ne_univ` shows that the slice `b_x = add(x ∘ snd, fst) : S_{κ(x)} ⟶ Sym^{g+g} C`
  meets the open `W′` on which the residue map `ρ` is defined and takes its values in the
  Brill–Noether chart `V`;
* hence, by FIBRE-GEN (`genericPoint_notMem_image_bcFst`), the generic point of `S` is not in
  `fst (Z_x)` where `Z_x = b_x⁻¹(W′)ᶜ`, i.e. the open `U_x = S ∖ fst(Z_x)` is nonempty;
* SEP-PT (`exists_sepPt_landsIn`) applied to the quotient `quotMap : C^g ⟶ S` then produces a
  finite separable extension `k₁ ⊆ SeparableClosure K` and a point `E` of `S` over `k₁` whose
  closed point lies in `U_x`;
* `mem_omegaOpen_of_landsIn_step3U` converts `E ∈ U_x` into `x ∈ Ω_E`. -/
theorem exists_centre_of_isClosed {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SpecLin.DivBase C] (R : Work.Charts.RochData C) (I : Work.Charts.Step3Data R)
    (x : ((I.symGeom R.g).S).left) (hx : IsClosed ({x} : Set ((I.symGeom R.g).S).left))
    [FiniteDimensional K (Work.GCBasics.resField ((I.symGeom R.g).S) x)] :
    ∃ (k₁ : IntermediateField K (SeparableClosure K)) (_ : FiniteDimensional K ↥k₁)
      (E : Work.GCBasics.FPt ((I.symGeom R.g).S) ↥k₁),
      x ∈ Work.Charts.omegaOpen R I.symGeom I.resid I.geo E I.a I.d := by
  classical
  haveI hInt : AlgebraicGeometry.IsIntegral ((I.symGeom R.g).S).left := I.geo.integral_g
  haveI hGirr : AlgebraicGeometry.GeometricallyIrreducible ((I.symGeom R.g).S).hom :=
    I.geo.geomIrr_g
  haveI hlft : AlgebraicGeometry.LocallyOfFiniteType ((I.symGeom R.g).S).hom :=
    I.geo.locallyOfFiniteType_g
  -- the closed point `x` cut out by the slice `b_x` is a proper closed subset of `S_κ`
  have hZ : Work.Charts.step3Z R I.symGeom I.resid I.geo x I.a I.d ≠ Set.univ :=
    Work.Charts.step3Z_ne_univ R I x
  -- hence `U_x = S ∖ fst(Z_x)` is nonempty, by FIBRE-GEN
  have hU : Work.Charts.step3U R I.symGeom I.resid I.geo x I.a I.d ≠ ⊥ := by
    intro hbot
    have hset : (Work.Charts.step3U R I.symGeom I.resid I.geo x I.a I.d :
        Set ((I.symGeom R.g).S).left) = ∅ := by
      rw [hbot]; rfl
    have himg : (Work.Charts.bcFst ((I.symGeom R.g).S)
          (Work.GCBasics.resField ((I.symGeom R.g).S) x)).left.base ''
          (Work.Charts.step3Z R I.symGeom I.resid I.geo x I.a I.d) = Set.univ := by
      have h := congrArg (fun t : Set ((I.symGeom R.g).S).left => tᶜ) hset
      simpa [Work.Charts.step3U] using h
    have hgen := Work.Charts.genericPoint_notMem_image_bcFst (X := (I.symGeom R.g).S)
      (Work.GCBasics.resField ((I.symGeom R.g).S) x)
      (Work.Charts.step3Z R I.symGeom I.resid I.geo x I.a I.d)
      (Work.Charts.isClosed_step3Z R I.symGeom I.resid I.geo x I.a I.d) hZ
    exact hgen (himg ▸ Set.mem_univ _)
  -- SEP-PT for the quotient map `C^g ⟶ Sym^g C`
  haveI hsm : AlgebraicGeometry.Smooth (Work.Charts.Cprod C R.g).hom :=
    Work.SymQuot.smooth_pi_prod C R.g
  haveI huo : AlgebraicGeometry.UniversallyOpen C.toOver.hom := by infer_instance
  haveI hgi : AlgebraicGeometry.GeometricallyIrreducible (Work.Charts.Cprod C R.g).hom :=
    Work.SymQuot.Sym.geometricallyIrreducible_prod C.toOver R.g
  haveI hlftY : AlgebraicGeometry.LocallyOfFiniteType (Work.Charts.Cprod C R.g).hom :=
    inferInstance
  letI hsg : Work.SpecLin.SymGeom C R.g := I.symGeom R.g
  obtain ⟨k₁, hk₁, E, hE⟩ := Work.Charts.exists_sepPt_landsIn
    (X := (I.symGeom R.g).S) (Y := Work.Charts.Cprod C R.g)
    (q := Work.Charts.quotMap C R.g)
    (Work.Charts.isProper_quotMap R.g) (Work.Charts.surjective_quotMap R.g)
    (Work.Charts.step3U R I.symGeom I.resid I.geo x I.a I.d) hU
  exact ⟨k₁, hk₁, E, Work.Charts.mem_omegaOpen_of_landsIn_step3U
    R I.symGeom I.resid I.geo I.a I.d x ↥k₁ E hE⟩

end Work.Charts
