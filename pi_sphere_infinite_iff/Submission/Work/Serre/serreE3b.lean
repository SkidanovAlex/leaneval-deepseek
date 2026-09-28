import Mathlib
import Submission.Work.Serre.Engine
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.GysinFibreRange
import Submission.Work.StemsB.ThomRatShim
import Submission.Work.StemsB.Periodicity
import Submission.Work.StemsB.FieldDualUCT
import Submission.Work.Cohomology.DualComplex
import Submission.Work.Cohomology.cupNaturalH
import Submission.Work.Serre.ratH_zero_of_pathConnected
import Submission.Work.Serre.pathConnectedSpace_of_ratAcyclic
import Submission.Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration
import Submission.Work.Serre.strictFibre_ratH_homotopyFibre
import Submission.Work.Serre.cylRelPi
import Submission.Work.Serre.thomIsoCylFibreRange

set_option backward.isDefEq.respectTransparency false

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- **E3(b) from the global Thom class**: the assembly.  See the module docstring of
`Submission/Work/Serre/GysinFibreRange.lean`: the class `e` is the absolute class induced by the
Thom class `U`, and `x ↦ x ⌣ e` is the composite of the Thom isomorphism with the two
isomorphisms `relToAbs` (degree `≥ 2`) and `cylInr^*`. -/
theorem serreE3b_of_thomCyl (hT : ThomIsoCylFibreRange) : SerreE3b := by
  intro E B _ _ p e₀ r N hr hp hB hE hfib hgen m hm
  haveI : PathConnectedSpace B := inferInstance
  haveI hFund : Subsingleton (FundamentalGroup B (p e₀)) :=
    ⟨fun x y => Quotient.inductionOn₂ x y
      (fun u v => Quotient.sound (SimplyConnectedSpace.paths_homotopic u v))⟩
  have hsc : Subsingleton (HomotopyGroup (Fin 1) B (p e₀)) :=
    ⟨fun x y => (HomotopyGroup.pi1EquivFundamentalGroup (x := p e₀)).injective
      (Subsingleton.elim _ _)⟩
  have hEpc : PathConnectedSpace E := pathConnectedSpace_of_ratAcyclic hE
  haveI hpcFib : PathConnectedSpace (Work.StemsB.fibre p (p e₀)) :=
    pathConnectedSpace_fibre_of_isSerreFibration p hp (p e₀) hEpc inferInstance hsc
  have hbridge : ∀ j : ℕ, Nonempty (ratH (TopCat.of (Work.StemsB.fibre p (p e₀))) j ≅
      ratH (TopCat.of (Work.RatHurewicz.homotopyFibre p e₀)) j) :=
    fun j => strictFibre_ratH_homotopyFibre p hp e₀ (p e₀) inferInstance j
  have hfibS : ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      IsZero (ratH (TopCat.of (Work.StemsB.fibre p (p e₀))) t) :=
    fun t ht htr htN => IsZero.of_iso (hfib t ht htr htN) (hbridge t).some
  have hgenS : Nonempty (ratH (TopCat.of (Work.StemsB.fibre p (p e₀))) r ≅ ModuleCat.of ℚ ℚ) :=
    ⟨(hbridge r).some ≪≫ hgen.some⟩
  obtain ⟨U, hU⟩ := hT E B p (p e₀) r N hr hp hB hE hpcFib hfibS hgenS
  have hA : ∀ k : ℕ, 0 < k → IsZero (Work.Thom.Coh ℚ k ↥(Set.range (cylIncl p))) := by
    intro k hk
    obtain ⟨φ⟩ := cylHomeo p
    exact isZero_coh_of_homeo φ (isZero_coh_of_ratAcyclic hE hk)
  refine ⟨(Work.Thom.CohMap (cylInr p) ℚ (r + 1)).hom ((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (r + 1)).hom U), ?_⟩
  have hrelIso : IsIso (Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (m + r + 1)) :=
    isIso_relToAbs_succ (Set.range (cylIncl p)) (m + r) (by omega)
      (hA (m + r) (by omega)) (hA (m + r + 1) (by omega))
  have hcylIso : IsIso (Work.Thom.CohMap (cylInr p) ℚ (m + r + 1)) := isIso_cohMap_cylInr p _
  have hfIso : IsIso (ModuleCat.ofHom (((((Work.Thom.mixedCupC ℚ (Set.range (cylIncl p)) m (r + 1))).flip U) ∘ₗ
      (Work.Thom.CohMap (cylRetract p) ℚ m).hom))) := hU m hm
  have hfBij : Function.Bijective (((((Work.Thom.mixedCupC ℚ (Set.range (cylIncl p)) m (r + 1))).flip U) ∘ₗ
      (Work.Thom.CohMap (cylRetract p) ℚ m).hom)) := by
    simpa only [ModuleCat.hom_ofHom] using
      (CategoryTheory.ConcreteCategory.isIso_iff_bijective (ModuleCat.ofHom (((((Work.Thom.mixedCupC ℚ (Set.range (cylIncl p)) m (r + 1))).flip U) ∘ₗ
      (Work.Thom.CohMap (cylRetract p) ℚ m).hom)))).mp hfIso
  have hhBij : Function.Bijective ((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (m + r + 1)).hom) := by
    simpa only [ModuleCat.hom_ofHom] using
      (CategoryTheory.ConcreteCategory.isIso_iff_bijective
        (Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (m + r + 1))).mp hrelIso
  have hgBij : Function.Bijective ((Work.Thom.CohMap (cylInr p) ℚ (m + r + 1)).hom) := by
    simpa only [ModuleCat.hom_ofHom] using
      (CategoryTheory.ConcreteCategory.isIso_iff_bijective
        (Work.Thom.CohMap (cylInr p) ℚ (m + r + 1))).mp hcylIso
  have hkey : (cupWith (TopCat.of B) (r + 1) ((Work.Thom.CohMap (cylInr p) ℚ (r + 1)).hom ((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (r + 1)).hom U)) m) =
      ((Work.Thom.CohMap (cylInr p) ℚ (m + r + 1)).hom).comp (((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (m + r + 1)).hom).comp (((((Work.Thom.mixedCupC ℚ (Set.range (cylIncl p)) m (r + 1))).flip U) ∘ₗ
      (Work.Thom.CohMap (cylRetract p) ℚ m).hom))) := by
    ext x
    change Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of B)) m (r + 1) x
        ((Work.Thom.CohMap (cylInr p) ℚ (r + 1)).hom
          ((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (r + 1)).hom U)) =
      (Work.Thom.CohMap (cylInr p) ℚ (m + (r + 1))).hom
        ((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (m + (r + 1))).hom
          ((Work.Thom.mixedCupC ℚ (Set.range (cylIncl p)) m (r + 1))
            ((Work.Thom.CohMap (cylRetract p) ℚ m).hom x) U))
    rw [Work.StemsB.mixedCup_relToAbs_R ℚ (Set.range (cylIncl p)) m (r + 1)
      ((Work.Thom.CohMap (cylRetract p) ℚ m).hom x) U]
    rw [Work.Cohomology.cupNaturalH ℚ (TopCat.ofHom (cylInr p)) m (r + 1)
      ((Work.Thom.CohMap (cylRetract p) ℚ m).hom x)
      ((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (r + 1)).hom U)]
    rw [cohMap_cylInr_cylRetract p m x]
  rw [hkey]
  refine (CategoryTheory.ConcreteCategory.isIso_iff_bijective
    (ModuleCat.ofHom (((Work.Thom.CohMap (cylInr p) ℚ (m + r + 1)).hom).comp (((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (m + r + 1)).hom).comp (((((Work.Thom.mixedCupC ℚ (Set.range (cylIncl p)) m (r + 1))).flip U) ∘ₗ
      (Work.Thom.CohMap (cylRetract p) ℚ m).hom)))))).mpr ?_
  show Function.Bijective ⇑(((Work.Thom.CohMap (cylInr p) ℚ (m + r + 1)).hom).comp (((Work.Thom.relToAbs ℚ (Set.range (cylIncl p)) (m + r + 1)).hom).comp (((((Work.Thom.mixedCupC ℚ (Set.range (cylIncl p)) m (r + 1))).flip U) ∘ₗ
      (Work.Thom.CohMap (cylRetract p) ℚ m).hom))))
  exact hgBij.comp (hhBij.comp hfBij)

/-- **E3(b) (Gysin / Euler class of a rational spherical fibration).**

This is `serreE3b_of_thomCyl` applied to the global Thom class statement
`Work.Serre.thomIsoCylFibreRange` (`Submission/Work/Serre/thomIsoCylFibreRange.lean`), which is
itself the assembled one-liner
`thomIsoCylFibreRange_of_eulerFibreRange (eulerFibreRange_of_cwModelCase (cwModelThomCase_of_altCellStep thomCylCellStepAlt))`.

**The single remaining input of the whole E3(b) node is therefore the cellular step
`Work.Serre.ThomCylCellStepAlt`** (`Submission/Work/Serre/thomCylCellStepAlt.lean`): when that
statement is proved sorry-free, this declaration (and `Work.Serre.thomIsoCylFibreRange`, and hence
`Work.Drive.rh3_of_e3b`) becomes axiom-clean automatically.  Until then its axiom footprint contains
`sorryAx`, inherited from that one statement; the conditional forms are
`serreE3b_of_thomCyl : ThomIsoCylFibreRange → SerreE3b` above and
`Work.Serre.thomIsoCylFibreRange_of_cellStep` (`Submission/Work/Serre/ticfrAssembly.lean`). -/
theorem serreE3b : Work.Serre.SerreE3b :=
  serreE3b_of_thomCyl thomIsoCylFibreRange

end

end Work.Serre
