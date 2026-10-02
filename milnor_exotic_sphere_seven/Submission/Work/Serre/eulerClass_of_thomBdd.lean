import Mathlib
-- (The declarations this file needs (`Work.Serre.EulerFibreRange`,
-- `Work.Serre.thomIsoCylFibreRange_of_eulerFibreRange`, `isZero_coh_of_ratAcyclic`, …) were moved
-- to the upstream module `Submission.Work.Serre.EulerFibreRoot`; importing *that* instead of
-- `Submission.Work.Serre.thomIsoCylFibreRange` removes the import edge that made the target of
-- `thomIsoCylFibreRange.lean` unprovable (build cycle).  See
-- `Submission/Work/Serre/TICFR_SESSION_NOTES.md`, FINDING 1.)
import Submission.Work.Serre.EulerFibreRoot
import Submission.Work.Serre.Engine
import Submission.Work.StemsB.SuspensionStepR
import Submission.Work.Cohomology.cupNaturalH

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Bounded form of the Euler-class extraction from the relative (Thom) form of the Gysin theorem:
from a relative class `U` over a fibration `q : C(X,Γ)` whose total space has vanishing rational
cohomology in degrees `≤ N+1`, produce an Euler class on `Γ` whose cup product is an isomorphism in
the range `m + r + 1 ≤ N + 1`. -/
theorem eulerClass_of_thomBdd {Γ X : Type} [TopologicalSpace Γ] [TopologicalSpace X]
    (q : C(X, Γ)) (r N : ℕ) (hr : 1 ≤ r) (hrN : r + 1 ≤ N + 1)
    (hX : ∀ k : ℕ, 0 < k → k ≤ N + 1 →
      CategoryTheory.Limits.IsZero (Work.Thom.Coh ℚ k X))
    (hU : ∃ U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q)),
      ∀ m : ℕ, m + r + 1 ≤ N + 1 → CategoryTheory.IsIso (ModuleCat.ofHom
        (((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl q)) m (r + 1))).flip U ∘ₗ
          (Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ m).hom))) :
    ∃ e : Work.Thom.Coh ℚ (r + 1) Γ, ∀ m : ℕ, m + r + 1 ≤ N + 1 →
      CategoryTheory.IsIso (ModuleCat.ofHom (Work.Serre.cupWith (TopCat.of Γ) (r + 1) e m)) := by
  obtain ⟨U, hU⟩ := hU
  refine ⟨(Work.Thom.CohMap (cylInr q) ℚ (r + 1)).hom
      ((Work.Thom.relToAbs ℚ (Set.range (cylIncl q)) (r + 1)).hom U), fun m hm => ?_⟩
  -- the bounded acyclicity of the bottom copy of the source
  have hA : ∀ k : ℕ, 0 < k → k ≤ N + 1 →
      IsZero (Work.Thom.Coh ℚ k ↥(Set.range (cylIncl q))) := by
    intro k hk hkN
    obtain ⟨φ⟩ := cylHomeo q
    exact isZero_coh_of_homeo φ (hX k hk hkN)
  -- the key identity: `⌣ e` is the composite of the retraction pullback, the cup with `U`, the
  -- forgetful map and the pullback along `cylInr q`
  have hkey : (cupWith (TopCat.of Γ) (r + 1)
        ((Work.Thom.CohMap (cylInr q) ℚ (r + 1)).hom
          ((Work.Thom.relToAbs ℚ (Set.range (cylIncl q)) (r + 1)).hom U)) m) =
      ((Work.Thom.CohMap (cylInr q) ℚ (m + (r + 1))).hom).comp
        (((Work.Thom.relToAbs ℚ (Set.range (cylIncl q)) (m + (r + 1))).hom).comp
          (((Work.Thom.mixedCupC ℚ (Set.range (cylIncl q)) m (r + 1))).flip U ∘ₗ
            (Work.Thom.CohMap (cylRetract q) ℚ m).hom)) := by
    ext x
    change Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of Γ)) m (r + 1) x
        ((Work.Thom.CohMap (cylInr q) ℚ (r + 1)).hom
          ((Work.Thom.relToAbs ℚ (Set.range (cylIncl q)) (r + 1)).hom U)) =
      (Work.Thom.CohMap (cylInr q) ℚ (m + (r + 1))).hom
        ((Work.Thom.relToAbs ℚ (Set.range (cylIncl q)) (m + (r + 1))).hom
          ((Work.Thom.mixedCupC ℚ (Set.range (cylIncl q)) m (r + 1))
            ((Work.Thom.CohMap (cylRetract q) ℚ m).hom x) U))
    rw [Work.StemsB.mixedCup_relToAbs_R ℚ (Set.range (cylIncl q)) m (r + 1)
      ((Work.Thom.CohMap (cylRetract q) ℚ m).hom x) U]
    rw [Work.Cohomology.cupNaturalH ℚ (TopCat.ofHom (cylInr q)) m (r + 1)
      ((Work.Thom.CohMap (cylRetract q) ℚ m).hom x)
      ((Work.Thom.relToAbs ℚ (Set.range (cylIncl q)) (r + 1)).hom U)]
    rw [cohMap_cylInr_cylRetract q m x]
  have hbijF : Function.Bijective (((Work.Thom.mixedCupC ℚ (Set.range (cylIncl q)) m
      (r + 1))).flip U ∘ₗ (Work.Thom.CohMap (cylRetract q) ℚ m).hom) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective
      (ModuleCat.ofHom (((Work.Thom.mixedCupC ℚ (Set.range (cylIncl q)) m (r + 1))).flip U ∘ₗ
        (Work.Thom.CohMap (cylRetract q) ℚ m).hom))).mp (hU m hm)
  have hbijInr : Function.Bijective (Work.Thom.CohMap (cylInr q) ℚ (m + (r + 1))).hom :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective
      (Work.Thom.CohMap (cylInr q) ℚ (m + (r + 1)))).mp (isIso_cohMap_cylInr q (m + (r + 1)))
  have hbijRel : Function.Bijective
      ((Work.Thom.relToAbs ℚ (Set.range (cylIncl q)) (m + (r + 1))).hom) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective
      (Work.Thom.relToAbs ℚ (Set.range (cylIncl q)) (m + (r + 1)))).mp
        (isIso_relToAbs_succ (Set.range (cylIncl q)) (m + r) (by omega)
          (hA (m + r) (by omega) (by omega)) (hA (m + r + 1) (by omega) (by omega)))
  have hbij : Function.Bijective (cupWith (TopCat.of Γ) (r + 1)
      ((Work.Thom.CohMap (cylInr q) ℚ (r + 1)).hom
        ((Work.Thom.relToAbs ℚ (Set.range (cylIncl q)) (r + 1)).hom U)) m) := by
    rw [hkey]
    exact hbijInr.comp (hbijRel.comp hbijF)
  exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective
    (ModuleCat.ofHom (cupWith (TopCat.of Γ) (r + 1)
      ((Work.Thom.CohMap (cylInr q) ℚ (r + 1)).hom
        ((Work.Thom.relToAbs ℚ (Set.range (cylIncl q)) (r + 1)).hom U)) m))).mpr hbij

end

end Work.Serre
