import Mathlib
import Submission.Work.ThomBordism.Grassmann.sumPiecesSetup
import Submission.Work.ThomBordism.Grassmann.sumPiecesCont
import Submission.Work.ThomBordism.Grassmann.sumPiecesHomeo
import Submission.Work.ThomBordism.Grassmann.sumPiecesHomotopy
import Submission.Work.Thom.thomClassOf
import Submission.Work.Thom.bijective_proj_zeroComplement_gen
import Submission.Work.LerayHirsch.nonempty_homeo_projSpace_bundleComap_subtype

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The vanishing of the cohomology of the intersection of the two pieces

For complex bundles `A` (rank `a`) and `C` (rank `b ≥ 1`) over `B`, the intersection of the two
pieces is the zero complement of the pullback `sumZ A C` of the realification of `C` to the
punctured total space of the realification of `A`, a real bundle of rank `2 * b`.  This module
proves

  `subsingleton_Coh_interPieces` :
    `Subsingleton (Coh ℤ (m - 1) ↥(pieceFst A C ∩ pieceSnd A C))`

from `Subsingleton (Coh ℤ (m - 1) ↥(sumBaseA A))` and
`Subsingleton (Coh ℤ (m - 2 * b) ↥(sumBaseA A))`.

The route is the long exact sequence of the pair `(E, E∖0)` of the pullback bundle
(`Work.Thom.pairRange_eq_ker₃`): its relative groups are `0` in degrees `≤ 2 * b` (the low-degree
vanishing `Work.Thom.subsingleton_OpenThom_genFibre`, together with the Thom isomorphism
`Work.Thom.ThomClass.thomEquiv` of the pullback, whose Thom class is
`Work.Thom.thomClassOf`), and the absolute group `H^{m-1}(E)` is that of the base `sumBaseA A`
(the bundle projection is a homotopy equivalence, `Work.Thom.bijective_CohMap_bundleProj`).
-/

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {a b : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]

/-- **The cohomology of the zero complement of the pullback `sumZ A C` vanishes in degree
`m - 1`.** -/
theorem subsingleton_Coh_zeroComplement_sumZ
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) (m : ℕ) (hb : 1 ≤ b)
    (h₁ : Subsingleton (Work.Thom.Coh ℤ (m - 1) ↥(sumBaseA A)))
    (h₂ : Subsingleton (Work.Thom.Coh ℤ (m - 2 * b) ↥(sumBaseA A))) :
    Subsingleton (Work.Thom.Coh ℤ (m - 1)
      ↥(Work.Thom.zeroComplement (sumZ A C))) := by
  haveI hE : Subsingleton (Work.Thom.Coh ℤ (m - 1) (sumZ A C).TotalSpace) := by
    have hbij := Work.Thom.bijective_CohMap_bundleProj (sumZ A C) (m - 1)
    exact ⟨fun x y => by
      obtain ⟨x', rfl⟩ := hbij.2 x
      obtain ⟨y', rfl⟩ := hbij.2 y
      rw [h₁.elim x' y']⟩
  haveI hO : Subsingleton (Work.Thom.OpenThom (sumZ A C) ((m - 1) + 1)) := by
    by_cases hlt : (m - 1) + 1 < 2 * b
    · refine Work.Thom.subsingleton_OpenThom_genFibre (sumZ A C) ((m - 1) + 1) ?_
      rw [Work.Thom.finrank_real_euclidean_complex]
      exact hlt
    · push_neg at hlt
      have hTthom : Work.Thom.ThomClass (sumZ A C) (2 * b) :=
        Work.Thom.thomClassOf (m := b) hb (sumZc A C)
      have hgoal : ((m - 1) + 1 - 2 * b) + 2 * b = (m - 1) + 1 := by omega
      have hdeg : (m - 1) + 1 - 2 * b = m - 2 * b := by omega
      haveI hsub2 : Subsingleton (Work.Thom.Coh ℤ ((m - 1) + 1 - 2 * b) ↥(sumBaseA A)) :=
        hdeg ▸ h₂
      haveI hsub : Subsingleton (Work.Thom.OpenThom (sumZ A C)
          (((m - 1) + 1 - 2 * b) + 2 * b)) :=
        Function.Surjective.subsingleton (hTthom.thomEquiv ((m - 1) + 1 - 2 * b)).surjective
      rw [hgoal] at hsub
      exact hsub
  have hinj : Function.Injective
      (Work.Thom.pairδC (Work.Thom.zeroComplement (sumZ A C)) (m - 1)).hom := by
    rw [← LinearMap.ker_eq_bot]
    rw [← Work.Thom.pairRange_eq_ker₃ (Work.Thom.zeroComplement (sumZ A C)) (m - 1)]
    rw [LinearMap.range_eq_bot]
    ext x
    calc (Work.Thom.restrCoh (Work.Thom.zeroComplement (sumZ A C)) ℤ (m - 1)).hom x
        = (Work.Thom.restrCoh (Work.Thom.zeroComplement (sumZ A C)) ℤ (m - 1)).hom 0 := by
          rw [Subsingleton.elim x 0]
      _ = 0 := map_zero _
  exact ⟨fun x y => hinj (Subsingleton.elim _ _)⟩

/-- **The cohomology of the intersection of the two pieces vanishes in degree `m - 1`.** -/
theorem subsingleton_Coh_interPieces
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) (m : ℕ) (hb : 1 ≤ b)
    (h₁ : Subsingleton (Work.Thom.Coh ℤ (m - 1) ↥(sumBaseA A)))
    (h₂ : Subsingleton (Work.Thom.Coh ℤ (m - 2 * b) ↥(sumBaseA A))) :
    Subsingleton (Work.Thom.Coh ℤ (m - 1) ↥(pieceFst A C ∩ pieceSnd A C)) := by
  have hs := subsingleton_Coh_zeroComplement_sumZ A C m hb h₁ h₂
  obtain ⟨iso⟩ :=
    Work.Cohomology.cohomologyIso_of_homotopyEquiv (sumUVHomeo A C).toHomotopyEquiv (m - 1)
  exact Work.Cohomology.subsingleton_of_iso iso hs

end

end Work.ThomBordism.Grassmann
