import Mathlib
import Submission.Work.ThomBordism.Grassmann.SphereCover
import Submission.Work.ThomBordism.Grassmann.UpSetRetract
import Submission.Work.ThomBordism.Grassmann.IncidenceTriv
import Submission.Work.ThomBordism.Grassmann.IncidenceAnnulus
import Submission.Work.Cohomology.sphereBandHomotopyEquiv
import Submission.Work.Cohomology.punctured_homotopyEquiv_sphere
import Submission.Work.Cohomology.SphDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The band parameter space and its cohomology

`bandStd (k+m-1)` is the equatorial band `{|x_last| < 1/2}` of the unit sphere of
`Amb ((k+m-1)+1)` (a space equal to `Amb (k+m)` up to the arithmetic identity `(k+m-1)+1 = k+m`).
It is the parameter space of the trivialisation of the band of the incidence fibration.

This module records (i) the homotopy equivalence `bandStd (k+m-1) ≃ Punc (k+m-1)` (band ≃
equator ≃ punctured space, the first from `Work.Cohomology.sphereBandHomotopyEquiv`, the second
from `Work.Cohomology.punctured_homotopyEquiv_sphere`), and (ii) the resulting fact that the
first projection of `fibreVec × bandStd (k+m-1)` is a cohomology isomorphism in degrees
`j + 2 ≤ k + m - 1`.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial Topology

namespace Work.ThomBordism.Grassmann

noncomputable section

open Work.Cohomology

/-- The standard equatorial band of the unit sphere of `Amb (r+1)`, as a set. -/
abbrev bandStd (r : ℕ) : Set (Amb (r+1)) :=
  {x | ‖x‖ = 1 ∧ x (Fin.last r) > -(1/2) ∧ x (Fin.last r) < 1/2}

/-- **The band of the sphere is homotopy equivalent to the punctured space.** -/
theorem nonempty_homotopyEquiv_band_punc (r : ℕ) (hr : 1 ≤ r) :
    Nonempty (ContinuousMap.HomotopyEquiv ↥(bandStd r) ↥(puncSet r)) := by
  obtain ⟨e₁⟩ := Work.Cohomology.sphereBandHomotopyEquiv r hr
  obtain ⟨e₂⟩ := Work.Cohomology.punctured_homotopyEquiv_sphere (EuclideanSpace ℝ (Fin r))
  have hset : Metric.sphere (0 : EuclideanSpace ℝ (Fin r)) 1 = sphSet r := by
    ext y
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    rfl
  exact ⟨e₁.trans (((Homeomorph.setCongr hset).symm).toHomotopyEquiv.trans e₂.symm)⟩

/-- **The projection `fibreVec × bandStd (k+m-1) → fibreVec` is bijective on cohomology** in
degrees `j + 2 ≤ k + m - 1`. -/
theorem bandProjection_bijective (k m j : ℕ) (hk : 1 ≤ k) (hj : j + 2 ≤ k + m - 1) :
    Function.Bijective ((Work.Cohomology.singularCohomologyMap ℤ
      (TopCat.of (↥(fibreVec k m) × ↥(bandStd (k + m - 1))))
      (TopCat.of ↥(fibreVec k m))
      (TopCat.ofHom ⟨fun p => p.1, continuous_fst⟩) j).hom) := by
  have hr : 1 ≤ k + m - 1 := by omega
  obtain ⟨e⟩ := nonempty_homotopyEquiv_band_punc (k + m - 1) hr
  let eP : ContinuousMap.HomotopyEquiv (↥(fibreVec k m) × ↥(bandStd (k + m - 1)))
      (↥(fibreVec k m) × ↥(puncSet (k + m - 1))) :=
    ContinuousMap.HomotopyEquiv.prodCongr (ContinuousMap.HomotopyEquiv.refl _) e
  let fC := eP.toFun
  let pfC : C(↥(fibreVec k m) × ↥(puncSet (k + m - 1)), ↥(fibreVec k m)) :=
    ⟨fun p => p.1, continuous_fst⟩
  let paC : C(↥(fibreVec k m) × ↥(bandStd (k + m - 1)), ↥(fibreVec k m)) :=
    ⟨fun p => p.1, continuous_fst⟩
  let f : TopCat.of (↥(fibreVec k m) × ↥(bandStd (k + m - 1))) ⟶
      TopCat.of (↥(fibreVec k m) × ↥(puncSet (k + m - 1))) := TopCat.ofHom fC
  let g : TopCat.of (↥(fibreVec k m) × ↥(puncSet (k + m - 1))) ⟶
      TopCat.of (↥(fibreVec k m) × ↥(bandStd (k + m - 1))) := TopCat.ofHom eP.invFun
  have h1 : TopCat.Homotopy (f ≫ g) (𝟙 _) := eP.left_inv.some
  have h2 : TopCat.Homotopy (g ≫ f) (𝟙 _) := eP.right_inv.some
  have hiso : IsIso (Work.Cohomology.singularCohomologyMap ℤ
      (TopCat.of (↥(fibreVec k m) × ↥(bandStd (k + m - 1))))
      (TopCat.of (↥(fibreVec k m) × ↥(puncSet (k + m - 1)))) f j) :=
    Work.Cohomology.homotopyEquiv ℤ _ _ f g h1 h2 j
  have hf : Function.Bijective ((Work.Cohomology.singularCohomologyMap ℤ
      (TopCat.of (↥(fibreVec k m) × ↥(bandStd (k + m - 1))))
      (TopCat.of (↥(fibreVec k m) × ↥(puncSet (k + m - 1)))) f j).hom) :=
    bijective_of_isIso_moduleCat _
  have hfun : paC = pfC.comp fC := by
    apply ContinuousMap.ext
    intro p
    rfl
  have hcomp : (Work.Cohomology.singularCohomologyMap ℤ
        (TopCat.of (↥(fibreVec k m) × ↥(bandStd (k + m - 1))))
        (TopCat.of ↥(fibreVec k m)) (TopCat.ofHom paC) j)
      = (Work.Cohomology.singularCohomologyMap ℤ
          (TopCat.of (↥(fibreVec k m) × ↥(puncSet (k + m - 1)))) (TopCat.of ↥(fibreVec k m))
          (TopCat.ofHom pfC) j) ≫ (Work.Cohomology.singularCohomologyMap ℤ
        (TopCat.of (↥(fibreVec k m) × ↥(bandStd (k + m - 1))))
        (TopCat.of (↥(fibreVec k m) × ↥(puncSet (k + m - 1)))) f j) := by
    rw [show TopCat.ofHom paC = f ≫ TopCat.ofHom pfC from by
      change TopCat.ofHom paC = TopCat.ofHom (pfC.comp fC)
      rw [hfun]]
    exact Work.Cohomology.singularCohomologyMap_comp (R := ℤ) f (TopCat.ofHom pfC) j
  have hpf : Function.Bijective ((Work.Cohomology.singularCohomologyMap ℤ
      (TopCat.of (↥(fibreVec k m) × ↥(puncSet (k + m - 1)))) (TopCat.of ↥(fibreVec k m))
      (TopCat.ofHom pfC) j).hom) := by
    show Function.Bijective ((Work.Cohomology.singularCohomologyMap ℤ
      (TopCat.of (↥(fibreVec k m) × {v : EuclideanSpace ℝ (Fin (k + m - 1)) // v ≠ 0}))
      (TopCat.of ↥(fibreVec k m))
      (TopCat.ofHom ⟨fun p => p.1, continuous_fst⟩) j).hom)
    exact trivPuncturedCohomology (k + m - 1) j hj ↥(fibreVec k m)
  show Function.Bijective ((Work.Cohomology.singularCohomologyMap ℤ
    (TopCat.of (↥(fibreVec k m) × ↥(bandStd (k + m - 1))))
    (TopCat.of ↥(fibreVec k m)) (TopCat.ofHom paC) j).hom)
  rw [hcomp, ModuleCat.hom_comp]
  exact ⟨fun x y hxy => hpf.1 (hf.1 hxy), fun z => by
    obtain ⟨w, hw⟩ := hf.2 z
    obtain ⟨v, hv⟩ := hpf.2 w
    exact ⟨v, by rw [LinearMap.comp_apply, hv, hw]⟩⟩

end

end Work.ThomBordism.Grassmann
