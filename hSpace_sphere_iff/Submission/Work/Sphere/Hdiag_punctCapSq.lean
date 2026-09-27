/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: hSpace_sphere_iff team

# `H^{n+1}` of the punctured square of caps vanishes

`Work.Sphere.punctCapSq n` is the open square `capMinus n × capMinus n` of the two caps of
`Sⁿ⁺¹` with the point `(polePt, polePt)` removed.  Since `capMinus n` is an open cap of the
sphere, it is homeomorphic to `ℝ^{n+1}` (stereographic projection), so `punctCapSq n` is
homeomorphic to `ℝ^{2n+2}` with a point removed, which in turn is homeomorphic to
`S^{2n+1} × (0, ∞)` (polar coordinates, `homeomorphUnitSphereProd`) and hence homotopy equivalent
to `S^{2n+1}`.  Since `n + 1 ≠ 2n + 1` for `n ≥ 1`, the cohomology in degree `n+1` vanishes
(`Work.Sphere.sphere_subsingleton`).

The two geometric inputs are factored out:

* `Work.Sphere.capMinus_homeo_Euclid` (file `Sphere/capMinus_homeo_Euclid.lean`): the cap is
  homeomorphic to `ℝ^{n+1}`;
* `Work.Sphere.punctedProd_homeo` (file `Sphere/punctedProd_homeo.lean`): a punctured product of
  two Euclidean spaces is homeomorphic to a punctured Euclidean space of the sum of the
  dimensions.
-/
import Mathlib
import Submission.Work.Sphere.HdiagBase
import Submission.Work.Sphere.ProdSetup
import Submission.Work.Sphere.ProdRec
import Submission.Work.Sphere.Values
import Submission.Work.Sphere.capMinus_homeo_Euclid
import Submission.Work.Sphere.punctedProd_homeo

namespace Work.Sphere

open CategoryTheory Simplicial Opposite
open Submission.Cohomology

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-! ## Plumbing for punctured spaces -/

/-- A homeomorphism restricts to the complements of a point. -/
def restrictPunct {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) : ({x}ᶜ : Set X) ≃ₜ ({e x}ᶜ : Set Y) where
  toFun y := ⟨e y.1, fun h => y.2 (e.injective h)⟩
  invFun y := ⟨e.symm y.1, fun h => y.2 ((e.apply_symm_apply y.1).symm.trans (congrArg e h))⟩
  left_inv y := by ext; exact e.symm_apply_apply y.1
  right_inv y := by ext; exact e.apply_symm_apply y.1
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The subtype `{x // x ≠ z ∧ x ∈ s}` is the complement of `z` inside `↥s`. -/
def punctedSubtype {Z : Type*} [TopologicalSpace Z] (s : Set Z) (z : Z) (hz : z ∈ s) :
    {x : Z // x ≠ z ∧ x ∈ s} ≃ₜ ({⟨z, hz⟩}ᶜ : Set ↥s) where
  toFun x := ⟨⟨x.1, x.2.2⟩, fun h => x.2.1 (Subtype.ext_iff.mp h)⟩
  invFun y := ⟨y.1.1, ⟨fun h => y.2 (Subtype.ext h), y.1.2⟩⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The pole, as a point of the negative cap. -/
def capPole (n : ℕ) : ↥(Submission.Sphere.capMinus n) :=
  ⟨Submission.Sphere.polePt (n+1), by
    rw [Submission.Sphere.capMinus_eq]
    exact Submission.Sphere.polePt_ne_negPolePt (n+1)⟩

/-! ## The rational cohomology of a punctured Euclidean space -/

/-- **`H^k(ℝ^m ∖ {0}) = 0` away from the top degree `m-1`.**  Indeed `ℝ^m ∖ {0}` is
homeomorphic to `S^{m-1} × (0,∞)` (`homeomorphUnitSphereProd`), and a product with the
contractible factor `(0,∞)` is homotopy equivalent to `S^{m-1}`, whose cohomology vanishes in
degree `k` when `0 < k ≠ m - 1`. -/
theorem subsingleton_H_punctEuclid (m k : ℕ) (hm : 1 ≤ m) (hk : 0 < k) (hkm : k ≠ m - 1) :
    Subsingleton (H
      (TopCat.toSSet.obj (TopCat.of ({0}ᶜ : Set (EuclideanSpace ℝ (Fin m))))) ℚ k) := by
  haveI : ContractibleSpace ↥(Set.Ioi (0:ℝ)) :=
    (convex_Ioi 0).contractibleSpace Set.nonempty_Ioi
  have hsphere : Subsingleton (H (TopCat.toSSet.obj
      (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1))) ℚ k) := by
    rw [show m = (m-1)+1 from (Nat.sub_add_cancel hm).symm]
    exact sphere_subsingleton (m-1) k hk hkm
  obtain ⟨e₁⟩ := H_iso_of_homeo (A := TopCat.of ({0}ᶜ : Set (EuclideanSpace ℝ (Fin m))))
    (B := TopCat.of (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) × ↥(Set.Ioi (0:ℝ))))
    (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin m))) k
  obtain ⟨e₂⟩ := H_iso_of_homeo
    (A := TopCat.of (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) × ↥(Set.Ioi (0:ℝ))))
    (B := TopCat.of (↥(Set.Ioi (0:ℝ)) × ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1)))
    (Homeomorph.prodComm (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1))
      (↥(Set.Ioi (0:ℝ)))) k
  obtain ⟨e₃⟩ := H_contractible_prod_iso
    (A := TopCat.of ↥(Set.Ioi (0:ℝ)))
    (B := TopCat.of ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1)) k
  exact subsingleton_of_linearEquiv (e₁.trans (e₂.trans e₃)) hsphere

/-! ## The punctured cap square -/

/-- `punctCapSq n` is homeomorphic to `ℝ^{2n+2} ∖ {0}`: apply the stereographic chart
`capMinus_homeo_Euclid` to both coordinates, then concatenate the two Euclidean coordinates
(`punctedProd_homeo`). -/
theorem punctCapSq_homeo_punctEuclid (n : ℕ) :
    Nonempty (↥(Work.Sphere.punctCapSq n) ≃ₜ
      ↥({0}ᶜ : Set (EuclideanSpace ℝ (Fin ((n+1) + (n+1)))))) := by
  obtain ⟨φ⟩ := capMinus_homeo_Euclid n
  obtain ⟨ψ⟩ := punctedProd_homeo (n+1) (n+1) (φ (capPole n), φ (capPole n))
  -- `punctCapSq n` is the complement of the pole in the square of the cap, ...
  have hA : Nonempty (↥(Work.Sphere.punctCapSq n) ≃ₜ
      ↥({(capPole n, capPole n)}ᶜ :
        Set (↥(Submission.Sphere.capMinus n) × ↥(Submission.Sphere.capMinus n)))) :=
    ⟨(punctedSubtype (Submission.Sphere.capMinus n ×ˢ Submission.Sphere.capMinus n)
        (Submission.Sphere.polePt (n+1), Submission.Sphere.polePt (n+1))
        ⟨(capPole n).2, (capPole n).2⟩).trans
      (restrictPunct (Homeomorph.Set.prod (Submission.Sphere.capMinus n)
        (Submission.Sphere.capMinus n)) _)⟩
  obtain ⟨eA⟩ := hA
  -- ... the chart identifies it with the complement of a point of `ℝ^{n+1} × ℝ^{n+1}`, and the
  -- concatenation identifies that with the complement of `0` in `ℝ^{2n+2}`.
  exact ⟨eA.trans ((restrictPunct (φ.prodCongr φ) (capPole n, capPole n)).trans ψ)⟩

/-! ## The target -/

theorem Hdiag_punctCapSq (n : ℕ) (hn : 1 ≤ n) :
    Subsingleton (Submission.Cohomology.H
      (TopCat.toSSet.obj (Work.Sphere.punctCapSq n)) ℚ (n+1)) := by
  obtain ⟨e⟩ := punctCapSq_homeo_punctEuclid n
  refine subsingleton_of_linearEquiv (Classical.choice (H_iso_of_homeo
    (A := TopCat.of (Work.Sphere.punctCapSq n))
    (B := TopCat.of ({0}ᶜ : Set (EuclideanSpace ℝ (Fin ((n+1)+(n+1)))))) e (n+1))) ?_
  exact subsingleton_H_punctEuclid ((n+1)+(n+1)) (n+1) (by omega) (by omega) (by omega)

end

end Work.Sphere
