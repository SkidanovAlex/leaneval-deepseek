import Submission.Work.StemsB.SerreSphereAssembly
import Submission.Work.StemsB.FibreTransport

set_option synthInstance.maxHeartbeats 400000

/-!
# The Serre exact sequence over a sphere, with the fibre data at the base point

`Work.StemsB.serreExactSphere_of_fibrewiseTrivial` takes the fibre data at a point `d₀` of the inner
cube and concludes a statement about `p⁻¹∞`.  This file removes that discrepancy, using
`Work.StemsB.nonempty_homology_fibre_iso` (the fibre homology of a Hurewicz fibration does not depend
on the point of the base along a path) and the fact that `SphModel b` is path connected for
`b ≥ 1`: the fibre conditions at `∞` transfer to `d₀`, and the theorem applies.

This is the form that matches `Work.StemsB.SerreExactSphere` in `SerreExact.lean`.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace Work.StemsB

noncomputable section

/-- **`SphModel b` is path connected for `b ≥ 1`**: any point is joined to `∞`. -/
theorem joined_infty_SphModel (b : ℕ) (hb : 1 ≤ b) (y : SphModel b) :
    Joined OnePoint.infty y := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (b + 1))) := by
    rw [← Module.finrank_eq_rank]
    simp
    omega
  haveI : PathConnectedSpace ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (b + 1))) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere hrank 0 (by norm_num))
  let e : SphModel b ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (b + 1))) 1 :=
    onePointEquivSphereOfFinrankEq (V := EuclideanSpace ℝ (Fin b)) (ι := Fin (b + 1)) (by simp)
  obtain ⟨P⟩ := PathConnectedSpace.joined (e OnePoint.infty) (e y)
  have hP : Path (e.symm (e OnePoint.infty)) (e.symm (e y)) := P.map e.symm.continuous
  rw [e.symm_apply_apply, e.symm_apply_apply] at hP
  exact ⟨hP⟩

/-- **The Serre exact sequence over a sphere, with the fibre data at the base point `∞`.**

Let `p : E → Sᵇ` be a Hurewicz fibration, fibrewise trivial over the inner cube with fibre over some
point `d₀` of the cube, and let the fibre over `∞` be path connected with vanishing reduced homology
below degree `f`.  Then `H_i(E, p⁻¹∞) → H_i(Sᵇ, {∞})` is an isomorphism for `i < b + f`. -/
theorem serreExactSphere_infty (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hp : IsHurewiczFibration p) (d₀ : ↥(sphLoopBig b)) (f : ℕ)
    (hT : FibrewiseTrivial p (sphLoopBig b) d₀)
    (eInf : E) (heInf : p eInf = OnePoint.infty)
    (hconn : Subsingleton (HomotopyGroup (Fin 0) (↥(p ⁻¹' {OnePoint.infty})) ⟨eInf, heInf⟩))
    (hH : ∀ j : ℕ, 0 < j → j < f →
      IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(p ⁻¹' {OnePoint.infty}))).homology j))
    (i : ℕ) (hi : i < b + f) :
    IsIso (HomologicalComplex.homologyMap (relPairMap p OnePoint.infty) i) := by
  -- a path from `∞` to `d₀.1`
  obtain ⟨P⟩ := joined_infty_SphModel b hb d₀.1
  let γ : C(unitInterval, SphModel b) := P.toContinuousMap
  have h0 : γ 0 = OnePoint.infty := P.source
  have h1 : γ 1 = d₀.1 := P.target
  -- `H₀` of the fibre over `∞` is `ℤ`
  have hmem : eInf ∈ p ⁻¹' {OnePoint.infty} := Set.mem_singleton_iff.mpr heInf
  haveI hPC : PathConnectedSpace ↥(p ⁻¹' {OnePoint.infty}) :=
    pathConnectedSpace_of_subsingleton_pi0 ⟨eInf, hmem⟩ hconn
  have hH0 : Nonempty (((Work.Cohomology.singularChains ℤ
      (TopCat.of ↥(p ⁻¹' {OnePoint.infty}))).homology 0) ≃ₗ[ℤ] ℤ) := by
    haveI hε : IsIso (TopCat.singularHomology₀ε (TopCat.of ↥(p ⁻¹' {OnePoint.infty}))
        (ModuleCat.of ℤ ℤ)) := inferInstance
    exact ⟨Work.Cohomology.uctIsoToLinearEquiv
      (asIso (TopCat.singularHomology₀ε (TopCat.of ↥(p ⁻¹' {OnePoint.infty}))
        (ModuleCat.of ℤ ℤ)))⟩
  -- transfer the fibre conditions to `d₀`
  have hγ0 : p ⁻¹' {γ 0} = p ⁻¹' {OnePoint.infty} := by rw [h0]
  have hγ1 : p ⁻¹' {γ 1} = p ⁻¹' {d₀.1} := by rw [h1]
  have hH' : ∀ j : ℕ, 0 < j → j < f →
      IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(p ⁻¹' {γ 0}))).homology j) := by
    intro j hj hjf
    rw [hγ0]
    exact hH j hj hjf
  have hHd : ∀ j : ℕ, 0 < j → j < f →
      IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(p ⁻¹' {d₀.1}))).homology j) := by
    intro j hj hjf
    have h := (isZero_homology_fibre_of_path p hp γ j).mp (hH' j hj hjf)
    rwa [hγ1] at h
  have hH0' : Nonempty (((Work.Cohomology.singularChains ℤ
      (TopCat.of ↥(p ⁻¹' {γ 0}))).homology 0) ≃ₗ[ℤ] ℤ) := by
    rw [hγ0]
    exact hH0
  have hH0d : Nonempty (((Work.Cohomology.singularChains ℤ
      (TopCat.of ↥(p ⁻¹' {d₀.1}))).homology 0) ≃ₗ[ℤ] ℤ) := by
    have h := nonempty_homologyZero_fibre_linEquiv p hp γ hH0'
    rwa [hγ1] at h
  -- a point of the fibre over `d₀.1`, transported along the path
  have hmemγ : eInf ∈ p ⁻¹' {γ 0} := by rw [hγ0]; exact hmem
  have hy₀ : Nonempty ↥(p ⁻¹' {d₀.1}) :=
    ⟨by
      have h := fibreOneHom p γ (poG p hp γ (fibreZeroHomInv p γ ⟨eInf, hmemγ⟩).1)
      rw [hγ1] at h
      exact h⟩
  exact serreExactSphere_of_fibrewiseTrivial_hH0 b hb E p hp d₀ f hT hy₀.some hH0d hHd i hi

end

end Work.StemsB
