import Submission.Work.EvenBound.Imports

/-!
# At the closest cut point there are exactly two minimising directions

Xu's Theorem B (`Submission.XuTrap.xuCornerExcluded`) asserts that two distinct minimising geodesics
from `p` to its closest cut point `q` arrive at `q` with **opposite** velocities.  This module draws
the classical consequence used by the even-dimensional Klingenberg argument: there are **at most
two** unit directions at `p` whose ray of length `m` ends at `q` — and they are `±ξ`.

The proof is a two-line linear-algebra argument once Xu is available for two pairs sharing the first
ray `ξ` (the non-conjugacy hypothesis of Xu concerns the *first* ray, which is why `ξ` is kept
first): if `w ≠ ξ` also satisfies `GExp p (m • w) = q`, then its ray is automatically minimising at
`m` (its endpoint is at distance `m = ‖m • w‖`), so Xu applied to `(ξ, w)` gives
`ρ'(m) = -α'(m)`, while Xu applied to `(ξ, η)` gives `β'(m) = -α'(m)`; hence `ρ'(m) = β'(m)`, so the
rays `s ↦ GExp p ((m + s) • w)` and `s ↦ GExp p ((m + s) • η)` are geodesics with the same initial
data at `s = 0`; by `Submission.KlingenbergEven.curveVelocity_eq_of_isGeodesicAt_eq` their velocities
agree at every parameter, and evaluating at `s = -m` gives `w = η`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.JacobiGlobal
open Submission.Length
open Submission.InjRadius
open Submission.InjSup
open Submission.CurvatureVec
open Submission.GeodesicSpeed

namespace Work.EvenBound.OnlyTwo

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **At most two minimising directions at the closest cut point.**  Let `m` be a maximal injectivity
radius at `p`, `ξ ≠ η` unit directions whose rays meet at time `m`, both minimising there, and
suppose `p` is not conjugate to the meeting point along the `ξ`-ray.  Then a third unit direction `w`
whose ray also meets them at time `m` must be one of `ξ`, `η`. -/
theorem eq_or_eq_of_two_minimising_of_xu
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {m : ℝ} (hm : 0 < m)
    (hinj : Submission.InjRadius.InjAtLeast hmet p m)
    (hmax : ∀ r : ℝ, m < r → ¬ Submission.InjRadius.InjAtLeast hmet p r)
    {ξ η w : TangentSpace I p} (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) (hw : ‖w‖ = 1)
    (hξη : ξ ≠ η)
    (hmeet : GExp (cov := cov) hmet p (m • ξ) = GExp (cov := cov) hmet p (m • η))
    (hminξ : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (m • ξ))
      = ENNReal.ofReal m)
    (hnc : ¬ Submission.ConjRadius.IsConjugateTime cov
      (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m)
    (hwmeet : GExp (cov := cov) hmet p (m • w) = GExp (cov := cov) hmet p (m • ξ)) :
    w = ξ ∨ w = η := by
  classical
  by_cases hwξ : w = ξ
  · exact Or.inl hwξ
  refine Or.inr ?_
  have hwne : w ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hw
    norm_num at hw
  have hξne : ξ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hξ
    norm_num at hξ
  have hηne : η ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hη
    norm_num at hη
  have hminη : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (m • η))
      = ENNReal.ofReal m := by rw [← hmeet]; exact hminξ
  have hminw : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (m • w))
      = ENNReal.ofReal m := by rw [hwmeet]; exact hminξ
  have hXu := Submission.XuTrap.xuCornerExcluded (cov := cov) hmet htor
  -- Xu for the pair `(ξ, η)`
  have hA : curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m
      = -curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) m :=
    hXu p hm hinj hmax ξ η hξ hη hξη hminξ hminη hmeet hnc
  -- Xu for the pair `(ξ, w)`
  have hB : curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m
      = -curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • w)) m :=
    hXu p hm hinj hmax ξ w hξ hw (fun h => hwξ h.symm) hminξ hminw hwmeet.symm hnc
  -- hence the two velocities at the meeting point agree
  have hC : curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • w)) m
      = curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) m := by
    rw [hA] at hB
    exact neg_injective hB.symm
  -- the shifted rays
  set σ : ℝ → M := fun s : ℝ => GExp (cov := cov) hmet p ((1 * s + m) • w) with hσdef
  set τ : ℝ → M := fun s : ℝ => GExp (cov := cov) hmet p ((1 * s + m) • η) with hτdef
  have hσsm : ContMDiff 𝓘(ℝ) I ∞ σ := by
    rw [hσdef]
    exact (Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hwne).comp
      (f := fun t : ℝ => 1 * t + m)
      (((contMDiff_const (I := 𝓘(ℝ)).mul contMDiff_id).add contMDiff_const))
  have hτsm : ContMDiff 𝓘(ℝ) I ∞ τ := by
    rw [hτdef]
    exact (Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hηne).comp
      (f := fun t : ℝ => 1 * t + m)
      (((contMDiff_const (I := 𝓘(ℝ)).mul contMDiff_id).add contMDiff_const))
  have hσgeo : ∀ s : ℝ, IsGeodesicAt cov σ s := by
    intro s
    rw [hσdef]
    have h := Submission.HopfRinow.isGeodesicAt_comp_affine (cov := cov)
      (σ := fun t : ℝ => GExp (cov := cov) hmet p (t • w)) (a := 1) (b := m)
      (c := 1 * s + m - 1) (d := 1 * s + m + 1) one_ne_zero
      ((Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hwne).contMDiffOn.mono
        (Set.subset_univ _))
      (fun y _ => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet p hwne y)
      (r := s) ⟨by linarith, by linarith⟩
    simpa using h
  have hτgeo : ∀ s : ℝ, IsGeodesicAt cov τ s := by
    intro s
    rw [hτdef]
    have h := Submission.HopfRinow.isGeodesicAt_comp_affine (cov := cov)
      (σ := fun t : ℝ => GExp (cov := cov) hmet p (t • η)) (a := 1) (b := m)
      (c := 1 * s + m - 1) (d := 1 * s + m + 1) one_ne_zero
      ((Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hηne).contMDiffOn.mono
        (Set.subset_univ _))
      (fun y _ => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet p hηne y)
      (r := s) ⟨by linarith, by linarith⟩
    simpa using h
  have hσne : ∀ s : ℝ, curveVelocity (I := I) σ s ≠ 0 := by
    intro s h0
    rw [hσdef] at h0
    have hv := Submission.Length.curveVelocity_comp_mul_add (I := I)
      (γ := fun t : ℝ => GExp (cov := cov) hmet p (t • w)) (c := 1) (d := m) (t := s)
      ((Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hwne).contMDiffAt.mdifferentiableAt
        (by simp))
    rw [h0, one_smul] at hv
    exact Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet p hwne (1 * s + m)
      hv.symm
  have hτne : ∀ s : ℝ, curveVelocity (I := I) τ s ≠ 0 := by
    intro s h0
    rw [hτdef] at h0
    have hv := Submission.Length.curveVelocity_comp_mul_add (I := I)
      (γ := fun t : ℝ => GExp (cov := cov) hmet p (t • η)) (c := 1) (d := m) (t := s)
      ((Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hηne).contMDiffAt.mdifferentiableAt
        (by simp))
    rw [h0, one_smul] at hv
    exact Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet p hηne (1 * s + m)
      hv.symm
  have hσ0 : σ 0 = τ 0 := by
    rw [hσdef, hτdef]
    simp only [one_mul, zero_add]
    rw [hwmeet, hmeet]
  have hσvel : curveVelocity (I := I) σ 0
      = curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • w)) m := by
    rw [hσdef]
    have h := Submission.Length.curveVelocity_comp_mul_add (I := I)
      (γ := fun t : ℝ => GExp (cov := cov) hmet p (t • w)) (c := 1) (d := m) (t := (0 : ℝ))
      ((Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hwne).contMDiffAt.mdifferentiableAt
        (by simp))
    rw [one_mul, zero_add, one_smul] at h
    exact h
  have hτvel : curveVelocity (I := I) τ 0
      = curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) m := by
    rw [hτdef]
    have h := Submission.Length.curveVelocity_comp_mul_add (I := I)
      (γ := fun t : ℝ => GExp (cov := cov) hmet p (t • η)) (c := 1) (d := m) (t := (0 : ℝ))
      ((Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hηne).contMDiffAt.mdifferentiableAt
        (by simp))
    rw [one_mul, zero_add, one_smul] at h
    exact h
  have hvel0 : curveVelocity (I := I) σ 0 = curveVelocity (I := I) τ 0 := by
    rw [hσvel, hτvel, hC]
  -- the velocities agree at every parameter
  have hvelall : curveVelocity (I := I) σ (-m) = curveVelocity (I := I) τ (-m) :=
    Submission.KlingenbergEven.curveVelocity_eq_of_isGeodesicAt_eq (cov := cov) hσsm hτsm
      hσgeo hτgeo hσne hτne hσ0 hvel0 (-m)
  -- identify the two sides with `w` and `η`
  have hσend : curveVelocity (I := I) σ (-m) = w := by
    rw [hσdef]
    have h := Submission.Length.curveVelocity_comp_mul_add (I := I)
      (γ := fun t : ℝ => GExp (cov := cov) hmet p (t • w)) (c := 1) (d := m) (t := (-m))
      ((Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hwne).contMDiffAt.mdifferentiableAt
        (by simp))
    rw [show (1 : ℝ) * (-m) + m = 0 from by ring] at h
    rw [h, one_smul, Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet p hwne]
  have hτend : curveVelocity (I := I) τ (-m) = η := by
    rw [hτdef]
    have h := Submission.Length.curveVelocity_comp_mul_add (I := I)
      (γ := fun t : ℝ => GExp (cov := cov) hmet p (t • η)) (c := 1) (d := m) (t := (-m))
      ((Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hηne).contMDiffAt.mdifferentiableAt
        (by simp))
    rw [show (1 : ℝ) * (-m) + m = 0 from by ring] at h
    rw [h, one_smul, Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet p hηne]
  rw [hσend, hτend] at hvelall
  exact hvelall

end

end Work.EvenBound.OnlyTwo
