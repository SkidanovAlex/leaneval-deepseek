import Submission.InjHalf
import Submission.GExpRayZero
import Submission.RayJacobi
import Submission.HopfRinow2

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.HopfRinow
open Submission.InjRadius
open Submission.CutStep2

namespace Submission.XuStep

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The `GExp`-ray agrees with the canonical `geodCurve` on a neighbourhood of the origin.**
Both are smooth geodesics with unit speed and the same initial data `(p, ξ)`, so they agree wherever
both are defined (geodesic uniqueness, `eqOn_Ioo_of_isGeodesicAt_of_eq`). -/
theorem GExp_ray_eqOn_geodCurve (hmet : IsMetricCompatible cov) {p : M} {ξ : TangentSpace I p}
    (hξ : ‖ξ‖ = 1) {m : ℝ} (hm : 0 < m) :
    EqOn (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ))
      (geodCurve (cov := cov) hmet m hm.le p ξ hξ)
      (Ioo (-(geodDelta (cov := cov) hmet)) (m + geodDelta (cov := cov) hmet)) := by
  have hξ0 : ξ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hξ
    norm_num at hξ
  obtain ⟨h0G, hvG, hsmG, hgeoG, hspG⟩ := geodCurve_spec (cov := cov) hmet m hm.le p ξ hξ
  have h0mem : (0 : ℝ) ∈ Ioo (-(geodDelta (cov := cov) hmet)) (m + geodDelta (cov := cov) hmet) :=
    Set.mem_Ioo.mpr ⟨by linarith [geodDelta_pos (cov := cov) hmet],
      by linarith [geodDelta_pos (cov := cov) hmet]⟩
  have hsmγ : ContMDiffOn 𝓘(ℝ) I ∞ (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ))
      (Ioo (-(geodDelta (cov := cov) hmet)) (m + geodDelta (cov := cov) hmet)) :=
    (Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hξ0).mono (Set.subset_univ _)
  have hgeoγ : ∀ t ∈ Ioo (-(geodDelta (cov := cov) hmet)) (m + geodDelta (cov := cov) hmet),
      IsGeodesicAt cov (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) t :=
    fun t _ => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet p hξ0 t
  have hneγ : ∀ t ∈ Ioo (-(geodDelta (cov := cov) hmet)) (m + geodDelta (cov := cov) hmet),
      curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) t ≠ 0 :=
    fun t _ => Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet p hξ0 t
  have hneG : ∀ t ∈ Ioo (-(geodDelta (cov := cov) hmet)) (m + geodDelta (cov := cov) hmet),
      curveVelocity (I := I) (geodCurve (cov := cov) hmet m hm.le p ξ hξ) t ≠ 0 := by
    intro t ht hzero
    have h := hspG t ht
    rw [hzero, norm_zero] at h
    norm_num at h
  exact eqOn_Ioo_of_isGeodesicAt_of_eq (cov := cov) hsmγ hsmG hgeoγ hgeoG hneγ hneG h0mem
    (by rw [zero_smul, GExp_zero, h0G])
    (by rw [Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet p hξ0, hvG])

/-- **Two distinct rays meeting again have distinct velocities at the meeting time.**  This is
geodesic uniqueness in ray form, and it *discharges the non-reversal hypothesis* of the corner bound
for the broken minimising loop of the cut-point step: two minimising geodesics from `p` to `q` cannot
meet tangentially at `q` unless they are the same geodesic. -/
theorem velocity_ne_of_meet (hmet : IsMetricCompatible cov)
    {p : M} {ξ η : TangentSpace I p} (hξ : ξ ≠ 0) (hη : η ≠ 0) {m : ℝ} (hm : 0 < m)
    (hmeet : GExp (cov := cov) hmet p (m • ξ) = GExp (cov := cov) hmet p (m • η)) (hne : ξ ≠ η) :
    curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) m
      ≠ curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) m := by
  intro hvel
  have hδ := geodDelta_pos (cov := cov) hmet
  have hmmem : m ∈ Ioo (-(geodDelta (cov := cov) hmet)) (m + geodDelta (cov := cov) hmet) :=
    Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  have h0mem : (0 : ℝ) ∈ Ioo (-(geodDelta (cov := cov) hmet)) (m + geodDelta (cov := cov) hmet) :=
    Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  have hsm₁ : ContMDiffOn 𝓘(ℝ) I ∞ (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ))
      (Ioo (-(geodDelta (cov := cov) hmet)) (m + geodDelta (cov := cov) hmet)) :=
    (Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hξ).mono (Set.subset_univ _)
  have hsm₂ : ContMDiffOn 𝓘(ℝ) I ∞ (fun t : ℝ => GExp (cov := cov) hmet p (t • η))
      (Ioo (-(geodDelta (cov := cov) hmet)) (m + geodDelta (cov := cov) hmet)) :=
    (Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hη).mono (Set.subset_univ _)
  have hgeo₁ : ∀ t ∈ Ioo (-(geodDelta (cov := cov) hmet)) (m + geodDelta (cov := cov) hmet),
      IsGeodesicAt cov (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) t :=
    fun t _ => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet p hξ t
  have hgeo₂ : ∀ t ∈ Ioo (-(geodDelta (cov := cov) hmet)) (m + geodDelta (cov := cov) hmet),
      IsGeodesicAt cov (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) t :=
    fun t _ => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet p hη t
  have hne₁ : ∀ t ∈ Ioo (-(geodDelta (cov := cov) hmet)) (m + geodDelta (cov := cov) hmet),
      curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) t ≠ 0 :=
    fun t _ => Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet p hξ t
  have hne₂ : ∀ t ∈ Ioo (-(geodDelta (cov := cov) hmet)) (m + geodDelta (cov := cov) hmet),
      curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) t ≠ 0 :=
    fun t _ => Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet p hη t
  have hEq := eqOn_Ioo_of_isGeodesicAt_of_eq (cov := cov) hsm₁ hsm₂ hgeo₁ hgeo₂ hne₁ hne₂ hmmem
    hmeet hvel
  have hev : (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ))
      =ᶠ[𝓝 (0:ℝ)] (fun t : ℝ => GExp (cov := cov) hmet p (t • η)) :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds h0mem) hEq
  have hv := Submission.RayJacobi.curveVelocity_congr (I := I) hev
  rw [Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet p hξ,
    Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet p hη] at hv
  exact hne hv

/-- **The `inj ≤ ½ℓ` corner bound at a cut point, with the non-reversal discharged.**  If two
*unit* directions `u ≠ v` at `p` give the same point at distance `m`, then the injectivity radius at
that point is at most `m`, i.e. at most half the length `2m` of the broken minimising loop.  This is
`InjHalf.injAtLeast_le_corner_of_GExp_broken_loop` with its corner-non-reversal hypothesis supplied
by geodesic uniqueness (`velocity_ne_of_meet`): **two distinct geodesics from `p` to the same point
can never meet tangentially there.**

For the cut-point step (`RayConj.exists_two_minimising_of_injAtLeast_of_lt_pi_div_sqrt`), where
`u ≠ v` are the two minimising vectors of norm `m`, this is therefore *hypothesis-free*: the corner
is automatically genuine. -/
theorem injAtLeast_le_corner_of_cutpoint
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {m : ℝ} (hm : 0 < m)
    {u v : TangentSpace I p} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (hu1 : ‖u‖ = 1) (hv1 : ‖v‖ = 1)
    (hmeet : GExp (cov := cov) hmet p (m • u) = GExp (cov := cov) hmet p (m • v))
    {r : ℝ} (hinj : InjAtLeast hmet (GExp (cov := cov) hmet p (m • u)) r) :
    r ≤ m := by
  have hδ := geodDelta_pos (cov := cov) hmet
  have hmmem : m ∈ Ioo (-(geodDelta (cov := cov) hmet)) (m + geodDelta (cov := cov) hmet) :=
    Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  -- transfer between the ray and `geodCurve` forms of the velocities
  have htransfer : ∀ {w : TangentSpace I p} (hw : w ≠ 0) (hw1 : ‖w‖ = 1),
      curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • w)) m
        = curveVelocity (I := I) (geodCurve (cov := cov) hmet m hm.le p w hw1) m := by
    intro w _ hw1
    refine Submission.RayJacobi.curveVelocity_congr (I := I) ?_
    exact Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hmmem)
      (GExp_ray_eqOn_geodCurve (cov := cov) hmet hw1 hm)
  have hvelG : curveVelocity (I := I) (geodCurve (cov := cov) hmet m hm.le p u hu1) m
      ≠ curveVelocity (I := I) (geodCurve (cov := cov) hmet m hm.le p v hv1) m := by
    intro hbad
    refine velocity_ne_of_meet (cov := cov) hmet hu hv hm hmeet huv ?_
    rw [htransfer hu hu1, htransfer hv hv1]
    exact hbad
  exact Submission.InjHalf.injAtLeast_le_corner_of_GExp_broken_loop (cov := cov) hmet htor hm
    hu1 hv1 hmeet hvelG hinj

end

end Submission.XuStep
