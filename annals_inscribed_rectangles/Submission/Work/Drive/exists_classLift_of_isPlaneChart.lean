import Mathlib
import Submission.Work.Drive.diskLiftHomotopy
import Submission.Work.Drive.classTripleAssemblyLiftFree
import Submission.Work.Drive.planeChartDefs
import Submission.Work.Drive.hcLinCappingManifold
import Submission.Work.Drive.exists_local_unit_lift_projCharted
import Submission.Work.Drive.lift_eq_or_neg_of_isPreconnected
import Submission.Work.Drive.box_lift_assembly
import Submission.Work.Drive.isCoveringMap_projOfUnitSphere
import Submission.Work.Drive.linearPlaneChart
import Submission.Work.Drive.projImmersion

/-!
# A smooth non-vanishing lift of the class map of a plane chart

`Work.Drive.IsPlaneChart γ hγne Q` says that `Q : ℂ → CappingSpace` is a smooth disk model of the
capped plane of `γ`.  This file provides the *lift* of such a chart: a `C^∞`, nowhere vanishing
`V : ℂ → ℝ⁴` whose projective class is the class of `Q` everywhere
(`Work.Drive.IsClassLift Q V hVne`).

The mathematics is the standard contractibility argument: the covering map `S³ → ℝP³` has a
continuous section over the (contractible, locally path connected) disk `ℂ`, and the local smooth
lifts obtained from the projective charts agree with that continuous lift up to a locally constant
sign, so the continuous lift is smooth.

Concretely the argument runs over `ℝ²` (where the workspace's projective-chart machinery is stated)
and is transported to `ℂ` along the linear isometry `cplxOf`.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology LinearAlgebra.Projectivization

noncomputable section

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

set_option maxHeartbeats 1000000

/-- **A global smooth non-vanishing unit lift of a `C^∞` map into `ℝP³`.**

If `h : ℝ² → ℝP³` is `C^∞`, then there is a globally `C^∞`, nowhere vanishing unit vector field
`V : ℝ² → ℝ⁴` whose projective class is `h` everywhere.

The proof is the contractibility argument: the covering map `S³ → ℝP³` lifts `h` to a continuous
unit field `v` (`existsUnique_continuousMap_lifts`, applicable because `ℝ²` is contractible and
locally path connected), the projective charts give a *smooth* unit lift of `h` on a neighbourhood of
each point, and two unit lifts of the same map into `ℝP³` on a ball agree up to sign
(`lift_eq_or_neg_of_isPreconnected`), so that `v` is smooth near every point. -/
theorem exists_global_unit_lift_projCharted
    {h : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)}
    (hh : ContMDiff (𝓡 2) (𝓡 3) Ctop h) :
    ∃ (V : EuclideanSpace ℝ (Fin 2) → Eucl 3) (hV : ∀ y, V y ≠ 0),
      ContDiff ℝ Ctop V ∧ (∀ y, ‖V y‖ = 1) ∧
      ∀ y, Projectivization.mk ℝ (V y) (hV y) = h y := by
  classical
  have hcov : IsCoveringMap (Work.Drive.projOfUnitSphere (n := 3)) :=
    Work.Drive.isCoveringMap_projOfUnitSphere
  -- the global continuous unit lift of `h`
  let F : C(EuclideanSpace ℝ (Fin 2), Projectivization ℝ (Eucl 3)) := ⟨h, hh.continuous⟩
  obtain ⟨e₀, he₀⟩ := Work.Drive.surjective_projOfUnitSphere (h 0)
  obtain ⟨G, ⟨-, hGlift⟩, -⟩ := hcov.existsUnique_continuousMap_lifts F 0 e₀ he₀
  have hGlift' : ∀ y, Work.Drive.projOfUnitSphere (G y) = h y := fun y => congr_fun hGlift y
  -- its smoothness, from the local smooth unit lifts of the projective charts
  have hsm : ContDiff ℝ Ctop (fun y => (G y : Eucl 3)) := by
    rw [contDiff_iff_contDiffAt]
    intro p
    -- a local smooth unit lift near `p`, valid on a box around `p`
    obtain ⟨r, hr, u, hune, husm, hunorm, hueq⟩ :=
      Work.Drive.exists_local_unit_lift_projCharted (p 0 - 1) (p 0 + 1) (p 1 - 1) (p 1 + 1)
        (by linarith) (by linarith) hh.contMDiffOn p
        (by rw [Set.mem_Icc]; constructor <;> linarith)
        (by rw [Set.mem_Icc]; constructor <;> linarith)
    have hpos : 0 < min r 1 := lt_min hr one_pos
    have hSpre : IsPreconnected (Metric.ball p (min r 1)) :=
      (convex_ball p (min r 1)).isPreconnected
    have hcoord : ∀ y : EuclideanSpace ℝ (Fin 2), ∀ i : Fin 2, |y i - p i| ≤ dist y p := by
      intro y i
      have h := PiLp.norm_apply_le (y - p) i
      have h2 : (y - p) i = y i - p i := by simp
      rw [h2, Real.norm_eq_abs] at h
      rwa [dist_eq_norm]
    have hboxmem : ∀ y ∈ Metric.ball p (min r 1),
        y 0 ∈ Set.Icc (p 0 - 1) (p 0 + 1) ∧ y 1 ∈ Set.Icc (p 1 - 1) (p 1 + 1) := by
      intro y hy
      have hd : dist y p < 1 := lt_of_lt_of_le (Metric.mem_ball.mp hy) (min_le_right _ _)
      have h0 := abs_lt.mp (lt_of_le_of_lt (hcoord y 0) hd)
      have h1 := abs_lt.mp (lt_of_le_of_lt (hcoord y 1) hd)
      exact ⟨⟨by linarith [h0.1], by linarith [h0.2]⟩, ⟨by linarith [h1.1], by linarith [h1.2]⟩⟩
    -- the local lift as a map into the unit sphere
    let u' : EuclideanSpace ℝ (Fin 2) → unitSphere 3 := fun y =>
      ⟨u y, by rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hunorm y⟩
    have hu'cont : ContinuousOn u' (Metric.ball p (min r 1)) := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact Continuous.subtype_mk (husm.continuous.comp continuous_subtype_val) _
    have hGcont : ContinuousOn (fun y => G y) (Metric.ball p (min r 1)) :=
      G.continuous.continuousOn
    have hvu : ∀ y ∈ Metric.ball p (min r 1),
        Work.Drive.projOfUnitSphere (G y) = Work.Drive.projOfUnitSphere (u' y) := by
      intro y hy
      have h1 : Work.Drive.projOfUnitSphere (u' y) = Projectivization.mk ℝ (u y) (hune y) := by
        rw [Work.Drive.projOfUnitSphere_eq, Work.Drive.projOfUnit_eq_mk]
      exact (hGlift' y).trans ((h1.trans (hueq y (hboxmem y hy).1 (hboxmem y hy).2
        (lt_of_lt_of_le (Metric.mem_ball.mp hy) (min_le_left _ _)))).symm)
    -- on the ball the two unit lifts agree up to sign
    rcases Work.Drive.lift_eq_or_neg_of_isPreconnected hcov hSpre hGcont hu'cont hvu
      (p := p) (Metric.mem_ball_self hpos) with hcase | hcase
    · have hcon : ContDiffOn ℝ Ctop (fun y => (G y : Eucl 3)) (Metric.ball p (min r 1)) :=
        husm.contDiffOn.congr (fun y hy => congrArg Subtype.val (hcase y hy))
      exact hcon.contDiffAt (Metric.ball_mem_nhds p hpos)
    · have hcon : ContDiffOn ℝ Ctop (fun y => (G y : Eucl 3)) (Metric.ball p (min r 1)) :=
        (husm.neg).contDiffOn.congr (fun y hy => by
          have h := congrArg Subtype.val (hcase y hy)
          rw [Work.Drive.negSphere_coe] at h
          exact h)
      exact hcon.contDiffAt (Metric.ball_mem_nhds p hpos)
  refine ⟨fun y => (G y : Eucl 3), fun y => norm_eq_one_ne_zero (norm_coe_unitSphere (G y)),
    hsm, fun y => norm_coe_unitSphere (G y), ?_⟩
  intro y
  exact (mk_coe_eq_projOfUnitSphere (G y) _).trans (hGlift' y)

/-- **The plane chart's class map has a smooth non-vanishing lift.**  For a smooth disk model `Q` of
the capped plane of `γ` (`Work.Drive.IsPlaneChart`), there is a `C^∞` nowhere vanishing
`V : ℂ → ℝ⁴` with `Work.Drive.IsClassLift Q V hVne`: the class of `Q z` is the line of `V z`. -/
theorem exists_classLift_of_isPlaneChart {γ : Circle → ℝ × ℝ} (hγne : ∀ x : Circle, γ x ≠ 0) {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q) : ∃ (V : ℂ → Eucl 3) (hVne : ∀ z : ℂ, V z ≠ 0), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V ∧ IsClassLift Q V hVne := by
  have hQsm : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop Q := hQ.1
  have hcomp : ContMDiff (𝓡 2) (𝓡 4) Ctop
      (fun y : EuclideanSpace ℝ (Fin 2) => Q (cplxOf y)) :=
    hQsm.comp (contMDiff_iff_contDiff.mpr contDiff_cplxOf)
  have hcls : ContMDiff (𝓡 2) (𝓡 3) Ctop
      (fun y : EuclideanSpace ℝ (Fin 2) => (cappingSpaceHomeoProj (Q (cplxOf y))).2) :=
    fun y => contMDiffAt_cls_of_contMDiff hcomp y
  obtain ⟨V', hV'ne, hV'sm, -, hV'mk⟩ := exists_global_unit_lift_projCharted hcls
  refine ⟨fun z => V' (cplxOfInv z), fun z => hV'ne (cplxOfInv z),
    hV'sm.comp cplxOfInv_contDiff, ?_⟩
  intro z
  have h := (hV'mk (cplxOfInv z)).symm
  rw [cplxOf_cplxOfInv] at h
  exact h

end

end Work.Drive
