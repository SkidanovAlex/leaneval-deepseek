import Mathlib
import Submission.Work.ThomBordism.BCUDefs
import Submission.Work.Orient.Boundary.injective_localisation_aux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Continuity of the boundary collapse `bcuPhi`, and its values in the standard half-ball

`Work.ThomBordism.bcuPhi n W y τ χ z = BCU.profile2 0 (χ z) (τ • (chart y z - chart y y))`
(`Submission/Work/ThomBordism/BCUDefs.lean`) is the collapse map used by
`boundarySign_boundaryChartAt_univ`.  This file proves that it is continuous on all of `W`, and
that it takes its values in the standard half-ball `stdHalfBall (n+1)`.

The two inputs are:

* **outside the support `K` of the bump** (which is assumed inside the chart at `y`) the bump
  vanishes, so the collapse is the *constant* north pole
  (`bcuPhi_eq_northPole`), hence continuous, and the north pole lies in the half-ball
  (`BCU.bcu_northPole_mem`);
* **inside `K`** the point is in the (open) source of the chart at `y`, where the chart value is
  continuous, so the map `z ↦ (χ z, bcuVa n W y τ z)` is continuous and the profile
  `(t, v) ↦ profile2 0 t v` is continuous at its image — the latter is the hypothesis `hcont`,
  whose side condition `v ≠ 0 ∨ t = 1` is exactly the hypothesis `hvan` at the pairs `(χ z, bcuVa z)`
  with `bcuVa z = 0`.  Membership is then the first conjunct of `bcu_profile2_properties`, whose
  sign hypothesis `0 ≤ (bcuVa z) 0` holds because the chart at the boundary point `y` puts `y` on
  the hyperplane (`Work.Orient.Boundary.chartAt_boundary_coord_zero`) while the chart sends every
  point of its source into the half-space.
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open scoped Manifold Topology

namespace Work.ThomBordism

theorem continuous_bcuPhi_and_mem (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (τ : ℝ) (hτ : 0 < τ) (χ : W → ℝ) (K : Set W)
    (hχ : Continuous χ) (hχ01 : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (hK : IsCompact K) (hKsub : K ⊆ (chartAt (EuclideanHalfSpace (n + 1)) y).source)
    (hout : ∀ z ∉ K, χ z = 0)
    (hvan : ∀ z ∈ (chartAt (EuclideanHalfSpace (n + 1)) y).source,
      Work.ThomBordism.bcuVa n W y τ z = 0 → χ z = 1)
    (hcont : ∀ t₀ : ℝ, ∀ v₀ : EuclideanSpace ℝ (Fin (n + 1)), 0 ≤ t₀ → t₀ ≤ 1 →
      (v₀ ≠ 0 ∨ t₀ = 1) →
      ContinuousAt (fun p : ℝ × EuclideanSpace ℝ (Fin (n + 1)) =>
        Work.ThomBordism.BCU.profile2 (0 : EuclideanSpace ℝ (Fin (n + 1))) p.1 p.2) (t₀, v₀)) :
    Continuous (Work.ThomBordism.bcuPhi n W y τ χ) ∧
      (∀ z, Work.ThomBordism.bcuPhi n W y τ χ z ∈ Work.ThomBordism.stdHalfBall (n + 1)) := by
  classical
  have hKcl : IsClosed K := hK.isClosed
  refine ⟨?_, ?_⟩
  · -- Continuity: the collapse is locally constant outside `K` and a composition of continuous
    -- maps inside the (open) source of the chart at `y`.
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hzK : z ∈ K
    · have hzsrc : z ∈ (chartAt (EuclideanHalfSpace (n + 1)) y).source := hKsub hzK
      have hch : ContinuousAt (fun w : W =>
          (((chartAt (EuclideanHalfSpace (n + 1)) y) w).1 :
            EuclideanSpace ℝ (Fin (n + 1)))) z :=
        continuous_subtype_val.continuousAt.comp
          ((chartAt (EuclideanHalfSpace (n + 1)) y).continuousAt hzsrc)
      have hva : ContinuousAt (fun w : W => Work.ThomBordism.bcuVa n W y τ w) z := by
        simp only [Work.ThomBordism.bcuVa, Work.ThomBordism.bcuCh]
        exact (hch.sub continuousAt_const).const_smul τ
      have hpair : ContinuousAt (fun w : W => (χ w, Work.ThomBordism.bcuVa n W y τ w)) z :=
        hχ.continuousAt.prodMk hva
      have hcase : Work.ThomBordism.bcuVa n W y τ z ≠ 0 ∨ χ z = 1 := by
        by_cases h : Work.ThomBordism.bcuVa n W y τ z = 0
        · exact Or.inr (hvan z hzsrc h)
        · exact Or.inl h
      have hprof := hcont (χ z) (Work.ThomBordism.bcuVa n W y τ z)
        (hχ01 z).1 (hχ01 z).2 hcase
      exact ContinuousAt.comp
        (f := fun w : W => (χ w, Work.ThomBordism.bcuVa n W y τ w)) hprof hpair
    · have hev : (fun w => Work.ThomBordism.bcuPhi n W y τ χ w) =ᶠ[𝓝 z]
          (fun _ => Work.ThomBordism.BCU.northPole n) := by
        filter_upwards [hKcl.isOpen_compl.mem_nhds hzK] with w hw
        exact Work.ThomBordism.bcuPhi_eq_northPole n W y τ χ w (hout w hw)
      exact (continuousAt_const (y := Work.ThomBordism.BCU.northPole n)).congr hev.symm
  · -- Membership in the standard half-ball.  Outside `K` the collapse is the north pole; inside
    -- `K` one applies `bcu_profile2_properties` to the chart value, which lies in the half-space.
    intro z
    by_cases hzK : z ∈ K
    · have hcoord : 0 ≤ (Work.ThomBordism.bcuVa n W y τ z) 0 := by
        rw [Work.ThomBordism.bcuVa]
        simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
        have h1 : 0 ≤ (((chartAt (EuclideanHalfSpace (n + 1)) y) z).1 :
            EuclideanSpace ℝ (Fin (n + 1))) 0 :=
          ((chartAt (EuclideanHalfSpace (n + 1)) y) z).2
        have h2 : (((chartAt (EuclideanHalfSpace (n + 1)) y) y).1 :
            EuclideanSpace ℝ (Fin (n + 1))) 0 = 0 :=
          Work.Orient.Boundary.chartAt_boundary_coord_zero n W hy
        have h3 : (((chartAt (EuclideanHalfSpace (n + 1)) y) z).1 :
              EuclideanSpace ℝ (Fin (n + 1))) 0 -
            (((chartAt (EuclideanHalfSpace (n + 1)) y) y).1 :
              EuclideanSpace ℝ (Fin (n + 1))) 0 ≥ 0 := by linarith
        exact mul_nonneg (le_of_lt hτ) h3
      have hmem := (Work.ThomBordism.bcu_profile2_properties n).1 0
        (Work.ThomBordism.bcuVa n W y τ z) (χ z) (by simp) hcoord (hχ01 z).1 (hχ01 z).2
      simpa [Work.ThomBordism.bcuPhi] using hmem
    · rw [Work.ThomBordism.bcuPhi_eq_northPole n W y τ χ z (hout z hzK)]
      exact Work.ThomBordism.BCU.bcu_northPole_mem n

end Work.ThomBordism
