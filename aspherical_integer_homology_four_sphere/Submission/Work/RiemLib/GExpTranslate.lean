import Submission.Work.RiemLib.XuStep
import Submission.Work.RiemLib.CornerStrict

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


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
open Submission.InjRadius
open Submission.HopfRinow

namespace Submission.GExpTranslate

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

/-- **The `GExp`-ray is a genuine (two-sided) geodesic flow line.**  For a unit direction `ξ` at `q`
and *arbitrary* real parameters `s, t`,

`GExp (GExp q (s • ξ)) (t • w) = GExp q ((s + t) • ξ)`,  where
`w = curveVelocity (fun r ↦ GExp q (r • ξ)) s`

is the velocity of the ray at time `s`.  This is the two-sided refinement of
`GExpGlob.GExp_add_smul` (which needs `s > 0`, `t ≥ 0`) and the general form of
`CornerStrict.GExp_ray_back` (the case `s = -ε`, `t ∈ {ε, 2ε}`).  Proof: geodesic uniqueness
(`eqOn_Ioo_of_isGeodesicAt_of_eq`): the two curves `r ↦ GExp (GExp q (s • ξ)) (r • w)` and
`r ↦ GExp q ((r + s) • ξ)` are geodesics with the same value and velocity at `r = 0`. -/
theorem GExp_translate (hmet : IsMetricCompatible cov) (q : M) {ξ : TangentSpace I q}
    (hξ : ‖ξ‖ = 1) (s t : ℝ) :
    GExp (cov := cov) hmet (GExp (cov := cov) hmet q (s • ξ))
        (t • curveVelocity (I := I) (fun r : ℝ => GExp (cov := cov) hmet q (r • ξ)) s)
      = GExp (cov := cov) hmet q ((s + t) • ξ) := by
  classical
  have hξne : ξ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hξ; norm_num at hξ
  set w : TangentSpace I (GExp (cov := cov) hmet q (s • ξ)) :=
    curveVelocity (I := I) (fun r : ℝ => GExp (cov := cov) hmet q (r • ξ)) s with hwdef
  have hwne : w ≠ 0 := by
    rw [hwdef]
    exact Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet q hξne s
  have hraymd : ∀ r : ℝ, MDifferentiableAt 𝓘(ℝ) I
      (fun r : ℝ => GExp (cov := cov) hmet q (r • ξ)) r := fun r =>
    ((Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet q hξne).contMDiffAt
      Filter.univ_mem).mdifferentiableAt (by simp)
  set M₀ : ℝ := |s| + |t| + 1 with hM₀def
  have hM₀pos : 0 < M₀ := by rw [hM₀def]; positivity
  have htmem : t ∈ Ioo (-M₀) M₀ := by
    rw [hM₀def]
    exact Set.mem_Ioo.mpr ⟨by
      have := abs_nonneg t; linarith [neg_abs_le t, abs_nonneg s], by
      have := abs_nonneg s; linarith [le_abs_self t]⟩
  have hσsm : ContMDiffOn 𝓘(ℝ) I ∞
      (fun r : ℝ => GExp (cov := cov) hmet q ((1 * r + s) • ξ)) (Ioo (-M₀) M₀) := by
    have hg : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun r : ℝ => 1 * r + s) :=
      (contMDiff_const.mul contMDiff_id).add contMDiff_const
    have h := (Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet q hξne).comp
      (hg.contMDiffOn (s := Ioo (-M₀) M₀)) (fun r _ => Set.mem_univ _)
    rw [show (fun r : ℝ => GExp (cov := cov) hmet q (r • ξ)) ∘ (fun r : ℝ => 1 * r + s)
        = (fun r : ℝ => GExp (cov := cov) hmet q ((1 * r + s) • ξ)) from rfl] at h
    exact h
  have hσrev : curveVelocity (I := I)
      (fun r : ℝ => GExp (cov := cov) hmet q ((1 * r + s) • ξ)) 0 = w := by
    rw [Submission.Length.curveVelocity_comp_mul_add (I := I)
      (γ := fun r : ℝ => GExp (cov := cov) hmet q (r • ξ)) (c := 1) (d := s) (t := 0)
      (hraymd (1 * 0 + s))]
    rw [one_mul, zero_add, one_smul, hwdef]
  have hσ0 : (fun r : ℝ => GExp (cov := cov) hmet q ((1 * r + s) • ξ)) 0
      = (fun r : ℝ => GExp (cov := cov) hmet (GExp (cov := cov) hmet q (s • ξ)) (r • w)) 0 := by
    simp only [zero_smul, GExp_zero, one_mul, zero_add]
  have hEqOn := eqOn_Ioo_of_isGeodesicAt_of_eq (cov := cov) (a := -M₀) (b := M₀)
    ((Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet
      (GExp (cov := cov) hmet q (s • ξ)) hwne).mono (Set.subset_univ _))
    hσsm
    (fun r _ => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet
      (GExp (cov := cov) hmet q (s • ξ)) hwne r)
    (fun r hr => by
      have h := isGeodesicAt_comp_affine (cov := cov)
        (σ := fun ρ : ℝ => GExp (cov := cov) hmet q (ρ • ξ)) (a := 1) (b := s)
        (c := -(M₀ + |s| + 1)) (d := M₀ + |s| + 1) (by norm_num)
        ((Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet q hξne).mono
          (Set.subset_univ _))
        (fun y _ => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet q hξne y)
        (r := r) (Set.mem_Ioo.mpr ⟨by
            have h1 : -(M₀ + |s| + 1) ≤ -(|s| + 1) := by
              have : (0:ℝ) ≤ M₀ := hM₀pos.le; linarith
            have h2 : -(|s| + 1) ≤ s := by
              have := neg_abs_le s; linarith
            linarith [hr.1], by
            have h2 : s ≤ |s| + 1 := by
              have := le_abs_self s; linarith
            linarith [hr.2]⟩)
      simpa using h)
    (fun r _ => Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet
      (GExp (cov := cov) hmet q (s • ξ)) hwne r)
    (fun r hr => by
      rw [Submission.Length.curveVelocity_comp_mul_add (I := I)
        (γ := fun ρ : ℝ => GExp (cov := cov) hmet q (ρ • ξ)) (c := 1) (d := s) (t := r)
        (hraymd (1 * r + s))]
      rw [one_smul]
      exact Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet q hξne (1 * r + s))
    (show (0 : ℝ) ∈ Ioo (-M₀) M₀ from Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩)
    hσ0.symm
    (by
      rw [Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet
        (GExp (cov := cov) hmet q (s • ξ)) hwne, hσrev])
  have h := hEqOn htmem
  simpa [one_mul, add_comm, add_left_comm, add_assoc] using h

end

end Submission.GExpTranslate
