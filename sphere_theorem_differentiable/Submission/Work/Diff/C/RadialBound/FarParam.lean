import Mathlib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.far_sphere_size
import Submission.Work.Diff.C.dmRadialBridge
import Submission.Work.Diff.C.JacobiLogDeriv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The far-sphere parametrisation (shared between `far_sphere_diameter` and its pieces)

`Work.Diff.C.far_sphere_param`: every point `x` of the "far sphere" `{rdist q · = ρ}` of a centre `q`
(`ρ > 0`) is `GExp q (ρ • u)` for a unit vector `u`, and the ray `t ↦ GExp q (t • u)` is minimising
up to `ρ`.

This module exists so that the lemmas of `Submission/Work/Diff/C/RadialBound/` can use
`far_sphere_param` without importing `Submission.Work.Diff.C.far_sphere_diameter` itself (which
imports those lemmas, so that a direct import would be an import cycle).
-/

namespace Work.Diff.C

open Bundle
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

open Bundle in
/-- **Every point of the far sphere is hit by a minimising unit-speed ray from `q`.**

If `rdist q x = ρ > 0` then there is a unit vector `u : T_qM` with `x = GExp q (ρ • u)` and
`rdist q (GExp q (t • u)) = t` for every `t ∈ [0, ρ]` (so the ray is a minimising unit-speed
geodesic arc from `q` to `x`).  Proof: Hopf–Rinow produces `v` with `GExp q v = x` and
`‖v‖ = rdist q x = ρ`; the ray has length `ρ` and the exponential map decreases distances
(`Submission.GExpRay2.edist_GExp_smul_le_mul_norm`) and moves at unit speed along it
(`Submission.GExpRay.edist_GExp_smul_le`), so the triangle inequality forces equality. -/
theorem far_sphere_param
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q x : M} {ρ : ℝ} (hρ0 : 0 < ρ)
    (hx : Work.Diff.C.rdist (I := I) (M := M) q x = ρ) :
    ∃ u : TangentSpace I q, ‖u‖ = 1 ∧
      Submission.GlobalExp.GExp (cov := cov) hmet q (ρ • u) = x ∧
      (∀ t ∈ Set.Icc (0 : ℝ) ρ,
        Work.Diff.C.rdist (I := I) (M := M) q
          (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)) = t) := by
  classical
  haveI : RegularSpace M := inferInstance
  obtain ⟨v, hvG, hved⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (I := I) (cov := cov) hmet htor q x
  -- `‖v‖ = ρ`
  have hvn : ‖v‖ = ρ := by
    rw [Work.Diff.C.rdist, hved, ENNReal.toReal_ofReal (norm_nonneg v)] at hx
    exact hx
  have hvne : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hvn
    exact absurd hvn.symm (ne_of_gt hρ0)
  -- the unit direction
  have hu : ‖ρ⁻¹ • v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ0), hvn]
    exact inv_mul_cancel₀ (ne_of_gt hρ0)
  have hρv : ρ • (ρ⁻¹ • v) = v := by
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hρ0), one_smul]
  refine ⟨ρ⁻¹ • v, hu, ?_, ?_⟩
  · rw [hρv]
    exact hvG
  · intro t ht
    rw [Set.mem_Icc] at ht
    -- upper bound `rdist q (γ t) ≤ t`
    have hup : Manifold.riemannianEDist I q
        (Submission.GlobalExp.GExp (cov := cov) hmet q (t • (ρ⁻¹ • v)))
        ≤ ENNReal.ofReal t := by
      have h := Submission.GExpRay2.edist_GExp_smul_le_mul_norm (I := I) (M := M) (cov := cov)
        hmet q (v := ρ⁻¹ • v) (a := 0) (b := t) le_rfl ht.1
      rw [zero_smul, Submission.GlobalExp.GExp_zero, hu, sub_zero, mul_one] at h
      exact h
    -- lower bound `rdist q (γ t) ≥ t`
    have hlow : ENNReal.ofReal t ≤ Manifold.riemannianEDist I q
        (Submission.GlobalExp.GExp (cov := cov) hmet q (t • (ρ⁻¹ • v))) := by
      have hfin1 : Manifold.riemannianEDist I q
          (Submission.GlobalExp.GExp (cov := cov) hmet q (t • (ρ⁻¹ • v))) ≠ ⊤ :=
        (Submission.HopfRinow.riemannianEDist_lt_top (I := I) hmet htor q _).ne
      -- the ray from `γ t` to `x` has length `ρ - t`
      have hseg : Manifold.riemannianEDist I
          (Submission.GlobalExp.GExp (cov := cov) hmet q (t • (ρ⁻¹ • v))) x
          ≤ ENNReal.ofReal (ρ - t) := by
        have h := Submission.GExpRay.edist_GExp_smul_le (I := I) (M := M) (cov := cov) hmet q
          (v := ρ⁻¹ • v) hu (a := t) (b := ρ) ht.1 hρ0.le ht.2
        rw [hρv, hvG] at h
        exact h
      -- the triangle inequality
      have htri := Manifold.riemannianEDist_triangle (I := I) (x := q)
        (y := Submission.GlobalExp.GExp (cov := cov) hmet q (t • (ρ⁻¹ • v))) (z := x)
      have hqx : Manifold.riemannianEDist I q x = ENNReal.ofReal ρ := by
        rw [hved, hvn]
      have hle : ENNReal.ofReal ρ ≤ Manifold.riemannianEDist I q
          (Submission.GlobalExp.GExp (cov := cov) hmet q (t • (ρ⁻¹ • v)))
          + ENNReal.ofReal (ρ - t) := by
        calc ENNReal.ofReal ρ = Manifold.riemannianEDist I q x := hqx.symm
          _ ≤ Manifold.riemannianEDist I q
                (Submission.GlobalExp.GExp (cov := cov) hmet q (t • (ρ⁻¹ • v)))
              + Manifold.riemannianEDist I
                (Submission.GlobalExp.GExp (cov := cov) hmet q (t • (ρ⁻¹ • v))) x := htri
          _ ≤ _ := add_le_add le_rfl hseg
      have hb : (0 : ℝ) ≤ ρ - t := by linarith
      have h := ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr ⟨hfin1, ENNReal.ofReal_ne_top⟩) hle
      simp only [ENNReal.toReal_add hfin1 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hρ0.le,
        ENNReal.toReal_ofReal hb, Work.Diff.C.rdist] at h
      exact (ENNReal.ofReal_le_iff_le_toReal hfin1).mpr (by linarith)
    have hup' : Work.Diff.C.rdist (I := I) (M := M) q
        (Submission.GlobalExp.GExp (cov := cov) hmet q (t • (ρ⁻¹ • v))) ≤ t := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hup
      simpa only [ENNReal.toReal_ofReal ht.1, Work.Diff.C.rdist] using h
    have hlow' : t ≤ Work.Diff.C.rdist (I := I) (M := M) q
        (Submission.GlobalExp.GExp (cov := cov) hmet q (t • (ρ⁻¹ • v))) := by
      have hfin : Manifold.riemannianEDist I q
          (Submission.GlobalExp.GExp (cov := cov) hmet q (t • (ρ⁻¹ • v))) ≠ ⊤ :=
        (Submission.HopfRinow.riemannianEDist_lt_top (I := I) hmet htor q _).ne
      simpa only [Work.Diff.C.rdist] using (ENNReal.ofReal_le_iff_le_toReal hfin).mp hlow
    exact le_antisymm hup' hlow'
end Work.Diff.C
