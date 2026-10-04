import Mathlib
import Submission.Work.Diff.C.geoCrux.RadialAux
import Submission.Work.Diff.C.ray_minimising_near_perturbation
import Submission.Work.Diff.C.rgrad_rdist_eikonal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.Diff.C.GeoCrux.RdistMinProp`: smoothness and eikonal on the closed ball

The distance function `rdist q` is `C^∞` with unit gradient at `GExp q u` for every non-zero `u` of
norm `≤ ρ₀ = π - arccos (1-c)` whose ray is minimising.  The smoothness is the `arccos` trick of
`Work.Diff.C.GeoCrux.rdist_smooth_eikonal` (with the non-strict region hypothesis `rdist ≤ ρ₀`), and
the eikonal is `Work.Diff.C.rgrad_rdist_eikonal` (which needs only the smoothness and `rdist ≠ 0`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

namespace Work.Diff.C.GeoCrux

/-- **`rdist q` is smooth on the closed ball `{rdist q ≤ ρ₀}`** (away from the centre). -/
theorem rdist_smooth_of_le_rho
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    (hdiam : ∀ x y : M, rdist (I := I) (M := M) x y ≤ Real.pi)
    {q y : M} (hy0 : 0 < rdist (I := I) (M := M) q y)
    (hle : rdist (I := I) (M := M) q y ≤ Real.pi - Real.arccos (1 - c)) :
    CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z) y := by
  have hρπ : Real.pi - Real.arccos (1 - c) ≤ Real.pi := by
    have h : 0 ≤ Real.arccos (1 - c) := Real.arccos_nonneg (1 - c)
    linarith
  have hρlt : Real.pi - Real.arccos (1 - c) < Real.pi := by
    have h : 0 < Real.arccos (1 - c) := Real.arccos_pos.mpr (by linarith)
    linarith
  have hcosρ : Real.cos (Real.pi - Real.arccos (1 - c)) = -1 + c := by
    rw [Real.cos_pi_sub, Real.cos_arccos (by linarith) (by linarith)]
    ring
  have hfcos_ge : -1 + c ≤ fcos (I := I) (M := M) q y := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi
      (x := rdist (I := I) (M := M) q y)
      (y := Real.pi - Real.arccos (1 - c)) hy0.le hρπ hle
    rw [hcosρ] at h
    exact h
  have hsm : CMDiffAt ∞ (fcos (I := I) (M := M) q) y := hsmC q y hfcos_ge
  have hdpi : rdist (I := I) (M := M) q y < Real.pi := lt_of_le_of_lt hle hρlt
  have hfcos_ne : fcos (I := I) (M := M) q y ≠ -1 ∧ fcos (I := I) (M := M) q y ≠ 1 := by
    have hcos : fcos (I := I) (M := M) q y = Real.cos (rdist (I := I) (M := M) q y) := rfl
    constructor
    · rw [hcos]
      intro h
      have h' : Real.cos (rdist (I := I) (M := M) q y) = Real.cos Real.pi := by
        rw [h, Real.cos_pi]
      have := Real.strictAntiOn_cos.injOn ⟨hy0.le, hdpi.le⟩ ⟨Real.pi_pos.le, le_rfl⟩ h'
      linarith
    · rw [hcos]
      intro h
      have h' : Real.cos (rdist (I := I) (M := M) q y) = Real.cos 0 := by
        rw [h, Real.cos_zero]
      have := Real.strictAntiOn_cos.injOn ⟨hy0.le, hdpi.le⟩ ⟨le_refl 0, Real.pi_pos.le⟩ h'
      linarith
  have hcos_sm : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ Real.arccos
      (fcos (I := I) (M := M) q y) :=
    (Real.contDiffAt_arccos hfcos_ne.1 hfcos_ne.2).contMDiffAt
  have harccos_sm : CMDiffAt ∞
      (fun z : M ↦ Real.arccos (fcos (I := I) (M := M) q z)) y := by
    have h := ContMDiffAt.comp (I := I) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, ℝ))
      (f := fcos (I := I) (M := M) q) (g := Real.arccos) y hcos_sm hsm
    exact h
  have hev : (fun z : M ↦ rdist (I := I) (M := M) q z) =ᶠ[𝓝 y]
      (fun z : M ↦ Real.arccos (fcos (I := I) (M := M) q z)) := by
    have hcont := Work.Diff.C.rdist_continuous (I := I) (M := M) q
    have h1 : ∀ᶠ z in 𝓝 y, 0 < rdist (I := I) (M := M) q z :=
      hcont.continuousAt (isOpen_Ioi.mem_nhds hy0)
    have h2 : ∀ᶠ z in 𝓝 y, rdist (I := I) (M := M) q z < Real.pi :=
      hcont.continuousAt (isOpen_Iio.mem_nhds hdpi)
    filter_upwards [h1, h2] with z hz1 hz2
    show rdist (I := I) (M := M) q z = Real.arccos (fcos (I := I) (M := M) q z)
    rw [show fcos (I := I) (M := M) q z = Real.cos (rdist (I := I) (M := M) q z) from rfl,
      Real.arccos_cos hz1.le hz2.le]
  exact harccos_sm.congr_of_eventuallyEq hev

/-- **`Work.Diff.C.GeoCrux.RdistMinProp`.** -/
theorem rdist_min : RdistMinProp := by
  intro E iE1 iE2 iE3 iE4 H iH I M iM1 iM2 iM3 iM4 iRB iCM iBL iNE iCS iPC cov iCD
    hmet htor c ε₁ hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hdiam q u hu hρ hmin
  have hrd : rdist (I := I) (M := M) q
      (Submission.GlobalExp.GExp (cov := cov) hmet q u) = ‖u‖ := by
    have h := Work.Diff.C.rdist_GExp_smul_of_minimising (I := I) (M := M) (cov := cov) hmet hu
      hmin (s := (1 : ℝ)) zero_le_one le_rfl
    rw [one_smul, one_mul] at h
    exact h
  have hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z)
      (Submission.GlobalExp.GExp (cov := cov) hmet q u) :=
    rdist_smooth_of_le_rho (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC hHess
      hcont hgrad hdiam (q := q) (y := Submission.GlobalExp.GExp (cov := cov) hmet q u)
      (by rw [hrd]; exact norm_pos_iff.mpr hu) (by rw [hrd]; exact hρ)
  exact ⟨hsm, Work.Diff.C.rgrad_rdist_eikonal (I := I) (M := M) (cov := cov) hmet htor
    (q := q) (x := Submission.GlobalExp.GExp (cov := cov) hmet q u)
    (by rw [hrd]; exact ne_of_gt (norm_pos_iff.mpr hu)) hsm⟩

end Work.Diff.C.GeoCrux
