import Mathlib
import Submission.Work.Diff.C.geoCrux.sharp.Defs
import Submission.Work.Diff.C.geoCrux.inj_radius_core
import Submission.Work.Diff.C.no_conjTime_le_arccos
import Submission.Work.Diff.C.dmRadialBridge
import Submission.Work.Diff.C.far_sphere_size
import Submission.Work.Diff.C.geoCrux.TwoCentre.Families

set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.Diff.C.geoCrux.sharp.varfield_ne_zero`

**Non-vanishing of the radial variation field** (`Work.Diff.C.geoCrux.SharpNeZeroProp`): for a unit
vector `v ∈ T_qM`, a direction `ξ ⊥ v` with `ξ ≠ 0` and `0 < t ≤ ρ₀ = π - arccos (1-c)`,

`∂_r|₀ GExp q (t • (v + r • ξ)) ≠ 0`.

## Route

The field `J s := ∂_r|₀ GExp q (s • (v + r • ξ))` is a Jacobi field along the ray
`γ s = GExp q (s • v)` (`Submission.RayJacobi.isJacobiAt_GExp_variation`) with `J 0 = 0`
(`Work.OddBound.longHomotopy.variation_zero_at_zero`), orthogonal to `γ'`
(`Work.Diff.C.dmRadialOrthogonal`, the Gauss pairing) and `≢ 0`
(`Submission.SingularConj.exists_pos_variation_ne_zero`, `ξ ≠ 0`).

Assume `J t = 0` with `0 < t ≤ ρ₀`.  Since `hcut : InjAtLeast hmet q ρ₀` every ray of length `≤ ρ₀`
is minimising, so on `(0,t)`:

* `∇(rdist q)(γ s) = γ'(s)` (`Work.Diff.C.geoCrux.tc_grad_gam`, from
  `Work.Diff.C.curveVelocity_GExp_eq_smul_rgrad` and the eikonal `Work.Diff.C.rgrad_rdist_eikonal`);
* `rdist q` is `C^∞` at `γ s` (`Work.Diff.C.geoCrux.tc_sm_gam`, the arccos trick);
* `⟪∇_{γ'} J, J⟫ = Hess (rdist q)(J,J)` (`Work.Diff.C.dmRadialBridge`; at a zero of `J` both sides
  vanish) and `(cot s - ε₁/sin s)⟪J,J⟫ ≤ Hess (rdist q)(J,J)`
  (`Work.Diff.C.rhess_rdist_bound_of_hHess` from the `hHess` hypothesis).

Thus all the hypotheses of the Sturm comparison `Work.Diff.C.no_conjTime_le_arccos` (with
`L := ρ₀ < π`) are met, giving `False`.

This is the `hdiam`-free version of the argument of
`Submission/Work/Diff/C/geoCrux/radial_variation.lean`: the global diameter bound is never used
because the injectivity radius `hcut` alone makes the rays minimising
(`Submission.CutTime.edist_GExp_smul_eq_of_injAtLeast`) and smooths `rdist` inside the ball
(`Submission.Work.Diff.C.geoCrux.TwoCentre.Setup`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 6400000
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.C.geoCrux.sharp

theorem varfield_ne_zero : Work.Diff.C.geoCrux.SharpNeZeroProp := by
  intro E iE1 iE2 iE3 iE4 H iH I M iM1 iM2 iM3 iM4 iRB iCM iBL iNE iCS iPC cov iCD
    hmet htor c ε₁ hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hcut q v hv ξ hξ hξ0 t ht0 htρ
  intro hJt
  have hv1 : ‖v‖ = 1 := by
    have h : ‖v‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hv
    nlinarith [norm_nonneg v]
  have hv0 : v ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hv1; norm_num at hv1
  haveI : RegularSpace M := inferInstance
  have hρ₀π : rho0 c < Real.pi := by
    rw [rho0]
    have h : 0 < Real.arccos (1 - c) := Real.arccos_pos.mpr (by linarith)
    linarith
  have hρ₀π' : rho0 c ≤ Real.pi := le_of_lt hρ₀π
  have hρ₀cos : Real.cos (rho0 c) = -1 + c := by
    rw [rho0, Real.cos_pi_sub, Real.cos_arccos (by linarith) (by linarith)]
    ring
  -- the radial variation field
  let J : (s : ℝ) → TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) :=
    fun s => Submission.Geodesic.curveVelocity (I := I)
      (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • (v + r • ξ))) 0
  -- ## The ray is minimising up to `ρ₀` (from `hcut` alone)
  have hminE : ∀ s ∈ Set.Icc (0 : ℝ) t, Manifold.riemannianEDist I q
      (Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) = ENNReal.ofReal s := by
    intro s hs
    exact Submission.CutTime.edist_GExp_smul_eq_of_injAtLeast (I := I) (cov := cov) hmet htor
      (hcut q) hv1 hs.1 (le_trans hs.2 htρ)
  have hrd : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      rdist (I := I) (M := M) q (Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) = s := by
    intro s hs
    have h := hminE s ⟨hs.1.le, hs.2.le⟩
    show (Manifold.riemannianEDist I q
      (Submission.GlobalExp.GExp (cov := cov) hmet q (s • v))).toReal = s
    rw [h, ENNReal.toReal_ofReal hs.1.le]
  have hrdρ : ∀ s ∈ Set.Ioo (0 : ℝ) t, s < rho0 c := fun s hs => lt_of_lt_of_le hs.2 htρ
  -- ## `rdist q` is smooth along the ray
  have hsm_s : ∀ s ∈ Set.Ioo (0 : ℝ) t, CMDiffAt ∞
      (fun z : M ↦ rdist (I := I) (M := M) q z)
      (Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) := by
    intro s hs
    exact tc_sm_gam (cov := cov) hmet htor hc hc1 hcut hsmC hv1 hs.1 (hrdρ s hs).le
  -- ## `∇(rdist q) = γ'` along the ray
  have hgrad_eq : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
        (Submission.GlobalExp.GExp (cov := cov) hmet q (s • v))
      = Submission.Geodesic.curveVelocity (I := I)
          (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (r • v)) s := by
    intro s hs
    exact tc_grad_gam (cov := cov) hmet htor hc hc1 hcut hsmC hv1 hv0 hs.1 (hrdρ s hs).le
  -- ## the Jacobi field data
  have hJ : ∀ s : ℝ, Submission.RauchGlobal.IsJacobiAt cov
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) J s :=
    fun s => Submission.RayJacobi.isJacobiAt_GExp_variation (cov := cov) hmet htor hv0 hv1 s
  have hJ0 : J 0 = 0 :=
    Work.OddBound.longHomotopy.variation_zero_at_zero (cov := cov) hmet (p := q) (u := v) (η := ξ)
  have hJd : J t = 0 := hJt
  obtain ⟨δ, hδpos, hδne⟩ :=
    Submission.SingularConj.exists_pos_variation_ne_zero (cov := cov) hmet (p := q) (u := v)
      (η := ξ) hv1 hξ0
  have hne : ∃ s ∈ Set.Ioo (0 : ℝ) t, J s ≠ 0 := by
    refine ⟨min δ t / 2, ⟨?_, ?_⟩, ?_⟩
    · have h1 : 0 < min δ t := lt_min hδpos ht0
      linarith
    · have h1 : min δ t ≤ t := min_le_right δ t
      linarith
    · have h1 : min δ t / 2 < δ := by
        have h2 : min δ t ≤ δ := min_le_left δ t
        linarith
      exact hδne (min δ t / 2) ⟨by have h3 : 0 < min δ t := lt_min hδpos ht0; linarith, h1⟩
  -- ## orthogonality to the radial direction (Gauss)
  have hperp : ∀ s ∈ Set.Ioo (0 : ℝ) t, Inner.inner ℝ (J s)
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
        (Submission.GlobalExp.GExp (cov := cov) hmet q (s • v))) = 0 := by
    intro s hs
    rw [hgrad_eq s hs]
    exact Work.Diff.C.dmRadialOrthogonal (I := I) (M := M) (cov := cov) hmet htor (p := q)
      (d := s) (u := v) (η := ξ) hv hξ
  -- ## the varied rays out of `q` are smooth
  have hcsm : ∀ s ∈ Set.Ioo (0 : ℝ) t, ContMDiff (modelWithCornersSelf ℝ ℝ) I ∞
      (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • (v + r • ξ))) := by
    intro s hs r
    have hfam := Submission.RayJacobi.contMDiffAt_GExp_family (cov := cov) hmet (p := q)
      (u := v) (η := ξ) s r
    have hpair : ContMDiffAt (modelWithCornersSelf ℝ ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
        (fun r' : ℝ => (s, r')) r := by
      rw [contMDiffAt_iff_contDiffAt]
      fun_prop
    exact (hfam.comp r hpair).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun r' => rfl)
  -- ## the bridge identity
  have hbridge : ∀ s ∈ Set.Ioo (0 : ℝ) t, Inner.inner ℝ
      (Submission.JacobiGlobal.covAlong cov
        (γ := fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (r • v)) J s) (J s)
      = Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
          (Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) (J s) (J s) := by
    intro s hs
    by_cases hz : J s = 0
    · rw [hz]
      simp only [Work.Diff.C.rhess, inner_zero_right, map_zero]
    · exact Work.Diff.C.dmRadialBridge (I := I) (M := M) (cov := cov) hmet htor (p := q)
        (d := s) hs.1 (u := v) (η := ξ) hv hξ (hsm_s s hs) (hgrad_eq s hs) (hcsm s hs) hz
        (tc_minW_gam (cov := cov) hmet htor hcut hv1 hs.1 (hrdρ s hs))
  -- ## the shape-operator bound
  have hshape : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      (Real.cot s - ε₁ / Real.sin s) * Inner.inner ℝ (J s) (J s)
      ≤ Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
          (Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) (J s) (J s) := by
    intro s hs
    have hsρ : s < rho0 c := hrdρ s hs
    have hx : -1 + c < fcos (I := I) (M := M) q
        (Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) := by
      have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := s) (y := rho0 c) hs.1.le hρ₀π' hsρ
      rw [hρ₀cos] at h
      have hfcos : fcos (I := I) (M := M) q
          (Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) = Real.cos s := by
        rw [show fcos (I := I) (M := M) q
              (Submission.GlobalExp.GExp (cov := cov) hmet q (s • v))
            = Real.cos (rdist (I := I) (M := M) q
                (Submission.GlobalExp.GExp (cov := cov) hmet q (s • v))) from rfl,
          hrd s hs]
      rw [hfcos]
      exact h
    have hV : Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q)
        (Submission.GlobalExp.GExp (cov := cov) hmet q (s • v))) (J s) = 0 := by
      rw [Work.Diff.C.rgrad_fcos (I := I) (M := M) (q := q) (hsm_s s hs), real_inner_smul_left,
        real_inner_comm, hperp s hs, mul_zero]
    have hb := Work.Diff.C.rhess_rdist_bound_of_hHess (I := I) (M := M) (cov := cov) (c := c)
      (ε := ε₁) (q := q) (hHess q) (x := Submission.GlobalExp.GExp (cov := cov) hmet q (s • v))
      hx (hsm_s s hs) (by rw [hrd s hs]; exact hs.1)
      (by rw [hrd s hs]; exact lt_of_lt_of_le hsρ hρ₀π') (J s) hV
    rw [hrd s hs] at hb
    have hJJ : Inner.inner ℝ (J s) (J s) = ‖J s‖ * ‖J s‖ := by
      rw [real_inner_self_eq_norm_sq]; ring
    rw [hJJ] at hb ⊢
    have h1 := (abs_le.mp hb).1
    have h2 : (Real.cot s - ε₁ / Real.sin s) * (‖J s‖ * ‖J s‖)
        = Real.cot s * (‖J s‖ * ‖J s‖) - (ε₁ / Real.sin s) * (‖J s‖ * ‖J s‖) := by ring
    linarith [h1, h2]
  -- ## the Sturm comparison
  exact Work.Diff.C.no_conjTime_le_arccos (I := I) (M := M) (cov := cov) hmet htor hε₁ hρ₀π hv1
    ht0 htρ hJ hJ0 hJd hne hperp hbridge hshape

end Work.Diff.C.geoCrux.sharp
