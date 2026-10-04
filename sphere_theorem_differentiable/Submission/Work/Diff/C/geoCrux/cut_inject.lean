import Mathlib
import Submission.Work.Diff.C.geoCrux.RauchInputDefs
import Submission.CutStep3
import Submission.SingularConj
import Submission.Work.Diff.C.no_conjTime_le_arccos
import Submission.Work.Diff.C.geoCrux.RadialKit
import Submission.Work.Diff.C.dmRadialBridge
import Submission.Work.Diff.C.ray_minimising_near_perturbation
import Submission.Work.Diff.C.geoCrux.CutDefs
import Submission.Work.Diff.C.rgrad_fcos
import Submission.Work.Diff.C.far_sphere_size

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `CutInjectProp`: no cut point before `π - arccos (1-c)`

The target `Work.Diff.C.GeoCrux.CutInjectProp` says that the exponential map at every point `q` is
injective on the ball of radius `ρ₀ = π - arccos (1-c)`, given the hypothesis package of the
classical high-pinching endgame (`hHess` for `fcos q`, `hgrad`, `hsmC`, `hcont`, `diam ≤ π` and
`4 ε₁ π < c`).

## Route (the classical cut-point analysis)

Let `m` be the **maximal** injectivity radius at `q`
(`Submission.InjRadius.exists_injAtLeast_max`).  We show `ρ₀ ≤ m`; the claim follows from
`Submission.InjRadius.injAtLeast_mono`.

Assume `m < ρ₀`.  By Klingenberg's lemma in the form
`Submission.CutStep3.exists_two_minimising_of_hloc_sphere` — which needs only the *local*
injectivity of `GExp q` at the vectors of norm `m` — we get two distinct **minimising** vectors
`u ≠ v` of norm `m` with the same image.

* *The two-minimising alternative* is excluded by `Work.Diff.C.GeoCrux.false_of_two_minimising`
  (`two_min_kill`): at the common endpoint `rdist q` is `C^∞` (it lies strictly inside the ball of
  radius `ρ₀`, `Work.Diff.C.GeoCrux.rdist_smooth_eikonal`) with unit gradient
  (`Work.Diff.C.rgrad_rdist_eikonal`), so the chain rule identifies both arrival velocities with
  `∇ (rdist q)` and two geodesics with the same value and velocity coincide.

* *The local-injectivity input* `hloc` is the non-conjugacy statement (`no_conj_at_inj_aux`): if
  `GExp q` were **not** locally injective at `w` with `‖w‖ = m`, then `d (GExp q)` would be singular
  at `w` (a `C^1` map with injective derivative is locally injective,
  `Submission.GExpLocalInj.locallyInjectiveAtGExp_of_injective_mfderiv`, contrapositive), so
  `Submission.RayConj.exists_ne_zero_apply_eq_zero` produces a non-zero kernel vector `ξ`.  With
  `η := m⁻¹ • ξ`, the radial variation field `J s = ∂_r GExp q (s • (ξ' + r • η))|_0`
  (`ξ' = unitOf w`) vanishes at `s = m` (chain rule,
  `Submission.ChartGeoAt.curveVelocity_eq_mfderiv_comp`, plus the kernel condition), and the Gauss
  pairing `Work.Diff.C.ShapeAux.gauss_pairing_scalar` reads `⟪J m, γ'(m)⟫ = m ⟪η, ξ'⟫`, so
  `η ⊥ ξ'`.  Then `NoConjAtInjProp` (the Sturm comparison `Work.Diff.C.no_conjTime_le_arccos`,
  started at the *first* zero of `J`) gives the contradiction.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

namespace Work.Diff.C.geoCrux

/-- **The two-minimising alternative of Klingenberg's lemma is impossible below `ρ₀`.**

Direct application of `Work.Diff.C.GeoCrux.false_of_two_minimising`: at the common endpoint of the
two minimising rays `rdist q` is smooth (the endpoint is strictly inside the ball of radius `ρ₀`)
with unit gradient. -/
theorem two_min_kill : TwoMinKillProp := by
  intro E iE1 iE2 iE3 iE4 H iH I M iM1 iM2 iM3 iM4 iRB iCM iBL iNE iCS iPC cov iCD
    hmet htor c ε₁ hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hdiam q m hm0 hmρ u v
    huv hG hun hvn hminu
  haveI : RegularSpace M := inferInstance
  have hminu' : Manifold.riemannianEDist I q (Submission.GlobalExp.GExp (cov := cov) hmet q u)
      = ENNReal.ofReal ‖u‖ := by rw [hminu, hun]
  have hminv : Manifold.riemannianEDist I q (Submission.GlobalExp.GExp (cov := cov) hmet q v)
      = ENNReal.ofReal ‖v‖ := by rw [← hG, hminu', hun, hvn]
  have hrd : rdist (I := I) (M := M) q (Submission.GlobalExp.GExp (cov := cov) hmet q u) = m := by
    rw [Work.Diff.C.rdist, hminu, ENNReal.toReal_ofReal (le_of_lt hm0)]
  have hy0 : 0 < rdist (I := I) (M := M) q (Submission.GlobalExp.GExp (cov := cov) hmet q u) := by
    rw [hrd]; exact hm0
  have hyπ : rdist (I := I) (M := M) q (Submission.GlobalExp.GExp (cov := cov) hmet q u)
      < Real.pi - Real.arccos (1 - c) := by rw [hrd]; exact hmρ
  have hsm := Work.Diff.C.GeoCrux.rdist_smooth_eikonal (I := I) (M := M) (cov := cov) hmet htor
    hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hdiam q
    (Submission.GlobalExp.GExp (cov := cov) hmet q u) hy0 hyπ
  have heik := Work.Diff.C.rgrad_rdist_eikonal (I := I) (M := M) (cov := cov) hmet htor
    (q := q) (x := Submission.GlobalExp.GExp (cov := cov) hmet q u)
    (by rw [hrd]; exact ne_of_gt hm0) hsm
  exact Work.Diff.C.GeoCrux.false_of_two_minimising (I := I) (M := M) (cov := cov) hmet htor
    huv hG hminu' hminv hsm heik

/-- **No conjugate time below `ρ₀` for the radial variation fields** (`NoConjAtInjProp`).

The radial variation field `J s = ∂_r GExp q (s • (ξ + r • η))|_0` is a Jacobi field along the ray
`γ s = GExp q (s • ξ)`, with `J 0 = 0`, `J ≢ 0` near `0`
(`Submission.SingularConj.exists_pos_variation_ne_zero`) and `J m = 0`.  Let `t₀` be the **first**
zero of `J` after `0`: on `(0,t₀)` the field does not vanish, so the bridge identity
`⟪∇J, J⟫ = Hess (rdist q)(J,J)` (`Work.Diff.C.dmRadialBridge`), the Gauss pairing
(`Work.Diff.C.ShapeAux.gauss_pairing_scalar`, which gives `J t ⊥ γ'(t)` because `η ⊥ ξ`) and the
shape-operator bound (`Work.Diff.C.rhess_rdist_bound_of_hHess`) are all available on `(0,t₀)`, and
`Work.Diff.C.no_conjTime_le_arccos` delivers the contradiction. -/
theorem no_conj_at_inj_aux : NoConjAtInjProp := by
  intro E iE1 iE2 iE3 iE4 H iH I M iM1 iM2 iM3 iM4 iRB iCM iBL iNE iCS iPC cov iCD
    hmet htor c ε₁ hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hdiam q m hm0 hmρ hinj ξ η
    hξ hη horth hJm
  haveI : RegularSpace M := inferInstance
  have hξ0 : ξ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hξ
    norm_num at hξ
  have hξin : Inner.inner ℝ ξ ξ = 1 := by
    rw [real_inner_self_eq_norm_sq, hξ]
    norm_num
  have harccos_pos : 0 < Real.arccos (1 - c) := Real.arccos_pos.mpr (by linarith)
  have hLpi : Real.pi - Real.arccos (1 - c) < Real.pi := sub_lt_self _ harccos_pos
  -- the radial variation field
  set J : (t : ℝ) → TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)) :=
    fun t => Submission.Geodesic.curveVelocity (I := I) (M := M)
      (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • (ξ + r • η))) 0 with hJdef
  have hJm' : J m = 0 := by
    rw [hJdef]
    exact hJm
  have hJ0 : J 0 = 0 := by
    change Submission.Geodesic.curveVelocity (I := I) (M := M)
      (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q
        ((0 : ℝ) • (ξ + r • η))) 0 = 0
    have hev : (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q
        ((0 : ℝ) • (ξ + r • η))) =ᶠ[𝓝 (0 : ℝ)] (fun _ : ℝ => q) := by
      filter_upwards with r
      rw [zero_smul, Submission.GlobalExp.GExp_zero]
    rw [Submission.RayJacobi.curveVelocity_congr (I := I) hev]
    exact Submission.Geodesic.curveVelocity_const (I := I) q 0
  have hJac : ∀ s : ℝ, Submission.RauchGlobal.IsJacobiAt cov
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • ξ)) J s := by
    intro s
    rw [hJdef]
    exact Submission.RayJacobi.isJacobiAt_GExp_variation (cov := cov) hmet htor hξ0 hξ s
  have hcontJ : Continuous (fun s : ℝ => Inner.inner ℝ (J s) (J s)) :=
    continuous_iff_continuousAt.mpr fun s =>
      Submission.RauchGlobal.continuousAt_inner_self_of_isJacobiAt (cov := cov) (hJac s)
  -- `J` does not vanish near `0`
  obtain ⟨δ, hδpos, hδne⟩ := Submission.SingularConj.exists_pos_variation_ne_zero
    (I := I) (M := M) (cov := cov) hmet hξ hη
  have hδm : δ ≤ m := by
    by_contra hcon
    rw [not_le] at hcon
    exact hδne m ⟨hm0, hcon⟩ hJm
  -- the first zero of `J` after `0`
  set Z : Set ℝ := {s : ℝ | s ∈ Set.Icc δ m ∧ Inner.inner ℝ (J s) (J s) = 0} with hZ
  have hZne : Z.Nonempty :=
    ⟨m, ⟨⟨hδm, le_rfl⟩, by rw [hJm', inner_self_eq_zero.mpr rfl]⟩⟩
  have hZclosed : IsClosed Z := by
    rw [hZ]
    exact isClosed_Icc.inter (isClosed_eq hcontJ continuous_const)
  have hZbdd : BddBelow Z := by
    refine ⟨δ, fun s hs => ?_⟩
    rw [hZ] at hs
    exact hs.1.1
  set t₀ : ℝ := sInf Z with ht₀def
  have ht₀Z : t₀ ∈ Z := hZclosed.csInf_mem hZne hZbdd
  have ht₀ge : δ ≤ t₀ := ht₀Z.1.1
  have ht₀pos : 0 < t₀ := lt_of_lt_of_le hδpos ht₀ge
  have ht₀le : t₀ ≤ m := ht₀Z.1.2
  have hJt₀ : J t₀ = 0 := inner_self_eq_zero.mp ht₀Z.2
  have hne₀ : ∀ s ∈ Set.Ioo (0 : ℝ) t₀, J s ≠ 0 := by
    intro s hs hzero
    have hsz : s ∈ Z := by
      refine ⟨⟨?_, le_of_lt (lt_of_lt_of_le hs.2 ht₀le)⟩, ?_⟩
      · by_contra hlt
        rw [not_le] at hlt
        exact (hδne s ⟨hs.1, hlt⟩) hzero
      · rw [hzero, inner_self_eq_zero.mpr rfl]
    have hle : t₀ ≤ s := by
      rw [ht₀def]
      exact csInf_le hZbdd hsz
    exact absurd hle (not_le.mpr hs.2)
  -- ## the geometry along the ray below `t₀`
  have hmin_t : ∀ t ∈ Set.Ioo (0 : ℝ) t₀,
      Manifold.riemannianEDist I q (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ))
        = ENNReal.ofReal t := by
    intro t ht
    have htt : t < m := lt_of_lt_of_le ht.2 ht₀le
    have hnorm : ‖t • ξ‖ = t := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1, hξ, mul_one]
    have hmin := Submission.InjRadius.edist_GExp_eq_norm_of_injAtLeast (I := I) (cov := cov)
      hmet htor hinj (by rw [hnorm]; exact htt) (smul_ne_zero (ne_of_gt ht.1) hξ0)
    rwa [hnorm] at hmin
  have hrd_t : ∀ t ∈ Set.Ioo (0 : ℝ) t₀, rdist (I := I) (M := M) q
      (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)) = t := by
    intro t ht
    rw [Work.Diff.C.rdist, hmin_t t ht, ENNReal.toReal_ofReal ht.1.le]
  have hlt_ρ : ∀ t ∈ Set.Ioo (0 : ℝ) t₀, t < Real.pi - Real.arccos (1 - c) :=
    fun t ht => lt_trans (lt_of_lt_of_le ht.2 ht₀le) hmρ
  have hsm_t : ∀ t ∈ Set.Ioo (0 : ℝ) t₀, CMDiffAt ∞
      (fun z : M ↦ rdist (I := I) (M := M) q z)
      (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)) := by
    intro t ht
    exact Work.Diff.C.GeoCrux.rdist_smooth_eikonal (I := I) (M := M) (cov := cov) hmet htor
      hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hdiam q _
      (by rw [hrd_t t ht]; exact ht.1) (by rw [hrd_t t ht]; exact hlt_ρ t ht)
  have heik_t : ∀ t ∈ Set.Ioo (0 : ℝ) t₀, Inner.inner ℝ
      (Work.Diff.C.rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
        (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)))
      (Work.Diff.C.rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
        (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ))) = 1 := by
    intro t ht
    exact Work.Diff.C.rgrad_rdist_eikonal (I := I) (M := M) (cov := cov) hmet htor
      (q := q) (x := Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ))
      (by rw [hrd_t t ht]; exact ne_of_gt ht.1) (hsm_t t ht)
  have hrgrad_t : ∀ t ∈ Set.Ioo (0 : ℝ) t₀,
      Work.Diff.C.rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
        (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ))
      = Submission.Geodesic.curveVelocity (I := I) (M := M)
          (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • ξ)) t := by
    intro t ht
    have htt : t < m := lt_of_lt_of_le ht.2 ht₀le
    have hnorm : ‖t • ξ‖ = t := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1, hξ, mul_one]
    have hmin1 : Manifold.riemannianEDist I q
        (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)) = ENNReal.ofReal ‖t • ξ‖ := by
      rw [hnorm]
      exact hmin_t t ht
    have hsm1 : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z)
        (Submission.GlobalExp.GExp (cov := cov) hmet q ((1 : ℝ) • (t • ξ))) := by
      rw [one_smul]
      exact hsm_t t ht
    have hunit1 : Inner.inner ℝ
        (Work.Diff.C.rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
          (Submission.GlobalExp.GExp (cov := cov) hmet q ((1 : ℝ) • (t • ξ))))
        (Work.Diff.C.rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
          (Submission.GlobalExp.GExp (cov := cov) hmet q ((1 : ℝ) • (t • ξ)))) = 1 := by
      rw [one_smul]
      exact heik_t t ht
    have hvel := Work.Diff.C.curveVelocity_GExp_eq_smul_rgrad (I := I) (M := M) (cov := cov)
      hmet (p := q) (u := t • ξ) (smul_ne_zero (ne_of_gt ht.1) hξ0) hmin1 hsm1 hunit1
    rw [hnorm, one_smul] at hvel
    have hcurve : (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • (t • ξ)))
        = fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q ((t * s) • ξ) := by
      funext s
      congr 1
      rw [smul_smul, mul_comm]
    rw [hcurve] at hvel
    have hscale := Submission.GlobalExp.curveVelocity_comp_mul (I := I)
      (γ := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • ξ)) (c := t) (t := 1)
      ((Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet q hξ0).mdifferentiableAt
        (by decide))
    rw [hscale, mul_one] at hvel
    exact (smul_right_inj (ne_of_gt ht.1)).mp hvel.symm
  -- the Gauss pairing
  have hgauss : ∀ t ∈ Set.Ioo (0 : ℝ) t₀,
      Inner.inner ℝ (J t) (Submission.Geodesic.curveVelocity (I := I) (M := M)
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • ξ)) t)
        = t * Inner.inner ℝ η ξ := by
    intro t ht
    have hgp := Work.Diff.C.ShapeAux.gauss_pairing_scalar (I := I) (cov := cov) hmet htor t
      (u := ξ) (η := η) 0
    rw [zero_smul, add_zero] at hgp
    rw [hJdef]
    exact hgp
  have hperpVel : ∀ t ∈ Set.Ioo (0 : ℝ) t₀,
      Inner.inner ℝ (J t) (Submission.Geodesic.curveVelocity (I := I) (M := M)
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • ξ)) t) = 0 := by
    intro t ht
    rw [hgauss t ht, real_inner_comm, horth, mul_zero]
  -- the gradient of `fcos q` is orthogonal to `J t`
  have hVfcos : ∀ t ∈ Set.Ioo (0 : ℝ) t₀,
      Inner.inner ℝ (Work.Diff.C.rgrad (I := I) (M := M) (fcos (I := I) (M := M) q)
        (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ))) (J t) = 0 := by
    intro t ht
    have hrfc := Work.Diff.C.rgrad_fcos (I := I) (M := M) (q := q) (x :=
      Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)) (hsm_t t ht)
    rw [hrfc, inner_smul_left, hrgrad_t t ht, real_inner_comm]
    rw [hperpVel t ht, mul_zero]
  -- the smoothness of the varied curve
  have hcsm_t : ∀ t ∈ Set.Ioo (0 : ℝ) t₀, ContMDiff (modelWithCornersSelf ℝ ℝ) I ∞
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • (ξ + s • η))) := by
    intro t ht
    rw [← contMDiffOn_univ]
    refine Work.Diff.C.ShapeAux.contMDiffOn_of_contMDiffAt (fun s _ => ?_)
    have hpair : ContMDiffAt (modelWithCornersSelf ℝ ℝ) (𝓘(ℝ, ℝ × ℝ)) ∞
        (fun s' : ℝ => (t, s')) s := by
      have hcd : ContDiffAt ℝ ∞ (fun s' : ℝ => (t, s')) s :=
        contDiffAt_const.prodMk contDiffAt_id
      rw [contMDiffAt_iff_contDiffAt]
      exact hcd
    exact (Submission.RayJacobi.contMDiffAt_GExp_family (cov := cov) hmet (p := q) (u := ξ)
      (η := η) t s).comp s hpair
  -- the perturbed rays are minimising at scale `t`
  have hminW_t : ∀ t ∈ Set.Ioo (0 : ℝ) t₀, ∀ᶠ s in 𝓝 (0 : ℝ),
      rdist (I := I) (M := M) q
        (Submission.GlobalExp.GExp (cov := cov) hmet q (t • (ξ + s • η)))
      = ‖t • (ξ + s • η)‖ := by
    intro t ht
    have htt : t < m := lt_of_lt_of_le ht.2 ht₀le
    have hcont_n : ContinuousAt (fun s : ℝ => ‖t • (ξ + s • η)‖) 0 := by
      refine ContinuousAt.norm ?_
      exact ((continuous_const.smul (continuous_const.add (continuous_id.smul
        continuous_const))).continuousAt)
    have h0 : ‖t • (ξ + (0 : ℝ) • η)‖ = t := by
      rw [zero_smul, add_zero, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1, hξ, mul_one]
    have hlt_nhds : ∀ᶠ s in 𝓝 (0 : ℝ), ‖t • (ξ + s • η)‖ < m := by
      refine hcont_n.eventually (isOpen_Iio.mem_nhds ?_)
      show ‖t • (ξ + (0 : ℝ) • η)‖ < m
      rw [h0]
      exact htt
    have hcont2 : ContinuousAt (fun s : ℝ => ‖ξ + s • η‖) 0 := by
      refine ContinuousAt.norm ?_
      exact (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
    have hev : ∀ᶠ s in 𝓝 (0 : ℝ), ξ + s • η ≠ 0 := by
      have hpos : (0 : ℝ) < ‖ξ + (0 : ℝ) • η‖ := by
        rw [zero_smul, add_zero, hξ]
        norm_num
      filter_upwards [hcont2.eventually (isOpen_Ioi.mem_nhds hpos)] with s hs
      exact norm_pos_iff.mp hs
    filter_upwards [hlt_nhds, hev] with s hs hsne
    have hne_s : t • (ξ + s • η) ≠ 0 := smul_ne_zero (ne_of_gt ht.1) hsne
    have hmin_s := Submission.InjRadius.edist_GExp_eq_norm_of_injAtLeast (I := I) (cov := cov)
      hmet htor hinj hs hne_s
    rw [Work.Diff.C.rdist, hmin_s, ENNReal.toReal_ofReal (norm_nonneg _)]
  -- ## the three hypotheses of the Sturm comparison
  have hperp : ∀ t ∈ Set.Ioo (0 : ℝ) t₀, Inner.inner ℝ (J t)
      (Work.Diff.C.rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
        (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ))) = 0 := by
    intro t ht
    rw [hrgrad_t t ht]
    exact hperpVel t ht
  have hbridge : ∀ t ∈ Set.Ioo (0 : ℝ) t₀,
      Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J t) (J t)
        = Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
            (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)) (J t) (J t) := by
    intro t ht
    have hbr := Work.Diff.C.dmRadialBridge (I := I) (M := M) (cov := cov) hmet htor ht.1
      (u := ξ) (η := η) hξin horth (hsm_t t ht) (hrgrad_t t ht) (hcsm_t t ht)
      (hne₀ t ht) (hminW_t t ht)
    simpa [hJdef] using hbr
  have hshape : ∀ t ∈ Set.Ioo (0 : ℝ) t₀,
      (Real.cot t - ε₁ / Real.sin t) * Inner.inner ℝ (J t) (J t)
        ≤ Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
            (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)) (J t) (J t) := by
    intro t ht
    have hx : -1 + c < fcos (I := I) (M := M) q
        (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)) := by
      have hfcos : fcos (I := I) (M := M) q
          (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)) = Real.cos t := by
        rw [Work.Diff.C.fcos, hrd_t t ht]
      rw [hfcos]
      have hcosρ : Real.cos (Real.pi - Real.arccos (1 - c)) = -1 + c := by
        rw [Real.cos_pi_sub, Real.cos_arccos (by linarith) (by linarith)]
        ring
      have hlepi : Real.pi - Real.arccos (1 - c) ≤ Real.pi := by
        have h := Real.arccos_nonneg (1 - c)
        linarith
      have hlt := Real.cos_lt_cos_of_nonneg_of_le_pi ht.1.le hlepi (hlt_ρ t ht)
      linarith [hcosρ]
    have hb := Work.Diff.C.rhess_rdist_bound_of_hHess (I := I) (M := M) (cov := cov)
      (c := c) (ε := ε₁) (hHess q) hx (hsm_t t ht)
      (by rw [hrd_t t ht]; exact ht.1)
      (by rw [hrd_t t ht]; exact lt_trans (hlt_ρ t ht) hLpi) (J t) (hVfcos t ht)
    have hsq : Inner.inner ℝ (J t) (J t) = ‖J t‖ ^ 2 := real_inner_self_eq_norm_sq (J t)
    rw [hrd_t t ht] at hb
    rw [hsq] at hb ⊢
    have hnn : (0:ℝ) ≤ ‖J t‖ ^ 2 := sq_nonneg _
    have h2 : Real.cot t * ‖J t‖ ^ 2 - ε₁ / Real.sin t * ‖J t‖ ^ 2
        ≤ Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z)
            (Submission.GlobalExp.GExp (cov := cov) hmet q (t • ξ)) (J t) (J t) := by
      have := (abs_le.mp hb).1
      linarith
    have hrw : (Real.cot t - ε₁ / Real.sin t) * ‖J t‖ ^ 2
        = Real.cot t * ‖J t‖ ^ 2 - ε₁ / Real.sin t * ‖J t‖ ^ 2 := by ring
    rw [hrw]
    exact h2
  -- ## the conclusive Sturm comparison
  refine Work.Diff.C.no_conjTime_le_arccos (I := I) (M := M) (cov := cov) hmet htor hε₁ hLpi hξ
    ht₀pos (le_of_lt (lt_of_le_of_lt ht₀le hmρ)) hJac hJ0 hJt₀ ?_ hperp hbridge hshape
  refine ⟨δ / 2, ⟨by linarith, by linarith⟩, ?_⟩
  rw [hJdef]
  exact hδne (δ / 2) ⟨by linarith, by linarith⟩

/-- **The exponential map is injective below `π - arccos (1-c)`.** -/
theorem cut_inject : Work.Diff.C.GeoCrux.CutInjectProp := by
  intro E iE1 iE2 iE3 iE4 H iH I M iM1 iM2 iM3 iM4 iRB iCM iBL iNE iCS iPC cov iCD
    hmet htor c ε₁ hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hdiam q
  haveI : RegularSpace M := inferInstance
  -- the numerical data
  have hrho_pos : 0 < Real.pi - Real.arccos (1 - c) := by
    have h := Real.arccos_lt_pi.mpr (show -1 < (1 : ℝ) - c by linarith)
    linarith
  -- the diameter bound, in `edist` form
  have hdiamE : ∀ y : M, Manifold.riemannianEDist I q y ≤ ENNReal.ofReal Real.pi := by
    intro y
    have hlt : Manifold.riemannianEDist I q y < ⊤ :=
      Submission.HopfRinow.riemannianEDist_lt_top (I := I) (cov := cov) hmet htor q y
    rw [← ENNReal.ofReal_toReal hlt.ne]
    exact ENNReal.ofReal_le_ofReal (hdiam q y)
  -- the maximal injectivity radius at `q`
  obtain ⟨m, hinj, hmax⟩ :=
    Submission.InjRadius.exists_injAtLeast_max (I := I) (cov := cov) hmet (x := q)
      ⟨0, Submission.InjSup.injAtLeast_zero (I := I) (cov := cov) hmet q⟩
      ⟨Real.pi + 2, Submission.InjSup.not_injAtLeast_of_lt_diam (I := I) (cov := cov) hmet htor
        (show (0 : ℝ) < Real.pi + 1 by linarith [Real.pi_pos])
        (show Real.pi < Real.pi + 1 by linarith) hdiamE (by linarith)⟩
  have hm0ge : 0 ≤ m := by
    by_contra hcon
    rw [not_le] at hcon
    exact hmax 0 hcon (Submission.InjSup.injAtLeast_zero (I := I) (cov := cov) hmet q)
  -- the key inequality
  have hmL : Real.pi - Real.arccos (1 - c) ≤ m := by
    by_contra hcon
    have hmρ : m < Real.pi - Real.arccos (1 - c) := lt_of_not_ge hcon
    rcases eq_or_lt_of_le hm0ge with hm0eq | hm0pos
    · -- `m = 0`: the dichotomy produces `‖u‖ = ‖v‖ = 0`
      have hloc : ∀ w : TangentSpace I q, ‖w‖ = m →
          Submission.CutStep2.LocallyInjectiveAtGExp (I := I) hmet q w := by
        intro w hw
        have hw0 : w = 0 := norm_eq_zero.mp (by rw [hw, hm0eq])
        subst hw0
        refine Submission.GExpLocalInj.locallyInjectiveAtGExp_of_injective_mfderiv (I := I)
          (cov := cov) hmet ?_
        have hcast : (show E from (0 : TangentSpace I q)) = (0 : E) := rfl
        rw [hcast, Submission.GExpLocalInj.mfderiv_GExp_zero (I := I) (cov := cov) hmet q]
        exact fun a b hab => hab
      obtain ⟨u, v, huv, -, hun, hvn, -⟩ :=
        Submission.CutStep3.exists_two_minimising_of_hloc_sphere (I := I) (cov := cov) hmet htor
          hinj hmax hloc
      have hu0 : u = 0 := norm_eq_zero.mp (by rw [hun, hm0eq])
      have hv0 : v = 0 := norm_eq_zero.mp (by rw [hvn, hm0eq])
      exact huv (by rw [hu0, hv0])
    · -- `m > 0`: the merging branch is killed by the non-conjugacy statement
      have hloc : ∀ w : TangentSpace I q, ‖w‖ = m →
          Submission.CutStep2.LocallyInjectiveAtGExp (I := I) hmet q w := by
        intro w hw
        by_contra hnotinj
        have hwne : w ≠ 0 := by
          intro h0
          rw [h0, norm_zero] at hw
          linarith
        -- a non-zero kernel vector of the (singular) differential
        have hsing : ¬ (mfderiv 𝓘(ℝ, E) I
            (fun u : E => Submission.GlobalExp.GExp (cov := cov) hmet q
              (show TangentSpace I q from u))
            (show E from w)).IsInvertible :=
          Submission.GExpLocalInj.not_isInvertible_of_not_injective (I := I) (cov := cov) hmet
            (p := q) (v := w)
            (Submission.GExpLocalInj.not_injective_mfderiv_of_not_locallyInjective (I := I)
              (cov := cov) hmet (p := q) hnotinj)
        obtain ⟨ξ, hξne, hξker⟩ :=
          Submission.RayConj.exists_ne_zero_apply_eq_zero (I := I) (q := q) hsing
        set η : TangentSpace I q := m⁻¹ • (show TangentSpace I q from ξ) with heta
        have hηne : η ≠ 0 := by
          rw [heta]
          exact smul_ne_zero (inv_ne_zero (ne_of_gt hm0pos)) hξne
        have heta_eq : m • η = (show TangentSpace I q from ξ) := by
          rw [heta, smul_smul, mul_inv_cancel₀ (ne_of_gt hm0pos), one_smul]
        -- the variation field of `η` vanishes at time `m` (chain rule + kernel condition)
        have hJm : Submission.Geodesic.curveVelocity (I := I) (M := M)
            (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q
              (m • (Submission.GlobalExp.unitOf (I := I) w hwne + r • η))) 0 = 0 := by
          have h1 : HasDerivAt
              (fun r : ℝ => Submission.GlobalExp.unitOf (I := I) w hwne + r • η) η (0 : ℝ) := by
            have h := (hasDerivAt_id (0 : ℝ)).smul_const η
            simpa using h.const_add (Submission.GlobalExp.unitOf (I := I) w hwne)
          have h2 : HasDerivAt
              (fun r : ℝ => m • (Submission.GlobalExp.unitOf (I := I) w hwne + r • η))
              (m • η) (0 : ℝ) := h1.const_smul m
          have hmd : MDifferentiableAt 𝓘(ℝ, E) I
              (fun u : E => Submission.GlobalExp.GExp (cov := cov) hmet q
                (show TangentSpace I q from u))
              (show E from (m • (Submission.GlobalExp.unitOf (I := I) w hwne + (0 : ℝ) • η))) :=
            (Submission.GExpLocalInj.contMDiffAt_GExp_one (I := I) (cov := cov) hmet q
              (m • (Submission.GlobalExp.unitOf (I := I) w hwne + (0 : ℝ) • η))).mdifferentiableAt
              one_ne_zero
          have hchain := Submission.ChartGeoAt.curveVelocity_eq_mfderiv_comp (I := I)
            (f := fun u : E => Submission.GlobalExp.GExp (cov := cov) hmet q
              (show TangentSpace I q from u))
            (σ := fun r : ℝ => m • (Submission.GlobalExp.unitOf (I := I) w hwne + r • η))
            (σ' := fun _ : ℝ => (m • η : TangentSpace I q))
            (γ := fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q
              (m • (Submission.GlobalExp.unitOf (I := I) w hwne + r • η))) h2 hmd
            (Filter.Eventually.of_forall fun r => rfl)
          rw [hchain]
          rw [show m • (Submission.GlobalExp.unitOf (I := I) w hwne + (0 : ℝ) • η) = w from by
            rw [zero_smul, add_zero, Submission.GlobalExp.unitOf, smul_smul, hw,
              mul_inv_cancel₀ (ne_of_gt hm0pos), one_smul]]
          rw [heta_eq]
          exact hξker
        -- the Gauss pairing makes `η` orthogonal to the direction of the ray
        have horth : Inner.inner ℝ (Submission.GlobalExp.unitOf (I := I) w hwne) η = 0 := by
          have hgp := Work.Diff.C.ShapeAux.gauss_pairing_scalar (I := I) (cov := cov) hmet htor m
            (u := Submission.GlobalExp.unitOf (I := I) w hwne) (η := η) 0
          rw [zero_smul, add_zero] at hgp
          have hzero : m * Inner.inner ℝ η (Submission.GlobalExp.unitOf (I := I) w hwne) = 0 := by
            rw [← hgp]
            rw [hJm]
            exact inner_zero_left _
          have h0 := (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hm0pos)
          rw [real_inner_comm] at h0
          exact h0
        exact no_conj_at_inj_aux (hmet := hmet) (htor := htor) (hc := hc) (hc1 := hc1)
          (hε₁ := hε₁) (hnum2 := hnum2) hsmC hHess hcont hgrad hdiam hm0pos hmρ hinj
          (Submission.GlobalExp.unitOf_norm (I := I) w hwne) hηne horth hJm
      obtain ⟨u, v, huv, hG, hun, hvn, hminu⟩ :=
        Submission.CutStep3.exists_two_minimising_of_hloc_sphere (I := I) (cov := cov) hmet htor
          hinj hmax hloc
      exact two_min_kill (hmet := hmet) (htor := htor) (hc := hc) (hc1 := hc1) (hε₁ := hε₁)
        (hnum2 := hnum2) hsmC hHess hcont hgrad hdiam hm0pos hmρ huv hG hun hvn hminu
  exact Submission.InjRadius.injAtLeast_mono (I := I) (cov := cov) hmet hinj hmL

end Work.Diff.C.geoCrux
