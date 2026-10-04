import Mathlib
import Submission.Work.Diff.C.geoCrux.sharp.Defs
import Submission.Work.Diff.C.geoCrux.inj_radius_core
import Submission.Work.Diff.C.rgrad_rdist_eikonal
import Submission.Work.Diff.C.dmRadialBridge
import Submission.Work.Diff.C.rgrad_fcos

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.Diff.C.geoCrux.sharp.ray_package`

The ray package `Work.Diff.C.geoCrux.SharpRayProp`: along the unit ray `γ t = GExp q (t • v)`,
at every time `t ∈ (0, ρ₀)` with `ρ₀ = π - arccos (1-c)`, from the C-area hypotheses **alone**
(no `hcut`, no diameter bound):

* `rdist q` is `C^∞` at `γ t`;
* the ray is minimising: `rdist q (γ t) = t`;
* `∇(rdist q)(γ t) = γ'(t)`;
* orthogonality transfers from `∇(rdist q)` to `∇(fcos q)`;
* the bridge: `⟪∇Z_ξ(t), Z_ξ(t)⟫ = rhess (rdist q)(γ t)(Z_ξ(t), Z_ξ(t))` for the radial variation
  field `Z_ξ(t) = ∂_r|₀ GExp q (t • (v + r • ξ))`, `ξ ⊥ v`.

## Route

Minimality comes from `Work.Diff.C.geoCrux.InjCore.ray_minimising_upto'` — the closed/open
argument of `geoCrux/inj_radius_core.lean`, which needs only `hsmC`/`hHess`/`hcont`/`hgrad`
(never the injectivity-radius hypothesis `hcut`).  On `[0,t]` the ray is then minimising, so
`rayD = id` there; the identity `rayC t = 1` is the derivative of this identity from the left
(uniqueness of the derivative within `Iic t`), and Cauchy–Schwarz equality with the eikonal
`⟪∇d,∇d⟫ = 1` and the unit speed `‖γ'‖ = 1` gives `∇(rdist q)(γ t) = γ'(t)`.

The perturbed rays `d • (v + s • ξ)` are minimising for `s` near `0` because their norms stay
`< ρ₀` there, so `InjCore.ray_minimising_upto'` applies to the normalised direction.  Together with
`Work.Diff.C.dmRadialBridge` this gives the bridge identity (the degenerate case `Z_ξ(t) = 0` is
trivial since both sides vanish).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.C.geoCrux.sharp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-- **The perturbed rays out of `q` are smooth.**  The map
`s ↦ GExp q (d • (v + s • ξ))` is `C^∞`: it is the exponential map composed with the smooth pair
`q ↦ (d, q.2)` (`Submission.RayJacobi.contMDiffAt_GExp_family`). -/
theorem ray_csm (hmet : IsMetricCompatible cov) {q : M} {v ξ : TangentSpace I q} {d : ℝ} :
    ContMDiff (modelWithCornersSelf ℝ ℝ) I ∞
      (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet q (d • (v + s • ξ))) := by
  intro s
  have hfam := Submission.RayJacobi.contMDiffAt_GExp_family (cov := cov) hmet (p := q)
    (u := v) (η := ξ) d s
  have hpair : ContMDiffAt (modelWithCornersSelf ℝ ℝ) (𝓘(ℝ, ℝ × ℝ)) ∞
      (fun r' : ℝ ↦ (d, r')) s := by
    rw [contMDiffAt_iff_contDiffAt]
    fun_prop
  exact (hfam.comp s hpair).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r' => rfl)

/-- **Perturbed rays are minimising near the unperturbed one.**  For `0 < d < π - arccos (1-c)`,
the rays `s ↦ GExp q (d • (v + s • ξ))` are minimising at time `1` for all `s` near `0`: the norm
`‖d • (v + s • ξ)‖` stays below `ρ₀` near `s = 0`, so
`Work.Diff.C.geoCrux.InjCore.ray_minimising_upto'` applies to the normalised direction. -/
theorem ray_perturbed_min
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
    {q : M} {v : TangentSpace I q} (hv : Inner.inner ℝ v v = 1)
    {ξ : TangentSpace I q} {d : ℝ} (hd0 : 0 < d)
    (hd : d < Real.pi - Real.arccos (1 - c)) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      rdist (I := I) (M := M) q
          (Submission.GlobalExp.GExp (cov := cov) hmet q (d • (v + s • ξ)))
        = ‖d • (v + s • ξ)‖ := by
  have hv1 : ‖v‖ = 1 := by
    have h : ‖v‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hv
    nlinarith [norm_nonneg v]
  have hpath : Continuous (fun s : ℝ ↦ v + s • ξ) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hvn : Continuous (fun s : ℝ ↦ ‖v + s • ξ‖) := continuous_norm.comp hpath
  have hsmall : ∀ᶠ s in 𝓝 (0 : ℝ), d * ‖v + s • ξ‖ < Real.pi - Real.arccos (1 - c) := by
    refine (continuous_const.mul hvn).continuousAt (isOpen_Iio.mem_nhds ?_)
    show d * ‖v + (0 : ℝ) • ξ‖ < Real.pi - Real.arccos (1 - c)
    rw [zero_smul, add_zero, hv1, mul_one]
    exact hd
  have hne : ∀ᶠ s in 𝓝 (0 : ℝ), (1 / 2 : ℝ) < ‖v + s • ξ‖ := by
    refine hvn.continuousAt (isOpen_Ioi.mem_nhds ?_)
    show (1 / 2 : ℝ) < ‖v + (0 : ℝ) • ξ‖
    rw [zero_smul, add_zero, hv1]
    norm_num
  filter_upwards [hsmall, hne] with s hs hns
  have hwle : ‖(d • (v + s • ξ) : TangentSpace I q)‖
      ≤ Real.pi - Real.arccos (1 - c) := by
    rw [norm_smul, Real.norm_of_nonneg hd0.le]
    exact hs.le
  have hwne : (d • (v + s • ξ) : TangentSpace I q) ≠ 0 := by
    intro h0
    have h1 : v + s • ξ = 0 := by
      rcases smul_eq_zero.mp h0 with h | h
      · exact absurd h (ne_of_gt hd0)
      · exact h
    have h2 : ‖v + s • ξ‖ = 0 := by rw [h1, norm_zero]
    linarith [hns, h2]
  have hunit : Inner.inner ℝ
      (Submission.GlobalExp.unitOf (d • (v + s • ξ)) hwne)
      (Submission.GlobalExp.unitOf (d • (v + s • ξ)) hwne) = 1 := by
    rw [real_inner_self_eq_norm_sq,
      Submission.GlobalExp.unitOf_norm (d • (v + s • ξ)) hwne]
    norm_num
  have hsc : ‖(d • (v + s • ξ) : TangentSpace I q)‖
      • Submission.GlobalExp.unitOf (d • (v + s • ξ)) hwne = d • (v + s • ξ) := by
    rw [Submission.GlobalExp.unitOf, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hwne), one_smul]
  have hmin : rayD hmet q (Submission.GlobalExp.unitOf (d • (v + s • ξ)) hwne)
      ‖(d • (v + s • ξ) : TangentSpace I q)‖
      = ‖(d • (v + s • ξ) : TangentSpace I q)‖ :=
    InjCore.ray_minimising_upto' (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2
      hsmC hHess hcont hgrad hunit ‖(d • (v + s • ξ) : TangentSpace I q)‖
      ⟨norm_nonneg _, hwle⟩
  have hmin' : rdist (I := I) (M := M) q
      (Submission.GlobalExp.GExp (cov := cov) hmet q
        (‖(d • (v + s • ξ) : TangentSpace I q)‖
          • Submission.GlobalExp.unitOf (d • (v + s • ξ)) hwne))
      = ‖(d • (v + s • ξ) : TangentSpace I q)‖ := hmin
  rw [hsc] at hmin'
  exact hmin'

/-- **The gradient of the distance is the velocity of the ray.**  Along the unit ray
`γ t = GExp q (t • v)`, for `0 < t < π - arccos (1-c)`, `∇(rdist q)(γ t) = γ'(t)`.

The ray is minimising on `[0,t]` (`InjCore.ray_minimising_upto'`), so `rayD = id` there; hence the
derivative of `rayD` within `Iic t` is both `1` and `rayC t`, i.e. `rayC t = 1`.  Since `∇(rdist q)`
is a unit vector (eikonal) and `γ'` is a unit vector (unit speed), the Cauchy–Schwarz equality
identifies them. -/
theorem ray_grad_eq_vel
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
    {q : M} {v : TangentSpace I q} (hv : Inner.inner ℝ v v = 1)
    {t : ℝ} (ht0 : 0 < t) (htρ : t < Real.pi - Real.arccos (1 - c)) :
    rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
        (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v))
      = Submission.Geodesic.curveVelocity (I := I)
          (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) t := by
  have hv1 : ‖v‖ = 1 := by
    have h : ‖v‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hv
    nlinarith [norm_nonneg v]
  have hv0 : v ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hv1; norm_num at hv1
  have hρ : t ≤ Real.pi - Real.arccos (1 - c) := le_of_lt htρ
  have hmin := InjCore.ray_minimising_upto' (I := I) (M := M) (cov := cov) hmet htor hc hc1
    hε₁ hnum2 hsmC hHess hcont hgrad hv
  have hray : rayD hmet q v t = t := hmin t ⟨ht0.le, hρ⟩
  have hray' : ∀ s ∈ Set.Icc (0 : ℝ) t, rayD hmet q v s = s := fun s hs =>
    hmin s ⟨hs.1, le_trans hs.2 hρ⟩
  have hrd0 : 0 < rayD hmet q v t := by rw [hray]; exact ht0
  have hrdρ : rayD hmet q v t < Real.pi - Real.arccos (1 - c) := by rw [hray]; exact htρ
  have hRp := InjCore.ray_pointwise' (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2
    hsmC hHess hcont hgrad hv ht0 hrd0 hrdρ
  have hC1 : rayC hmet q v t = 1 := by
    have h1 : HasDerivWithinAt (rayD hmet q v) 1 (Set.Iic t) t := by
      refine (hasDerivWithinAt_id t (Set.Iic t)).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [self_mem_nhdsWithin,
          nhdsWithin_le_nhds (Ioi_mem_nhds (show t / 2 < t by linarith))] with s hs hgt
        exact hray' s ⟨le_of_lt (lt_trans (by linarith : (0 : ℝ) < t / 2) hgt), hs⟩
      · exact hray' t ⟨ht0.le, le_rfl⟩
    have h2 : HasDerivWithinAt (rayD hmet q v) (rayC hmet q v t) (Set.Iic t) t :=
      hRp.2.2.hasDerivWithinAt
    have e1 := h1.derivWithin (uniqueDiffWithinAt_Iic t)
    have e2 := h2.derivWithin (uniqueDiffWithinAt_Iic t)
    rw [e1] at e2
    exact e2.symm
  have hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z)
      (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)) :=
    InjCore.rdist_smooth_ball (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2
      hsmC hHess hcont hgrad q _ hrd0 hrdρ
  have heik : Inner.inner ℝ
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
        (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)))
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
        (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v))) = 1 :=
    Work.Diff.C.rgrad_rdist_eikonal (I := I) (M := M) (cov := cov) hmet htor
      (q := q) (x := Submission.GlobalExp.GExp (cov := cov) hmet q (t • v))
      (show rdist (I := I) (M := M) q (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)) ≠ 0
        from ne_of_gt hrd0) hsm
  have hvn : ‖Submission.Geodesic.curveVelocity (I := I)
      (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) t‖ = 1 := by
    rw [Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet q hv0
      (ne_of_gt ht0), hv1]
  have hinner : Inner.inner ℝ
      (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
        (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)))
      (Submission.Geodesic.curveVelocity (I := I)
        (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) t) = 1 := by
    rw [← hC1]
    rfl
  have hww : Inner.inner ℝ
      (Submission.Geodesic.curveVelocity (I := I)
        (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) t)
      (Submission.Geodesic.curveVelocity (I := I)
        (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) t) = 1 := by
    rw [real_inner_self_eq_norm_sq, hvn]
    norm_num
  have hzero : rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
        (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v))
      - Submission.Geodesic.curveVelocity (I := I)
          (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) t = 0 := by
    have h2 : ‖rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
          (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v))
        - Submission.Geodesic.curveVelocity (I := I)
            (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) t‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right]
      rw [heik, hinner, hww,
        real_inner_comm
          (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
            (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)))
          (Submission.Geodesic.curveVelocity (I := I)
            (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) t),
        hinner]
      ring
    have h3 : ‖rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
          (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v))
        - Submission.Geodesic.curveVelocity (I := I)
            (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) t‖ = 0 := by
      nlinarith [norm_nonneg (rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
        (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v))
        - Submission.Geodesic.curveVelocity (I := I)
            (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) t)]
    exact norm_eq_zero.mp h3
  exact sub_eq_zero.mp hzero

/-- **The ray package.**  See `Work.Diff.C.geoCrux.SharpRayProp`. -/
theorem ray_package : Work.Diff.C.geoCrux.SharpRayProp := by
  intro E iE1 iE2 iE3 iE4 H iH I M iM1 iM2 iM3 iM4 iRB iCM iBL iNE iCS iPC cov iCD
    hmet htor c ε₁ hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad q v hv t ht0 htρ
  have hray : rayD hmet q v t = t :=
    InjCore.ray_minimising_upto' (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2
      hsmC hHess hcont hgrad hv t ⟨ht0.le, le_of_lt htρ⟩
  have hrd0 : 0 < rayD hmet q v t := by rw [hray]; exact ht0
  have hrdρ : rayD hmet q v t < Real.pi - Real.arccos (1 - c) := by rw [hray]; exact htρ
  have hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z)
      (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)) :=
    InjCore.rdist_smooth_ball (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2
      hsmC hHess hcont hgrad q (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)) hrd0 hrdρ
  have hgrad_eq : rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z)
      (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v))
      = Submission.Geodesic.curveVelocity (I := I)
          (fun s : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) t :=
    ray_grad_eq_vel (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hv ht0 htρ
  refine ⟨hsm, hray, hgrad_eq, ?_, ?_⟩
  · intro V hV
    rw [Work.Diff.C.rgrad_fcos (I := I) (M := M) (q := q) hsm, real_inner_smul_left, hV, mul_zero]
  · intro ξ hξ
    by_cases h0 : fv (cov := cov) hmet q v ξ t = 0
    · rw [h0]
      simp only [Work.Diff.C.rhess, inner_zero_right, map_zero]
    · refine Work.Diff.C.dmRadialBridge (I := I) (M := M) (cov := cov) hmet htor (p := q)
        (d := t) ht0 (u := v) (η := ξ) hv hξ hsm hgrad_eq ?_ ?_ ?_
      · exact ray_csm (cov := cov) hmet (d := t)
      · simpa only [fv] using h0
      · exact ray_perturbed_min (cov := cov) hmet htor hc hc1 hε₁ hnum2 hsmC hHess hcont
          hgrad hv ht0 htρ

end Work.Diff.C.geoCrux.sharp
