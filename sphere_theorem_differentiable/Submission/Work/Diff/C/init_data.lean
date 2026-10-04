import Mathlib
import Submission.Work.Diff.C.Setup
-- `inner_rgrad_mvfderiv'` is declared in `ray_cos_compare`; it used to be *duplicated* here, which
-- made it impossible for any module to import both `init_data` and `ray_cos_compare` (Lean:
-- "… has already been declared").  We re-export it by import instead of re-declaring it.
import Submission.Work.Diff.C.ray_cos_compare
import Submission.LensLoop
import Submission.GExpVelocity
import Submission.GExpRay2
import Submission.Work.OddBound.pvCrux.edist_GExp_ray_sub
import Submission.Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve
import Submission.EDist

set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.GlobalExp Submission.Geodesic

namespace Work.Diff.C

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-- `rdist` is symmetric. -/
theorem rdist_comm' (x y : M) : rdist (I := I) x y = rdist (I := I) y x := by
  rw [rdist, rdist, Manifold.riemannianEDist_comm]

/-- The ray `s ↦ GExp x (s • v)` of the global exponential map is differentiable at `0`. -/
theorem init_ray_mdiffAt (hmet : IsMetricCompatible cov) (x : M) (v : TangentSpace I x) :
    MDifferentiableAt 𝓘(ℝ) I (fun s : ℝ => GExp (cov := cov) hmet x (s • v)) 0 := by
  rcases eq_or_ne v 0 with rfl | hv
  · have hconst : (fun s : ℝ => GExp (cov := cov) hmet x (s • (0 : TangentSpace I x)))
        = fun _ : ℝ => x := by
      funext s
      rw [smul_zero, GExp_zero]
    rw [hconst]
    exact mdifferentiableAt_const
  · exact ((Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet x hv).contMDiffAt
      Filter.univ_mem).mdifferentiableAt (by simp)

/-- The distance between two points of a ray, in the `rdist` vocabulary. -/
theorem init_rdist_ray_sub (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (p : M) {ρ : ℝ} (hInj : Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet p ρ)
    (hρ : Real.pi / 2 < ρ) {v : TangentSpace I p} (hv : ‖v‖ = 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ Real.pi / 2) :
    rdist (I := I) (GExp (cov := cov) hmet p (t • v))
      (GExp (cov := cov) hmet p ((Real.pi / 2) • v)) = Real.pi / 2 - t := by
  have hpi : 0 < Real.pi / 2 := by positivity
  have hne : Real.pi / 2 ≠ 0 := ne_of_gt hpi
  have hnorm : ‖(Real.pi / 2) • v‖ = Real.pi / 2 := by
    rw [norm_smul, Real.norm_of_nonneg hpi.le, hv, mul_one]
  have hkey := Work.OddBound.pvCrux.edist_GExp_ray_sub (cov := cov) hmet htor
    (p := p) (ρ := ρ) hInj (v := (Real.pi / 2) • v) (by rw [hnorm]; exact hρ.le)
    (a := t / (Real.pi / 2)) (b := 1) (by positivity) (by rw [div_le_one hpi]; exact ht) le_rfl
  have h1 : (t / (Real.pi / 2)) • ((Real.pi / 2) • v) = t • v := by
    rw [smul_smul, div_mul_cancel₀ t hne]
  have h2 : (1 : ℝ) • ((Real.pi / 2) • v) = (Real.pi / 2) • v := one_smul _ _
  rw [h1, h2] at hkey
  simp only [hnorm, mul_one] at hkey
  have harg : (1 - t / (Real.pi / 2)) * (Real.pi / 2) = Real.pi / 2 - t := by
    field_simp
  rw [harg] at hkey
  rw [rdist, hkey, ENNReal.toReal_ofReal (by linarith)]

/-- The chart distance bounds `rdist` near the base point. -/
theorem init_rdist_le_chart (p : M) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ y in 𝓝 p,
      rdist (I := I) p y ≤ C * ‖extChartAt I p y - extChartAt I p p‖ := by
  haveI hcont : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I) (M := M)
  obtain ⟨C, hCpos, hC⟩ := eventually_riemannianEDist_le_edist_extChartAt (I := I) (M := M) p
  refine ⟨(C : ℝ), by exact_mod_cast hCpos, ?_⟩
  filter_upwards [hC] with y hy
  have hfin : ((C : ℝ≥0∞) * edist (extChartAt I p p) (extChartAt I p y)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top
      (by rw [edist_dist]; exact ENNReal.ofReal_ne_top)
  have h1 : rdist (I := I) p y
      ≤ ((C : ℝ≥0∞) * edist (extChartAt I p p) (extChartAt I p y)).toReal := by
    rw [rdist]
    exact ENNReal.toReal_mono hfin hy
  have h2 : ((C : ℝ≥0∞) * edist (extChartAt I p p) (extChartAt I p y)).toReal
      = (C : ℝ) * ‖extChartAt I p y - extChartAt I p p‖ := by
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal, edist_dist,
      ENNReal.toReal_ofReal dist_nonneg, dist_eq_norm, norm_sub_rev]
  linarith [h1, h2.le]

-- `⟪rgrad F x, v⟫ = mvfderiv I F x v` is `Work.Diff.C.inner_rgrad_mvfderiv'`, declared in
-- `Submission.Work.Diff.C.ray_cos_compare` (imported above; declared there and not here, so that
-- both modules can be imported together), and used just below.

/-- The chain rule for `cos` at the level of gradients. -/
theorem init_rgrad_cos_comp {g : M → ℝ} {x : M} (hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g x) :
    rgrad (I := I) (fun y : M => Real.cos (g y)) x = - Real.sin (g x) • rgrad (I := I) g x := by
  have hcos_md : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.cos (g x) :=
    Real.differentiableAt_cos.mdifferentiableAt
  have key : ∀ v : TangentSpace I x,
      mvfderiv I (fun y : M => Real.cos (g y)) x v = - Real.sin (g x) * mvfderiv I g x v := by
    intro v
    have h := mvfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := I)
      (f := g) (g := Real.cos) x hcos_md hg v
    have hscal : (mvfderiv (I := 𝓘(ℝ, ℝ)) Real.cos (g x)) ((mfderiv% g x) v)
        = - Real.sin (g x) * mvfderiv I g x v := by
      have h1 : (mvfderiv (I := 𝓘(ℝ, ℝ)) Real.cos (g x)) ((mfderiv% g x) v)
          = (fderiv ℝ Real.cos (g x)) ((mfderiv% g x) v) :=
        congrArg (fun L : ℝ →L[ℝ] ℝ => L ((mfderiv% g x) v)) mvfderiv_eq_fderiv
      rw [h1, show (mfderiv% g x) v = mvfderiv I g x v from rfl,
        (Real.hasDerivAt_cos (g x)).hasFDerivAt.fderiv,
        ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
      ring
    exact h.trans hscal
  refine ext_inner_left ℝ (fun v => ?_)
  rw [real_inner_comm (x := rgrad (I := I) (fun y : M => Real.cos (g y)) x) (y := v),
    inner_rgrad_mvfderiv', key v, inner_smul_right,
    real_inner_comm (x := rgrad (I := I) g x) (y := v), inner_rgrad_mvfderiv']

/-- A function with a quadratic bound at a point has gradient `0` there. -/
theorem init_rgrad_eq_zero_of_quad {F : M → ℝ} {x : M}
    (hbd : ∃ C : ℝ, ∀ᶠ y in 𝓝 x,
      |F y - F x| ≤ C * ‖extChartAt I x y - extChartAt I x x‖ ^ 2) :
    rgrad (I := I) F x = 0 := by
  obtain ⟨C, hC⟩ := hbd
  set C' : ℝ := max C 1 with hC'def
  have hC'1 : (1 : ℝ) ≤ C' := le_max_right _ _
  have hC'pos : 0 < C' := lt_of_lt_of_le one_pos hC'1
  have hCC' : C ≤ C' := le_max_left _ _
  have hCbound : ∀ᶠ y in 𝓝 x, |F y - F x| ≤ C' * ‖extChartAt I x y - extChartAt I x x‖ ^ 2 :=
    hC.mono (fun y hy => hy.trans (mul_le_mul_of_nonneg_right hCC' (sq_nonneg _)))
  set Z : E := (extChartAt I x) x with hZdef
  have hZtgt : Z ∈ (extChartAt I x).target := by
    rw [hZdef]; exact mem_extChartAt_target x
  have hsymmZ : (extChartAt I x).symm Z = x := by
    rw [hZdef]; exact PartialEquiv.left_inv _ (mem_extChartAt_source x)
  have hcont_symm : ContinuousAt (extChartAt I x).symm Z := by
    rw [hZdef]; exact continuousAt_extChartAt_symm x
  have htend : Tendsto (extChartAt I x).symm (𝓝 Z) (𝓝 x) := by
    have h := hcont_symm.tendsto
    rwa [hsymmZ] at h
  have hpull : ∀ᶠ z in 𝓝 Z,
      |F ((extChartAt I x).symm z) - F x| ≤ C' * ‖z - Z‖ ^ 2 := by
    have h1 : ∀ᶠ z in 𝓝 Z, |F ((extChartAt I x).symm z) - F x|
        ≤ C' * ‖(extChartAt I x) ((extChartAt I x).symm z) - (extChartAt I x) x‖ ^ 2 :=
      htend.eventually hCbound
    filter_upwards [h1, (isOpen_extChartAt_target x).mem_nhds hZtgt] with z hz hzt
    have hzbar : (extChartAt I x) ((extChartAt I x).symm z) = z := PartialEquiv.right_inv _ hzt
    calc |F ((extChartAt I x).symm z) - F x|
        ≤ C' * ‖(extChartAt I x) ((extChartAt I x).symm z) - (extChartAt I x) x‖ ^ 2 := hz
      _ = C' * ‖z - Z‖ ^ 2 := by rw [hzbar, ← hZdef]
  have hderiv : HasFDerivAt (fun z : E => F ((extChartAt I x).symm z)) (0 : E →L[ℝ] ℝ) Z := by
    rw [hasFDerivAt_iff_isLittleO]
    refine Asymptotics.IsLittleO.of_bound ?_
    intro c hc
    have hδ : 0 < min 1 (c / C') := lt_min one_pos (div_pos hc hC'pos)
    filter_upwards [hpull, Metric.ball_mem_nhds Z hδ] with z hz hzball
    rw [Metric.mem_ball, dist_eq_norm] at hzball
    have hlec : ‖z - Z‖ ≤ c / C' := le_trans hzball.le (min_le_right _ _)
    have hlast : C' * ‖z - Z‖ ^ 2 ≤ c * ‖z - Z‖ := by
      have hstep : C' * ‖z - Z‖ ^ 2 ≤ C' * ‖z - Z‖ * (c / C') := by
        rw [show C' * ‖z - Z‖ ^ 2 = (C' * ‖z - Z‖) * ‖z - Z‖ by ring]
        exact mul_le_mul_of_nonneg_left hlec (by positivity)
      have hsimp : C' * ‖z - Z‖ * (c / C') = c * ‖z - Z‖ := by field_simp
      linarith [hstep, hsimp.le, hsimp.ge]
    have heq : F ((extChartAt I x).symm z) - F ((extChartAt I x).symm Z)
        - (0 : E →L[ℝ] ℝ) (z - Z) = F ((extChartAt I x).symm z) - F x := by
      rw [hsymmZ]
      simp
    rw [heq, Real.norm_eq_abs]
    exact hz.trans hlast
  have hcontF : ContinuousAt F x := by
    have h2 : Tendsto (fun y : M => extChartAt I x y) (𝓝 x) (𝓝 ((extChartAt I x) x)) :=
      (continuousAt_extChartAt x).tendsto
    have h3 : Tendsto (fun y : M => ‖extChartAt I x y - (extChartAt I x) x‖) (𝓝 x) (𝓝 0) := by
      have h := (h2.sub (tendsto_const_nhds :
        Tendsto (fun _ : M => (extChartAt I x) x) (𝓝 x) (𝓝 ((extChartAt I x) x)))).norm
      simpa using h
    have h4 : Tendsto (fun y : M => C' * ‖extChartAt I x y - (extChartAt I x) x‖ ^ 2)
        (𝓝 x) (𝓝 0) := by
      have h := (tendsto_const_nhds : Tendsto (fun _ : M => C') (𝓝 x) (𝓝 C')).mul (h3.pow 2)
      simpa using h
    have h5 : Tendsto (fun y : M => |F y - F x|) (𝓝 x) (𝓝 0) :=
      squeeze_zero' (Eventually.of_forall fun y => abs_nonneg _) hCbound h4
    have h6 : Tendsto (fun y : M => F y - F x) (𝓝 x) (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simpa [Real.norm_eq_abs] using h5
    have h8 : Tendsto (fun y : M => F y) (𝓝 x) (𝓝 (F x)) := by
      have h7 := h6.add (tendsto_const_nhds :
        Tendsto (fun _ : M => F x) (𝓝 x) (𝓝 (F x)))
      simpa [sub_add_cancel] using h7
    exact h8
  have hkey : HasFDerivWithinAt (fun z : E => F ((extChartAt I x).symm z)) 0
      (Set.range I) ((extChartAt I x) x) := hderiv.hasFDerivWithinAt
  have hmf : HasMFDerivAt I 𝓘(ℝ, ℝ) F x 0 := by
    refine ⟨hcontF, ?_⟩
    have hw : writtenInExtChartAt I 𝓘(ℝ, ℝ) x F = fun z : E => F ((extChartAt I x).symm z) := by
      rw [writtenInExtChartAt, extChartAt_self_eq]
      rfl
    rw [hw]
    simp only [ContinuousLinearMap.comp_zero, ContinuousLinearMap.zero_comp]
    exact hkey
  rw [rgrad, hmf.mfderiv, map_zero]

/-- **The gradient points along the ray on which the function decreases at unit speed.** -/
theorem init_rgrad_eq_neg_of_ray {g : M → ℝ} {γ : ℝ → M} {p : M} {v : TangentSpace I p}
    (hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g p)
    (hunit : Inner.inner ℝ (rgrad (I := I) g p) (rgrad (I := I) g p) = 1)
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ 0) (hγ0 : γ 0 = p)
    (hγv : mfderiv 𝓘(ℝ) I γ 0 (1 : ℝ) = v) (hv : ‖v‖ = 1)
    (hval : ∀ᶠ t in 𝓝[≥] (0 : ℝ), g (γ t) = g p - t) :
    rgrad (I := I) g p = -v := by
  have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (g ∘ γ) 0 :=
    (hγ0 ▸ hg).comp 0 hγ
  have hderivF : HasDerivAt (g ∘ γ) (deriv (g ∘ γ) 0) 0 :=
    (mdifferentiableAt_iff_differentiableAt.mp hmd).hasDerivAt
  have hA : HasFDerivWithinAt (g ∘ γ)
      (ContinuousLinearMap.toSpanSingleton ℝ (deriv (g ∘ γ) 0)) (Set.Ici 0) 0 :=
    (hasDerivWithinAt_iff_hasFDerivWithinAt).mp hderivF.hasDerivWithinAt
  have hB : HasFDerivWithinAt (g ∘ γ) (ContinuousLinearMap.toSpanSingleton ℝ (-1))
      (Set.Ici 0) 0 := by
    have hbase : HasDerivAt (fun t : ℝ => g p - t) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_sub (g p)
    have h0 : (g ∘ γ) 0 = (fun t : ℝ => g p - t) 0 := by
      show g (γ 0) = g p - 0
      rw [hγ0, sub_zero]
    exact (hasDerivWithinAt_iff_hasFDerivWithinAt).mp
      (hbase.hasDerivWithinAt.congr_of_eventuallyEq hval h0)
  have hderivval : deriv (g ∘ γ) 0 = -1 :=
    ContinuousLinearMap.toSpanSingleton_inj.mp ((uniqueDiffWithinAt_Ici 0).eq hA hB)
  have hchain : mfderiv I 𝓘(ℝ, ℝ) g p v = deriv (g ∘ γ) 0 := by
    have h := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I) (g := g) (γ := γ)
      (t := 0) (hγ0 ▸ hg) hγ
    have h2 : (mvfderiv I g (γ 0)) ((mfderiv 𝓘(ℝ) I γ 0) (1 : ℝ)) = (mvfderiv I g p) v := by
      rw [hγ0]
      exact congrArg (fun w => (mvfderiv I g p) w) hγv
    exact h2.symm.trans h
  have hinner : Inner.inner ℝ (rgrad (I := I) g p) v = -1 := by
    rw [inner_rgrad, hchain, hderivval]
  have hv1 : Inner.inner ℝ v v = 1 := by
    rw [real_inner_self_eq_norm_sq, hv, one_pow]
  have hinner' : Inner.inner ℝ v (rgrad (I := I) g p) = -1 := by
    rw [real_inner_comm (x := rgrad (I := I) g p) (y := v)]
    exact hinner
  have hsum : Inner.inner ℝ (rgrad (I := I) g p + v) (rgrad (I := I) g p + v) = 0 := by
    simp only [inner_add_left, inner_add_right, hinner, hinner', hv1, hunit]
    ring
  have hzero : rgrad (I := I) g p + v = 0 := (inner_self_eq_zero.mp hsum)
  exact eq_neg_of_add_eq_zero_left hzero

end Helpers

theorem init_data
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {η : ℝ} (hη : 0 < η) (hη3 : η < 3)
    (hInj : Submission.InjRadius.InjAllAtLeast (I := I) (cov := cov) hmet
      (Real.pi / Real.sqrt (1 + η)))
    (hEik : EikonalInput (I := I) (M := M) cov η)
    {n : ℕ} {p : M} {e : Fin n → TangentSpace I p}
    (hON : ∀ i j, Inner.inner ℝ (e i) (e j) = if i = j then 1 else 0) :
    InitData (I := I) (M := M) (cov := cov) hmet p e := by
  -- the injectivity radius exceeds `π/2`
  have hsqrt2 : Real.sqrt (1 + η) < 2 := by
    rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 2)]
    linarith
  have hsqrtpos : 0 < Real.sqrt (1 + η) := Real.sqrt_pos_of_pos (by linarith)
  have hρgt : Real.pi / 2 < Real.pi / Real.sqrt (1 + η) := by
    have hinv : 1 / (2 : ℝ) < 1 / Real.sqrt (1 + η) :=
      one_div_lt_one_div_of_lt hsqrtpos hsqrt2
    have h := mul_lt_mul_of_pos_left hinv Real.pi_pos
    simpa [div_eq_mul_inv] using h
  -- the orthonormality data
  have he_norm : ∀ i : Fin n, ‖e i‖ = 1 := by
    intro i
    have h1 : ‖e i‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, hON i i, if_pos rfl]
    nlinarith [norm_nonneg (e i)]
  have he_ne : ∀ i : Fin n, e i ≠ 0 := by
    intro i h
    have h1 := he_norm i
    rw [h, norm_zero] at h1
    norm_num at h1
  -- the points of the construction
  have hqpt : ∀ i : Fin n,
      qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ i)
        = GExp (cov := cov) hmet p ((Real.pi / 2) • e i) := by
    intro i
    rw [qpt, dirv, Fin.cases_succ]
  have hIcc : Set.Icc (0:ℝ) (Real.pi / 2) ∈ 𝓝[Set.Ici 0] (0:ℝ) := by
    rw [mem_nhdsWithin_iff]
    refine ⟨Real.pi / 2, by positivity, fun t ht => ⟨ht.2, ?_⟩⟩
    have ht1 : t ∈ Metric.ball (0:ℝ) (Real.pi / 2) := ht.1
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt] at ht1
    exact ht1.2.le
  rw [InitData]
  refine ⟨?_, ?_, ?_⟩
  · -- `fcos p p = 1`
    have h0 : rdist (I := I) p p = 0 := by
      rw [rdist, Manifold.riemannianEDist_self, ENNReal.toReal_zero]
    show Real.cos (rdist (I := I) p p) = 1
    rw [h0, Real.cos_zero]
  · -- `rgrad (fcos p) p = 0`
    refine init_rgrad_eq_zero_of_quad (I := I) (M := M) (F := fcos (I := I) (M := M) p)
      (x := p) ?_
    obtain ⟨C, hCpos, hC⟩ := init_rdist_le_chart (I := I) (M := M) p
    refine ⟨C ^ 2 / 2, ?_⟩
    have h00 : fcos (I := I) (M := M) p p = 1 := by
      have h0 : rdist (I := I) p p = 0 := by
        rw [rdist, Manifold.riemannianEDist_self, ENNReal.toReal_zero]
      show Real.cos (rdist (I := I) p p) = 1
      rw [h0, Real.cos_zero]
    filter_upwards [hC] with y hy
    have hcos : |Real.cos (rdist (I := I) p y) - 1| ≤ (rdist (I := I) p y) ^ 2 / 2 := by
      have h1 : 1 - (rdist (I := I) p y) ^ 2 / 2 ≤ Real.cos (rdist (I := I) p y) :=
        Real.one_sub_sq_div_two_le_cos
      have h2 : Real.cos (rdist (I := I) p y) ≤ 1 := Real.cos_le_one _
      rw [abs_of_nonpos (by linarith), neg_sub]
      linarith
    have hnn : 0 ≤ rdist (I := I) p y := ENNReal.toReal_nonneg
    have hy2 : (rdist (I := I) p y) ^ 2 / 2
        ≤ (C * ‖extChartAt I p y - extChartAt I p p‖) ^ 2 / 2 := by
      nlinarith [hy, hnn, norm_nonneg (extChartAt I p y - extChartAt I p p), hCpos]
    have hfin : (C * ‖extChartAt I p y - extChartAt I p p‖) ^ 2 / 2
        = C ^ 2 / 2 * ‖extChartAt I p y - extChartAt I p p‖ ^ 2 := by ring
    show |fcos (I := I) (M := M) p y - fcos (I := I) (M := M) p p| ≤ C ^ 2 / 2 *
      ‖extChartAt I p y - extChartAt I p p‖ ^ 2
    rw [h00]
    show |Real.cos (rdist (I := I) p y) - 1| ≤ _
    linarith [hcos, hy2, hfin.le, hfin.ge]
  · -- the family at `q_i`
    intro i
    have hqi : qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ i)
        = GExp (cov := cov) hmet p ((Real.pi / 2) • e i) := hqpt i
    have hdistp : rdist (I := I) p
        (GExp (cov := cov) hmet p ((Real.pi / 2) • e i)) = Real.pi / 2 := by
      have h := init_rdist_ray_sub (I := I) (M := M) (cov := cov) hmet htor p (hInj p) hρgt
        (v := e i) (he_norm i) (t := 0) le_rfl (by positivity)
      rw [zero_smul, GExp_zero, sub_zero] at h
      exact h
    have hdistq : rdist (I := I) (GExp (cov := cov) hmet p ((Real.pi / 2) • e i)) p
        = Real.pi / 2 := by
      rw [rdist_comm']
      exact hdistp
    constructor
    · -- `fcos q_i p = 0`
      rw [hqi]
      show Real.cos (rdist (I := I)
        (GExp (cov := cov) hmet p ((Real.pi / 2) • e i)) p) = 0
      rw [hdistq, Real.cos_pi_div_two]
    · -- `rgrad (fcos q_i) p = e i`
      rw [hqi]
      set q : M := GExp (cov := cov) hmet p ((Real.pi / 2) • e i) with hqdef
      have hqdist : rdist (I := I) q p = Real.pi / 2 := by
        rw [hqdef]; exact hdistq
      have hppos : 0 < rdist (I := I) q p := by rw [hqdist]; positivity
      have hplt : rdist (I := I) q p < Real.pi / Real.sqrt (1 + η) := by
        rw [hqdist]; exact hρgt
      obtain ⟨hgsm, hunit⟩ := hEik q p hppos hplt
      have hgmd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => rdist (I := I) q y) p :=
        hgsm.mdifferentiableAt (by simp)
      have hγmd : MDifferentiableAt 𝓘(ℝ) I
          (fun s : ℝ => GExp (cov := cov) hmet p (s • e i)) 0 :=
        init_ray_mdiffAt (I := I) (M := M) (cov := cov) hmet p (e i)
      have hγ0 : (fun s : ℝ => GExp (cov := cov) hmet p (s • e i)) 0 = p := by
        show GExp (cov := cov) hmet p ((0 : ℝ) • e i) = p
        rw [zero_smul]
        exact GExp_zero hmet p
      have hγv : mfderiv 𝓘(ℝ) I
          (fun s : ℝ => GExp (cov := cov) hmet p (s • e i)) 0 (1 : ℝ) = e i := by
        rw [← curveVelocity_apply]
        exact Submission.GExpVelocity.curveVelocity_GExp_smul_zero hmet p (he_ne i)
      have hval : ∀ᶠ t in 𝓝[≥] (0 : ℝ),
          rdist (I := I) q (GExp (cov := cov) hmet p (t • e i))
            = rdist (I := I) q p - t := by
        filter_upwards [hIcc] with t ht
        have hray : rdist (I := I) (GExp (cov := cov) hmet p (t • e i)) q
            = Real.pi / 2 - t := by
          rw [hqdef]
          exact init_rdist_ray_sub (I := I) (M := M) (cov := cov) hmet htor p (hInj p) hρgt
            (v := e i) (he_norm i) ht.1 ht.2
        rw [rdist_comm', hray, hqdist]
      have hgrad : rgrad (I := I) (fun y : M => rdist (I := I) q y) p = -(e i) :=
        init_rgrad_eq_neg_of_ray (I := I) (M := M) (g := fun y : M => rdist (I := I) q y)
          (γ := fun s : ℝ => GExp (cov := cov) hmet p (s • e i)) (v := e i)
          hgmd hunit hγmd hγ0 hγv (he_norm i) hval
      have hcos := init_rgrad_cos_comp (I := I) (M := M)
        (g := fun y : M => rdist (I := I) q y) (x := p) hgmd
      show rgrad (I := I) (fcos (I := I) (M := M) q) p = e i
      rw [show fcos (I := I) (M := M) q = fun y : M => Real.cos (rdist (I := I) q y)
          from rfl,
        hcos, hqdist, Real.sin_pi_div_two, hgrad]
      simp

end Work.Diff.C
