import Mathlib
import Submission.Work.EvenBound.Imports
import Submission.Work.EvenBound.FarthestPoint.inner_eq_zero_of_isLocalMax_edist
import Submission.Work.EvenBound.ThirdGeodesic.tendsto_chartVel_variation
import Submission.Work.EvenBound.ThirdGeodesic.tendsto_velCoords_endpoint

namespace Work.EvenBound.ThirdGeodesic

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory
open Submission.GlobalExp Submission.Geodesic Submission.Length Submission.JacobiGlobal
  Submission.InjRadius Submission.ConjRadius Submission.CutTime Submission.ChartConnection
  Submission.JacobiCoords
open Submission.GExpJointPt

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- The distance between the endpoints of a curve is at most its length. -/
theorem edist_le_ofReal_curveLength [I.Boundaryless] {γ : ℝ → M} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (Set.Icc a b))
    (hspc : ContinuousOn (fun t : ℝ => Submission.Length.curveSpeed (I := I) γ t) (Set.Icc a b))
    (hab : a ≤ b) :
    Manifold.riemannianEDist I (γ a) (γ b)
      ≤ ENNReal.ofReal (Submission.Length.curveLength (I := I) γ a b) := by
  have h1 : Manifold.riemannianEDist I (γ a) (γ b) ≤ Manifold.pathELength I γ a b :=
    Manifold.riemannianEDist_le_pathELength hγ rfl rfl hab
  have hlen : Manifold.pathELength I γ a b
      = ENNReal.ofReal (∫ t in a..b, Submission.Length.curveSpeed (I := I) γ t) := by
    refine Commons.Geometry.Manifold.pathELength_eq_ofReal_integral_of_enorm_eq_nonneg
      (I := I) (γ := γ) (a := a) (b := b)
      (f := fun t : ℝ => Submission.Length.curveSpeed (I := I) γ t) hab
      (hspc.integrableOn_Icc) (fun t _ => Submission.Length.curveSpeed_nonneg (I := I) γ t) ?_
    intro t ht
    show ‖(mfderiv 𝓘(ℝ) I γ t) 1‖ₑ = ENNReal.ofReal (Submission.Length.curveSpeed (I := I) γ t)
    rw [Submission.Minimal.enorm_eq_ofReal_norm, Submission.GeodesicSpeed.curveSpeed_eq_norm (I := I) γ t]
    rfl
  rw [hlen] at h1
  rwa [Submission.Length.curveLength_def]

/-- `SmoothAlongAt` is preserved by rescaling the field by a constant. -/
theorem smoothAlongAt_const_smul [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {γ : ℝ → M} {V : (t : ℝ) → TangentSpace I (γ t)} {s : ℝ}
    (h : Submission.JacobiGlobal.SmoothAlongAt (I := I) γ V s) (c : ℝ) :
    Submission.JacobiGlobal.SmoothAlongAt (I := I) γ (fun t => c • V t) s := by
  obtain ⟨U, hUo, hsU, hsrc, hcd⟩ := h
  refine ⟨U, hUo, hsU, hsrc, ?_⟩
  rw [Submission.IndexScale.chartCoords_smul]
  exact hcd.const_smul c

/-- Joint convergence of the Riemannian distance. -/
theorem tendsto_riemannianEDist [RegularSpace M] {an bn : ℕ → M} {x y : M}
    (ha : Tendsto an atTop (𝓝 x)) (hb : Tendsto bn atTop (𝓝 y)) :
    Tendsto (fun n => Manifold.riemannianEDist I (an n) (bn n)) atTop
      (𝓝 (Manifold.riemannianEDist I x y)) := by
  haveI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  have hcont : Continuous (fun p : M × M => edist p.1 p.2) := continuous_edist
  have h1 : Tendsto (fun n => (an n, bn n)) atTop (𝓝 (x, y)) :=
    (Prod.tendsto_iff (fun n => (an n, bn n)) (x, y)).mpr ⟨ha, hb⟩
  have h2 := hcont.continuousAt.tendsto.comp h1
  have hxy := Submission.EDist.edist_eq_riemannianEDist (I := I) x y
  rw [hxy] at h2
  refine h2.congr' ?_
  filter_upwards with n
  exact (Submission.EDist.edist_eq_riemannianEDist (I := I) (an n) (bn n)).symm

/-- **A smooth reparametrisation of the line that is the identity near `a`** and whose values stay
in the interval `(0,1)`.  It turns a curve that is smooth only near `a` into a globally smooth one,
which is what the first-variation lemma needs (its curve is required to be `C^∞` on all of `ℝ`). -/
theorem exists_contDiff_reparam {a : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ t : ℝ, |ψ t - a| < min a (1 - a)) ∧
      (ψ =ᶠ[𝓝 a] id) ∧ ψ a = a := by
  set ε : ℝ := min a (1 - a) / 4 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith [lt_min ha.1 (by linarith [ha.2] : (0:ℝ) < 1 - a)]
  have hεlt : ε < min a (1 - a) := by
    rw [hεdef]; linarith [lt_min ha.1 (by linarith [ha.2] : (0:ℝ) < 1 - a)]
  set f : ContDiffBump (0 : ℝ) := ⟨ε / 2, ε, by linarith, by linarith⟩ with hfdef
  have hfrIn : f.rIn = ε / 2 := rfl
  have hfrOut : f.rOut = ε := rfl
  refine ⟨fun t : ℝ => a + (t - a) * f (t - a), ?_, ?_, ?_, ?_⟩
  · exact ContDiff.add contDiff_const (ContDiff.mul (contDiff_id.sub contDiff_const)
      (f.contDiff.comp (contDiff_id.sub contDiff_const)))
  · intro t
    show |a + (t - a) * f (t - a) - a| < min a (1 - a)
    have hdist : ∀ x : ℝ, dist (x - a) (0 : ℝ) = |x - a| := fun x => by
      rw [Real.dist_eq, sub_zero]
    by_cases h : ε ≤ |t - a|
    · have hz : f (t - a) = 0 := by
        rw [ContDiffBump.zero_of_le_dist (x := t - a) (c := (0 : ℝ))]
        rwa [hfrOut, hdist]
      rw [hz, mul_zero, add_zero]
      rw [sub_self, abs_zero]
      exact lt_min ha.1 (by linarith [ha.2])
    · rw [not_le] at h
      have hb : |f (t - a)| ≤ 1 := by
        rw [abs_of_nonneg f.nonneg]
        exact f.le_one
      calc |a + (t - a) * f (t - a) - a| = |t - a| * |f (t - a)| := by
            rw [add_sub_cancel_left, abs_mul]
        _ ≤ |t - a| * 1 := by
            exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        _ = |t - a| := mul_one _
        _ < ε := h
        _ ≤ min a (1 - a) := le_of_lt hεlt
  · have h1 : f =ᶠ[𝓝 (0 : ℝ)] 1 := ContDiffBump.eventuallyEq_one (c := (0 : ℝ)) f
    have h2 : Tendsto (fun t : ℝ => t - a) (𝓝 a) (𝓝 ((0 : ℝ))) := by
      have h := (tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 a) (𝓝 a)).sub_const a
      rwa [sub_self] at h
    filter_upwards [h2 h1] with t ht
    show a + (t - a) * f (t - a) = t
    rw [ht]
    simp only [Pi.one_apply, mul_one]
    ring
  · show a + (a - a) * f (a - a) = a
    rw [sub_self, zero_mul, add_zero]

/-- **`GExp` of a shrinking tangent vector converges to the base point.**  If `‖w n‖ → 0` then
`GExp z (w n) → z`.  The proof is the ray bound `d(z, GExp z v) ≤ ‖v‖` plus the fact that small
extended distances give topological convergence. -/
theorem tendsto_GExp_zero [I.Boundaryless] [Nontrivial E] [CompactSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} [ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (z : M)
    {w : ℕ → TangentSpace I z} (hw : Tendsto (fun n => ‖w n‖) atTop (𝓝 0)) :
    Tendsto (fun n => Submission.GlobalExp.GExp (cov := cov) hmet z (w n)) atTop (𝓝 z) := by
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  refine Submission.GExpJointPt.tendsto_of_eventually_edist_lt (I := I) (x := z) ?_
  intro ε hε
  filter_upwards [hw (Iio_mem_nhds hε)] with n hn
  have h3 := Submission.GExpRay2.edist_GExp_smul_le_mul_norm (cov := cov) hmet z
    (v := w n) (a := 0) (b := 1) (by norm_num) (by norm_num)
  simp only [zero_smul, one_smul, sub_zero, one_mul, GExp_zero] at h3
  refine lt_of_le_of_lt h3 ?_
  rw [ENNReal.ofReal_lt_ofReal_iff hε]
  exact hn

/-- **Polarisation identity for the chart metric.** -/
theorem chartGram_polarization (z p : M) (x y : E) :
    chartGram (I := I) z p (x + y) (x + y) - chartGram (I := I) z p (x - y) (x - y)
      = 4 * chartGram (I := I) z p x y := by
  have h1 : chartGram (I := I) z p (x + y) (x + y)
      = chartGram (I := I) z p x x + chartGram (I := I) z p x y
        + chartGram (I := I) z p y x + chartGram (I := I) z p y y := by
    rw [chartGram_add_fst, chartGram_add_snd, chartGram_add_snd]
    ring
  have h2 : chartGram (I := I) z p (x - y) (x - y)
      = chartGram (I := I) z p x x - chartGram (I := I) z p x y
        - chartGram (I := I) z p y x + chartGram (I := I) z p y y := by
    rw [sub_eq_add_neg, chartGram_add_fst, chartGram_add_snd, chartGram_add_snd,
      show (-y : E) = (-1 : ℝ) • y from (neg_one_smul ℝ y).symm]
    simp only [chartGram_smul_fst, chartGram_smul_snd]
    ring
  rw [h1, h2, chartGram_comm (I := I) z p y x]
  ring

/-- **Joint continuity of the chart metric (bilinear form).**  For `q` in the chart at `z`, the
function `(p, a, b) ↦ chartGram z p a b` is continuous at `(q, a, b)`.  This is
`continuousAt_chartGram_prod` together with the polarisation identity. -/
theorem continuousAt_chartGram3 (z : M) {q : M} (hq : q ∈ (chartAt H z).source) (a b : E) :
    ContinuousAt (fun u : (M × E) × E => chartGram (I := I) z u.1.1 u.1.2 u.2) ((q, a), b) := by
  have hF1 : ContinuousAt (fun u : (M × E) × E => (u.1.1, u.1.2 + u.2)) ((q, a), b) := by
    fun_prop
  have hF2 : ContinuousAt (fun u : (M × E) × E => (u.1.1, u.1.2 - u.2)) ((q, a), b) := by
    fun_prop
  have hP : ContinuousAt
      (fun u : (M × E) × E => chartGram (I := I) z u.1.1 (u.1.2 + u.2) (u.1.2 + u.2)) ((q, a), b) :=
    ContinuousAt.comp (f := fun u : (M × E) × E => (u.1.1, u.1.2 + u.2)) (x := ((q, a), b))
      (Submission.ChartBounds.continuousAt_chartGram_prod (I := I) z hq (a + b)) hF1
  have hM : ContinuousAt
      (fun u : (M × E) × E => chartGram (I := I) z u.1.1 (u.1.2 - u.2) (u.1.2 - u.2)) ((q, a), b) :=
    ContinuousAt.comp (f := fun u : (M × E) × E => (u.1.1, u.1.2 - u.2)) (x := ((q, a), b))
      (Submission.ChartBounds.continuousAt_chartGram_prod (I := I) z hq (a - b)) hF2
  have hΦ : (fun u : (M × E) × E => chartGram (I := I) z u.1.1 u.1.2 u.2)
      = fun u : (M × E) × E => (4 : ℝ)⁻¹ * (chartGram (I := I) z u.1.1 (u.1.2 + u.2) (u.1.2 + u.2)
          - chartGram (I := I) z u.1.1 (u.1.2 - u.2) (u.1.2 - u.2)) := by
    funext u
    have h := chartGram_polarization (I := I) z u.1.1 u.1.2 u.2
    linarith
  rw [hΦ]
  exact continuousAt_const.mul (hP.sub hM)

/-- **The "third minimal geodesic" contradiction (no curvature hypothesis).**  A `1`-periodic
closed geodesic `γ` of length `2m` (constant speed `2m` on `[0,1]`), with `p = γ 0`, `q = γ (1/2)`
and `d(p,q) = m`, at whose base point the *only* unit tangent directions `w` with
`GExp p (m • w) = q` are the two directions `±(2m)⁻¹ • γ'(0)` of `γ` itself — such a "flush" closed
geodesic **cannot be shortened by closed curves** coming from a field variation
`t ↦ GExp (γ t) (σ • (d • Z t))`. -/
theorem no_shorter_closed_of_only_two_minimising
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p q : M} {m : ℝ} (hm : 0 < m)
    (hinjall : Submission.InjRadius.InjAllAtLeast hmet m)
    (hpq : Manifold.riemannianEDist I p q = ENNReal.ofReal m)
    {γ : ℝ → M} (hγ0 : γ 0 = p) (hγhalf : γ (1 / 2) = q)
    (hper : ∀ t : ℝ, γ (t + 1) = γ t) (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hgeo : ∀ t : ℝ, Submission.Geodesic.IsGeodesicAt cov γ t)
    (hsp : ∀ t ∈ Set.Icc (0 : ℝ) 1, Submission.Length.curveSpeed (I := I) γ t = 2 * m)
    (honly : ∀ w : TangentSpace I p, ‖w‖ = 1 →
      Submission.GlobalExp.GExp (cov := cov) hmet p (m • w) = q →
      w = (2 * m)⁻¹ • Submission.Geodesic.curveVelocity (I := I) γ 0 ∨
        w = -((2 * m)⁻¹ • Submission.Geodesic.curveVelocity (I := I) γ 0))
    {Z : (t : ℝ) → TangentSpace I (γ t)} (hZ1 : Z 1 = Z 0)
    (hZsm : ∀ s ∈ Set.Icc (0 - 1) ((1 : ℝ) + 1),
      Submission.JacobiGlobal.SmoothAlongAt (I := I) γ Z s)
    {d : ℝ} (hd : 0 < d)
    (hshort : ∀ᶠ σ in 𝓝[>] (0 : ℝ),
      Submission.Length.curveLength (I := I)
        (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (γ t) (σ • (d • Z t))) 0 1 < 2 * m) :
    False := by
  classical
  subst hγ0
  subst hγhalf
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  -- ## 0. Notation
  let F : ℝ → ℝ → M := fun σ t => GExp (cov := cov) hmet (γ t) (σ • (d • Z t))
  have hγ1 : γ 1 = γ 0 := by simpa using hper 0
  have hFclosed : ∀ σ : ℝ, F σ 1 = F σ 0 := by
    intro σ
    show GExp (cov := cov) hmet (γ 1) (σ • (d • Z 1))
      = GExp (cov := cov) hmet (γ 0) (σ • (d • Z 0))
    rw [hγ1, hZ1]
  let sn : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hsn_pos : ∀ n, 0 < sn n := by intro n; simp only [sn]; positivity
  have hsn_tend : Tendsto sn atTop (𝓝 0) := by
    simpa [sn, one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  -- ## 1. Eventually the variation is strictly shorter than `2m`
  have hshort_n : ∀ᶠ n in atTop, Submission.Length.curveLength (I := I) (F (sn n)) 0 1 < 2 * m := by
    have htend : Tendsto sn atTop (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hsn_tend, Filter.Eventually.of_forall hsn_pos⟩
    exact htend.eventually hshort
  -- ## 2. Smoothness of the variation
  have hVs : ∀ s ∈ Set.Icc ((0 : ℝ) - 1) ((1 : ℝ) + 1),
      Submission.JacobiGlobal.SmoothAlongAt (I := I) γ (fun t => d • Z t) s :=
    fun s hs => smoothAlongAt_const_smul (I := I) (hZsm s hs) d
  obtain ⟨c₀, hc₀pos, hspec⟩ :=
    Submission.EnergyRaySmooth.contMDiffOn_geodesic_family (cov := cov) hmet htor
      (γ := γ) (V := fun t => d • Z t) hγsm.contMDiffOn hVs (by norm_num : (0 : ℝ) < 1)
  have hFsm : ∀ᶠ n in atTop,
      ContMDiffOn 𝓘(ℝ) I ∞ (F (sn n)) (Set.Icc 0 1) ∧
      ContinuousOn (fun t : ℝ => Submission.Length.curveSpeed (I := I) (F (sn n)) t)
        (Set.Icc 0 1) := by
    have hDpos : 0 < min 1 c₀ := lt_min one_pos hc₀pos
    have hDmem : min 1 c₀ ∈ Set.Ioc (0 : ℝ) c₀ := ⟨hDpos, min_le_right 1 c₀⟩
    have hspec' := hspec (min 1 c₀) hDmem
    have hres : Tendsto (fun n => sn n / min 1 c₀) atTop (𝓝 0) := by
      simpa using hsn_tend.div_const (min 1 c₀)
    have hfun : ∀ n, (fun t : ℝ => GExp (cov := cov) hmet (γ t)
        ((sn n / min 1 c₀) • ((min 1 c₀) • (d • Z t)))) = F (sn n) := by
      intro n; funext t
      show GExp (cov := cov) hmet (γ t) ((sn n / min 1 c₀) • ((min 1 c₀) • (d • Z t)))
        = GExp (cov := cov) hmet (γ t) (sn n • (d • Z t))
      congr 1
      rw [smul_smul, div_mul_cancel₀ _ (ne_of_gt hDpos)]
    filter_upwards [hres.eventually hspec'] with n hn
    rw [hfun n] at hn
    exact hn
  have hFsm1 : ∀ᶠ n in atTop,
      ContMDiffOn 𝓘(ℝ) I 1 (F (sn n)) (Set.Icc 0 1) ∧
      ContinuousOn (fun t : ℝ => Submission.Length.curveSpeed (I := I) (F (sn n)) t)
        (Set.Icc 0 1) :=
    hFsm.mono fun n hn => ⟨hn.1.of_le (by simp), hn.2⟩
  -- ## 3. The farthest point `tₙ` on the variation
  have hfpt : ∀ᶠ n in atTop, ∃ τ ∈ Set.Icc (0 : ℝ) 1,
      ∀ τ' ∈ Set.Icc (0 : ℝ) 1,
        Manifold.riemannianEDist I (F (sn n) 0) (F (sn n) τ')
          ≤ Manifold.riemannianEDist I (F (sn n) 0) (F (sn n) τ) := by
    filter_upwards [hFsm1] with n hn
    exact isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr zero_le_one)
      ((Submission.HopfRinow.continuous_riemannianEDist_left (I := I) (F (sn n) 0)).comp_continuousOn
        hn.1.continuousOn)
  let tn : ℕ → ℝ := fun n => if h : ∃ τ ∈ Set.Icc (0 : ℝ) 1,
      ∀ τ' ∈ Set.Icc (0 : ℝ) 1,
        Manifold.riemannianEDist I (F (sn n) 0) (F (sn n) τ')
          ≤ Manifold.riemannianEDist I (F (sn n) 0) (F (sn n) τ)
    then Classical.choose h else 1 / 2
  have htn : ∀ᶠ n in atTop, tn n ∈ Set.Icc (0 : ℝ) 1 ∧
      (∀ τ' ∈ Set.Icc (0 : ℝ) 1,
        Manifold.riemannianEDist I (F (sn n) 0) (F (sn n) τ')
          ≤ Manifold.riemannianEDist I (F (sn n) 0) (F (sn n) (tn n))) := by
    filter_upwards [hfpt] with n hn
    have htnn : tn n = Classical.choose hn := by
      show (if h : _ then Classical.choose h else 1 / 2) = Classical.choose hn
      rw [dif_pos hn]
    rw [htnn]
    exact Classical.choose_spec hn
  -- ## 4. Convergence of the base point and of the midpoint
  have hnorm_smul : ∀ {z : M} (w : TangentSpace I z),
      Tendsto (fun n => ‖sn n • (d • w)‖) atTop (𝓝 0) := by
    intro z w
    have h1 : Tendsto (fun n => sn n * (d * ‖w‖)) atTop (𝓝 0) := by
      simpa using hsn_tend.mul_const (d * ‖w‖)
    refine h1.congr' ?_
    filter_upwards with n
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (hsn_pos n).le, Real.norm_of_nonneg hd.le]
  have hFx0 : Tendsto (fun n => F (sn n) 0) atTop (𝓝 (γ 0)) :=
    tendsto_GExp_zero (I := I) (cov := cov) hmet (γ 0) (hnorm_smul (Z 0))
  have hFhalf : Tendsto (fun n => F (sn n) (1 / 2)) atTop (𝓝 (γ (1 / 2))) :=
    tendsto_GExp_zero (I := I) (cov := cov) hmet (γ (1 / 2)) (hnorm_smul (Z (1 / 2)))
  have hDmid : Tendsto (fun n => Manifold.riemannianEDist I (F (sn n) 0) (F (sn n) (1 / 2)))
      atTop (𝓝 (ENNReal.ofReal m)) := by
    have h := tendsto_riemannianEDist (I := I) hFx0 hFhalf
    simpa only [hpq] using h
  -- ## 5. The minimising vectors from the base point to the farthest point
  let xn : ℕ → M := fun n => F (sn n) 0
  let rn : ℕ → M := fun n => F (sn n) (tn n)
  have hVn : ∀ n, ∃ v : TangentSpace I (xn n),
      GExp (cov := cov) hmet (xn n) v = rn n ∧
      Manifold.riemannianEDist I (xn n) (rn n) = ENNReal.ofReal ‖v‖ :=
    fun n => Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor
      (xn n) (rn n)
  let Vn : (n : ℕ) → TangentSpace I (xn n) := fun n => Classical.choose (hVn n)
  have hVn_spec : ∀ n, GExp (cov := cov) hmet (xn n) (Vn n) = rn n ∧
      Manifold.riemannianEDist I (xn n) (rn n) = ENNReal.ofReal ‖Vn n‖ :=
    fun n => Classical.choose_spec (hVn n)
  let ln : ℕ → ℝ := fun n => ‖Vn n‖
  -- ## 6. Two upper bounds for `d(xₙ,rₙ)`
  have hbound1 : ∀ᶠ n in atTop, Manifold.riemannianEDist I (xn n) (rn n)
      ≤ ENNReal.ofReal (Submission.Length.curveLength (I := I) (F (sn n)) 0 (tn n)) := by
    filter_upwards [hFsm1, htn] with n hn htnn
    exact edist_le_ofReal_curveLength (I := I)
      (hn.1.mono (Set.Icc_subset_Icc_right htnn.1.2))
      (hn.2.mono (Set.Icc_subset_Icc_right htnn.1.2))
      htnn.1.1
  have hbound2 : ∀ᶠ n in atTop, Manifold.riemannianEDist I (xn n) (rn n)
      ≤ ENNReal.ofReal (Submission.Length.curveLength (I := I) (F (sn n)) (tn n) 1) := by
    filter_upwards [hFsm1, htn] with n hn htnn
    have h2 := edist_le_ofReal_curveLength (I := I) (γ := F (sn n)) (a := tn n) (b := 1)
      (hn.1.mono (Set.Icc_subset_Icc_left htnn.1.1))
      (hn.2.mono (Set.Icc_subset_Icc_left htnn.1.1))
      htnn.1.2
    calc Manifold.riemannianEDist I (xn n) (rn n)
        = Manifold.riemannianEDist I (rn n) (xn n) := Manifold.riemannianEDist_comm
      _ = Manifold.riemannianEDist I (F (sn n) (tn n)) (F (sn n) 0) := rfl
      _ = Manifold.riemannianEDist I (F (sn n) (tn n)) (F (sn n) 1) := by
            rw [← hFclosed (sn n)]
      _ ≤ ENNReal.ofReal (Submission.Length.curveLength (I := I) (F (sn n)) (tn n) 1) := h2
  -- ## 7. `ln n → m`
  have hlen_sum : ∀ᶠ n in atTop,
      Submission.Length.curveLength (I := I) (F (sn n)) 0 (tn n)
        + Submission.Length.curveLength (I := I) (F (sn n)) (tn n) 1
      = Submission.Length.curveLength (I := I) (F (sn n)) 0 1 := by
    filter_upwards [hFsm1, htn] with n hn htnn
    refine Submission.Length.curveLength_add_of_integrable (I := I) (F (sn n))
      (b := tn n) ?_ ?_
    · exact (hn.2.mono (Set.Icc_subset_Icc_right htnn.1.2)).intervalIntegrable_of_Icc htnn.1.1
    · exact (hn.2.mono (Set.Icc_subset_Icc_left htnn.1.1)).intervalIntegrable_of_Icc htnn.1.2
  have hln_lt : ∀ᶠ n in atTop, ln n < m := by
    filter_upwards [hbound1, hbound2, hlen_sum, hshort_n, htn] with n hb1 hb2 hsum hsh htnn
    have hdx : Manifold.riemannianEDist I (xn n) (rn n) = ENNReal.ofReal (ln n) := (hVn_spec n).2
    have hl1 : 0 ≤ Submission.Length.curveLength (I := I) (F (sn n)) 0 (tn n) :=
      Submission.Length.curveLength_nonneg (I := I) _ htnn.1.1
    have hl2 : 0 ≤ Submission.Length.curveLength (I := I) (F (sn n)) (tn n) 1 :=
      Submission.Length.curveLength_nonneg (I := I) _ htnn.1.2
    have hA : ln n ≤ Submission.Length.curveLength (I := I) (F (sn n)) 0 (tn n) := by
      have h := hb1
      rw [hdx] at h
      exact (ENNReal.ofReal_le_ofReal_iff hl1).mp h
    have hB : ln n ≤ Submission.Length.curveLength (I := I) (F (sn n)) (tn n) 1 := by
      have h := hb2
      rw [hdx] at h
      exact (ENNReal.ofReal_le_ofReal_iff hl2).mp h
    have hsum' : Submission.Length.curveLength (I := I) (F (sn n)) 0 (tn n)
        + Submission.Length.curveLength (I := I) (F (sn n)) (tn n) 1 < 2 * m := by
      rw [hsum]; exact hsh
    linarith
  have hln_tend : Tendsto ln atTop (𝓝 m) := by
    have hupper : ∀ᶠ n in atTop, ENNReal.ofReal (ln n) ≤ ENNReal.ofReal m := by
      filter_upwards [hln_lt] with n hn
      exact ENNReal.ofReal_le_ofReal hn.le
    have hlower : ∀ᶠ n in atTop,
        Manifold.riemannianEDist I (F (sn n) 0) (F (sn n) (1 / 2))
          ≤ ENNReal.ofReal (ln n) := by
      filter_upwards [htn] with n hn
      have h := hn.2 (1 / 2) (by constructor <;> norm_num)
      rwa [show Manifold.riemannianEDist I (F (sn n) 0) (F (sn n) (tn n))
        = ENNReal.ofReal (ln n) from (hVn_spec n).2] at h
    have hmid : Tendsto (fun n => ENNReal.ofReal (ln n)) atTop (𝓝 (ENNReal.ofReal m)) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' hDmid tendsto_const_nhds hlower hupper
    have h1 := (ENNReal.tendsto_toReal (a := ENNReal.ofReal m) ENNReal.ofReal_ne_top).comp hmid
    rw [ENNReal.toReal_ofReal hm.le] at h1
    refine h1.congr' ?_
    filter_upwards with n
    exact ENNReal.toReal_ofReal (norm_nonneg (Vn n))
  -- ## 8. The farthest parameter is an interior point of `[0,1]`
  have htn_Ioo : ∀ᶠ n in atTop, tn n ∈ Set.Ioo (0 : ℝ) 1 := by
    filter_upwards [htn, hln_tend.eventually (Ioi_mem_nhds hm)] with n htnn hlnpos
    have hdx : Manifold.riemannianEDist I (xn n) (rn n) = ENNReal.ofReal (ln n) := (hVn_spec n).2
    have hzero : Manifold.riemannianEDist I (xn n) (rn n) = 0 → False := by
      intro h0
      have h1 : ENNReal.ofReal (ln n) = 0 := by rw [← hdx]; exact h0
      have h2 : ln n = 0 := by
        have h3 : (ENNReal.ofReal (ln n)).toReal = (0 : ENNReal).toReal :=
          congrArg ENNReal.toReal h1
        rw [ENNReal.toReal_zero,
          ENNReal.toReal_ofReal (show (0 : ℝ) ≤ ln n from norm_nonneg (Vn n))] at h3
        exact h3
      linarith
    constructor
    · rcases eq_or_lt_of_le htnn.1.1 with h | h
      · exfalso
        refine hzero ?_
        rw [show rn n = xn n from by
          show F (sn n) (tn n) = F (sn n) 0
          rw [← h]]
        exact Manifold.riemannianEDist_self
      · exact h
    · rcases eq_or_lt_of_le htnn.1.2 with h | h
      · exfalso
        refine hzero ?_
        rw [show rn n = xn n from by
          show F (sn n) (tn n) = F (sn n) 0
          rw [h]
          exact hFclosed (sn n)]
        exact Manifold.riemannianEDist_self
      · exact h
  -- ## 9. The unit direction of the minimising vector
  let un : (n : ℕ) → TangentSpace I (xn n) := fun n => (ln n)⁻¹ • Vn n
  have hun_norm : ∀ n, 0 < ln n → ‖un n‖ = 1 := by
    intro n hn
    show ‖(ln n)⁻¹ • Vn n‖ = 1
    rw [norm_smul, Real.norm_of_nonneg (le_of_lt (inv_pos.mpr hn)),
      show ‖Vn n‖ = ln n from rfl]
    field_simp
  -- ## 10. The first-variation orthogonality at the farthest point
  have horth : ∀ᶠ n in atTop,
      inner ℝ (curveVelocity (I := I) (F (sn n)) (tn n))
        (curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet (xn n) (s • un n))
          (ln n)) = 0 := by
    filter_upwards [hFsm, htn, htn_Ioo, hln_lt, hln_tend.eventually (Ioi_mem_nhds hm)]
      with n hn htnn htnIoo hlnlt hlnpos
    obtain ⟨ψ, hψsm, hψbd, hψev, hψa⟩ := exists_contDiff_reparam (a := tn n) htnIoo
    set c : ℝ → M := fun t => F (sn n) (ψ t) with hcdef
    have hc_mem : ∀ t : ℝ, ψ t ∈ Set.Ioo (0 : ℝ) 1 := by
      intro t
      have h := abs_lt.mp (hψbd t)
      have hmin1 : min (tn n) (1 - tn n) ≤ tn n := min_le_left _ _
      have hmin2 : min (tn n) (1 - tn n) ≤ 1 - tn n := min_le_right _ _
      constructor <;> linarith [h.1, h.2, hmin1, hmin2]
    have hcsm : ContMDiff 𝓘(ℝ) I ∞ c := by
      intro t
      exact (hn.1.contMDiffAt (Icc_mem_nhds (hc_mem t).1 (hc_mem t).2)).comp t
        hψsm.contDiffAt.contMDiffAt
    have hc_val : c (tn n) = rn n := by
      show F (sn n) (ψ (tn n)) = F (sn n) (tn n)
      rw [hψa]
    have hc_ev : c =ᶠ[𝓝 (tn n)] F (sn n) := by
      filter_upwards [hψev] with t ht
      show F (sn n) (ψ t) = F (sn n) t
      rw [ht]
      rfl
    have hmax : ∀ᶠ τ in 𝓝 (tn n),
        Manifold.riemannianEDist I (xn n) (c τ)
          ≤ Manifold.riemannianEDist I (xn n) (c (tn n)) := by
      filter_upwards with τ
      show Manifold.riemannianEDist I (F (sn n) 0) (F (sn n) (ψ τ))
        ≤ Manifold.riemannianEDist I (F (sn n) 0) (F (sn n) (ψ (tn n)))
      rw [hψa]
      exact htnn.2 (ψ τ) ⟨(hc_mem τ).1.le, (hc_mem τ).2.le⟩
    have hinj : ∃ ρ : ℝ, ln n < ρ ∧ Submission.InjRadius.InjAtLeast hmet (xn n) ρ :=
      ⟨m, hlnlt, hinjall (xn n)⟩
    have hun1 : ‖un n‖ = 1 := hun_norm n hlnpos
    have hnc : ¬ Submission.ConjRadius.IsConjugateTime cov
        (fun t : ℝ => GExp (cov := cov) hmet (xn n) (t • un n)) (ln n) := by
      intro hconj
      have h1 : Submission.CutTime.cutTime (I := I) hmet (xn n) (un n) ≤ ln n :=
        Submission.ConjEnergy.cutTime_le_of_isConjugateTime (cov := cov) hmet htor hun1 hconj
      have h2 : m ≤ Submission.CutTime.cutTime (I := I) hmet (xn n) (un n) :=
        Submission.CutTime.injAtLeast_le_cutTime (cov := cov) hmet htor (hinjall (xn n)) hun1
      linarith
    have hy : GExp (cov := cov) hmet (xn n) (ln n • un n) = rn n := by
      have hvu : ln n • un n = Vn n := by
        show ln n • ((ln n)⁻¹ • Vn n) = Vn n
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hlnpos), one_smul]
      rw [hvu]
      exact (hVn_spec n).1
    have hkey := Work.EvenBound.FarthestPoint.inner_eq_zero_of_isLocalMax_edist (cov := cov)
      hmet htor (x := xn n) (y := rn n) (v := un n) hun1 hlnpos hy (hVn_spec n).2 hinj hnc
      (t₀ := tn n) hc_val hcsm hmax
    have hvel : curveVelocity (I := I) c (tn n)
        = curveVelocity (I := I) (F (sn n)) (tn n) := by
      rw [curveVelocity_apply, curveVelocity_apply]
      exact congrArg (fun (f : ℝ →L[ℝ] TangentSpace I (F (sn n) (tn n))) => f 1)
        (hc_ev.mfderiv_eq (I := 𝓘(ℝ)) (I' := I))
    rw [hvel] at hkey
    rw [hc_val] at hkey
    exact hkey
  have hln_pos_ev : ∀ᶠ n in atTop, 0 < ln n := hln_tend.eventually (Ioi_mem_nhds hm)
  -- ## 11. A chart frame at `γ 0` and a bounded coordinate sequence
  obtain ⟨CF⟩ := Submission.GExpJointPt.exists_chartFrame (cov := cov) hmet (z := γ 0) (p := γ 0)
    (mem_chart_source H (γ 0))
  have hZnhds : CF.Z ∈ 𝓝 (γ 0) :=
    CF.nhds_of_strict (mem_chart_source H (γ 0))
      (by rw [CF.hx, sub_self, norm_zero]; exact CF.hη)
  have hxnZ : ∀ᶠ n in atTop, xn n ∈ CF.Z := hFx0 hZnhds
  let cve : ℕ → E := fun n =>
    (trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (xn n) (Vn n)
  let R : ℝ := (Real.sqrt CF.lam)⁻¹ * m
  have hRpos : 0 < R :=
    mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr CF.hlam)) hm
  have hframe_cve : ∀ᶠ n in atTop, frameVector (I := I) (γ 0) (xn n) (cve n) = Vn n := by
    filter_upwards [hxnZ] with n hnZ
    have hsrc : xn n ∈ (extChartAt I (γ 0)).source := by
      rw [extChartAt_source]; exact CF.hZsrc hnZ
    exact Submission.GExpFlow.frameVector_clm (I := I) (z₀ := γ 0) hsrc (Vn n)
  have hcve_bound : ∀ᶠ n in atTop, ‖cve n‖ ≤ R := by
    filter_upwards [hxnZ, hln_lt, hframe_cve] with n hnZ hnlt hframe
    have hsl : 0 < Real.sqrt CF.lam := Real.sqrt_pos.mpr CF.hlam
    have hb := (CF.hbnd (xn n) hnZ (cve n)).1
    have hcg : chartGram (I := I) (γ 0) (xn n) (cve n) (cve n)
        = ‖frameVector (I := I) (γ 0) (xn n) (cve n)‖ ^ 2 := by
      rw [Submission.GExpFlow.norm_frameVector,
        Real.sq_sqrt (Submission.Minimal.chartGram_self_nonneg (γ 0) (xn n) (cve n))]
    rw [hcg, hframe] at hb
    have hb3 : Real.sqrt CF.lam * ‖cve n‖ ≤ ln n := by
      have h := Real.sqrt_le_sqrt hb
      rw [Real.sqrt_mul CF.hlam.le, Real.sqrt_sq (norm_nonneg (cve n)),
        Real.sqrt_sq (norm_nonneg (Vn n))] at h
      exact h
    have h1 : ‖cve n‖ = (Real.sqrt CF.lam)⁻¹ * (Real.sqrt CF.lam * ‖cve n‖) := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hsl), one_mul]
    rw [h1]
    show (Real.sqrt CF.lam)⁻¹ * (Real.sqrt CF.lam * ‖cve n‖) ≤ (Real.sqrt CF.lam)⁻¹ * m
    exact mul_le_mul_of_nonneg_left (le_of_lt (lt_of_le_of_lt hb3 hnlt)) (le_of_lt (inv_pos.mpr hsl))
  let an : ℕ → E := fun n => if ‖cve n‖ ≤ R then cve n else 0
  have han_bdd : ∀ n, ‖an n‖ ≤ R := by
    intro n
    by_cases h : ‖cve n‖ ≤ R
    · show ‖(if ‖cve n‖ ≤ R then cve n else 0)‖ ≤ R
      rw [if_pos h]; exact h
    · show ‖(if ‖cve n‖ ≤ R then cve n else 0)‖ ≤ R
      rw [if_neg h, norm_zero]; exact hRpos.le
  have han_eq : ∀ᶠ n in atTop, an n = cve n := by
    filter_upwards [hcve_bound] with n hn
    show (if ‖cve n‖ ≤ R then cve n else 0) = cve n
    rw [if_pos hn]
  have han_frame : ∀ᶠ n in atTop, frameVector (I := I) (γ 0) (xn n) (an n) = Vn n := by
    filter_upwards [han_eq, hframe_cve] with n he hf
    rw [he]; exact hf
  -- ## 12. A subsequence on which every pointwise datum holds
  obtain ⟨K₁, hK₁⟩ := Filter.eventually_atTop.mp hxnZ
  obtain ⟨K₂, hK₂⟩ := Filter.eventually_atTop.mp han_eq
  obtain ⟨K₄, hK₄⟩ := Filter.eventually_atTop.mp hln_pos_ev
  set K : ℕ := K₁ + K₂ + K₄ with hKdef
  have hKmem : ∀ n, K ≤ n → xn n ∈ CF.Z ∧ an n = cve n ∧ 0 < ln n := by
    intro n hn
    exact ⟨hK₁ n (by omega), hK₂ n (by omega), hK₄ n (by omega)⟩
  have hKev : ∀ᶠ n in atTop, (an n, tn n) ∈ Metric.closedBall (0 : E) R ×ˢ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [Filter.Eventually.of_forall han_bdd, htn] with n hb hn
    exact ⟨Metric.mem_closedBall.mpr (by simpa using hb), hn.1⟩
  have hKcomp : IsCompact (Metric.closedBall (0 : E) R ×ˢ Set.Icc (0 : ℝ) 1) :=
    (isCompact_closedBall (0 : E) R).prod isCompact_Icc
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hKev
  obtain ⟨z₀, _hz₀mem, θ, hθmono, hθtend⟩ := hKcomp.tendsto_subseq
    (x := fun k => (an (k + N₀ + K), tn (k + N₀ + K)))
    (fun k => hN₀ (k + N₀ + K) (by omega))
  obtain ⟨a, ts⟩ := z₀
  set φ : ℕ → ℕ := fun k => θ k + N₀ + K with hφdef
  have hφmono : StrictMono φ := by
    intro i j hij
    have hlt := hθmono hij
    show θ i + N₀ + K < θ j + N₀ + K
    omega
  have hφtend : Tendsto φ atTop atTop := hφmono.tendsto_atTop
  have hφK : ∀ k, K ≤ φ k := by
    intro k
    show K ≤ θ k + N₀ + K
    omega
  have hxnZ_φ : ∀ k, xn (φ k) ∈ CF.Z := fun k => (hKmem (φ k) (hφK k)).1
  have han_eq_φ : ∀ k, an (φ k) = cve (φ k) := fun k => (hKmem (φ k) (hφK k)).2.1
  have hln_pos_φ : ∀ k, 0 < ln (φ k) := fun k => (hKmem (φ k) (hφK k)).2.2
  have hln_ne_φ : ∀ k, ln (φ k) ≠ 0 := fun k => ne_of_gt (hln_pos_φ k)
  have han_frame_φ : ∀ k, frameVector (I := I) (γ 0) (xn (φ k)) (an (φ k)) = Vn (φ k) := by
    intro k
    have hsrc : xn (φ k) ∈ (extChartAt I (γ 0)).source := by
      rw [extChartAt_source]; exact CF.hZsrc (hxnZ_φ k)
    rw [han_eq_φ k]
    exact Submission.GExpFlow.frameVector_clm (I := I) (z₀ := γ 0) hsrc (Vn (φ k))
  have hxn_tend : Tendsto (fun k => xn (φ k)) atTop (𝓝 (γ 0)) := hFx0.comp hφtend
  have ha_tend : Tendsto (fun k => an (φ k)) atTop (𝓝 a) :=
    (continuous_fst.tendsto (a, ts)).comp hθtend
  have hts_tend : Tendsto (fun k => tn (φ k)) atTop (𝓝 ts) :=
    (continuous_snd.tendsto (a, ts)).comp hθtend
  have hts_mem : ts ∈ Set.Icc (0 : ℝ) 1 :=
    isClosed_Icc.mem_of_tendsto hts_tend
      ((hφtend.eventually htn).mono (fun k hk => hk.1))
  have hln_tend' : Tendsto (fun k => ln (φ k)) atTop (𝓝 m) := hln_tend.comp hφtend
  -- ## 13. The limit point `qlim`
  let qlim : M := GExp (cov := cov) hmet (γ 0) (frameVector (I := I) (γ 0) (γ 0) a)
  have hqlim : Tendsto (fun k => rn (φ k)) atTop (𝓝 qlim) := by
    have hmain := Submission.GExpJointPt.tendsto_GExp_frameVector (cov := cov) hmet htor
      (z₀ := γ 0) (p := γ 0) (mem_chart_source H (γ 0)) hxn_tend ha_tend
    refine hmain.congr' ?_
    filter_upwards with k
    show GExp (cov := cov) hmet (xn (φ k))
      (frameVector (I := I) (γ 0) (xn (φ k)) (an (φ k))) = rn (φ k)
    rw [han_frame_φ k]
    exact (hVn_spec (φ k)).1
  have hnorm_a : ‖frameVector (I := I) (γ 0) (γ 0) a‖ = m := by
    have h1 := Submission.KlingenbergAttain.tendsto_norm_frameVector (cov := cov) hmet
      (z₀ := γ 0) (p₀ := γ 0) (mem_chart_source H (γ 0)) hxn_tend ha_tend
    have h2 : Tendsto (fun k => ‖frameVector (I := I) (γ 0) (xn (φ k)) (an (φ k))‖) atTop
        (𝓝 m) := by
      refine hln_tend'.congr' ?_
      filter_upwards with k
      rw [han_frame_φ k]
    exact tendsto_nhds_unique h1 h2
  have hdist_qlim : Manifold.riemannianEDist I (γ 0) qlim = ENNReal.ofReal m := by
    have h1 := tendsto_riemannianEDist (I := I) hxn_tend hqlim
    have h2 : Tendsto (fun k => Manifold.riemannianEDist I (xn (φ k)) (rn (φ k))) atTop
        (𝓝 (ENNReal.ofReal m)) := by
      refine (ENNReal.tendsto_ofReal hln_tend').congr' ?_
      filter_upwards with k
      exact (hVn_spec (φ k)).2.symm
    exact tendsto_nhds_unique h1 h2

  -- ## 14. The limiting minimising geodesic ends at `γ ts`
  have hrn_tend : Tendsto (fun k => rn (φ k)) atTop (𝓝 (γ ts)) := by
    obtain ⟨U, hUopen, htsU, hUsrc, hUcd⟩ :=
      hZsm ts (by constructor <;> linarith [hts_mem.1, hts_mem.2])
    have hxU : ∀ᶠ k in atTop, tn (φ k) ∈ U :=
      hts_tend.eventually (hUopen.mem_nhds htsU)
    have hq : Tendsto (fun k => γ (tn (φ k))) atTop (𝓝 (γ ts)) :=
      (hγsm.continuous.tendsto ts).comp hts_tend
    have hu : Tendsto (fun k => chartCoords (I := I) (γ ts) γ Z (tn (φ k))) atTop
        (𝓝 (chartCoords (I := I) (γ ts) γ Z ts)) :=
      (hUcd.continuousOn.continuousWithinAt htsU).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr ⟨hts_tend, hxU⟩)
    have hc_d : Tendsto (fun k => sn (φ k) * d) atTop (𝓝 0) := by
      simpa using (hsn_tend.comp hφtend).mul_const d
    have ha : Tendsto (fun k => (sn (φ k) * d) • chartCoords (I := I) (γ ts) γ Z (tn (φ k)))
        atTop (𝓝 0) := by
      simpa using hc_d.smul hu
    have hmain := Submission.GExpJointPt.tendsto_GExp_frameVector (cov := cov) hmet htor
      (z₀ := γ ts) (p := γ ts) (hUsrc ts htsU) hq ha
    have hlim : GExp (cov := cov) hmet (γ ts) (frameVector (I := I) (γ ts) (γ ts) 0) = γ ts := by
      rw [Submission.ChartBounds.frameVector_zero', GExp_zero]
    rw [hlim] at hmain
    refine Filter.Tendsto.congr' ?_ hmain
    filter_upwards [hxU] with k hkU
    have hsrc : γ (tn (φ k)) ∈ (chartAt H (γ ts)).source := hUsrc (tn (φ k)) hkU
    show GExp (cov := cov) hmet (γ (tn (φ k)))
      (frameVector (I := I) (γ ts) (γ (tn (φ k)))
        ((sn (φ k) * d) • chartCoords (I := I) (γ ts) γ Z (tn (φ k)))) = rn (φ k)
    rw [frameVector_smul,
      Submission.JacobiCoords.frameVector_chartCoords (I := I) (γ := γ) (J := Z) hsrc,
      mul_smul]
  have hqlim_eq : qlim = γ ts := tendsto_nhds_unique hqlim hrn_tend
  have hdist_γ : Manifold.riemannianEDist I (γ 0) (γ ts) = ENNReal.ofReal m := by
    rw [← hqlim_eq]
    exact hdist_qlim
  -- ## 15. The parameter is `1/2`
  have hts_eq : ts = 1 / 2 := by
    have hspc1 : ContinuousOn (fun t : ℝ => curveSpeed (I := I) γ t) (Set.Icc (0 : ℝ) 1) :=
      (continuousOn_const (c := 2 * m)).congr (fun t ht => hsp t ht)
    have hup : m ≤ 2 * m * ts := by
      have h1 : Manifold.riemannianEDist I (γ 0) (γ ts)
          ≤ ENNReal.ofReal (curveLength (I := I) γ 0 ts) :=
        edist_le_ofReal_curveLength (I := I)
          ((hγsm.contMDiffOn.of_le (by simp)).mono (fun x _ => trivial))
          (hspc1.mono (Set.Icc_subset_Icc_right hts_mem.2)) hts_mem.1
      have h2 : curveLength (I := I) γ 0 ts = 2 * m * ts := by
        rw [Submission.BrokenLength.curveLength_eq_mul_of_curveSpeed_eq (I := I) hts_mem.1
          (fun t ht => hsp t (Set.Icc_subset_Icc_right hts_mem.2 ht))]
        ring
      rw [hdist_γ, h2] at h1
      exact (ENNReal.ofReal_le_ofReal_iff (by nlinarith [hm, hts_mem.1])).mp h1
    have hlow : m ≤ 2 * m * (1 - ts) := by
      have h1 : Manifold.riemannianEDist I (γ ts) (γ 1)
          ≤ ENNReal.ofReal (curveLength (I := I) γ ts 1) :=
        edist_le_ofReal_curveLength (I := I)
          ((hγsm.contMDiffOn.of_le (by simp)).mono (fun x _ => trivial))
          (hspc1.mono (Set.Icc_subset_Icc_left hts_mem.1)) hts_mem.2
      have h2 : curveLength (I := I) γ ts 1 = 2 * m * (1 - ts) :=
        Submission.BrokenLength.curveLength_eq_mul_of_curveSpeed_eq (I := I) hts_mem.2
          (fun t ht => hsp t (Set.Icc_subset_Icc_left hts_mem.1 ht))
      have h3 : Manifold.riemannianEDist I (γ ts) (γ 1) = ENNReal.ofReal m := by
        rw [hγ1, Manifold.riemannianEDist_comm]
        exact hdist_γ
      rw [h3, h2] at h1
      exact (ENNReal.ofReal_le_ofReal_iff (by nlinarith [hm, hts_mem.2])).mp h1
    have hup' : 1 ≤ 2 * ts := by nlinarith [hup, hm]
    have hlow' : 1 ≤ 2 * (1 - ts) := by nlinarith [hlow, hm]
    linarith
  have hqlim_eq' : qlim = γ (1 / 2) := by rw [hqlim_eq, hts_eq]
  have htn_half : Tendsto (fun k => tn (φ k)) atTop (𝓝 (1 / 2)) := by
    rw [← hts_eq]
    exact hts_tend
  -- ## 16. The speed of `γ` is `2m` everywhere and `γ` is the `GExp`-ray of its initial velocity
  have hstep : ∀ s : ℝ, curveSpeed (I := I) γ (s + 1) = curveSpeed (I := I) γ s := by
    intro s
    have h1 := Submission.SecondVarGlobal.curveSpeed_comp_add_right (I := I) γ 1 s
      (hγsm.mdifferentiableAt (by simp))
    rw [show (fun x : ℝ => γ (x + 1)) = γ from funext (fun x => hper x)] at h1
    exact h1.symm
  have hshift : ∀ (t : ℝ) (n : ℕ), curveSpeed (I := I) γ t = curveSpeed (I := I) γ (t - n) := by
    intro t n
    induction n with
    | zero => simp
    | succ m ih =>
        have hcast : (((m + 1 : ℕ)) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        calc curveSpeed (I := I) γ t = curveSpeed (I := I) γ (t - (m : ℝ)) := ih
          _ = curveSpeed (I := I) γ ((t - ((m : ℝ) + 1)) + 1) := by
                congr 1
                ring
          _ = curveSpeed (I := I) γ (t - ((m : ℝ) + 1)) := hstep (t - ((m : ℝ) + 1))
  have hshift' : ∀ (t : ℝ) (n : ℕ), curveSpeed (I := I) γ t = curveSpeed (I := I) γ (t + n) := by
    intro t n
    induction n with
    | zero => simp
    | succ m ih =>
        have hcast : (((m + 1 : ℕ)) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        calc curveSpeed (I := I) γ t = curveSpeed (I := I) γ (t + (m : ℝ)) := ih
          _ = curveSpeed (I := I) γ ((t + (m : ℝ)) + 1) := (hstep (t + (m : ℝ))).symm
          _ = curveSpeed (I := I) γ (t + ((m : ℝ) + 1)) := by
                congr 1
                ring
  have hsp_global : ∀ t : ℝ, curveSpeed (I := I) γ t = 2 * m := by
    intro t
    by_cases ht : (0 : ℝ) ≤ t
    · let n : ℕ := Nat.floor t
      have hmem : t - n ∈ Set.Icc (0 : ℝ) 1 := by
        have h1 : ((n : ℕ) : ℝ) ≤ t := Nat.floor_le ht
        have h2 : t < ((n : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one t
        exact ⟨by linarith, by linarith⟩
      rw [hshift t n]
      exact hsp _ hmem
    · push Not at ht
      let n : ℕ := Nat.ceil (-t)
      have hmem : t + n ∈ Set.Icc (0 : ℝ) 1 := by
        have h1 : -t ≤ ((n : ℕ) : ℝ) := Nat.le_ceil (-t)
        have h2 : ((n : ℕ) : ℝ) < -t + 1 := Nat.ceil_lt_add_one (by linarith)
        exact ⟨by linarith, by linarith⟩
      rw [hshift' t n]
      exact hsp _ hmem
  have hvel_ne : ∀ t : ℝ, curveVelocity (I := I) γ t ≠ 0 := by
    intro t h
    have h1 : curveSpeed (I := I) γ t = 0 := by
      rw [Submission.GeodesicSpeed.curveSpeed_eq_norm, h, norm_zero]
    rw [hsp_global t] at h1
    linarith
  have hvel_per : curveVelocity (I := I) γ (-(1 / 2)) = curveVelocity (I := I) γ (1 / 2) := by
    have h := Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := γ) (c := 1) (d := 1)
      (t := -(1 / 2)) (hγsm.mdifferentiableAt (by simp))
    rw [show (fun s : ℝ => γ (1 * s + 1)) = γ from funext (fun s => by
      rw [one_mul]; exact hper s)] at h
    rw [one_smul, show (1 : ℝ) * (-(1 / 2)) + 1 = 1 / 2 by ring] at h
    exact h
  have hray : ∀ T : ℝ, 0 ≤ T → ∀ t ∈ Set.Icc (0 : ℝ) T,
      γ t = GExp (cov := cov) hmet (γ 0) (t • curveVelocity (I := I) γ 0) := by
    intro T hT t ht
    exact Submission.GExpRayIdent.eqOn_Icc_GExp_of_isGeodesicAt (cov := cov) hmet (hvel_ne 0)
      (a := -(T + 1)) (b := T + 1) (by linarith) hT (by linarith)
      (hγsm.contMDiffOn.mono (fun x _ => trivial)) (fun s _ => hgeo s) (fun s _ => hvel_ne s)
      rfl rfl t ht
  have hray_affine : ∀ c : ℝ, c ≠ 0 → ∀ T : ℝ, 0 ≤ T → ∀ s ∈ Set.Icc (0 : ℝ) T,
      γ (c * s) = GExp (cov := cov) hmet (γ 0) (s • (c • curveVelocity (I := I) γ 0)) := by
    intro c hc T hT s hs
    let g : ℝ → M := fun r => γ (c * r)
    have hge : g = fun r : ℝ => γ (c * r) := rfl
    have hgg : g = fun r : ℝ => γ (c * r + 0) := by
      funext u
      rw [add_zero]
    set B : ℝ := (|c| + 1) * T + 1 with hBdef
    set D : ℝ := |c| * B + 1 with hDdef
    have hTB : T < B := by
      rw [hBdef]; nlinarith [abs_nonneg c, hT, mul_nonneg (abs_nonneg c) hT]
    have hB0 : 0 < B := lt_of_le_of_lt hT hTB
    have hD0 : 0 < D := by rw [hDdef]; nlinarith [abs_nonneg c, hB0]
    have hgsm : ContMDiffOn 𝓘(ℝ) I ∞ g (Set.Ioo (-B) B) :=
      (hγsm.comp (contDiff_const.mul contDiff_id).contMDiff).contMDiffOn.mono
        (fun x _ => trivial)
    have hggeo : ∀ r ∈ Set.Ioo (-B) B, IsGeodesicAt cov g r := by
      intro r hr
      have hrD : c * r + 0 ∈ Set.Ioo (-D) D := by
        have habs : |c * r| < D := by
          rw [hDdef, abs_mul]
          have h1 : |r| < B := by rw [abs_lt]; exact hr
          have h2 : 0 < |c| := abs_pos.mpr hc
          nlinarith
        have h2 := abs_lt.mp habs
        exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
      have h := Submission.HopfRinow.isGeodesicAt_comp_affine (cov := cov) (σ := γ)
        (c := -D) (d := D) (a := c) (b := 0) hc
        (hγsm.contMDiffOn.mono (fun x _ => trivial)) (fun y _ => hgeo y) hrD
      rw [hgg]
      simpa using h
    have hgne : ∀ r ∈ Set.Ioo (-B) B, curveVelocity (I := I) g r ≠ 0 := by
      intro r _
      have h' : curveVelocity (I := I) g r = c • curveVelocity (I := I) γ (c * r) := by
        have h := Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := γ) (c := c) (d := 0)
          (t := r) (hγsm.mdifferentiableAt (by simp))
        rw [← hgg, show c * r + 0 = c * r by ring] at h
        exact h
      rw [h']
      exact smul_ne_zero hc (hvel_ne (c * r))
    have hg0 : g 0 = γ 0 := by
      rw [hge]
      simp
    have hgv : curveVelocity (I := I) g 0 = c • curveVelocity (I := I) γ 0 := by
      have h := Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := γ) (c := c) (d := 0)
        (t := 0) (hγsm.mdifferentiableAt (by simp))
      rw [← hgg, mul_zero, add_zero] at h
      exact h
    exact Submission.GExpRayIdent.eqOn_Icc_GExp_of_isGeodesicAt (cov := cov) hmet
      (V := c • curveVelocity (I := I) γ 0) (smul_ne_zero hc (hvel_ne 0))
      (a := -B) (b := B) (by linarith) hT hTB hgsm hggeo hgne hg0 hgv s hs

  -- ## 17. The limit direction and the limit velocity
  let V : TangentSpace I (γ 0) := frameVector (I := I) (γ 0) (γ 0) a
  have hVnorm : ‖V‖ = m := hnorm_a
  have hV_geo : GExp (cov := cov) hmet (γ 0) V = γ (1 / 2) := hqlim_eq'
  have hcoef : m * (2 * m)⁻¹ = (2 : ℝ)⁻¹ := by field_simp
  have hwunit : ‖(m⁻¹ : ℝ) • V‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (le_of_lt (inv_pos.mpr hm)), hVnorm]
    field_simp
  have hV_dich : V = (2 : ℝ)⁻¹ • curveVelocity (I := I) γ 0
      ∨ V = -((2 : ℝ)⁻¹ • curveVelocity (I := I) γ 0) := by
    have hw : ‖(m⁻¹ : ℝ) • V‖ = 1 := hwunit
    have hG : GExp (cov := cov) hmet (γ 0) (m • ((m⁻¹ : ℝ) • V)) = γ (1 / 2) := by
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hm), one_smul]
      exact hV_geo
    have h := honly ((m⁻¹ : ℝ) • V) hw hG
    refine h.imp ?_ ?_
    · intro hh
      have h2 := congrArg (fun v : TangentSpace I (γ 0) => m • v) hh
      simp only [smul_smul, mul_inv_cancel₀ (ne_of_gt hm), one_smul] at h2
      rw [h2, hcoef]
    · intro hh
      have h2 := congrArg (fun v : TangentSpace I (γ 0) => m • v) hh
      simp only [smul_neg, smul_smul, mul_inv_cancel₀ (ne_of_gt hm), one_smul] at h2
      rw [h2, hcoef]
  have hW1 : V = (2 : ℝ)⁻¹ • curveVelocity (I := I) γ 0 →
      curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet (γ 0) (s • ((m⁻¹ : ℝ) • V))) m
        = (2 * m)⁻¹ • curveVelocity (I := I) γ (1 / 2) := by
    intro hV
    have h1 : (m⁻¹ : ℝ) • V = (2 * m)⁻¹ • curveVelocity (I := I) γ 0 := by
      rw [hV, smul_smul]
      congr 1
      field_simp
    have h2 : (fun s : ℝ => GExp (cov := cov) hmet (γ 0) (s • ((m⁻¹ : ℝ) • V)))
        =ᶠ[𝓝 m] (fun s : ℝ => γ ((2 * m)⁻¹ * s)) := by
      refine Filter.eventually_of_mem
        (isOpen_Ioo.mem_nhds (show m ∈ Set.Ioo (m / 2) (m + 1) by constructor <;> linarith)) ?_
      · intro s hs
        have hs0 : 0 ≤ s := le_of_lt (lt_trans (by linarith : (0 : ℝ) < m / 2) hs.1)
        have h := hray_affine ((2 * m)⁻¹) (by positivity) (m + 1) (by linarith) s
          ⟨hs0, le_of_lt hs.2⟩
        rw [h1]
        exact h.symm
    have h3 : curveVelocity (I := I) (fun s : ℝ => γ ((2 * m)⁻¹ * s)) m
        = (2 * m)⁻¹ • curveVelocity (I := I) γ (1 / 2) := by
      have harith : (2 * m)⁻¹ * m + 0 = (1 : ℝ) / 2 := by
        rw [show (2 * m)⁻¹ * m = (1 : ℝ) / 2 by field_simp, add_zero]
      have h4' : curveVelocity (I := I) (fun s : ℝ => γ ((2 * m)⁻¹ * s)) m
          = (2 * m)⁻¹ • curveVelocity (I := I) γ ((1 : ℝ) / 2) := by
        have h := Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := γ) (c := (2 * m)⁻¹)
          (d := 0) (t := m) (hγsm.mdifferentiableAt (by simp))
        rw [show (fun s : ℝ => γ ((2 * m)⁻¹ * s + 0)) = (fun s : ℝ => γ ((2 * m)⁻¹ * s)) from
          funext (fun u => by rw [add_zero]), harith] at h
        exact h
      rw [h4']
    rw [curveVelocity_apply, curveVelocity_apply, h2.mfderiv_eq (I := 𝓘(ℝ)) (I' := I)]
    exact h3
  have hW2 : V = -((2 : ℝ)⁻¹ • curveVelocity (I := I) γ 0) →
      curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet (γ 0) (s • ((m⁻¹ : ℝ) • V))) m
        = -((2 * m)⁻¹ • curveVelocity (I := I) γ (1 / 2)) := by
    intro hV
    have h1 : (m⁻¹ : ℝ) • V = -((2 * m)⁻¹) • curveVelocity (I := I) γ 0 := by
      rw [hV, smul_neg, smul_smul, ← neg_smul]
      congr 1
      field_simp
    have h2 : (fun s : ℝ => GExp (cov := cov) hmet (γ 0) (s • ((m⁻¹ : ℝ) • V)))
        =ᶠ[𝓝 m] (fun s : ℝ => γ ((-(2 * m)⁻¹) * s)) := by
      refine Filter.eventually_of_mem
        (isOpen_Ioo.mem_nhds (show m ∈ Set.Ioo (m / 2) (m + 1) by constructor <;> linarith)) ?_
      · intro s hs
        have hs0 : 0 ≤ s := le_of_lt (lt_trans (by linarith : (0 : ℝ) < m / 2) hs.1)
        have h := hray_affine (-((2 * m)⁻¹)) (neg_ne_zero.mpr (by positivity)) (m + 1)
          (by linarith) s ⟨hs0, le_of_lt hs.2⟩
        rw [← h1] at h
        exact h.symm
    have h3 : curveVelocity (I := I) (fun s : ℝ => γ ((-(2 * m)⁻¹) * s)) m
        = -((2 * m)⁻¹ • curveVelocity (I := I) γ (1 / 2)) := by
      have harith : (-(2 * m)⁻¹) * m + 0 = -(1 / 2) := by
        rw [neg_mul, show (2 * m)⁻¹ * m = (1 : ℝ) / 2 by field_simp, add_zero]
      have h4' : curveVelocity (I := I) (fun s : ℝ => γ ((-(2 * m)⁻¹) * s)) m
          = (-(2 * m)⁻¹) • curveVelocity (I := I) γ (-(1 / 2)) := by
        have h := Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := γ) (c := -((2 * m)⁻¹))
          (d := 0) (t := m) (hγsm.mdifferentiableAt (by simp))
        rw [show (fun s : ℝ => γ ((-(2 * m)⁻¹) * s + 0))
            = (fun s : ℝ => γ ((-(2 * m)⁻¹) * s)) from funext (fun u => by rw [add_zero]),
          harith] at h
        exact h
      rw [h4', hvel_per]
      exact neg_smul (2 * m)⁻¹ (curveVelocity (I := I) γ (1 / 2))
    rw [curveVelocity_apply, curveVelocity_apply, h2.mfderiv_eq (I := 𝓘(ℝ)) (I' := I)]
    exact h3
  have hW : curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet (γ 0) (s • ((m⁻¹ : ℝ) • V))) m
      = (2 * m)⁻¹ • curveVelocity (I := I) γ (1 / 2)
    ∨ curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet (γ 0) (s • ((m⁻¹ : ℝ) • V))) m
      = -((2 * m)⁻¹ • curveVelocity (I := I) γ (1 / 2)) := hV_dich.imp hW1 hW2
  -- ## 20. The two velocity convergences (H1 and H2)
  let W : TangentSpace I (γ (1 / 2)) := curveVelocity (I := I)
    (fun s : ℝ => GExp (cov := cov) hmet (γ 0) (s • ((m⁻¹ : ℝ) • V))) m
  let Ainf : E := deriv (fun τ : ℝ => (extChartAt I (γ (1 / 2))) (γ τ)) (1 / 2)
  let Binf : E := velCoordsLim (cov := cov) hmet (γ 0) (γ 0) ((m⁻¹ : ℝ) • a) (γ (1 / 2)) m
  have hW' : W = (2 * m)⁻¹ • curveVelocity (I := I) γ (1 / 2)
      ∨ W = -((2 * m)⁻¹ • curveVelocity (I := I) γ (1 / 2)) := hW
  have hA : Tendsto (fun k => deriv (fun τ : ℝ => (extChartAt I (γ (1 / 2))) (F (sn (φ k)) τ)) (tn (φ k)))
      atTop (𝓝 Ainf) :=
    tendsto_chartVel_variation (cov := cov) hmet htor
      (γ := γ) hγsm (V := Z) hZsm (d := d) hd (z := γ (1 / 2)) (mem_chart_source H (γ (1 / 2)))
      (σn := fun k => sn (φ k)) (hsn_tend.comp hφtend) (tn := fun k => tn (φ k)) htn_half
  have hraylim_fun : rayLim (cov := cov) hmet (γ 0) (γ 0) ((m⁻¹ : ℝ) • a)
      = (fun s : ℝ => GExp (cov := cov) hmet (γ 0) (s • ((m⁻¹ : ℝ) • V))) := by
    funext s
    show GExp (cov := cov) hmet (γ 0) (s • frameVector (I := I) (γ 0) (γ 0) ((m⁻¹ : ℝ) • a))
      = GExp (cov := cov) hmet (γ 0) (s • ((m⁻¹ : ℝ) • V))
    rw [frameVector_smul, show frameVector (I := I) (γ 0) (γ 0) a = V from rfl]
  have hraylim : rayLim (cov := cov) hmet (γ 0) (γ 0) ((m⁻¹ : ℝ) • a) m = γ (1 / 2) := by
    rw [hraylim_fun]
    show GExp (cov := cov) hmet (γ 0) (m • ((m⁻¹ : ℝ) • V)) = γ (1 / 2)
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hm), one_smul]
    exact hV_geo
  obtain ⟨CFz⟩ := Submission.GExpJointPt.exists_chartFrame (cov := cov) hmet (z := γ (1 / 2))
    (p := rayLim (cov := cov) hmet (γ 0) (γ 0) ((m⁻¹ : ℝ) • a) m)
    (by rw [hraylim]; exact mem_chart_source H (γ (1 / 2)))
  have hy_tend : Tendsto (fun k => (ln (φ k))⁻¹ • an (φ k)) atTop (𝓝 ((m⁻¹ : ℝ) • a)) :=
    (hln_tend'.inv₀ (ne_of_gt hm)).smul ha_tend
  have hunit : ∀ k, ‖frameVector (I := I) (γ 0) (xn (φ k)) ((ln (φ k))⁻¹ • an (φ k))‖ = 1 := by
    intro k
    rw [frameVector_smul, han_frame_φ k]
    exact hun_norm (φ k) (hln_pos_φ k)
  have hu0 : ‖frameVector (I := I) (γ 0) (γ 0) ((m⁻¹ : ℝ) • a)‖ = 1 := by
    rw [frameVector_smul, show frameVector (I := I) (γ 0) (γ 0) a = V from rfl]
    exact hwunit
  have hB : Tendsto (fun k => velCoords (cov := cov) hmet (γ 0) (fun m => xn (φ m))
      (fun m => (ln (φ m))⁻¹ • an (φ m)) (γ (1 / 2)) (ln (φ k)) k) atTop (𝓝 Binf) :=
    tendsto_velCoords_endpoint (cov := cov) hmet htor
      (z₀ := γ 0) (p := γ 0) (mem_chart_source H (γ 0))
      (q := fun k => xn (φ k)) (hFx0.comp hφtend)
      (y := fun k => (ln (φ k))⁻¹ • an (φ k)) (y₀ := (m⁻¹ : ℝ) • a) hy_tend hunit hu0
      (Ln := fun k => ln (φ k)) (L := m) hln_tend' (fun k => (hln_pos_φ k).le) hm
      (z := γ (1 / 2)) CFz (by rw [hraylim]; exact mem_chart_source H (γ (1 / 2)))
      hm (fun w _ => hinjall w)
  -- ## 21. The orthogonality, in chart coordinates
  have hrn_tend2 : Tendsto (fun k => rn (φ k)) atTop (𝓝 (γ (1 / 2))) := by
    rw [← hqlim_eq']
    exact hqlim
  have hrn_chart : ∀ᶠ k in atTop, rn (φ k) ∈ (chartAt H (γ (1 / 2))).source :=
    hrn_tend2 ((chartAt H (γ (1 / 2))).open_source.mem_nhds (mem_chart_source H (γ (1 / 2))))
  have hrayseq_gen : ∀ (n : ℕ) (t : ℝ), raySeq (cov := cov) hmet (γ 0) (fun m => xn (φ m))
      (fun m => (ln (φ m))⁻¹ • an (φ m)) t n = GExp (cov := cov) hmet (xn (φ n)) (t • un (φ n)) := by
    intro n t
    show GExp (cov := cov) hmet (xn (φ n))
        (t • frameVector (I := I) (γ 0) (xn (φ n)) ((ln (φ n))⁻¹ • an (φ n)))
      = GExp (cov := cov) hmet (xn (φ n)) (t • un (φ n))
    rw [frameVector_smul, han_frame_φ n]
  have hB_eq : ∀ k, velCoords (cov := cov) hmet (γ 0) (fun m => xn (φ m))
      (fun m => (ln (φ m))⁻¹ • an (φ m)) (γ (1 / 2)) (ln (φ k)) k
      = (trivializationAt E (TangentSpace I) (γ (1 / 2))).continuousLinearMapAt ℝ (rn (φ k))
          (curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet (xn (φ k)) (s • un (φ k)))
            (ln (φ k))) := by
    intro k
    have hpt : raySeq (cov := cov) hmet (γ 0) (fun m => xn (φ m))
        (fun m => (ln (φ m))⁻¹ • an (φ m)) (ln (φ k)) k = rn (φ k) := by
      rw [hrayseq_gen k (ln (φ k))]
      have hvu : ln (φ k) • un (φ k) = Vn (φ k) := by
        show ln (φ k) • ((ln (φ k))⁻¹ • Vn (φ k)) = Vn (φ k)
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (hln_pos_φ k)), one_smul]
      rw [hvu, (hVn_spec (φ k)).1]
    show (trivializationAt E (TangentSpace I) (γ (1 / 2))).continuousLinearMapAt ℝ
        (raySeq (cov := cov) hmet (γ 0) (fun m => xn (φ m))
          (fun m => (ln (φ m))⁻¹ • an (φ m)) (ln (φ k)) k)
        (curveVelocity (I := I) (fun r : ℝ => raySeq (cov := cov) hmet (γ 0) (fun m => xn (φ m))
          (fun m => (ln (φ m))⁻¹ • an (φ m)) r k) (ln (φ k)))
      = (trivializationAt E (TangentSpace I) (γ (1 / 2))).continuousLinearMapAt ℝ (rn (φ k))
          (curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet (xn (φ k)) (s • un (φ k)))
            (ln (φ k)))
    rw [show (fun r : ℝ => raySeq (cov := cov) hmet (γ 0) (fun m => xn (φ m))
          (fun m => (ln (φ m))⁻¹ • an (φ m)) r k)
        = (fun s : ℝ => GExp (cov := cov) hmet (xn (φ k)) (s • un (φ k))) from
        funext (fun r => hrayseq_gen k r), hpt]
  have hchart_orth : ∀ᶠ k in atTop,
      chartGram (I := I) (γ (1 / 2)) (rn (φ k))
        (deriv (fun τ : ℝ => (extChartAt I (γ (1 / 2))) (F (sn (φ k)) τ)) (tn (φ k)))
        (velCoords (cov := cov) hmet (γ 0) (fun m => xn (φ m)) (fun m => (ln (φ m))⁻¹ • an (φ m))
          (γ (1 / 2)) (ln (φ k)) k) = 0 := by
    filter_upwards [hφtend.eventually horth, hrn_chart, hφtend.eventually hFsm,
      hφtend.eventually htn, hφtend.eventually htn_Ioo] with k hk hsrck hsm htnk htnIook
    have hsrcE : rn (φ k) ∈ (extChartAt I (γ (1 / 2))).source := by
      rw [extChartAt_source]; exact hsrck
    have hmd : MDifferentiableAt 𝓘(ℝ) I (F (sn (φ k))) (tn (φ k)) :=
      (hsm.1.contMDiffAt (Icc_mem_nhds htnIook.1 htnIook.2)).mdifferentiableAt (by simp)
    have hA_eq : deriv (fun τ : ℝ => (extChartAt I (γ (1 / 2))) (F (sn (φ k)) τ)) (tn (φ k))
        = (trivializationAt E (TangentSpace I) (γ (1 / 2))).continuousLinearMapAt ℝ (rn (φ k))
            (curveVelocity (I := I) (F (sn (φ k))) (tn (φ k))) :=
      Submission.GlobalBM.deriv_extChartAt_eq_continuousLinearMapAt_curveVelocity (I := I)
        (x := γ (1 / 2)) (γ := F (sn (φ k))) (t := tn (φ k)) hmd hsrck
    calc chartGram (I := I) (γ (1 / 2)) (rn (φ k))
          (deriv (fun τ : ℝ => (extChartAt I (γ (1 / 2))) (F (sn (φ k)) τ)) (tn (φ k)))
          (velCoords (cov := cov) hmet (γ 0) (fun m => xn (φ m)) (fun m => (ln (φ m))⁻¹ • an (φ m))
            (γ (1 / 2)) (ln (φ k)) k)
        = chartGram (I := I) (γ (1 / 2)) (rn (φ k))
            ((trivializationAt E (TangentSpace I) (γ (1 / 2))).continuousLinearMapAt ℝ (rn (φ k))
              (curveVelocity (I := I) (F (sn (φ k))) (tn (φ k))))
            ((trivializationAt E (TangentSpace I) (γ (1 / 2))).continuousLinearMapAt ℝ (rn (φ k))
              (curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet (xn (φ k)) (s • un (φ k)))
                (ln (φ k)))) := by
          rw [hA_eq, hB_eq k]
      _ = inner ℝ (curveVelocity (I := I) (F (sn (φ k))) (tn (φ k)))
            (curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet (xn (φ k)) (s • un (φ k)))
              (ln (φ k))) :=
          Submission.GExpFlow.chartGram_clm (I := I) (z₀ := γ (1 / 2)) (q := rn (φ k)) hsrcE _ _
      _ = 0 := hk
  -- ## 22. Passing to the limit
  have hgram_tend : Tendsto (fun k => chartGram (I := I) (γ (1 / 2)) (rn (φ k))
      (deriv (fun τ : ℝ => (extChartAt I (γ (1 / 2))) (F (sn (φ k)) τ)) (tn (φ k)))
      (velCoords (cov := cov) hmet (γ 0) (fun m => xn (φ m)) (fun m => (ln (φ m))⁻¹ • an (φ m))
        (γ (1 / 2)) (ln (φ k)) k)) atTop
      (𝓝 (chartGram (I := I) (γ (1 / 2)) (γ (1 / 2)) Ainf Binf)) := by
    have hcont := continuousAt_chartGram3 (I := I) (z := γ (1 / 2))
      (mem_chart_source H (γ (1 / 2))) Ainf Binf
    have hpair : Tendsto (fun k => ((rn (φ k),
        deriv (fun τ : ℝ => (extChartAt I (γ (1 / 2))) (F (sn (φ k)) τ)) (tn (φ k))),
        velCoords (cov := cov) hmet (γ 0) (fun m => xn (φ m)) (fun m => (ln (φ m))⁻¹ • an (φ m))
          (γ (1 / 2)) (ln (φ k)) k)) atTop (𝓝 ((γ (1 / 2), Ainf), Binf)) :=
      (Prod.tendsto_iff (fun k => ((rn (φ k),
          deriv (fun τ : ℝ => (extChartAt I (γ (1 / 2))) (F (sn (φ k)) τ)) (tn (φ k))),
          velCoords (cov := cov) hmet (γ 0) (fun m => xn (φ m))
            (fun m => (ln (φ m))⁻¹ • an (φ m)) (γ (1 / 2)) (ln (φ k)) k))
        ((γ (1 / 2), Ainf), Binf)).mpr
        ⟨(Prod.tendsto_iff (fun k => (rn (φ k),
            deriv (fun τ : ℝ => (extChartAt I (γ (1 / 2))) (F (sn (φ k)) τ)) (tn (φ k))))
          (γ (1 / 2), Ainf)).mpr ⟨hrn_tend2, hA⟩, hB⟩
    exact hcont.tendsto.comp hpair
  have hlim_gram : chartGram (I := I) (γ (1 / 2)) (γ (1 / 2)) Ainf Binf = 0 := by
    have hconst : Tendsto (fun k => chartGram (I := I) (γ (1 / 2)) (rn (φ k))
        (deriv (fun τ : ℝ => (extChartAt I (γ (1 / 2))) (F (sn (φ k)) τ)) (tn (φ k)))
        (velCoords (cov := cov) hmet (γ 0) (fun m => xn (φ m)) (fun m => (ln (φ m))⁻¹ • an (φ m))
          (γ (1 / 2)) (ln (φ k)) k)) atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hchart_orth] with k hk
      exact hk.symm
    exact tendsto_nhds_unique hgram_tend hconst
  -- ## 23. The value of the chart metric is non-zero
  have hBinf : Binf
      = (trivializationAt E (TangentSpace I) (γ (1 / 2))).continuousLinearMapAt ℝ (γ (1 / 2)) W := by
    show (trivializationAt E (TangentSpace I) (γ (1 / 2))).continuousLinearMapAt ℝ
        (rayLim (cov := cov) hmet (γ 0) (γ 0) ((m⁻¹ : ℝ) • a) m)
        (curveVelocity (I := I) (rayLim (cov := cov) hmet (γ 0) (γ 0) ((m⁻¹ : ℝ) • a)) m)
      = (trivializationAt E (TangentSpace I) (γ (1 / 2))).continuousLinearMapAt ℝ (γ (1 / 2)) W
    rw [hraylim, hraylim_fun]
  have hAinf : Ainf = (trivializationAt E (TangentSpace I) (γ (1 / 2))).continuousLinearMapAt ℝ
      (γ (1 / 2)) (curveVelocity (I := I) γ (1 / 2)) :=
    Submission.GlobalBM.deriv_extChartAt_eq_continuousLinearMapAt_curveVelocity (I := I)
      (x := γ (1 / 2)) (γ := γ) (t := 1 / 2) (hγsm.mdifferentiableAt (by simp))
      (mem_chart_source H (γ (1 / 2)))
  have hsrc_self : γ (1 / 2) ∈ (extChartAt I (γ (1 / 2))).source := by
    rw [extChartAt_source]; exact mem_chart_source H (γ (1 / 2))
  have hvnorm : ‖curveVelocity (I := I) γ (1 / 2)‖ = 2 * m := by
    rw [← Submission.GeodesicSpeed.curveSpeed_eq_norm (I := I) γ (1 / 2)]
    exact hsp (1 / 2) (by constructor <;> norm_num)
  rcases hW' with hW' | hW'
  · have hval : chartGram (I := I) (γ (1 / 2)) (γ (1 / 2)) Ainf Binf = 2 * m := by
      rw [hAinf, hBinf, hW',
        Submission.GExpFlow.chartGram_clm (I := I) (z₀ := γ (1 / 2)) (q := γ (1 / 2)) hsrc_self]
      rw [inner_smul_right, real_inner_self_eq_norm_sq, hvnorm]
      have h2m : (2 * m : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hval] at hlim_gram
    exact absurd hlim_gram (ne_of_gt (by positivity : (0 : ℝ) < 2 * m))
  · have hval : chartGram (I := I) (γ (1 / 2)) (γ (1 / 2)) Ainf Binf = -(2 * m) := by
      rw [hAinf, hBinf, hW',
        Submission.GExpFlow.chartGram_clm (I := I) (z₀ := γ (1 / 2)) (q := γ (1 / 2)) hsrc_self]
      rw [inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq, hvnorm]
      have h2m : (2 * m : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hval] at hlim_gram
    exact absurd hlim_gram (neg_ne_zero.mpr (ne_of_gt (by positivity : (0 : ℝ) < 2 * m)))

end

end Work.EvenBound.ThirdGeodesic
