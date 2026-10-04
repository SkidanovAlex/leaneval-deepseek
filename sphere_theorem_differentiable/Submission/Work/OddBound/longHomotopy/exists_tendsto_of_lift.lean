import Mathlib
import Submission.Work.OddBound.LiftKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

namespace Work.OddBound.longHomotopy

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open LeanEval.Geometry.SphereTheorem Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length Submission.InjRadius

/-!
# The limit of a bounded lift under the (global) exponential map

If `h : ℝ → M` is continuous at `T`, `W : ℝ → T_pM` is a continuous lift of `h` on `(a,T)` (i.e.
`GExp p (W s) = h s`) whose values stay in the closed ball of radius `ρ < π/√K`, and `sec ≤ K` with
`0 < K`, then `W` has a limit as `s → T⁻`.

The point is that below `π/√K` the exponential map is a local diffeomorphism (no conjugate points,
`ConjCut`/`RayConj`), so the fibre `GExp p ⁻¹' {h T}` intersected with the compact ball is *finite*:
it is compact and every point is isolated.  The cluster set of `W` at `T⁻` is then contained in this
finite set, and continuity of `W` on the connected interval rules out more than one cluster point.
-/

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]

/-- **The left-neighbourhood filter has the intervals `Ioo (T - ε) T` as a basis.** -/
theorem eventually_nhdsLT_iff {T : ℝ} {P : ℝ → Prop} :
    (∀ᶠ s in 𝓝[<] T, P s) ↔ ∃ δ > 0, ∀ s, T - δ < s → s < T → P s := by
  constructor
  · intro h
    obtain ⟨u, hu, husub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp h
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hu
    refine ⟨δ, hδ, fun s hs1 hs2 => husub ⟨hball ?_, hs2⟩⟩
    rw [Metric.mem_ball, Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  · rintro ⟨δ, hδ, hP⟩
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨Set.Ioo (T - δ) (T + 1), ?_, ?_⟩
    · exact isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
    · rintro s ⟨hs1, hs2⟩
      rw [Set.mem_Ioo] at hs1
      rw [Set.mem_Iio] at hs2
      exact hP s hs1.1 hs2

/-- **Intermediate value theorem, order-agnostic version.**  If `f` is continuous on the interval
spanned by `x` and `y` (in either order) and `f x < c < f y`, then `c` is attained in between. -/
theorem exists_eq_of_continuousOn_Icc_of_lt {f : ℝ → ℝ} {x y c : ℝ}
    (hcont : ContinuousOn f (Set.Icc (min x y) (max x y)))
    (hx : f x < c) (hy : c < f y) :
    ∃ z, z ∈ Set.Icc (min x y) (max x y) ∧ f z = c := by
  rcases le_total x y with hxy | hyx
  · have hmin : min x y = x := min_eq_left hxy
    have hmax : max x y = y := max_eq_right hxy
    rw [hmin, hmax] at hcont ⊢
    have hmem : c ∈ Set.Icc (f x) (f y) := ⟨le_of_lt hx, le_of_lt hy⟩
    obtain ⟨z, hz, hfz⟩ := intermediate_value_Icc hxy hcont hmem
    exact ⟨z, hz, hfz⟩
  · have hmin : min x y = y := min_eq_right hyx
    have hmax : max x y = x := max_eq_left hyx
    rw [hmin, hmax] at hcont ⊢
    have hmem : c ∈ Set.Icc (f x) (f y) := ⟨le_of_lt hx, le_of_lt hy⟩
    obtain ⟨z, hz, hfz⟩ := intermediate_value_Icc' hyx hcont hmem
    exact ⟨z, hz, hfz⟩

/-- **Continuity of the exponential map at a fixed point in the fibre topology.**  The manifold
exponential map is `C^∞` in the *model* norm (`exists_contMDiffAt_GExp`); the fibre norm and the
model norm are comparable (`XuMain.exists_pos_model_fibre_norm`), which transfers the statement. -/
theorem continuousAt_GExp_tangent (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    (p : M) (v : TangentSpace I p) :
    ContinuousAt (fun w : TangentSpace I p => GExp (cov := cov) hmet p w) v := by
  obtain ⟨lam, hlam, Lam, hLam, hbnd⟩ := Submission.XuMain.exists_pos_model_fibre_norm (I := I) p
  have hslam : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hcoe : Tendsto (fun w : TangentSpace I p => (show E from w)) (𝓝 v) (𝓝 (show E from v)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [Metric.ball_mem_nhds v (mul_pos hε hslam)] with w hw
    rw [Metric.mem_ball] at hw
    rw [dist_eq_norm]
    have h1 := (hbnd (w - v)).1
    have h2 : (show E from (w - v)) = (show E from w) - (show E from v) := rfl
    rw [h2] at h1
    calc ‖(show E from w) - (show E from v)‖ ≤ ‖w - v‖ / Real.sqrt lam := h1
      _ < ε := by rw [div_lt_iff₀ hslam]; simpa only [dist_eq_norm] using hw
  have hmodel : Tendsto
      (fun w : E => GExp (cov := cov) hmet p (show TangentSpace I p from w))
      (𝓝 (show E from v)) (𝓝 (GExp (cov := cov) hmet p v)) :=
    (Submission.GExpSmooth.exists_contMDiffAt_GExp (cov := cov) hmet p v).continuousAt
  exact hmodel.comp hcoe

/-- Continuity of the exponential map on the whole tangent space, in the fibre topology. -/
theorem continuous_GExp_tangent (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    (p : M) : Continuous (fun w : TangentSpace I p => GExp (cov := cov) hmet p w) :=
  continuous_iff_continuousAt.mpr (fun v => continuousAt_GExp_tangent (cov := cov) hmet p v)

/-- **Sequential compactness of the closed ball in the tangent space.** -/
theorem exists_subseq_tendsto_closedBall (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    (p : M) {ρ : ℝ} {u : ℕ → TangentSpace I p}
    (hu : ∀ n, u n ∈ Metric.closedBall (0 : TangentSpace I p) ρ) :
    ∃ v ∈ Metric.closedBall (0 : TangentSpace I p) ρ, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 v) := by
  haveI : ProperSpace (TangentSpace I p) := by
    haveI : FiniteDimensional ℝ (TangentSpace I p) := ‹FiniteDimensional ℝ E›
    exact FiniteDimensional.proper ℝ (TangentSpace I p)
  exact IsCompact.tendsto_subseq (isCompact_closedBall (0 : TangentSpace I p) ρ) hu

end Helpers

theorem exists_tendsto_of_lift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hK : 0 < K) (hcurv : Submission.RauchK.CurvLe cov K)
    {p : M} {ρ : ℝ} (hρ : ρ < Real.pi / Real.sqrt K)
    {h : ℝ → M} {T a : ℝ} (haT : a < T) (hh : ContinuousAt h T)
    {W : ℝ → TangentSpace I p}
    (hWc : ContinuousOn W (Set.Ioo a T))
    (hWmem : ∀ s ∈ Set.Ioo a T, W s ∈ Metric.closedBall (0 : TangentSpace I p) ρ)
    (hWG : ∀ s ∈ Set.Ioo a T, GExp (cov := cov) hmet p (W s) = h s) :
    ∃ v : TangentSpace I p, Tendsto W (𝓝[<] T) (𝓝 v) := by
  classical
  haveI hproper : ProperSpace (TangentSpace I p) := by
    haveI : FiniteDimensional ℝ (TangentSpace I p) := ‹FiniteDimensional ℝ E›
    exact FiniteDimensional.proper ℝ (TangentSpace I p)
  have hcontG : Continuous (fun w : TangentSpace I p => GExp (cov := cov) hmet p w) :=
    continuous_GExp_tangent (cov := cov) hmet p
  have hloc : ∀ v : TangentSpace I p, ‖v‖ < Real.pi / Real.sqrt K →
      Submission.CutStep2.LocallyInjectiveAtGExp (I := I) hmet p v := by
    intro v hv
    by_cases hv0 : v = 0
    · subst hv0
      refine Submission.GExpLocalInj.locallyInjectiveAtGExp_of_injective_mfderiv (cov := cov) hmet ?_
      rw [show (show E from (0 : TangentSpace I p)) = (0 : E) from rfl,
        Submission.GExpLocalInj.mfderiv_GExp_zero (cov := cov) hmet p]
      exact Function.injective_id
    · exact Submission.RayConj.locallyInjectiveAtGExp_of_norm_lt_pi_div_sqrt (cov := cov) hmet htor
        hcurv hK hv0 hv
  -- ## The (finite) fibre of `h T` inside the compact ball
  set F : Set (TangentSpace I p) :=
    {v | v ∈ Metric.closedBall (0 : TangentSpace I p) ρ ∧ GExp (cov := cov) hmet p v = h T}
    with hFdef
  have hFmem : ∀ x : ↥F, x.1 ∈ Metric.closedBall (0 : TangentSpace I p) ρ ∧
      GExp (cov := cov) hmet p x.1 = h T := by
    intro x
    have hx : x.1 ∈ {v : TangentSpace I p |
        v ∈ Metric.closedBall (0 : TangentSpace I p) ρ ∧ GExp (cov := cov) hmet p v = h T} := by
      simpa only [hFdef] using x.2
    simpa only [Set.mem_setOf_eq] using hx
  have hFintro : ∀ y : TangentSpace I p, y ∈ Metric.closedBall (0 : TangentSpace I p) ρ →
      GExp (cov := cov) hmet p y = h T → y ∈ F := by
    intro y h1 h2
    rw [hFdef]
    exact ⟨h1, h2⟩
  have hFclosed : IsClosed F := by
    rw [hFdef]
    exact Metric.isClosed_closedBall.inter (isClosed_singleton.preimage hcontG)
  have hFcomp : IsCompact F :=
    (isCompact_closedBall (0 : TangentSpace I p) ρ).of_isClosed_subset hFclosed (fun y hy => hy.1)
  -- every point of `F` is isolated, because `GExp p` is locally injective there
  have hFfin : F.Finite := by
    have hiso : ∀ x : ↥F, ∃ U : Set (TangentSpace I p), IsOpen U ∧ x.1 ∈ U ∧ U ∩ F ⊆ {x.1} := by
      intro x
      obtain ⟨hx1, hx2⟩ := hFmem x
      have hxρ : ‖x.1‖ ≤ ρ := by
        rw [Metric.mem_closedBall, dist_zero_right] at hx1
        exact hx1
      obtain ⟨s, hs, hinj⟩ := hloc x.1 (lt_of_le_of_lt hxρ hρ)
      refine ⟨interior s, isOpen_interior,
        mem_of_mem_nhds (interior_mem_nhds.mpr hs), ?_⟩
      rintro y ⟨hyU, hyF⟩
      have hy_s : y ∈ s := interior_subset hyU
      have hx_s : x.1 ∈ s := interior_subset (mem_of_mem_nhds (interior_mem_nhds.mpr hs))
      have hGF : GExp (cov := cov) hmet p y = GExp (cov := cov) hmet p x.1 := by
        have hy2 := (hFmem ⟨y, hyF⟩).2
        rw [hy2, hx2]
      exact hinj y hy_s x.1 hx_s hGF
    choose U hUo hUx hUF using hiso
    have hcover : F ⊆ ⋃ x : ↥F, U x := fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hUx ⟨y, hy⟩⟩
    obtain ⟨t, ht⟩ := hFcomp.elim_finite_subcover U hUo hcover
    refine (Finset.finite_toSet (t.image (fun x : ↥F => x.1))).subset ?_
    intro y hy
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (ht hy)
    have hyeq : y = x.1 := by
      have := hUF x ⟨hyx, hy⟩
      simpa using this
    exact Finset.mem_image.mpr ⟨x, hxt, hyeq.symm⟩
  -- ## An explicit sequence in `(a,T)` tending to `T`
  set s : ℕ → ℝ := fun n => max (T - 1 / ((n : ℝ) + 1)) ((T + a) / 2) with hsdef
  have hs_mem : ∀ n, s n ∈ Set.Ioo a T := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    rw [Set.mem_Ioo]
    constructor
    · exact lt_of_lt_of_le (by linarith : a < (T + a) / 2) (le_max_right _ _)
    · exact max_lt (by linarith) (by linarith)
  have hs_tend : Tendsto s atTop (𝓝 T) := by
    have h1 : Tendsto (fun n : ℕ => T - 1 / ((n : ℝ) + 1)) atTop (𝓝 T) := by
      have h := (tendsto_const_nhds (x := T)).sub tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using h
    have h2 : Tendsto (fun _ : ℕ => (T + a) / 2) atTop (𝓝 ((T + a) / 2)) := tendsto_const_nhds
    have h3 : Tendsto (fun n : ℕ => max (T - 1 / ((n : ℝ) + 1)) ((T + a) / 2)) atTop
        (𝓝 (max T ((T + a) / 2))) := h1.max h2
    rw [max_eq_left (by linarith : (T + a) / 2 ≤ T)] at h3
    simpa only [hsdef] using h3
  -- ## A cluster value `v₀` of `W` along `s`
  obtain ⟨v₀, hv₀B, φ₁, hφ₁mono, hφ₁tend⟩ :=
    exists_subseq_tendsto_closedBall (cov := cov) hmet p (u := fun n => W (s n))
      (fun n => hWmem (s n) (hs_mem n))
  set s' : ℕ → ℝ := fun n => s (φ₁ n) with hs'def
  have hs'_mem : ∀ n, s' n ∈ Set.Ioo a T := fun n => hs_mem (φ₁ n)
  have hs'_tend : Tendsto s' atTop (𝓝 T) := hs_tend.comp hφ₁mono.tendsto_atTop
  have hWs'tend : Tendsto (fun n => W (s' n)) atTop (𝓝 v₀) := hφ₁tend
  have hv₀F : v₀ ∈ F := by
    refine hFintro v₀ hv₀B ?_
    have h1 : Tendsto (fun n => GExp (cov := cov) hmet p (W (s' n))) atTop
        (𝓝 (GExp (cov := cov) hmet p v₀)) :=
      (continuousAt_GExp_tangent (cov := cov) hmet p v₀).tendsto.comp hWs'tend
    have h2 : Tendsto (fun n => GExp (cov := cov) hmet p (W (s' n))) atTop (𝓝 (h T)) := by
      refine (hh.tendsto.comp hs'_tend).congr' ?_
      exact Eventually.of_forall (fun n => (hWG (s' n) (hs'_mem n)).symm)
    exact tendsto_nhds_unique h1 h2
  refine ⟨v₀, ?_⟩
  -- ## `W → v₀` along `𝓝[<] T`
  rw [Metric.tendsto_nhds]
  intro ε hε
  by_contra hcon
  -- the "bad" sequence, at distance at least `ε` from `v₀`
  have hbad : ∀ n : ℕ, ∃ t : ℝ,
      T - min (1 / ((n : ℝ) + 1)) ((T - a) / 2) < t ∧ t < T ∧ ε ≤ dist (W t) v₀ := by
    intro n
    have hδpos : 0 < min (1 / ((n : ℝ) + 1)) ((T - a) / 2) :=
      lt_min (by positivity) (by linarith)
    have hnot : ¬ ∃ δ > 0, ∀ s, T - δ < s → s < T → dist (W s) v₀ < ε :=
      (eventually_nhdsLT_iff (T := T) (P := fun s => dist (W s) v₀ < ε)).not.mp hcon
    push_neg at hnot
    obtain ⟨t, ht1, ht2, ht3⟩ := hnot (min (1 / ((n : ℝ) + 1)) ((T - a) / 2)) hδpos
    exact ⟨t, ht1, ht2, ht3⟩
  choose t htlow htT htdist using hbad
  have hta : ∀ n, a < t n := by
    intro n
    have hle : min (1 / ((n : ℝ) + 1)) ((T - a) / 2) ≤ (T - a) / 2 := min_le_right _ _
    linarith [htlow n]
  have htmem : ∀ n, t n ∈ Set.Ioo a T := fun n => ⟨hta n, htT n⟩
  have httend : Tendsto t atTop (𝓝 T) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun n => dist_nonneg) (fun n => ?_)
    rw [Real.dist_eq, abs_of_nonpos (by linarith [htT n] : t n - T ≤ 0)]
    have hle : min (1 / ((n : ℝ) + 1)) ((T - a) / 2) ≤ 1 / ((n : ℝ) + 1) := min_le_left _ _
    linarith [htlow n]
  -- a cluster value `w₁ ≠ v₀` of the bad sequence
  obtain ⟨w₁, hw₁B, φ₂, hφ₂mono, hφ₂tend⟩ :=
    exists_subseq_tendsto_closedBall (cov := cov) hmet p (u := fun n => W (t n))
      (fun n => hWmem (t n) (htmem n))
  set t' : ℕ → ℝ := fun n => t (φ₂ n) with ht'def
  have ht'mem : ∀ n, t' n ∈ Set.Ioo a T := fun n => htmem (φ₂ n)
  have ht'tend : Tendsto t' atTop (𝓝 T) := httend.comp hφ₂mono.tendsto_atTop
  have hWt'tend : Tendsto (fun n => W (t' n)) atTop (𝓝 w₁) := hφ₂tend
  have hw₁F : w₁ ∈ F := by
    refine hFintro w₁ hw₁B ?_
    have h1 : Tendsto (fun n => GExp (cov := cov) hmet p (W (t' n))) atTop
        (𝓝 (GExp (cov := cov) hmet p w₁)) :=
      (continuousAt_GExp_tangent (cov := cov) hmet p w₁).tendsto.comp hWt'tend
    have h2 : Tendsto (fun n => GExp (cov := cov) hmet p (W (t' n))) atTop (𝓝 (h T)) := by
      refine (hh.tendsto.comp ht'tend).congr' ?_
      exact Eventually.of_forall (fun n => (hWG (t' n) (ht'mem n)).symm)
    exact tendsto_nhds_unique h1 h2
  have hεle : ε ≤ dist w₁ v₀ := by
    have hlim : Tendsto (fun n => dist (W (t' n)) v₀) atTop (𝓝 (dist w₁ v₀)) :=
      hWt'tend.dist tendsto_const_nhds
    exact ge_of_tendsto hlim (Eventually.of_forall (fun n => htdist (φ₂ n)))
  have hw₁ne : w₁ ≠ v₀ := by
    intro hw
    rw [hw, dist_self] at hεle
    linarith
  -- ## The minimal positive distance from `v₀` to the other points of `F`
  have hF'fin : (F \ {v₀}).Finite := hFfin.sdiff
  have hF'ne : (F \ {v₀}).Nonempty :=
    ⟨w₁, by simp only [Set.mem_sdiff, Set.mem_singleton_iff]; exact ⟨hw₁F, hw₁ne⟩⟩
  obtain ⟨wstar, hwstar_mem, hwstar_min⟩ :=
    Set.exists_min_image (F \ {v₀}) (fun w => ‖w - v₀‖) hF'fin hF'ne
  set d : ℝ := ‖wstar - v₀‖ with hddef
  have hdpos : 0 < d := by
    have hne : wstar ≠ v₀ := by
      have hmem := hwstar_mem
      simp only [Set.mem_sdiff, Set.mem_singleton_iff] at hmem
      exact hmem.2
    rw [hddef, norm_pos_iff]
    exact sub_ne_zero.mpr hne
  have hdle : ∀ w ∈ F, w ≠ v₀ → d ≤ ‖w - v₀‖ := by
    intro w hw hwne
    refine hwstar_min w ?_
    simp only [Set.mem_sdiff, Set.mem_singleton_iff]
    exact ⟨hw, hwne⟩
  -- ## The intermediate value `c`
  set c : ℝ := min (d / 2) (ε / 2) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; exact lt_min (by linarith) (by linarith)
  have hcltd : c < d := by rw [hcdef]; linarith [min_le_left (d / 2) (ε / 2)]
  have hclte : c < ε := by rw [hcdef]; linarith [min_le_right (d / 2) (ε / 2)]
  have hev1 : ∀ᶠ n in atTop, dist (W (s' n)) v₀ < c := by
    have hlim : Tendsto (fun n => dist (W (s' n)) v₀) atTop (𝓝 0) := by
      have h := hWs'tend.dist (tendsto_const_nhds (x := v₀))
      simpa using h
    exact hlim.eventually (isOpen_Iio.mem_nhds hcpos)
  have hev2 : ∀ᶠ n in atTop, c < dist (W (t' n)) v₀ :=
    Eventually.of_forall (fun n => lt_of_lt_of_le hclte (htdist (φ₂ n)))
  have hev3 : ∀ᶠ n in atTop, ∃ z : ℝ,
      z ∈ Set.Icc (min (s' n) (t' n)) (max (s' n) (t' n)) ∧
      z ∈ Set.Ioo a T ∧ dist (W z) v₀ = c := by
    filter_upwards [hev1, hev2] with n hn1 hn2
    have hsub : Set.Icc (min (s' n) (t' n)) (max (s' n) (t' n)) ⊆ Set.Ioo a T := by
      intro u hu
      rw [Set.mem_Icc] at hu
      rw [Set.mem_Ioo]
      exact ⟨lt_of_lt_of_le (lt_min (hs'_mem n).1 (ht'mem n).1) hu.1,
             lt_of_le_of_lt hu.2 (max_lt (hs'_mem n).2 (ht'mem n).2)⟩
    have hcont : ContinuousOn (fun u : ℝ => dist (W u) v₀)
        (Set.Icc (min (s' n) (t' n)) (max (s' n) (t' n))) := by
      have hbase : ContinuousOn (fun u : ℝ => W u - v₀)
          (Set.Icc (min (s' n) (t' n)) (max (s' n) (t' n))) :=
        (hWc.mono hsub).sub continuousOn_const
      simpa only [dist_eq_norm] using hbase.norm
    obtain ⟨z, hzIcc, hzc⟩ :=
      exists_eq_of_continuousOn_Icc_of_lt (x := s' n) (y := t' n) (c := c) hcont hn1 hn2
    exact ⟨z, hzIcc, hsub hzIcc, hzc⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev3
  choose z hzIcc hzIoo hzc using fun k : ℕ => hN (N + k) (Nat.le_add_right N k)
  have hztend : Tendsto z atTop (𝓝 T) := by
    have hshift : Tendsto (fun k : ℕ => N + k) atTop atTop :=
      StrictMono.tendsto_atTop (fun a b hab => by omega)
    have h1 : Tendsto (fun k : ℕ => s' (N + k)) atTop (𝓝 T) := hs'_tend.comp hshift
    have h2 : Tendsto (fun k : ℕ => t' (N + k)) atTop (𝓝 T) := ht'tend.comp hshift
    have hmin : Tendsto (fun k : ℕ => min (s' (N + k)) (t' (N + k))) atTop (𝓝 T) := by
      have h3 := h1.min h2
      simpa using h3
    have hmax : Tendsto (fun k : ℕ => max (s' (N + k)) (t' (N + k))) atTop (𝓝 T) := by
      have h3 := h1.max h2
      simpa using h3
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hmin hmax
      (fun k => (hzIcc k).1) (fun k => (hzIcc k).2)
  -- ## The resulting cluster point `v₂ ∈ F`, at distance exactly `c` from `v₀`
  have hWzmem : ∀ k, W (z k) ∈ Metric.closedBall (0 : TangentSpace I p) ρ :=
    fun k => hWmem (z k) (hzIoo k)
  obtain ⟨v₂, hv₂B, φ₃, hφ₃mono, hφ₃tend⟩ :=
    exists_subseq_tendsto_closedBall (cov := cov) hmet p (u := fun k => W (z k)) hWzmem
  have hv₂F : v₂ ∈ F := by
    refine hFintro v₂ hv₂B ?_
    have hzt : Tendsto (fun k : ℕ => z (φ₃ k)) atTop (𝓝 T) := hztend.comp hφ₃mono.tendsto_atTop
    have h1 : Tendsto (fun k => GExp (cov := cov) hmet p (W (z (φ₃ k)))) atTop
        (𝓝 (GExp (cov := cov) hmet p v₂)) :=
      (continuousAt_GExp_tangent (cov := cov) hmet p v₂).tendsto.comp hφ₃tend
    have h2 : Tendsto (fun k => GExp (cov := cov) hmet p (W (z (φ₃ k)))) atTop (𝓝 (h T)) := by
      refine (hh.tendsto.comp hzt).congr' ?_
      exact Eventually.of_forall (fun k => (hWG (z (φ₃ k)) (hzIoo (φ₃ k))).symm)
    exact tendsto_nhds_unique h1 h2
  have hv₂dist : dist v₂ v₀ = c := by
    have hlim : Tendsto (fun k => dist (W (z (φ₃ k))) v₀) atTop (𝓝 (dist v₂ v₀)) :=
      hφ₃tend.dist tendsto_const_nhds
    have hconst : Tendsto (fun k => dist (W (z (φ₃ k))) v₀) atTop (𝓝 c) := by
      have hEq : (fun k => dist (W (z (φ₃ k))) v₀) = fun _ => c := funext (fun k => hzc (φ₃ k))
      rw [hEq]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hlim hconst
  have hv₂ne : v₂ ≠ v₀ := by
    intro hv
    rw [hv, dist_self] at hv₂dist
    linarith
  -- contradiction with the minimality of `d`
  have hdle' := hdle v₂ hv₂F hv₂ne
  have hdle'' : d ≤ c := by
    rw [← hv₂dist]
    simpa only [dist_eq_norm] using hdle'
  linarith

end Work.OddBound.longHomotopy
