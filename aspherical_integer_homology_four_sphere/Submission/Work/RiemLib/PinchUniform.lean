import Submission.Work.RiemLib.Pinch
import Submission.Work.RiemLib.ChartCurvCont
import Submission.Work.RiemLib.ChartBounds
import Submission.Work.RiemLib.IndexForm
import Submission.Work.RiemLib.Rauch

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Uniform strict pinching

`QuarterPinched cov` says that every sectional curvature is *strictly* bigger than `1` *at every
point and every orthonormal pair*: `1 < ⟪R(X,Y)Y, X⟫`.  Here we upgrade this pointwise strict bound
to a **uniform** one: on a compact manifold there is `c > 1` with `c < sec` at every orthonormal
pair.

The proof is the standard compactness argument, in coordinates.  For each `x₀` we produce a compact
neighbourhood `K ∋ x₀` (the image under the chart inverse of a closed ball inside the chart target)
and, using the joint continuity of the chart curvature `chartCurv` (available from
`ChartCurvCont.continuousAt_dB_prod` and `IndexForm.continuousAt_chrB_prod3`) together with the
chart-metric bounds `ChartBounds.exists_chartGram_bounds`, a constant `c_{x₀} > 1` strictly below the
sectional curvature of every orthonormal pair with foot in `K`.  Finitely many of the `K` cover `M`,
and the minimum of the finitely many `c_{x₀}` is the desired uniform constant.

## Main result

* `exists_uniform_lt_curvVec`: **uniform strict pinching**.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.ChartCurv
open Submission.ChartCurvCont
open Submission.ChartBounds
open Submission.IndexForm
open Submission.Pinch
open Submission.Curvature
open Submission.CurvatureVec
open Submission.Rauch

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.PinchUniform

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-! ## A compactness lemma for uniform strict lower bounds -/

/-- **Uniform strict lower bound on a compact set.**  If `S` is a subset of a compact set `C` which
is closed inside `C` (`closure S ∩ C ⊆ S`), and a continuous function `F` on `C` satisfies
`a < F` on `S`, then `a` can be improved to a value `c > a` with `c < F` on all of `S`. -/
lemma exists_lt_of_isCompact
    {X : Type*} [TopologicalSpace X] {C S : Set X} {F : X → ℝ} {a : ℝ}
    (hC : IsCompact C) (hSC : S ⊆ C) (hcl : closure S ∩ C ⊆ S) (hF : ContinuousOn F C)
    (h : ∀ q ∈ S, a < F q) : ∃ c, a < c ∧ ∀ q ∈ S, c < F q := by
  by_cases hne : S.Nonempty
  · have hSeq : S = closure S ∩ C :=
      Set.Subset.antisymm (fun q hq => ⟨subset_closure hq, hSC hq⟩) hcl
    have hScomp : IsCompact S := by
      rw [hSeq]; exact hC.inter_left isClosed_closure
    obtain ⟨x₀, hx₀S, hx₀min⟩ := hScomp.exists_isMinOn hne (hF.mono hSC)
    have hax : a < F x₀ := h x₀ hx₀S
    refine ⟨(a + F x₀) / 2, by linarith, fun q hq => ?_⟩
    have hle : F x₀ ≤ F q := hx₀min hq
    linarith
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    exact ⟨a + 1, by linarith, fun q hq => absurd (hne ▸ hq) (Set.notMem_empty q)⟩

/-! ## Joint continuity of the chart curvature -/

/-- **Joint continuity of `chartCurv`** in `(p, a, b)` at a point of the chart. -/
lemma continuousAt_chartCurv_prod (x₀ : M) {p₀ : M} (hp₀ : p₀ ∈ (chartAt H x₀).source) (a₀ b₀ : E) :
    ContinuousAt (fun q : M × E × E => chartCurv cov x₀ q.1 q.2.1 q.2.2) (p₀, a₀, b₀) := by
  have h1 : ContinuousAt (fun q : M × E × E => q.1) (p₀, a₀, b₀) := continuousAt_fst
  have h21 : ContinuousAt (fun q : M × E × E => q.2.1) (p₀, a₀, b₀) :=
    continuousAt_fst.comp continuousAt_snd
  have h22 : ContinuousAt (fun q : M × E × E => q.2.2) (p₀, a₀, b₀) :=
    continuousAt_snd.comp continuousAt_snd
  have h2 : ContinuousAt (fun q : M × E × E => dB cov x₀ q.1 q.2.1 q.2.2 q.2.2) (p₀, a₀, b₀) :=
    (continuousAt_dB_prod (cov := cov) (I := I) x₀ hp₀ a₀ b₀ b₀).comp
      (f := fun q : M × E × E => (q.1, q.2.1, q.2.2, q.2.2)) (x := (p₀, a₀, b₀))
      (h1.prodMk (h21.prodMk (h22.prodMk h22)))
  have h3 : ContinuousAt (fun q : M × E × E => dB cov x₀ q.1 q.2.2 q.2.2 q.2.1) (p₀, a₀, b₀) :=
    (continuousAt_dB_prod (cov := cov) (I := I) x₀ hp₀ b₀ b₀ a₀).comp
      (f := fun q : M × E × E => (q.1, q.2.2, q.2.2, q.2.1)) (x := (p₀, a₀, b₀))
      (h1.prodMk (h22.prodMk (h22.prodMk h21)))
  have hbb : ContinuousAt (fun q : M × E × E => chrB cov x₀ q.1 q.2.2 q.2.2) (p₀, a₀, b₀) :=
    (continuousAt_chrB_prod3 (cov := cov) (I := I) x₀ hp₀ b₀ b₀).comp
      (f := fun q : M × E × E => (q.1, q.2.2, q.2.2)) (x := (p₀, a₀, b₀))
      (h1.prodMk (h22.prodMk h22))
  have hba : ContinuousAt (fun q : M × E × E => chrB cov x₀ q.1 q.2.2 q.2.1) (p₀, a₀, b₀) :=
    (continuousAt_chrB_prod3 (cov := cov) (I := I) x₀ hp₀ b₀ a₀).comp
      (f := fun q : M × E × E => (q.1, q.2.2, q.2.1)) (x := (p₀, a₀, b₀))
      (h1.prodMk (h22.prodMk h21))
  have h4 : ContinuousAt (fun q : M × E × E =>
      chrB cov x₀ q.1 (chrB cov x₀ q.1 q.2.2 q.2.2) q.2.1) (p₀, a₀, b₀) :=
    (continuousAt_chrB_prod3 (cov := cov) (I := I) x₀ hp₀ (chrB cov x₀ p₀ b₀ b₀) a₀).comp
      (f := fun q : M × E × E => (q.1, chrB cov x₀ q.1 q.2.2 q.2.2, q.2.1)) (x := (p₀, a₀, b₀))
      (h1.prodMk (hbb.prodMk h21))
  have h5 : ContinuousAt (fun q : M × E × E =>
      chrB cov x₀ q.1 (chrB cov x₀ q.1 q.2.2 q.2.1) q.2.2) (p₀, a₀, b₀) :=
    (continuousAt_chrB_prod3 (cov := cov) (I := I) x₀ hp₀ (chrB cov x₀ p₀ b₀ a₀) b₀).comp
      (f := fun q : M × E × E => (q.1, chrB cov x₀ q.1 q.2.2 q.2.1, q.2.2)) (x := (p₀, a₀, b₀))
      (h1.prodMk (hba.prodMk h22))
  exact (((h2.sub h3).add h4).sub h5).congr
    (Filter.Eventually.of_forall fun q => by
      simp only [chartCurv, Pi.sub_apply, Pi.add_apply])

/-- **Joint continuity of `chartCurv`** on the chart source. -/
lemma continuousOn_chartCurv_prod (x₀ : M) :
    ContinuousOn (fun q : M × E × E => chartCurv cov x₀ q.1 q.2.1 q.2.2)
      ((chartAt H x₀).source ×ˢ (Set.univ : Set (E × E))) :=
  fun _q hq => (continuousAt_chartCurv_prod (cov := cov) (I := I) x₀ hq.1 _ _).continuousWithinAt

/-! ## The local uniform bound -/

variable [Nontrivial E]

/-- **Uniform strict pinching, locally.**  Every point has an open neighbourhood `U` contained in a
compact set `K` on which the sectional curvature of every orthonormal pair is bounded below by some
constant `> 1`. -/
theorem exists_uniform_lt_curvVec_local
    (hmet : IsMetricCompatible cov) (hpinch : QuarterPinched cov) (htor : cov.torsion = 0)
    (x₀ : M) :
    ∃ (U K : Set M), IsOpen U ∧ x₀ ∈ U ∧ U ⊆ K ∧ IsCompact K ∧ K ⊆ (chartAt H x₀).source ∧
      ∃ c : ℝ, 1 < c ∧ ∀ (p : M), p ∈ K → ∀ (u v : TangentSpace I p),
        inner ℝ u u = 1 → inner ℝ v v = 1 → inner ℝ u v = 0 →
        c < inner ℝ (curvVec cov p u v v) u := by
  classical
  set e : PartialEquiv M E := extChartAt I x₀ with hedef
  have htgt : IsOpen e.target := isOpen_extChartAt_target (I := I) x₀
  have hx0src : x₀ ∈ e.source := by
    rw [hedef, extChartAt_source]; exact mem_chart_source H x₀
  have hx0tgt : e x₀ ∈ e.target := e.map_source hx0src
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp htgt (e x₀) hx0tgt
  set r : ℝ := ε / 2 with hrdef
  have hrε : r < ε := by rw [hrdef]; linarith
  have hrpos : 0 < r := by rw [hrdef]; linarith
  have hrsub : closedBall (e x₀) r ⊆ e.target :=
    fun y hy => hεsub (closedBall_subset_ball hrε hy)
  set K : Set M := e.symm '' closedBall (e x₀) r with hKdef
  have hKcomp : IsCompact K := by
    rw [hKdef]
    refine IsCompact.image_of_continuousOn (isCompact_closedBall (e x₀) r) ?_
    have hc : ContinuousOn (e.symm : E → M) (e.target) := by
      rw [hedef]; exact continuousOn_extChartAt_symm (I := I) x₀
    exact hc.mono hrsub
  have hx0K : x₀ ∈ K := ⟨e x₀, mem_closedBall_self (le_of_lt hrpos), e.left_inv hx0src⟩
  have hKsrc : K ⊆ (chartAt H x₀).source := by
    rintro p ⟨y, hy, rfl⟩
    have h1 : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target (hrsub hy)
    rwa [extChartAt_source] at h1
  -- the open neighbourhood `U`
  set U : Set M := (chartAt H x₀).source ∩ (extChartAt I x₀) ⁻¹' ball (e x₀) r with hUdef
  have hUopen : IsOpen U := isOpen_extChartAt_preimage (I := I) x₀ Metric.isOpen_ball
  have hx0U : x₀ ∈ U := ⟨mem_chart_source H x₀, Metric.mem_ball_self hrpos⟩
  have hUK : U ⊆ K := by
    rintro p ⟨hps, hpb⟩
    refine ⟨e p, ?_, ?_⟩
    · exact Metric.ball_subset_closedBall hpb
    · have hps' : p ∈ e.source := by rw [hedef, extChartAt_source]; exact hps
      rw [hedef] at hpb ⊢
      exact (e.left_inv hps').symm ▸ rfl
  obtain ⟨lam, hlam, Lam, hLam, hbnd⟩ :=
    exists_chartGram_bounds (I := I) x₀ hKcomp ⟨x₀, hx0K⟩ hKsrc
  set R : ℝ := Real.sqrt (1 / lam) with hRdef
  have hRpos : 0 < R := Real.sqrt_pos.mpr (by positivity)
  have hnorm_le : ∀ (p : M), p ∈ K → ∀ a : E,
      chartGram (I := I) x₀ p a a = 1 → ‖a‖ ≤ R := by
    intro p hp a ha
    have h1 : lam * ‖a‖ ^ 2 ≤ 1 := by
      have := (hbnd p hp a).1
      rwa [ha] at this
    have h2 : ‖a‖ ^ 2 ≤ 1 / lam := by rw [le_div_iff₀ hlam]; linarith
    calc ‖a‖ = Real.sqrt (‖a‖ ^ 2) := (Real.sqrt_sq (norm_nonneg a)).symm
      _ ≤ Real.sqrt (1 / lam) := Real.sqrt_le_sqrt h2
      _ = R := rfl
  -- the compact set in coordinates and the "orthonormal pairs" locus
  set C : Set (M × E × E) := K ×ˢ (closedBall (0 : E) R ×ˢ closedBall (0 : E) R) with hCdef
  have hCcomp : IsCompact C :=
    hKcomp.prod ((isCompact_closedBall (0 : E) R).prod (isCompact_closedBall (0 : E) R))
  set S : Set (M × E × E) := C ∩ {q | chartGram (I := I) x₀ q.1 q.2.1 q.2.1 = 1 ∧
      chartGram (I := I) x₀ q.1 q.2.2 q.2.2 = 1 ∧
      chartGram (I := I) x₀ q.1 q.2.1 q.2.2 = 0} with hSdef
  have hSC : S ⊆ C := fun q hq => hq.1
  have hcl : closure S ∩ C ⊆ S := by
    rintro q ⟨hqcl, hqC⟩
    have hqK : q.1 ∈ K := hqC.1
    have hqsrc : q.1 ∈ (chartAt H x₀).source := hKsrc hqK
    have key : ∀ (f : M × E × E → ℝ) (a : ℝ), ContinuousAt f q → (∀ z ∈ S, f z = a) → f q = a := by
      intro f a hf hf1
      have hcl' : ClusterPt q (𝓟 S) := by
        rw [clusterPt_principal_iff]
        intro V hV
        obtain ⟨o, hVo, hoopen, hqo⟩ := mem_nhds_iff.mp hV
        exact ((mem_closure_iff.mp hqcl) o hoopen hqo).mono
          (fun z hz => ⟨hVo hz.1, hz.2⟩)
      have htend : Tendsto f (𝓟 S) (𝓟 ({a} : Set ℝ)) :=
        tendsto_principal_principal.mpr (fun z hz => hf1 z hz)
      have hres := hcl'.map hf htend
      rw [clusterPt_principal_iff] at hres
      by_contra hne'
      have hmem : ({a} : Set ℝ)ᶜ ∈ 𝓝 (f q) :=
        isOpen_compl_singleton.mem_nhds (by simpa using hne')
      obtain ⟨w, hw1, hw2⟩ := hres _ hmem
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hw1 hw2
      exact hw1 hw2
    have h21 : ContinuousAt (fun z : M × E × E => z.1) q := continuousAt_fst
    have h2 : ContinuousAt (fun z : M × E × E => z.2.1) q :=
      continuousAt_fst.comp continuousAt_snd
    have h3 : ContinuousAt (fun z : M × E × E => z.2.2) q :=
      continuousAt_snd.comp continuousAt_snd
    have c1 : chartGram (I := I) x₀ q.1 q.2.1 q.2.1 = 1 :=
      key _ 1 ((continuousAt_chartGram_prod3 (I := I) x₀ hqsrc q.2.1 q.2.1).comp
        (f := fun z : M × E × E => (z.1, z.2.1, z.2.1)) (x := q)
        (h21.prodMk (h2.prodMk h2))) (fun z hz => hz.2.1)
    have c2 : chartGram (I := I) x₀ q.1 q.2.2 q.2.2 = 1 :=
      key _ 1 ((continuousAt_chartGram_prod3 (I := I) x₀ hqsrc q.2.2 q.2.2).comp
        (f := fun z : M × E × E => (z.1, z.2.2, z.2.2)) (x := q)
        (h21.prodMk (h3.prodMk h3))) (fun z hz => hz.2.2.1)
    have c3 : chartGram (I := I) x₀ q.1 q.2.1 q.2.2 = 0 :=
      key _ 0 ((continuousAt_chartGram_prod3 (I := I) x₀ hqsrc q.2.1 q.2.2).comp
        (f := fun z : M × E × E => (z.1, z.2.1, z.2.2)) (x := q)
        (h21.prodMk (h2.prodMk h3))) (fun z hz => hz.2.2.2)
    exact ⟨hqC, c1, c2, c3⟩
  set F : M × E × E → ℝ := fun q => chartGram (I := I) x₀ q.1 q.2.1
      (chartCurv cov x₀ q.1 q.2.1 q.2.2) with hFdef
  have hFcont : ContinuousOn F C := by
    have hG : ContinuousOn (fun q : M × E × E => chartGram (I := I) x₀ q.1 q.2.1 q.2.2)
        ((chartAt H x₀).source ×ˢ (Set.univ : Set (E × E))) :=
      continuousOn_chartGram_prod3 (I := I) x₀
    have hcc : ContinuousOn (fun q : M × E × E => chartCurv cov x₀ q.1 q.2.1 q.2.2) C :=
      (continuousOn_chartCurv_prod (cov := cov) x₀).mono (fun q hq => ⟨hKsrc hq.1, trivial⟩)
    have hΦ : ContinuousOn
        (fun q : M × E × E => (q.1, q.2.1, chartCurv cov x₀ q.1 q.2.1 q.2.2)) C :=
      (continuousOn_id.fst).prodMk ((continuousOn_id.snd).fst |>.prodMk hcc)
    have hmap : MapsTo (fun q : M × E × E => (q.1, q.2.1, chartCurv cov x₀ q.1 q.2.1 q.2.2))
        C ((chartAt H x₀).source ×ˢ (Set.univ : Set (E × E))) :=
      fun q hq => ⟨hKsrc hq.1, trivial⟩
    exact hG.comp hΦ hmap
  have hFgt : ∀ q ∈ S, 1 < F q := by
    rintro ⟨p, a, b⟩ hq
    have hqC : (p, a, b) ∈ C := hq.1
    have hpK : p ∈ K := hqC.1
    have hpsrc : p ∈ (chartAt H x₀).source := hKsrc hpK
    have ha : chartGram (I := I) x₀ p a a = 1 := hq.2.1
    have hb : chartGram (I := I) x₀ p b b = 1 := hq.2.2.1
    have hab : chartGram (I := I) x₀ p a b = 0 := hq.2.2.2
    have h1 := one_lt_inner_curvVec (cov := cov) (p := p) (a := a) (b := b) ‹_› hmet hpinch
      (by rw [← chartGram_apply]; exact ha) (by rw [← chartGram_apply]; exact hb)
      (by rw [← chartGram_apply]; exact hab)
    have hkey := curvVec_frameVector_eq (cov := cov) htor x₀ hpsrc a b
    rw [hFdef]
    simp only
    rw [chartGram_apply, ← hkey]
    exact h1
  obtain ⟨c, hc1, hc⟩ := exists_lt_of_isCompact hCcomp hSC hcl hFcont hFgt
  refine ⟨U, K, hUopen, hx0U, hUK, hKcomp, hKsrc, c, hc1, ?_⟩
  intro p hp u v hu hv huv
  set a : E := (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p u with hadef
  set b : E := (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p v with hbdef
  have hpbase : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hKsrc hp
  have hfa : frameVector (I := I) x₀ p a = u := by
    rw [hadef, frameVector]
    exact Trivialization.symmL_continuousLinearMapAt (R := ℝ) _ hpbase u
  have hfb : frameVector (I := I) x₀ p b = v := by
    rw [hbdef, frameVector]
    exact Trivialization.symmL_continuousLinearMapAt (R := ℝ) _ hpbase v
  have hga : chartGram (I := I) x₀ p a a = 1 := by rw [chartGram_apply, hfa]; exact hu
  have hgb : chartGram (I := I) x₀ p b b = 1 := by rw [chartGram_apply, hfb]; exact hv
  have hgab : chartGram (I := I) x₀ p a b = 0 := by rw [chartGram_apply, hfa, hfb]; exact huv
  have haR : a ∈ closedBall (0 : E) R := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hnorm_le p hp a hga
  have hbR : b ∈ closedBall (0 : E) R := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hnorm_le p hp b hgb
  have hqS : (p, a, b) ∈ S := ⟨⟨hp, ⟨haR, hbR⟩⟩, hga, hgb, hgab⟩
  have hbound := hc (p, a, b) hqS
  rw [hFdef] at hbound
  simp only at hbound
  have hpsrc : p ∈ (chartAt H x₀).source := hKsrc hp
  rw [chartGram_apply, ← curvVec_frameVector_eq (cov := cov) htor x₀ hpsrc a b, hfa, hfb] at hbound
  rw [real_inner_comm] at hbound
  exact hbound

/-! ## The global uniform bound -/

/-- **Uniform strict pinching.**  On a compact manifold with pointwise strict quarter pinching
`sec > 1` there is a constant `c > 1` strictly below the sectional curvature of every orthonormal
pair at every point. -/
theorem exists_uniform_lt_curvVec [CompactSpace M] [Nonempty M]
    (hmet : IsMetricCompatible cov) (hpinch : QuarterPinched cov) (htor : cov.torsion = 0) :
    ∃ c : ℝ, 1 < c ∧ ∀ (p : M) (u v : TangentSpace I p),
      inner ℝ u u = 1 → inner ℝ v v = 1 → inner ℝ u v = 0 →
      c < inner ℝ (curvVec cov p u v v) u := by
  classical
  choose U K hUopen hxU hUK hKcomp hKsrc c hc1 hc using
    fun x : M => exists_uniform_lt_curvVec_local (cov := cov) hmet hpinch htor x
  have hcover : (Set.univ : Set M) ⊆ ⋃ x : M, U x :=
    fun y _ => Set.mem_iUnion.mpr ⟨y, hxU y⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U (fun x => hUopen x) hcover
  have htne : t.Nonempty := by
    obtain ⟨y⟩ := (inferInstance : Nonempty M)
    obtain ⟨x, hxt, -⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
    exact ⟨x, hxt⟩
  obtain ⟨z, hzt, hzmin⟩ := Finset.exists_min_image t c htne
  refine ⟨c z, hc1 z, ?_⟩
  intro p u v hu hv huv
  obtain ⟨x, hxt, hpx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ p))
  exact lt_of_le_of_lt (hzmin x hxt) (hc x p (hUK x hpx) u v hu hv huv)

end

end Submission.PinchUniform
