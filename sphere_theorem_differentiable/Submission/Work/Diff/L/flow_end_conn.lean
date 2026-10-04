import Mathlib
import Submission.Diff.Grad
import Submission.Work.Diff.L.Defs
import Submission.Work.Diff.L.ConnDefs
import Submission.Work.Diff.L.Stmt
import Submission.Work.Diff.L.lc_eq_cov
import Submission.Work.Diff.L.scalAt_ge_of_curv_pos
import Submission.Work.Diff.L.rmFrame_pinched_bounds
import Submission.Work.Diff.L.exists_spreadable_metric
import Submission.Work.Diff.L.pinched_of_frameBounds
import Submission.Work.Diff.L.secCurvAt_eq_frame_coord
import Submission.Work.Diff.L.gradSq_le_dRmNormSq_v3
import Submission.Work.Diff.L.initial_pinching_set_v2
import Submission.Work.Diff.L.maximal_flow_v3
import Submission.Work.Diff.L.scalar_growth_family_v3
import Submission.Work.Diff.L.scalAt_smooth_v3
import Submission.Work.Diff.L.spread_scalar_v2
import Submission.Work.Diff.L.pinchingSet_component_bound_v2
import Submission.Work.Diff.GE.Frame

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

CONTEXT: this is one area of the Brendle–Schoen differentiable sphere theorem, driven by the lead. Read HANDOFF.md.
The contracts in Submission/Diff/Interfaces.lean and Submission/Diff/Alg.lean are frozen. Your statement's hypotheses are other
areas' contracts: USE them, do not re-prove them.

This module is the ASSEMBLY of `Work.Diff.L.flow_end_conn`; its pieces are the sibling modules of this
directory:

* `scalAt_ge_of_curv_pos` — the initial metric has scalar curvature `> n(n-1)`;
* `initial_pinching_set` — a Böhm–Wilking pinching set `F` containing the initial curvature;
* `maximal_flow_v2`, `scalar_growth_family_v2`, `pinchingSet_component_bound_v2` — a Ricci flow from the
  initial metric carrying a time slice with nonnegative scalar curvature and arbitrarily large
  maximum of the scalar curvature;
* `scalAt_smooth_v2` — `scalAt (G t)` is smooth (so its maximum is attained);
* `gradSq_le_dRmNormSq` — a uniform constant with `|∇S|² ≤ K |∇Rm|²`;
* `exists_spreadable_metric` — that time slice, with `|∇S|² ≤ β²S³ + Cn`, `Cn ≤ β²S₀²`;
* `spread_scalar_v2` — `(1-ε)S₀ ≤ S` everywhere;
* `rmFrame_pinched_bounds`, `secCurvAt_eq_frame_coord`, `conn_kappa_arith`, `pinched_of_frameBounds`
  — the two-sided pinching of the output metric.

-/

set_option maxHeartbeats 2000000

namespace Work.Diff.L

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

/-- `curv` of `lcOf initSMet` agrees with `curv` of `cov` on smooth fields, when the two connections
agree there: `funext` + `lc_eq_cov` identifies the fields term by term. -/
private lemma curv_lcOf_eq_of_eq_on_smooth
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (hcov0 : ContMDiffCovariantDerivative (lcOf (initSMet (I := I) (M := M))) ∞)
    (hlc : ∀ (Y : Π x : M, TangentSpace I x), SmoothField Y → ∀ (x : M) (v : TangentSpace I x),
      lcOf (initSMet (I := I) (M := M)) Y x v = cov Y x v)
    (X Y Z : Π x : M, TangentSpace I x)
    (hX : SmoothField X) (hY : SmoothField Y) (hZ : SmoothField Z) (x : M) :
    curv (lcOf (initSMet (I := I) (M := M))) X Y Z x = curv cov X Y Z x := by
  have hYc : SmoothField (fun y : M => lcOf (initSMet (I := I) (M := M)) Z y (Y y)) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf (initSMet (I := I) (M := M))) hcov0 hZ hY
  have hXc : SmoothField (fun y : M => lcOf (initSMet (I := I) (M := M)) Z y (X y)) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf (initSMet (I := I) (M := M))) hcov0 hZ hX
  have h1 : (fun y : M => lcOf (initSMet (I := I) (M := M)) Z y (Y y))
      = fun y : M => cov Z y (Y y) := funext fun y => hlc Z hZ y (Y y)
  have h2 : (fun y : M => lcOf (initSMet (I := I) (M := M)) Z y (X y))
      = fun y : M => cov Z y (X y) := funext fun y => hlc Z hZ y (X y)
  simp only [curv]
  rw [hlc (fun y : M => lcOf (initSMet (I := I) (M := M)) Z y (Y y)) hYc x (X x),
    hlc (fun y : M => lcOf (initSMet (I := I) (M := M)) Z y (X y)) hXc x (Y x),
    hlc Z hZ x (mlieBracket I X Y x)]
  rw [h1, h2]

/-- `hpinch`, transported from `cov` to `lcOf initSMet` and phrased with `initSMet.inner` (which is
definitionally the ambient inner product). -/
private lemma initSMet_curv_pos
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (hcov0 : ContMDiffCovariantDerivative (lcOf (initSMet (I := I) (M := M))) ∞)
    (hlc : ∀ (Y : Π x : M, TangentSpace I x), SmoothField Y → ∀ (x : M) (v : TangentSpace I x),
      lcOf (initSMet (I := I) (M := M)) Y x v = cov Y x v)
    (hpinch : QuarterPinched cov) :
    ∀ (X Y : Π x : M, TangentSpace I x), SmoothField X → SmoothField Y → ∀ x : M,
      (initSMet (I := I) (M := M)).inner x (X x) (X x) = 1 →
      (initSMet (I := I) (M := M)).inner x (Y x) (Y x) = 1 →
      (initSMet (I := I) (M := M)).inner x (X x) (Y x) = 0 →
      (1 : ℝ) < (initSMet (I := I) (M := M)).inner x
        (curv (lcOf (initSMet (I := I) (M := M))) X Y Y x) (X x) := by
  intro X Y hX hY x h1 h2 h3
  have h1' : inner ℝ (X x) (X x) = 1 := h1
  have h2' : inner ℝ (Y x) (Y x) = 1 := h2
  have h3' : inner ℝ (X x) (Y x) = 0 := h3
  have hp := hpinch X Y hX hY x h1' h2' h3'
  have hcurv := curv_lcOf_eq_of_eq_on_smooth cov hcov0 hlc X Y Y hX hY hY x
  rw [hcurv, initSMet_inner]
  exact hp.1

/-- The maximum of `scalAt g` is attained. -/
private lemma exists_argmax_scalAt (hLC : LCSmooth I M) (g : SMet I M) :
    ∃ x₀ : M, ∀ x : M, scalAt g x ≤ scalAt g x₀ := by
  obtain ⟨S, hS, hSeq⟩ := (scalAt_smooth_v3 (I := I) (M := M) hLC g).1
  obtain ⟨x₀, -, hmax⟩ := IsCompact.exists_isMaxOn isCompact_univ
    ⟨Classical.arbitrary M, mem_univ _⟩ hS.continuous.continuousOn
  exact ⟨x₀, fun x => by rw [← hSeq x, ← hSeq x₀]; exact hmax (mem_univ x)⟩

/-- The lower bound for `secCurvAt` used by `spread_scalar_v2`: where the scalar curvature is `≥ ρ`,
every sectional curvature is `≥ δρ/(n(n-1))`. -/
private lemma secCurvAt_lower
    (hdim : 2 ≤ Module.finrank ℝ E) (hLC : LCSmooth I M) (g : SMet I M)
    (F : Set (Curv4 (Module.finrank ℝ E))) (hF : IsPinchingSet F) (hCurv : CurvIn g F)
    {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hρ' : ∀ R ∈ F, ρ ≤ scalAlg R → IsPinchedAlg δ R) :
    ∀ x : M, ρ ≤ scalAt g x → ∀ u v : TangentSpace I x,
      g.inner x u u = 1 → g.inner x v v = 1 → g.inner x u v = 0 →
      δ * ρ / ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1))
        ≤ Work.Diff.L.secCurvAt g x u v := by
  intro x hx u v hu hv huv
  obtain ⟨hcovg⟩ := (hLC g).1
  obtain ⟨u', v', hON, heq⟩ :=
    secCurvAt_eq_frame_coord (g := g) hdim hcovg x (onFrame g x) (onFrame_isONFrame g x)
      u v hu hv huv
  have hb := (rmFrame_pinched_bounds (SA := 0) hdim g F hF hCurv hδ hρ hρ').1 x hx u' v' hON
  rw [heq]
  exact hb

/-- At the time `0` the scalar curvature is nonnegative and its maximum exists. -/
private lemma big_scal_zero (hdim : 2 ≤ Module.finrank ℝ E) (hLC : LCSmooth I M)
    {T : ℝ} (hT : 0 < T) {G : ℝ → SMet I M}
    (hgb : ∀ t ∈ Ico 0 T, t < (Module.finrank ℝ E : ℝ) / 2 → ∀ x : M,
      (1 : ℝ) / (1 - (2 / (Module.finrank ℝ E : ℝ)) * t) ≤ scalAt (G t) x) :
    ∃ x₀ : M, (∀ x : M, 0 ≤ scalAt (G 0) x) ∧ 0 ≤ scalAt (G 0) x₀ ∧
      (∀ x : M, scalAt (G 0) x ≤ scalAt (G 0) x₀) := by
  have hnpos : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
    have h : 0 < Module.finrank ℝ E := by omega
    exact_mod_cast h
  have hone : (0 : ℝ) ≤ 1 / (1 - (2 / (Module.finrank ℝ E : ℝ)) * 0) := by
    rw [mul_zero, sub_zero, div_one]
    norm_num
  obtain ⟨x₀, hx₀⟩ := exists_argmax_scalAt (I := I) (M := M) hLC (G 0)
  exact ⟨x₀, fun x => le_trans hone (hgb 0 ⟨le_refl 0, hT⟩ (by linarith) x),
    le_trans hone (hgb 0 ⟨le_refl 0, hT⟩ (by linarith) x₀), hx₀⟩

/-- If the flow lives longer than `n/2`, the blow-up of the growth family gives a nonnegative time
slice whose maximum of the scalar curvature is as large as we want, at the time `nN/(2(N+1))`. -/
private lemma big_scal_pos (hdim : 2 ≤ Module.finrank ℝ E) (hLC : LCSmooth I M)
    {T : ℝ} (hT : 0 < T) {G : ℝ → SMet I M}
    (hgb : ∀ t ∈ Ico 0 T, t < (Module.finrank ℝ E : ℝ) / 2 → ∀ x : M,
      (1 : ℝ) / (1 - (2 / (Module.finrank ℝ E : ℝ)) * t) ≤ scalAt (G t) x)
    {N : ℝ} (hN : 0 < N)
    (hTn : (Module.finrank ℝ E : ℝ) * N / (2 * (N + 1)) < T) :
    ∃ t ∈ Ico 0 T, ∃ x₀ : M, (∀ x : M, 0 ≤ scalAt (G t) x) ∧
      N ≤ scalAt (G t) x₀ ∧ (∀ x : M, scalAt (G t) x ≤ scalAt (G t) x₀) := by
  have hnpos : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
    have h : 0 < Module.finrank ℝ E := by omega
    exact_mod_cast h
  set t : ℝ := (Module.finrank ℝ E : ℝ) * N / (2 * (N + 1)) with ht
  have h2N : (0 : ℝ) < 2 * (N + 1) := by linarith
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have htn : t < (Module.finrank ℝ E : ℝ) / 2 := by
    rw [ht]
    rw [div_lt_div_iff₀ h2N (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hphi : (1 : ℝ) / (1 - (2 / (Module.finrank ℝ E : ℝ)) * t) = N + 1 := by
    have hkey : (2 / (Module.finrank ℝ E : ℝ)) * t = N / (N + 1) := by
      rw [ht]
      field_simp
    have h2 : (1 : ℝ) - N / (N + 1) = 1 / (N + 1) := by
      field_simp
      ring
    have h3 : (1 : ℝ) / (1 / (N + 1)) = N + 1 := by
      have hN1 : (N + 1 : ℝ) ≠ 0 := by linarith
      field_simp
    rw [hkey, h2]
    exact h3
  obtain ⟨x₀, hx₀⟩ := exists_argmax_scalAt (I := I) (M := M) hLC (G t)
  refine ⟨t, ⟨ht0, hTn⟩, x₀, ?_, ?_, hx₀⟩
  · intro x
    have h := hgb t ⟨ht0, hTn⟩ htn x
    rw [hphi] at h
    linarith
  · have h := hgb t ⟨ht0, hTn⟩ htn x₀
    rw [hphi] at h
    linarith

/-- If the flow dies before time `n/2`, the unboundedness of its curvature (via the component bound
in a pinching set) still gives a nonnegative time slice of arbitrarily large maximum scalar
curvature. -/
private lemma big_scal_of_unbounded (hdim : 2 ≤ Module.finrank ℝ E) (hLC : LCSmooth I M)
    (F : Set (Curv4 (Module.finrank ℝ E))) (hF : IsPinchingSet F)
    {T : ℝ} (hT : 0 < T) {G : ℝ → SMet I M}
    (hCurv : ∀ t ∈ Ico 0 T, CurvIn (G t) F)
    (hunb : ¬ ∃ C : ℝ, ∀ t ∈ Ico 0 T, CurvBound (G t) C)
    (hshort : T ≤ (Module.finrank ℝ E : ℝ) / 2)
    (hgb : ∀ t ∈ Ico 0 T, t < (Module.finrank ℝ E : ℝ) / 2 → ∀ x : M,
      (1 : ℝ) / (1 - (2 / (Module.finrank ℝ E : ℝ)) * t) ≤ scalAt (G t) x)
    {N : ℝ} (hN : 0 < N) :
    ∃ t ∈ Ico 0 T, ∃ x₀ : M, (∀ x : M, 0 ≤ scalAt (G t) x) ∧
      N ≤ scalAt (G t) x₀ ∧ (∀ x : M, scalAt (G t) x ≤ scalAt (G t) x₀) := by
  have hnpos : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
    have h : 0 < Module.finrank ℝ E := by omega
    exact_mod_cast h
  obtain ⟨c, C₀, hc, hcomp⟩ := pinchingSet_component_bound_v2 (F := F) hF
  have hnotbound : ¬ (∀ t ∈ Ico 0 T, CurvBound (G t) (c * N + C₀ + 1)) := fun hb =>
    hunb ⟨c * N + C₀ + 1, hb⟩
  simp only [not_forall] at hnotbound
  obtain ⟨t, ht, hf⟩ := hnotbound
  have hstep : ∃ x : M, ∃ e : Fin (Module.finrank ℝ E) → TangentSpace I x,
      IsONFrame (G t) x e ∧ ∃ i j k l : Fin (Module.finrank ℝ E),
        c * N + C₀ + 1 < |rmFrame (G t) x e i j k l| := by
    by_contra hcon
    refine hf ?_
    intro x e he i j k l
    by_contra hle
    exact hcon ⟨x, e, he, i, j, k, l, not_le.mp hle⟩
  obtain ⟨x, e, he, i, j, k, l, hgt⟩ := hstep
  have hmem := hcomp _ (hCurv t ht x e he) i j k l
  have hscal : N < scalAlg (rmFrame (G t) x e) := by
    have h1 := lt_of_lt_of_le hgt hmem
    nlinarith [hc, hN]
  have hscalAt : N < scalAt (G t) x := by
    rw [← conn_scalAlg_rmFrame_eq (G t) hLC x e he]
    exact hscal
  obtain ⟨x₀, hx₀⟩ := exists_argmax_scalAt (I := I) (M := M) hLC (G t)
  refine ⟨t, ht, x₀, ?_, ?_, hx₀⟩
  · intro y
    have htn : t < (Module.finrank ℝ E : ℝ) / 2 := lt_of_lt_of_le ht.2 hshort
    have h := hgb t ht htn y
    have h1 : (0 : ℝ) < 1 / (1 - (2 / (Module.finrank ℝ E : ℝ)) * t) := by
      apply div_pos one_pos
      have h2 : (2 / (Module.finrank ℝ E : ℝ)) * t < 1 := by
        rw [div_mul_eq_mul_div, div_lt_one (by linarith : (0 : ℝ) < (Module.finrank ℝ E : ℝ))]
        nlinarith
      linarith
    linarith
  · exact le_trans (le_of_lt hscalAt) (hx₀ x)

end Helpers

/-- **The Ricci flow produces `(κ, (1+η)κ]`-pinched metrics** (contract `FlowContract`). -/
theorem flow_end_conn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
    (hdim : 2 ≤ Module.finrank ℝ E)
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov) (hpinch : QuarterPinched cov)
    (hLC : LCSmooth I M) (hLV : LCVariation I M) (hSTE : ShortTimeExistence I M)
    (hEXT : Extension I M) (hPP : PinchingPreserved I M)
    (hA0 : QuarterToPIC2 (Module.finrank ℝ E)) (hA1 : PinchingSetExists (Module.finrank ℝ E))
    (hGE : GradientEstimate I M) (hSMP : ScalarMaxPrinciple I M) :
    FlowContract I M := by
  intro η hη
  have hnR : (2 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast hdim
  have hnpos : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by linarith
  -- ## Step 0: the initial metric and the positivity of its scalar curvature
  let g₀ : SMet I M := initSMet
  obtain ⟨hcov0, -, -⟩ := hLC g₀
  obtain ⟨hcov0'⟩ := hcov0
  have hlc0 : ∀ (Y : Π x : M, TangentSpace I x), SmoothField Y →
      ∀ (x : M) (v : TangentSpace I x), lcOf g₀ Y x v = cov Y x v :=
    fun Y hY x v => lc_eq_cov (I := I) (M := M) cov htor hmet hLC Y hY x v
  have hpinch_g := initSMet_curv_pos (I := I) (M := M) cov hcov0' hlc0 hpinch
  have hscal0 : ∀ x : M, (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1)
      < scalAt g₀ x := scalAt_ge_of_curv_pos (I := I) (M := M) hdim g₀ hcov0' hpinch_g
  -- ## Step 1: the pinching set and the scalar-growth family
  obtain ⟨F, hF, hF0⟩ :=
    initial_pinching_set_v2 (I := I) (M := M) hdim cov htor hmet hpinch hLC hA0 hA1
  set Fam : ℝ → Set (Curv4 (Module.finrank ℝ E)) := fun t => {R | R ∈ F ∧
    (if t < (Module.finrank ℝ E : ℝ) / (2 * 1) then
      1 / (1 - (2 / (Module.finrank ℝ E : ℝ)) * 1 * t) else 0) ≤ scalAlg R} with hFam
  have hFamInv : IsInvariantFamily Fam := scalar_growth_family_v3 hF.1 (φ₀ := 1) one_pos
  have hFam0 : CurvIn g₀ (Fam 0) := by
    intro x e he
    rw [hFam]
    simp only [Set.mem_setOf_eq]
    have h1 : scalAlg (rmFrame g₀ x e) = scalAt g₀ x := conn_scalAlg_rmFrame_eq g₀ hLC x e he
    have h2 : (1 : ℝ) ≤ scalAlg (rmFrame g₀ x e) := by
      rw [h1]
      have h3 := hscal0 x
      nlinarith
    refine ⟨hF0 x e he, ?_⟩
    rw [if_pos (by positivity : (0 : ℝ) < (Module.finrank ℝ E : ℝ) / (2 * 1))]
    simpa using h2
  -- the pointwise lower bound for the scalar curvature along any admissible flow
  have growth_bound : ∀ (T : ℝ) (G : ℝ → SMet I M), 0 < T → IsRicciFlow G T → G 0 = g₀ →
      (∀ t ∈ Ico 0 T, CurvIn (G t) F) →
      ∀ t ∈ Ico 0 T, t < (Module.finrank ℝ E : ℝ) / 2 → ∀ x : M,
      (1 : ℝ) / (1 - (2 / (Module.finrank ℝ E : ℝ)) * t) ≤ scalAt (G t) x := by
    intro T G hT hflow hG0 hCurv t ht hlt x
    have hinit : CurvIn (G 0) (Fam 0) := by rw [hG0]; exact hFam0
    have hmem := hPP Fam hFamInv G T hflow hinit t ht x (onFrame (G t) x)
      (onFrame_isONFrame (G t) x)
    rw [hFam] at hmem
    simp only [Set.mem_setOf_eq] at hmem
    have hif : t < (Module.finrank ℝ E : ℝ) / (2 * 1) := by simpa using hlt
    rw [if_pos hif] at hmem
    simpa only [mul_one, scalAt, rmC] using hmem.2
  -- ## Step 2: a flow with a nonnegative time slice of arbitrarily large maximum scalar curvature
  have hbig : ∃ T : ℝ, 0 < T ∧ ∃ G : ℝ → SMet I M, IsRicciFlow G T ∧ G 0 = g₀ ∧
      (∀ t ∈ Ico 0 T, CurvIn (G t) F) ∧
      (∀ N : ℝ, ∃ t ∈ Ico 0 T, ∃ x₀ : M,
        (∀ x : M, 0 ≤ scalAt (G t) x) ∧ N ≤ scalAt (G t) x₀ ∧
        ∀ x : M, scalAt (G t) x ≤ scalAt (G t) x₀) := by
    rcases maximal_flow_v3 (I := I) (M := M) hSTE hEXT hPP g₀ F hF.1 hF0 with hglob | hmaxf
    · obtain ⟨G, hflow, hG0, hCurv⟩ := hglob ((Module.finrank ℝ E : ℝ) / 2 + 1) (by linarith)
      have hgb := growth_bound ((Module.finrank ℝ E : ℝ) / 2 + 1) G (by linarith) hflow hG0 hCurv
      refine ⟨(Module.finrank ℝ E : ℝ) / 2 + 1, by linarith, G, hflow, hG0, hCurv, ?_⟩
      intro N
      by_cases hN : N ≤ 0
      · obtain ⟨x₀, h1, h2, h3⟩ := big_scal_zero (I := I) (M := M) hdim hLC (by linarith) hgb
        exact ⟨0, ⟨le_refl 0, by linarith⟩, x₀, h1, le_trans hN h2, h3⟩
      · refine big_scal_pos (I := I) (M := M) hdim hLC (by linarith) hgb (not_le.mp hN) ?_
        have h2N : (0 : ℝ) < 2 * (N + 1) := by linarith
        have hkey : (Module.finrank ℝ E : ℝ) * N / (2 * (N + 1))
            < (Module.finrank ℝ E : ℝ) / 2 := by
          rw [div_lt_div_iff₀ h2N (by norm_num : (0 : ℝ) < 2)]
          nlinarith
        linarith
    · obtain ⟨T, hT, G, hflow, hG0, hCurv, hunb⟩ := hmaxf
      have hgb := growth_bound T G hT hflow hG0 hCurv
      refine ⟨T, hT, G, hflow, hG0, hCurv, ?_⟩
      intro N
      by_cases hTN : (Module.finrank ℝ E : ℝ) / 2 < T
      · by_cases hN : N ≤ 0
        · obtain ⟨x₀, h1, h2, h3⟩ := big_scal_zero (I := I) (M := M) hdim hLC hT hgb
          exact ⟨0, ⟨le_refl 0, hT⟩, x₀, h1, le_trans hN h2, h3⟩
        · refine big_scal_pos (I := I) (M := M) hdim hLC hT hgb (not_le.mp hN) ?_
          have h2N : (0 : ℝ) < 2 * (N + 1) := by linarith
          have hkey : (Module.finrank ℝ E : ℝ) * N / (2 * (N + 1))
              < (Module.finrank ℝ E : ℝ) / 2 := by
            rw [div_lt_div_iff₀ h2N (by norm_num : (0 : ℝ) < 2)]
            nlinarith
          linarith
      · push_neg at hTN
        by_cases hN : N ≤ 0
        · obtain ⟨x₀, h1, h2, h3⟩ := big_scal_zero (I := I) (M := M) hdim hLC hT hgb
          exact ⟨0, ⟨le_refl 0, hT⟩, x₀, h1, le_trans hN h2, h3⟩
        · exact big_scal_of_unbounded (I := I) (M := M) hdim hLC F hF hT hCurv hunb hTN hgb
            (not_le.mp hN)
  -- ## Step 3: choose the constants
  obtain ⟨T, hT, G, hflow, hG0, hCurv, hbig'⟩ := hbig
  obtain ⟨K, hK, hKb⟩ := gradSq_le_dRmNormSq_v3 (I := I) (M := M) hdim
  obtain ⟨ε, hε0, hε1⟩ := exists_between (show (0 : ℝ) < min 1 (η / (1 + η)) by positivity)
  have hεη : ε < η / (1 + η) := lt_of_lt_of_le hε1 (min_le_right _ _)
  have hε1' : ε < 1 := lt_of_lt_of_le hε1 (min_le_left _ _)
  have hbase : 1 < (1 + η) * (1 - ε) := by
    have h1 : η / (1 + η) < 1 := by
      rw [div_lt_one (by linarith : (0 : ℝ) < 1 + η)]
      linarith
    have h2 : 1 - η / (1 + η) = 1 / (1 + η) := by
      field_simp
      ring
    have h3 : (1 + η) * (1 / (1 + η)) = 1 := by
      field_simp
    nlinarith [hεη, hη, h1, h2, h3]
  have hbasepos : (0 : ℝ) < (1 + η) * (1 - ε) := by linarith
  obtain ⟨Θ, hΘ, hspread⟩ := spread_scalar_v2 (I := I) (M := M) hdim (ε := ε) hε0
  -- δ
  set s : ℝ := Real.sqrt (1 / ((1 + η) * (1 - ε))) with hs
  have hs2 : s ^ 2 = 1 / ((1 + η) * (1 - ε)) := Real.sq_sqrt (le_of_lt (one_div_pos.mpr hbasepos))
  have hslt : s < 1 := by
    have h1 : s ^ 2 < 1 := by
      rw [hs2, div_lt_one hbasepos]
      linarith
    nlinarith [Real.sqrt_nonneg (1 / ((1 + η) * (1 - ε)))]
  obtain ⟨δ, hsδ, hδ1⟩ := exists_between hslt
  have hδ0 : 0 < δ := lt_of_le_of_lt (Real.sqrt_nonneg _) hsδ
  have hδ2 : 1 < (1 + η) * δ ^ 2 * (1 - ε) := by
    have h1 : 1 < δ ^ 2 * ((1 + η) * (1 - ε)) := by
      have hb : s ^ 2 * ((1 + η) * (1 - ε)) = 1 := by
        rw [hs2, div_mul_cancel₀ _ (ne_of_gt hbasepos)]
      nlinarith [hsδ, hb, Real.sqrt_nonneg (1 / ((1 + η) * (1 - ε)))]
    nlinarith [h1]
  obtain ⟨ρ', hρ'⟩ := isPinchedAlg_of_scalAlg_le hF hδ1
  set c₀ : ℝ := δ * (1 - ε) / (2 * ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1)))
    with hc₀
  have hc₀0 : 0 < c₀ := by
    rw [hc₀]
    apply div_pos (mul_pos hδ0 (by linarith))
    nlinarith [hnR]
  obtain ⟨β₀, hβ₀, hspread'⟩ := hspread c₀ hc₀0
  set β : ℝ := β₀ / 2 with hβ
  have hβpos : 0 < β := by rw [hβ]; linarith
  have hββ₀ : β ≤ β₀ := by rw [hβ]; linarith
  -- ## Step 4: the spreadable time slice
  set Θ' : ℝ := max Θ (ρ' / (1 - ε) + 1) with hΘ'
  have hΘ'pos : 0 < Θ' := lt_of_lt_of_le hΘ (le_max_left _ _)
  obtain ⟨t, ht, x₀, S₀, Cn, hnonneg, hS₀eq, hΘ'S₀, hS₀pos, hS₀max, hgrad, hCn⟩ :=
    exists_spreadable_metric (I := I) (M := M) hdim hGE F hF hT hflow hCurv hbig' hK hKb Θ' β
      hΘ'pos hβpos
  obtain ⟨S, hSsm, hSeq⟩ := (scalAt_smooth_v3 (I := I) (M := M) hLC (G t)).1
  -- ## Step 5: spreading
  have hden : (0 : ℝ) < 1 - ε := by linarith
  have hρ'2 : ρ' ≤ (1 - ε) * S₀ := by
    have h2 : ρ' / (1 - ε) < Θ' := by
      have := le_max_right Θ (ρ' / (1 - ε) + 1)
      linarith
    have h5 := (div_lt_iff₀ hden).mp (lt_of_lt_of_le h2 hΘ'S₀)
    linarith
  have hρ'' : ∀ R ∈ F, (1 - ε) * S₀ ≤ scalAlg R → IsPinchedAlg δ R :=
    fun R hR hle => hρ' R hR (le_trans hρ'2 hle)
  have hΘS₀ : Θ ≤ S₀ := le_trans (le_max_left Θ (ρ' / (1 - ε) + 1)) hΘ'S₀
  have hspread_app := hspread' (G t) S x₀ S₀ β Cn hSsm hSeq hS₀eq hΘS₀ hβpos hββ₀
    (by intro x; rw [hSeq x]; exact hgrad x)
    hCn
    (by
      intro x hx u v hu hv huv
      have hρ : (1 - ε) * S₀ ≤ scalAt (G t) x := by rw [← hSeq x]; exact hx
      have hρ0 : 0 < (1 - ε) * S₀ := by nlinarith
      have hlow := secCurvAt_lower (I := I) (M := M) hdim hLC (G t) F hF (hCurv t ht) hδ0 hρ0
        hρ'' x hρ u v hu hv huv
      have h2c₀ : δ * ((1 - ε) * S₀)
          / ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1)) = 2 * (c₀ * S₀) := by
        rw [hc₀]
        field_simp
      have hlow' : 2 * (c₀ * S₀) ≤ Work.Diff.L.secCurvAt (G t) x u v := by
        rw [← h2c₀]
        exact hlow
      nlinarith [hlow', hS₀pos, hc₀0])
  have hglobal : ∀ x : M, (1 - ε) * S₀ ≤ scalAt (G t) x := by
    intro x
    rw [← hSeq x]
    exact hspread_app x
  -- ## Step 6: two-sided pinching
  have hρS : 0 < (1 - ε) * S₀ := by nlinarith
  have hbounds := rmFrame_pinched_bounds (I := I) (M := M) (SA := S₀) hdim (G t) F hF (hCurv t ht) hδ0 hρS hρ''
  set κ : ℝ := (S₀ / (δ * ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1))) / (1 + η)
      + δ * ((1 - ε) * S₀) / ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1))) / 2
    with hκ
  have harith := conn_kappa_arith (n := Module.finrank ℝ E) hdim (δ := δ) (ρ := (1 - ε) * S₀)
    (SA := S₀) (η := η) hδ0 hρS hS₀pos hη (by nlinarith [hδ2, hS₀pos])
  have hκpos : 0 < κ := by rw [hκ]; exact harith.1
  have hκL : κ < δ * ((1 - ε) * S₀)
      / ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1)) := by
    rw [hκ]; exact harith.2.1
  have hUκ : S₀ / (δ * ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1)))
      < (1 + η) * κ := by rw [hκ]; exact harith.2.2
  have hκframe : ∀ (x : M) (u v : Fin (Module.finrank ℝ E) → ℝ), IsONPair u v →
      κ < secK (rmFrame (G t) x (onFrame (G t) x)) u v ∧
      secK (rmFrame (G t) x (onFrame (G t) x)) u v ≤ (1 + η) * κ := by
    intro x u v hON
    exact ⟨lt_of_lt_of_le hκL (hbounds.1 x (hglobal x) u v hON),
      le_trans (hbounds.2 x (hglobal x) (hS₀max x) u v hON) (le_of_lt hUκ)⟩
  obtain ⟨hcovGt, -, -⟩ := hLC (G t)
  obtain ⟨hcovGt'⟩ := hcovGt
  have hdelE := pinched_of_frameBounds (I := I) (M := M) hdim (g := G t) (κ := κ) (η := η)
    hη hκpos hcovGt' hκframe
  -- ## Step 7: output
  refine ⟨G t, lcOf (G t), (hLC (G t)).1, (hLC (G t)).2.1, (hLC (G t)).2.2, κ, hκpos, ?_⟩
  intro X Y hX hY x h1 h2 h3
  exact hdelE X Y hX hY x h1 h2 h3

end Work.Diff.L
