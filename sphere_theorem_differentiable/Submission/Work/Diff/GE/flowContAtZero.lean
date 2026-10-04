import Mathlib
import Submission.Work.Diff.GE.FrameIndep
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.GE.chartcalc
import Submission.Work.Diff.GE.rmP_jointSmooth
import Submission.Work.Diff.GE.gramInv_jointSmooth
import Submission.Work.Diff.GE.rmNormSq_eq_N4_of_basis
import Submission.Work.Diff.GE.dRmNormSq_eq_N5_of_basis
import Submission.Work.Diff.GE.qPair_rot_eq_qPairGen
import Submission.Work.Diff.GE.CFQDefs
import Submission.Work.Diff.GE.laplAt_eq_sum_invGram
import Submission.Work.Diff.GE.metric_pairing_family_jointSmooth
import Submission.Work.Diff.EXT.continuousAt_mvfderiv_family
import Submission.Work.Diff.EXT.contMDiffAt_mvfderiv_along_field
import Submission.Work.Diff.GE.qPairAt_eq_qPairGen_Gram
import Submission.Work.Diff.GE.qPairGen_jointSmooth
import Submission.Work.Diff.EXT.reconDefs
import Submission.Work.Diff.GE.reconCoef_continuousAt
import Submission.Work.Diff.GE.covRmC5_continuousAt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Continuity at `t = 0` of the frozen curvature quantities along a Ricci flow

Target: `Work.Diff.GE.flowContAtZero`.

The statement is the `t = 0` endpoint input of Hamilton's evolution equation for `|Rm|²`
(`Work.Diff.GE.evol_rm_normsq`): the maps `s ↦ |Rm(G s)|²(x)` and
`s ↦ Δ|Rm|²(G s)(x) - 2|∇Rm|²(G s)(x) + 2⟪Rm,Q(Rm)⟫(G s)(x)` are continuous *within* `[0,T)` at
`0`.

Route.  `IsRicciFlow G T` gives joint smoothness of `t ↦ G t` only on the *half-open* interval
`[0,T)`; reparametrising time by `t = τ²` turns `[0,T)` into an *open* neighbourhood of `0`, on
which every frozen quantity is (jointly) smooth, and the result is transferred back by `s ↦ √s`.
On an open time interval the argument is the following.

* `|Rm|²` is frame independent, so it may be computed in the *coordinate frame* `cFrame x₀ ·` of
  the chart at a point `x₀` (a family of tangent vectors that is a basis at every point of the
  chart):  `rmNormSq g y = N4 (Gram) (curvature components in the coordinate frame)`
  (`rmNormSq_eq_N4_of_basis`).  The curvature components are `rmC4`, jointly smooth in `(t,y)` by
  `Work.Diff.GE.rmC4_jointSmooth`, and the inverse Gram matrix is jointly smooth by
  `Work.Diff.GE.gramInv_jointSmooth`; hence `|Rm|²` is jointly smooth.
* the remaining pieces `|∇Rm|²`, `⟪Rm,Q(Rm)⟫` and `Δ|Rm|²` (the latter through the inverse-Gram
  form of the Laplacian, `Work.Diff.GE.laplAt_eq_sum_invGram`) are handled by the lemmas
  `Work.Diff.GE.covRmC5_continuousAt`, `Work.Diff.GE.qPairAt_eq_qPairGen_Gram` +
  `Work.Diff.GE.qPairGen_jointSmooth` and `Work.Diff.GE.laplAt_rmNormSq_continuousAt`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## The coordinate frame spans the tangent space -/

/-- At every point of the chart at `x₀`, the coordinate frame `cFrame x₀ ·` is a basis: its
span is everything.  (The expansion of any section in the coordinate frame is
`Commons.Geometry.Manifold.Tangent.eqOn_sum_frameSection_of_basis`.) -/
theorem cFrame_span (x₀ : M) {p : M} (hp : p ∈ (chartAt H x₀).source) :
    Submodule.span ℝ (Set.range (fun i : Fin (Module.finrank ℝ E) ↦ cFrame (I := I) x₀ i p))
      = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun w => ?_
  have hb : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hp
  set c := (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p w with hc
  have hspec : Submission.Geodesic.frameSection (I := I) x₀ c p
      = ∑ i : Fin (Module.finrank ℝ E), ((Module.finBasis ℝ E).coord i) c
          • cFrame (I := I) x₀ i p := by
    have h1 := Commons.Geometry.Manifold.Tangent.eqOn_sum_frameSection_of_basis (I := I)
      (b := Module.finBasis ℝ E) x₀ (Submission.Geodesic.frameSection (I := I) x₀ c) hp
    have h2 : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p
        (Submission.Geodesic.frameSection (I := I) x₀ c p) = c := by
      show (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p
        ((trivializationAt E (TangentSpace I) x₀).symmL ℝ p c) = c
      exact Trivialization.continuousLinearMapAt_symmL _ hb c
    have h3 := h1
    simp only [] at h3
    rw [h3, h2]
    rfl
  have hlhs : Submission.Geodesic.frameSection (I := I) x₀ c p = w :=
    (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt hb w
  rw [← hlhs, hspec]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span (Set.mem_range_self i)

/-! ## Smoothness of the Gram contractions -/

/-- Joint smoothness of the general-basis Frobenius norm `N4`.

`N4 Γ R = ∑ Γ⁻¹ᵢₐ Γ⁻¹ⱼ_b Γ⁻¹ₖ_c Γ⁻¹ₗ_d R i j k l R a b c d` is a finite sum of products of entries
of `Γ⁻¹` and of `R`; hence it is jointly smooth as soon as those entries are. -/
theorem N4_jointSmooth {n : ℕ} {Γ : ℝ × M → Matrix (Fin n) (Fin n) ℝ}
    {R : ℝ × M → Curv4 n} {t₀ : ℝ} {x : M}
    (hΓ : ∀ i j, Work.Diff.EXT.JointSmoothAt I M (fun p : ℝ × M ↦ (Γ p)⁻¹ i j) t₀ x)
    (hR : ∀ i j k l, Work.Diff.EXT.JointSmoothAt I M (fun p : ℝ × M ↦ R p i j k l) t₀ x) :
    Work.Diff.EXT.JointSmoothAt I M (fun p : ℝ × M ↦ N4 (Γ p) (R p)) t₀ x := by
  show ContMDiffAt ((𝓘(ℝ,ℝ)).prod I) (𝓘(ℝ,ℝ)) ∞ (fun p : ℝ × M ↦ N4 (Γ p) (R p)) (t₀, x)
  simp only [N4]
  refine ContMDiffAt.sum (fun i _ ↦ ?_)
  refine ContMDiffAt.sum (fun j _ ↦ ?_)
  refine ContMDiffAt.sum (fun k _ ↦ ?_)
  refine ContMDiffAt.sum (fun l _ ↦ ?_)
  refine ContMDiffAt.sum (fun a _ ↦ ?_)
  refine ContMDiffAt.sum (fun b _ ↦ ?_)
  refine ContMDiffAt.sum (fun c _ ↦ ?_)
  refine ContMDiffAt.sum (fun d _ ↦ ?_)
  have h := ((((hΓ i a).mul (hΓ j b)).mul (hΓ k c)).mul (hΓ l d)).mul
    ((hR i j k l).mul (hR a b c d))
  convert h using 1
  ext p
  simp only [Pi.mul_apply]
  ring

/-- Joint smoothness of `N5`, the general-basis form of `|∇Rm|²`. -/
theorem N5_jointSmooth {n : ℕ} {Γ : ℝ × M → Matrix (Fin n) (Fin n) ℝ}
    {R : ℝ × M → Fin n → Curv4 n} {t₀ : ℝ} {x : M}
    (hΓ : ∀ i j, Work.Diff.EXT.JointSmoothAt I M (fun p : ℝ × M ↦ (Γ p)⁻¹ i j) t₀ x)
    (hR : ∀ m i j k l, Work.Diff.EXT.JointSmoothAt I M (fun p : ℝ × M ↦ R p m i j k l) t₀ x) :
    Work.Diff.EXT.JointSmoothAt I M (fun p : ℝ × M ↦ N5 (Γ p) (R p)) t₀ x := by
  show ContMDiffAt ((𝓘(ℝ,ℝ)).prod I) (𝓘(ℝ,ℝ)) ∞ (fun p : ℝ × M ↦ N5 (Γ p) (R p)) (t₀, x)
  simp only [N5]
  refine ContMDiffAt.sum (fun m _ ↦ ?_)
  refine ContMDiffAt.sum (fun i _ ↦ ?_)
  refine ContMDiffAt.sum (fun j _ ↦ ?_)
  refine ContMDiffAt.sum (fun k _ ↦ ?_)
  refine ContMDiffAt.sum (fun l _ ↦ ?_)
  refine ContMDiffAt.sum (fun a _ ↦ ?_)
  refine ContMDiffAt.sum (fun b _ ↦ ?_)
  refine ContMDiffAt.sum (fun c _ ↦ ?_)
  refine ContMDiffAt.sum (fun d _ ↦ ?_)
  refine ContMDiffAt.sum (fun e _ ↦ ?_)
  have h := (((((hΓ m a).mul (hΓ i b)).mul (hΓ j c)).mul (hΓ k d)).mul (hΓ l e)).mul
    ((hR m i j k l).mul (hR a b c d e))
  convert h using 1
  ext p
  simp only [Pi.mul_apply]
  ring

/-! ## Joint smoothness of `|Rm|²` -/

/-- **The squared norm of the curvature of a jointly smooth family of metrics is jointly
smooth**, and it may be computed in the coordinate frame.

The chart centre `x₀` and the evaluation point are the same here; the statement is the pointwise
form (`Work.Diff.EXT.JointSmoothAt`) that the continuity proof needs. -/
theorem rmNormSq_jointSmoothAt
    [T2Space M] [I.Boundaryless]
    (hLC : LCSmooth I M) {G : ℝ → SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x₀ : M) :
    Work.Diff.EXT.JointSmoothAt I M (fun p : ℝ × M ↦ rmNormSq (G p.1) p.2) t₀ x₀ := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t₀).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hex : Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ N4 (GramM (I := I) G x₀ p.1 p.2) (rmC4 (I := I) G x₀ p.1 p.2)) t₀ x₀ :=
    N4_jointSmooth (I := I) (M := M)
      (fun i j ↦ by
        simpa only [GramM, GramInv] using gramInv_jointSmooth (I := I) hJ hG ht₀ x₀ i j)
      (fun i j k l ↦ rmC4_jointSmooth (I := I) hLC hJ hG ht₀ x₀ i j k l)
  refine hex.congr_of_eventuallyEq ?_
  rw [nhds_prod_eq]
  filter_upwards [Filter.prod_mem_prod Filter.univ_mem
      ((chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀))] with p hp
  exact (rmNormSq_eq_N4_of_basis (I := I) hLC p.2
    (fun i ↦ cFrame (I := I) x₀ i p.2) (GramM (I := I) G x₀ p.1 p.2)
    (fun i j ↦ rfl) (cFrame_span (I := I) x₀ hp.2))

/-! ## Continuity in the time variable of the Gram contractions -/

/-- Continuity of a finite sum of continuous functions. -/
theorem continuousAt_finsetSum {ι M X : Type*} [TopologicalSpace M] [AddCommMonoid M]
    [ContinuousAdd M] [TopologicalSpace X] {f : ι → X → M} {x : X} (s : Finset ι)
    (h : ∀ i ∈ s, ContinuousAt (f i) x) :
    ContinuousAt (fun y ↦ ∑ i ∈ s, f i y) x :=
  tendsto_finset_sum s h

/-- Continuity in `t` of `N4 (Γ t) (R t)` from continuity of the entries of `Γ⁻¹` and of `R`. -/
theorem N4_continuousAt {n : ℕ} {Γ : ℝ → Matrix (Fin n) (Fin n) ℝ} {R : ℝ → Curv4 n}
    {t₀ : ℝ} (hΓ : ∀ i j, ContinuousAt (fun t ↦ (Γ t)⁻¹ i j) t₀)
    (hR : ∀ i j k l, ContinuousAt (fun t ↦ R t i j k l) t₀) :
    ContinuousAt (fun t ↦ N4 (Γ t) (R t)) t₀ := by
  show ContinuousAt (fun t ↦ N4 (Γ t) (R t)) t₀
  simp only [N4]
  refine continuousAt_finsetSum _ (fun i _ ↦ ?_)
  refine continuousAt_finsetSum _ (fun j _ ↦ ?_)
  refine continuousAt_finsetSum _ (fun k _ ↦ ?_)
  refine continuousAt_finsetSum _ (fun l _ ↦ ?_)
  refine continuousAt_finsetSum _ (fun a _ ↦ ?_)
  refine continuousAt_finsetSum _ (fun b _ ↦ ?_)
  refine continuousAt_finsetSum _ (fun c _ ↦ ?_)
  refine continuousAt_finsetSum _ (fun d _ ↦ ?_)
  fun_prop

/-- Continuity in `t` of `N5 (Γ t) (R t)`. -/
theorem N5_continuousAt {n : ℕ} {Γ : ℝ → Matrix (Fin n) (Fin n) ℝ} {R : ℝ → Fin n → Curv4 n}
    {t₀ : ℝ} (hΓ : ∀ i j, ContinuousAt (fun t ↦ (Γ t)⁻¹ i j) t₀)
    (hR : ∀ m i j k l, ContinuousAt (fun t ↦ R t m i j k l) t₀) :
    ContinuousAt (fun t ↦ N5 (Γ t) (R t)) t₀ := by
  show ContinuousAt (fun t ↦ N5 (Γ t) (R t)) t₀
  simp only [N5]
  refine continuousAt_finsetSum _ (fun m _ ↦ ?_)
  refine continuousAt_finsetSum _ (fun i _ ↦ ?_)
  refine continuousAt_finsetSum _ (fun j _ ↦ ?_)
  refine continuousAt_finsetSum _ (fun k _ ↦ ?_)
  refine continuousAt_finsetSum _ (fun l _ ↦ ?_)
  refine continuousAt_finsetSum _ (fun a _ ↦ ?_)
  refine continuousAt_finsetSum _ (fun b _ ↦ ?_)
  refine continuousAt_finsetSum _ (fun c _ ↦ ?_)
  refine continuousAt_finsetSum _ (fun d _ ↦ ?_)
  refine continuousAt_finsetSum _ (fun e _ ↦ ?_)
  fun_prop

/-- **Global smoothness of `y ↦ |Rm(G τ)|²(y)`** for a fixed time `τ ∈ J`: pointwise joint
smoothness of the family at `(τ,y)` gives smoothness of the time slice. -/
theorem rmNormSq_cmdiff_slice [I.Boundaryless] [T2Space M]
    (hLC : LCSmooth I M) {G : ℝ → SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : JointSmooth G J) {τ : ℝ} (hτ : τ ∈ J) :
    CMDiff ∞ (fun y : M ↦ rmNormSq (G τ) y) := by
  intro y
  have h := rmNormSq_jointSmoothAt (I := I) (M := M) hLC hJ hG hτ y
  have h2 : ContMDiffAt I (𝓘(ℝ,ℝ).prod I) ∞ (fun z : M ↦ (τ, z)) y :=
    (contMDiffAt_const (c := τ)).prodMk contMDiffAt_id
  have h3 := h.comp y h2
  simpa only [Function.comp_def, Prod.mk.eta] using h3

/-! ## Continuity at an interior time from joint smoothness -/

/-- Joint smoothness of `(t,y) ↦ Φ (t,y)` at `(t₀,x)` gives continuity in `t` of the slice
`t ↦ Φ (t,x)` at `t₀`. -/
theorem continuousAt_of_jointSmoothAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : ℝ × M → F} {t₀ : ℝ} {x : M} (h : Work.Diff.EXT.JointSmoothAt I M Φ t₀ x) :
    ContinuousAt (fun t : ℝ ↦ Φ (t, x)) t₀ := by
  have h2 : ContinuousAt (fun t : ℝ ↦ (t, x)) t₀ := continuousAt_id.prodMk continuousAt_const
  simpa only [Function.comp_def] using h.continuousAt.comp (f := fun t : ℝ ↦ (t, x)) h2

/-! ## The time reparametrisation `t = τ²` -/

/-- The time-reparametrised family `τ ↦ G (τ²)`. -/
noncomputable def sqFlow (G : ℝ → SMet I M) : ℝ → SMet I M := fun τ ↦ G (τ ^ 2)

/-- **The reparametrisation trick.**  A family of metrics jointly smooth on the *half-open*
interval `[0,T)` is jointly smooth on the *open* interval `(-ρ,ρ)` after `t = τ²`, as long as
`ρ² < T`.  This is the only place where the half-openness of `[0,T)` is used. -/
theorem jointSmooth_sqFlow {G : ℝ → SMet I M} {T ρ : ℝ}
    (hT : 0 < T) (hρ : 0 < ρ) (hρT : ρ ^ 2 < T) (h : JointSmooth G (Set.Ico 0 T)) :
    JointSmooth (sqFlow G) (Set.Ioo (-ρ) ρ) := by
  unfold JointSmooth
  have hsq : ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun p : ℝ × M ↦ (p.1) ^ 2) (Set.Ioo (-ρ) ρ ×ˢ (univ : Set M)) := by
    have h1 : ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M ↦ p.1)
        (Set.Ioo (-ρ) ρ ×ˢ (univ : Set M)) := contMDiffOn_fst
    simpa using h1.pow 2
  have hΛ : ContMDiffOn (𝓘(ℝ,ℝ).prod I) ((𝓘(ℝ,ℝ)).prod I) ∞
      (fun p : ℝ × M ↦ (p.1 ^ 2, p.2)) (Set.Ioo (-ρ) ρ ×ˢ (univ : Set M)) :=
    hsq.prodMk contMDiffOn_snd
  have hsub : (Set.Ioo (-ρ) ρ ×ˢ (univ : Set M))
      ⊆ (fun p : ℝ × M ↦ (p.1 ^ 2, p.2)) ⁻¹' (Set.Ico 0 T ×ˢ (univ : Set M)) := by
    intro p hp
    obtain ⟨hp1, -⟩ := hp
    obtain ⟨hlo, hhi⟩ := hp1
    refine ⟨⟨?_, ?_⟩, trivial⟩
    · nlinarith [sq_nonneg p.1]
    · nlinarith [hlo, hhi]
  exact (ContMDiffOn.comp h hΛ hsub).congr (fun p _ ↦ rfl)

/-- **Transfer from the reparametrised time.**  If `F` is continuous at `0` and agrees with `f`
after the substitution `s = τ²` on `[0,T)`, then `f` is continuous within `[0,T)` at `0`. -/
theorem continuousWithinAt_of_continuousAt_comp_sq {α : Type*} [TopologicalSpace α]
    {T : ℝ} (hT : 0 < T) {f F : ℝ → α} (hF : ContinuousAt F 0)
    (hf : ∀ s ∈ Set.Ico 0 T, f s = F (Real.sqrt s)) :
    ContinuousWithinAt f (Set.Ico 0 T) 0 := by
  have hsqrt : Filter.Tendsto Real.sqrt (𝓝[Set.Ico 0 T] 0) (𝓝 (Real.sqrt 0)) :=
    Real.continuous_sqrt.continuousAt.tendsto.mono_left inf_le_left
  rw [Real.sqrt_zero] at hsqrt
  have h1 : Filter.Tendsto (fun s : ℝ ↦ F (Real.sqrt s)) (𝓝[Set.Ico 0 T] 0) (𝓝 (F 0)) :=
    hF.tendsto.comp hsqrt
  have h2 : f =ᶠ[𝓝[Set.Ico 0 T] 0] fun s : ℝ ↦ F (Real.sqrt s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs using hf s hs
  have h3 : f 0 = F 0 := by rw [hf 0 ⟨le_refl 0, hT⟩, Real.sqrt_zero]
  show Filter.Tendsto f (𝓝[Set.Ico 0 T] 0) (𝓝 (f 0))
  rw [h3]
  exact h1.congr' h2.symm

/-! ## The first conjunct: continuity of `|Rm|²` -/

/-- **Continuity of `s ↦ |Rm(G s)|²(x)` within `[0,T)` at `0`.** -/
theorem continuousWithinAt_rmNormSq_zero [I.Boundaryless] [T2Space M]
    (hLC : LCSmooth I M) {G : ℝ → SMet I M} {T : ℝ} (hflow : IsRicciFlow G T) (x : M) :
    ContinuousWithinAt (fun s ↦ rmNormSq (G s) x) (Set.Ico 0 T) 0 := by
  by_cases hT : T ≤ 0
  · rw [Set.Ico_eq_empty_iff.mpr (not_lt.mpr hT)]
    simp [ContinuousWithinAt, nhdsWithin_empty]
  · have hTpos : 0 < T := not_le.mp hT
    set ρ := Real.sqrt T / 2 with hρdef
    have hρ : 0 < ρ := by positivity
    have hρT : ρ ^ 2 < T := by
      rw [hρdef, div_pow, Real.sq_sqrt (le_of_lt hTpos)]
      nlinarith
    have hsq := jointSmooth_sqFlow (I := I) (M := M) hTpos hρ hρT hflow.1
    have h0 : (0 : ℝ) ∈ Set.Ioo (-ρ) ρ := ⟨by linarith, hρ⟩
    have hrm := rmNormSq_jointSmoothAt (I := I) (M := M) hLC isOpen_Ioo hsq h0 x
    have hcont : ContinuousAt (fun τ : ℝ ↦ rmNormSq (sqFlow G τ) x) 0 :=
      continuousAt_of_jointSmoothAt (I := I) (M := M) hrm
    refine continuousWithinAt_of_continuousAt_comp_sq hTpos hcont ?_
    intro s hs
    show rmNormSq (G s) x = rmNormSq (sqFlow G (Real.sqrt s)) x
    rw [show sqFlow G (Real.sqrt s) = G ((Real.sqrt s) ^ 2) from rfl, Real.sq_sqrt hs.1]

/-! ## Continuity of `|∇Rm|²` -/

/-- **Continuity in `t` of `|∇Rm|²(G t)(x)`.**  The frame-independent general-basis form `N5`
(`dRmNormSq_eq_N5_of_basis`) is used, with the curvature components in the coordinate frame
(`Work.Diff.GE.covRmC5_continuousAt`). -/
theorem dRmNormSq_continuousAt [I.Boundaryless] [T2Space M]
    (hLC : LCSmooth I M) {G : ℝ → SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M) :
    ContinuousAt (fun t ↦ dRmNormSq (G t) x) t₀ := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t₀).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hΓ : ∀ i j, ContinuousAt (fun t ↦ (GramM (I := I) G x t x)⁻¹ i j) t₀ := by
    intro i j
    exact continuousAt_of_jointSmoothAt (I := I) (M := M)
      (by simpa only [GramM, GramInv] using gramInv_jointSmooth (I := I) hJ hG ht₀ x i j)
  have hR : ∀ m i j k l : Fin (Module.finrank ℝ E), ContinuousAt
      (fun t ↦ covRmC5 (I := I) G x t x m i j k l) t₀ :=
    fun m i j k l ↦ covRmC5_continuousAt (I := I) hLC hJ hG ht₀ x m i j k l
  have hN5 := N5_continuousAt (n := Module.finrank ℝ E) hΓ hR
  refine hN5.congr_of_eventuallyEq ?_
  filter_upwards with t
  exact dRmNormSq_eq_N5_of_basis (I := I) hLC x (fun i ↦ cFrame (I := I) x i x)
    (GramM (I := I) G x t x) (fun i j ↦ rfl) (cFrame_span (I := I) x (mem_chart_source H x))

/-! ## Continuity of the Laplacian of `|Rm|²` -/

/-- **Continuity in `t` of the Laplacian term `Δ|Rm|²(G t)(x)`.**

The frozen `laplAt` is the Hessian trace in the `Classical.epsilon` frame, so it is replaced by the
inverse-Gram contraction of the Hessian in the (time-independent) coordinate frame
(`laplAt_eq_sum_invGram`); the two entries of the Hessian,

`mvfderiv (fun y ↦ mvfderiv |Rm(G t)|² y (smoothExt x w y)) x v`  and
`mvfderiv |Rm(G t)|² x (lcOf (G t) (smoothExt x w) x v)`,

are continuous in `t` because the spatial derivatives of the jointly smooth family
`(t,y) ↦ |Rm(G t)|²(y)` are continuous in `t` (`continuousAt_mvfderiv_family`), and the *moving*
direction `lcOf (G t) (smoothExt x w) x v` is expanded in the coordinate frame with coefficients
continuous in `t` (`lcOf_eq_sum_reconCoef`, `reconCoef_continuousAt`). -/
theorem laplAt_rmNormSq_continuousAt_alt [I.Boundaryless] [T2Space M]
    (hLC : LCSmooth I M) {G : ℝ → SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M)
    (hrm : Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ rmNormSq (G p.1) p.2) t₀ x) :
    ContinuousAt (fun s ↦ laplAt (G s) (rmNormSq (G s)) x) t₀ := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t₀).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  -- the inverse-Gram contraction of the Hessian in the coordinate frame
  have hΓ : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousAt (fun s : ℝ ↦ (GramM (I := I) G x s x)⁻¹ i j) t₀ := by
    intro i j
    exact continuousAt_of_jointSmoothAt (I := I) (M := M)
      (by simpa only [GramM, GramInv] using gramInv_jointSmooth (I := I) hJ hG ht₀ x i j)
  -- the second slot `w` of the Hessian is a *fixed* smooth field
  have hW : ∀ w : TangentSpace I x,
      Work.Diff.EXT.SmoothField I M (smoothExt x w) :=
    fun w ↦ (Work.Diff.GE.smoothExt_cmdiff (I := I) (M := M) x w)
  -- the two entries of the Hessian are continuous in `t`
  have hA : ∀ (w v : TangentSpace I x), ContinuousAt (fun s : ℝ ↦
      mvfderiv I (fun y : M ↦ mvfderiv I (fun z : M ↦ rmNormSq (G s) z) y
        (smoothExt x w y)) x v) t₀ := by
    intro w v
    have hJ' : Work.Diff.EXT.JointSmoothAt I M
        (fun p : ℝ × M ↦ mvfderiv I (fun z : M ↦ rmNormSq (G p.1) z) p.2
          (smoothExt x w p.2)) t₀ x :=
      Work.Diff.EXT.contMDiffAt_mvfderiv_along_field (I := I) (M := M) (F := ℝ) hrm (hW w)
    exact Work.Diff.EXT.continuousAt_mvfderiv_family (I := I) (M := M) (F := ℝ) hJ' v
  have hB : ∀ (w v : TangentSpace I x), ContinuousAt (fun s : ℝ ↦
      mvfderiv I (fun z : M ↦ rmNormSq (G s) z) x (lcOf (G s) (smoothExt x w) x v)) t₀ := by
    intro w v
    -- expansion of the moving direction in the coordinate frame
    have hexp : ∀ s : ℝ, lcOf (G s) (smoothExt x w) x v
        = ∑ k, Work.Diff.EXT.reconCoef (I := I) G x (smoothExt x v) (smoothExt x w) k s x
            • Work.Diff.EXT.fr (I := I) x k x := by
      intro s
      have h := Work.Diff.EXT.lcOf_eq_sum_reconCoef (I := I) G x (smoothExt x v)
        (smoothExt x w) s (y := x) (mem_chart_source H x)
        ((hW v).contMDiffAt (x := x)) ((hW w).contMDiffAt (x := x))
      simpa only [Work.Diff.GE.smoothExt_apply, Work.Diff.EXT.fr] using h
    have hlin : ∀ s : ℝ, mvfderiv I (fun z : M ↦ rmNormSq (G s) z) x
          (lcOf (G s) (smoothExt x w) x v)
        = ∑ k, Work.Diff.EXT.reconCoef (I := I) G x (smoothExt x v) (smoothExt x w) k s x
            * mvfderiv I (fun z : M ↦ rmNormSq (G s) z) x (Work.Diff.EXT.fr (I := I) x k x) := by
      intro s
      rw [hexp s, map_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by rw [map_smul, smul_eq_mul]
    rw [funext hlin]
    refine continuousAt_finsetSum _ fun k _ ↦ ?_
    refine ContinuousAt.mul ?_ ?_
    · exact reconCoef_continuousAt (I := I) (M := M) hJ hG ht₀ x
        ((hW v).contMDiffAt (x := x)) ((hW w).contMDiffAt (x := x)) k
    · exact Work.Diff.EXT.continuousAt_mvfderiv_family (I := I) (M := M) (F := ℝ) hrm
        (Work.Diff.EXT.fr (I := I) x k x)
  have hhess : ∀ i j : Fin (Module.finrank ℝ E), ContinuousAt (fun s : ℝ ↦
      hessAt (G s) (fun y : M ↦ rmNormSq (G s) y) x
        (cFrame (I := I) x i x) (cFrame (I := I) x j x)) t₀ := by
    intro i j
    have h1 := hA (cFrame (I := I) x j x) (cFrame (I := I) x i x)
    have h2 := hB (cFrame (I := I) x j x) (cFrame (I := I) x i x)
    have h := h1.sub h2
    refine h.congr_of_eventuallyEq ?_
    filter_upwards with s
    simp only [hessAt, Pi.sub_apply, cFrame]
  -- the inverse-Gram contraction is continuous
  have hcont : ContinuousAt (fun s : ℝ ↦ ∑ i, ∑ j, (GramM (I := I) G x s x)⁻¹ i j
      * hessAt (G s) (fun y : M ↦ rmNormSq (G s) y) x
          (cFrame (I := I) x i x) (cFrame (I := I) x j x)) t₀ := by
    refine continuousAt_finsetSum _ fun i _ ↦ ?_
    refine continuousAt_finsetSum _ fun j _ ↦ ?_
    exact (hΓ i j).mul (hhess i j)
  -- and it agrees with `laplAt` on the open time set
  refine hcont.congr_of_eventuallyEq ?_
  filter_upwards [hJ.mem_nhds ht₀] with s hs
  exact laplAt_eq_sum_invGram (I := I) (M := M) hLC (G s) (fun y : M ↦ rmNormSq (G s) y) x
    (rmNormSq_cmdiff_slice (I := I) (M := M) hLC hJ hG hs)
    (fun i ↦ cFrame (I := I) x i x) (GramM (I := I) G x s x) (fun i j ↦ rfl)
    (cFrame_span (I := I) x (mem_chart_source H x))

/-! ## Continuity of `⟪Rm, Q(Rm)⟫` -/

/-- **Continuity in `t` of `⟪Rm, Q(Rm)⟫(G t)(x)`.**  The frozen `qPairAt` is computed in the
`Classical.epsilon` frame, which is not continuous in `t`; it is therefore replaced by the
frame-independent general-basis form `qPairGen` in the coordinate frame (`qPairAt_eq_qPairGen_Gram`,
jointly smooth by `qPairGen_jointSmooth`). -/
theorem qPairAt_continuousAt [I.Boundaryless] [T2Space M]
    (hLC : LCSmooth I M) {G : ℝ → SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M) :
    ContinuousAt (fun t ↦ qPairAt (G t) x) t₀ := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t₀).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hjoint : Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ qPairGen (GramM (I := I) G x p.1 p.2) (rmC4 (I := I) G x p.1 p.2))
      t₀ x :=
    qPairGen_jointSmooth (I := I) (M := M)
      (fun i j ↦ by
        simpa only [GramM, GramInv] using gramInv_jointSmooth (I := I) hJ hG ht₀ x i j)
      (fun i j k l ↦ rmC4_jointSmooth (I := I) hLC hJ hG ht₀ x i j k l)
  have hcont := continuousAt_of_jointSmoothAt (I := I) (M := M) hjoint
  refine hcont.congr_of_eventuallyEq ?_
  filter_upwards with t
  exact qPairAt_eq_qPairGen_Gram (I := I) hLC G x (mem_chart_source H x) t

theorem flowContAtZero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) :
    ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T → ∀ x : M,
      ContinuousWithinAt (fun s ↦ Submission.Diff.rmNormSq (G s) x) (Set.Ico 0 T) 0 ∧
      ContinuousWithinAt (fun s ↦ Submission.Diff.laplAt (G s) (Submission.Diff.rmNormSq (G s)) x
        - 2 * Submission.Diff.dRmNormSq (G s) x + 2 * Submission.Diff.qPairAt (G s) x)
        (Set.Ico 0 T) 0 := by
  intro G T hflow x
  refine ⟨continuousWithinAt_rmNormSq_zero (I := I) (M := M) hLC hflow x, ?_⟩
  by_cases hT : T ≤ 0
  · rw [Set.Ico_eq_empty_iff.mpr (not_lt.mpr hT)]
    simp [ContinuousWithinAt, nhdsWithin_empty]
  · have hTpos : 0 < T := not_le.mp hT
    set ρ := Real.sqrt T / 2 with hρdef
    have hρ : 0 < ρ := by positivity
    have hρT : ρ ^ 2 < T := by
      rw [hρdef, div_pow, Real.sq_sqrt (le_of_lt hTpos)]
      nlinarith
    have hsq := jointSmooth_sqFlow (I := I) (M := M) hTpos hρ hρT hflow.1
    have h0 : (0 : ℝ) ∈ Set.Ioo (-ρ) ρ := ⟨by linarith, hρ⟩
    have hrm := rmNormSq_jointSmoothAt (I := I) (M := M) hLC isOpen_Ioo hsq h0 x
    have hlapl := laplAt_rmNormSq_continuousAt_alt (I := I) (M := M) hLC isOpen_Ioo hsq h0 x hrm
    have hdr := dRmNormSq_continuousAt (I := I) (M := M) hLC isOpen_Ioo hsq h0 x
    have hqp := qPairAt_continuousAt (I := I) (M := M) hLC isOpen_Ioo hsq h0 x
    have hcomb : ContinuousAt (fun τ : ℝ ↦
        Submission.Diff.laplAt (sqFlow G τ) (Submission.Diff.rmNormSq (sqFlow G τ)) x
          - 2 * Submission.Diff.dRmNormSq (sqFlow G τ) x
          + 2 * Submission.Diff.qPairAt (sqFlow G τ) x) 0 :=
      (hlapl.sub (hdr.const_mul 2)).add (hqp.const_mul 2)
    refine continuousWithinAt_of_continuousAt_comp_sq hTpos hcomb ?_
    intro s hs
    show Submission.Diff.laplAt (G s) (Submission.Diff.rmNormSq (G s)) x
        - 2 * Submission.Diff.dRmNormSq (G s) x + 2 * Submission.Diff.qPairAt (G s) x
      = Submission.Diff.laplAt (sqFlow G (Real.sqrt s))
          (Submission.Diff.rmNormSq (sqFlow G (Real.sqrt s))) x
        - 2 * Submission.Diff.dRmNormSq (sqFlow G (Real.sqrt s)) x
        + 2 * Submission.Diff.qPairAt (sqFlow G (Real.sqrt s)) x
    rw [show sqFlow G (Real.sqrt s) = G s from by
      rw [sqFlow, Real.sq_sqrt hs.1]]

end Work.Diff.GE
