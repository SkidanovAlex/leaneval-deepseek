import Mathlib
import Submission.Work.Diff.GE.FrameIndep
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.GE.chartcalc
import Submission.Work.Diff.GE.rmPDeps
import Submission.Work.Diff.GE.rmP_jointSmooth
import Submission.Work.Diff.GE.gramInv_jointSmooth
import Submission.Work.Diff.GE.rmNormSq_eq_N4_of_basis
import Submission.Work.Diff.GE.dRmNormSq_eq_N5_of_basis
import Submission.Work.Diff.GE.rmFrame_eq_rot
import Submission.Work.Diff.GE.qPair_rot_eq_qPairGen
import Submission.Work.Diff.GE.hessAt_comm
import Submission.Work.Diff.GE.laplAt_eq_sum_invGram
import Submission.Work.Diff.GE.Kato3.CovRmKit
import Submission.Work.Diff.GE.mvfderivWithin_apply_mlieBracketWithin_two
import Submission.Work.Diff.GE.metric_pairing_family_jointSmooth
import Submission.Work.Diff.GE.tower_jointSmooth
import Submission.Work.Diff.GE.Gest.Base
import Submission.Work.Diff.GE.Gest.hess_mul_field
import Submission.Work.Diff.T.lcOf_apply_inner_koszul
import Submission.Work.Diff.EXT.continuousAt_mvfderiv_family
import Submission.Work.Diff.GE.rmP_jointSmoothNoCompact
import Submission.Work.Diff.GE.reconCoef_continuousAt
import Submission.Work.Diff.GE.qPairAt_eq_qPairGen_Gram
import Submission.Work.Diff.GE.qPairGen_jointSmooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Continuity of the curvature quantities along a Ricci flow at the initial time

Target: `Work.Diff.GE.continuous_flow_quantities`.

`IsRicciFlow G T` gives joint smoothness of the metric family only on the *half-open* interval
`[0,T)`; reparametrising time by `t = τ²` turns `[0,T)` into an *open* interval around `0`, on
which every frozen quantity is a continuous function of the metric family, and the conclusion is
transferred back along `s ↦ √s`.

On the open interval the four frozen quantities are handled as follows.

* `rmNormSq` and `dRmNormSq` are frame independent: they may be computed in the *coordinate frame*
  `cFrame x ·` of the chart at the point `x` (a basis of `T_yM` at every `y` of the chart), by
  `rmNormSq_eq_N4_of_basis` / `dRmNormSq_eq_N5_of_basis`.  The inverse Gram matrix and the
  curvature components `rmC4` are jointly smooth (`gramInv_jointSmooth`, `rmC4_jointSmooth`), and
  the `∇Rm` components are handled through the field form of `∇Rm`
  (`Work.Diff.GE.Kato3.covRm_field_form`) together with the chart Christoffel symbol
  (`chrB_const_jointSmooth`).
* `qPairAt` is frame independent as well; `qPair_rot_eq_qPairGen` shows that in a general basis
  with Gram matrix `Γ` and curvature components `C` it equals the polynomial contraction
  `qPairGen Γ C`, which is continuous in `(Γ⁻¹, C)`.
* `laplAt` is the contraction of the Hessian with the inverse Gram matrix
  (`laplAt_eq_sum_invGram`); the Hessian is computed with the *field* form of `hessAt`
  (`cfq_hessAt_field`), so that its second argument only enters through the value at `x` and the
  Christoffel symbols can be read off in the coordinate frame.

All the `_jointSmooth` inputs are local in `x`, hence no compactness of `M` is used anywhere
(the frozen statement has no `CompactSpace` hypothesis).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric

section Helpers

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- At every point of the chart at `x₀`, the coordinate frame `cFrame x₀ ·` is a basis: its
span is everything.  (The expansion of any section in the coordinate frame is
`Commons.Geometry.Manifold.Tangent.eqOn_sum_frameSection_of_basis`.) -/
theorem cfq_cFrame_span (x₀ : M) {p : M} (hp : p ∈ (chartAt H x₀).source) :
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
theorem cfq_N4_jointSmooth {n : ℕ} {Γ : ℝ × M → Matrix (Fin n) (Fin n) ℝ}
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
theorem cfq_N5_jointSmooth {n : ℕ} {Γ : ℝ × M → Matrix (Fin n) (Fin n) ℝ}
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
theorem cfq_rmNormSq_jointSmoothAt
    [T2Space M] [I.Boundaryless]
    (hLC : LCSmooth I M) {G : ℝ → SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x₀ : M) :
    Work.Diff.EXT.JointSmoothAt I M (fun p : ℝ × M ↦ rmNormSq (G p.1) p.2) t₀ x₀ := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t₀).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hex : Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ N4 (GramM (I := I) G x₀ p.1 p.2) (rmC4 (I := I) G x₀ p.1 p.2)) t₀ x₀ :=
    cfq_N4_jointSmooth (I := I) (M := M)
      (fun i j ↦ by
        simpa only [GramM, GramInv] using gramInv_jointSmooth (I := I) hJ hG ht₀ x₀ i j)
      (fun i j k l ↦ rmC4_jointSmooth (I := I) hLC hJ hG ht₀ x₀ i j k l)
  refine hex.congr_of_eventuallyEq ?_
  rw [nhds_prod_eq]
  filter_upwards [Filter.prod_mem_prod Filter.univ_mem
      ((chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀))] with p hp
  exact (rmNormSq_eq_N4_of_basis (I := I) hLC p.2
    (fun i ↦ cFrame (I := I) x₀ i p.2) (GramM (I := I) G x₀ p.1 p.2)
    (fun i j ↦ rfl) (cfq_cFrame_span (I := I) x₀ hp.2))

/-! ## Continuity in the time variable of the Gram contractions -/

/-- Continuity of a finite sum of continuous functions. -/
theorem cfq_continuousAt_finsetSum {ι M X : Type*} [TopologicalSpace M] [AddCommMonoid M]
    [ContinuousAdd M] [TopologicalSpace X] {f : ι → X → M} {x : X} (s : Finset ι)
    (h : ∀ i ∈ s, ContinuousAt (f i) x) :
    ContinuousAt (fun y ↦ ∑ i ∈ s, f i y) x :=
  tendsto_finset_sum s h

/-- Continuity in `t` of `N4 (Γ t) (R t)` from continuity of the entries of `Γ⁻¹` and of `R`. -/
theorem cfq_N4_continuousAt {n : ℕ} {Γ : ℝ → Matrix (Fin n) (Fin n) ℝ} {R : ℝ → Curv4 n}
    {t₀ : ℝ} (hΓ : ∀ i j, ContinuousAt (fun t ↦ (Γ t)⁻¹ i j) t₀)
    (hR : ∀ i j k l, ContinuousAt (fun t ↦ R t i j k l) t₀) :
    ContinuousAt (fun t ↦ N4 (Γ t) (R t)) t₀ := by
  show ContinuousAt (fun t ↦ N4 (Γ t) (R t)) t₀
  simp only [N4]
  refine cfq_continuousAt_finsetSum _ (fun i _ ↦ ?_)
  refine cfq_continuousAt_finsetSum _ (fun j _ ↦ ?_)
  refine cfq_continuousAt_finsetSum _ (fun k _ ↦ ?_)
  refine cfq_continuousAt_finsetSum _ (fun l _ ↦ ?_)
  refine cfq_continuousAt_finsetSum _ (fun a _ ↦ ?_)
  refine cfq_continuousAt_finsetSum _ (fun b _ ↦ ?_)
  refine cfq_continuousAt_finsetSum _ (fun c _ ↦ ?_)
  refine cfq_continuousAt_finsetSum _ (fun d _ ↦ ?_)
  fun_prop

/-- Continuity in `t` of `N5 (Γ t) (R t)`. -/
theorem cfq_N5_continuousAt {n : ℕ} {Γ : ℝ → Matrix (Fin n) (Fin n) ℝ} {R : ℝ → Fin n → Curv4 n}
    {t₀ : ℝ} (hΓ : ∀ i j, ContinuousAt (fun t ↦ (Γ t)⁻¹ i j) t₀)
    (hR : ∀ m i j k l, ContinuousAt (fun t ↦ R t m i j k l) t₀) :
    ContinuousAt (fun t ↦ N5 (Γ t) (R t)) t₀ := by
  show ContinuousAt (fun t ↦ N5 (Γ t) (R t)) t₀
  simp only [N5]
  refine cfq_continuousAt_finsetSum _ (fun m _ ↦ ?_)
  refine cfq_continuousAt_finsetSum _ (fun i _ ↦ ?_)
  refine cfq_continuousAt_finsetSum _ (fun j _ ↦ ?_)
  refine cfq_continuousAt_finsetSum _ (fun k _ ↦ ?_)
  refine cfq_continuousAt_finsetSum _ (fun l _ ↦ ?_)
  refine cfq_continuousAt_finsetSum _ (fun a _ ↦ ?_)
  refine cfq_continuousAt_finsetSum _ (fun b _ ↦ ?_)
  refine cfq_continuousAt_finsetSum _ (fun c _ ↦ ?_)
  refine cfq_continuousAt_finsetSum _ (fun d _ ↦ ?_)
  refine cfq_continuousAt_finsetSum _ (fun e _ ↦ ?_)
  fun_prop

/-! ## Continuity at an interior time from joint smoothness -/

/-- Joint smoothness of `(t,y) ↦ Φ (t,y)` at `(t₀,x)` gives continuity in `t` of the slice
`t ↦ Φ (t,x)` at `t₀`. -/
theorem cfq_continuousAt_of_jointSmoothAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : ℝ × M → F} {t₀ : ℝ} {x : M} (h : Work.Diff.EXT.JointSmoothAt I M Φ t₀ x) :
    ContinuousAt (fun t : ℝ ↦ Φ (t, x)) t₀ := by
  have h2 : ContinuousAt (fun t : ℝ ↦ (t, x)) t₀ := continuousAt_id.prodMk continuousAt_const
  simpa only [Function.comp_def] using h.continuousAt.comp (f := fun t : ℝ ↦ (t, x)) h2
/-! ## The time reparametrisation `t = τ²` -/

/-- The time-reparametrised family `τ ↦ G (τ²)`. -/
noncomputable def cfq_sqFlow (G : ℝ → Submission.Diff.SMet I M) :
    ℝ → Submission.Diff.SMet I M := fun τ ↦ G (τ ^ 2)

/-- **The reparametrisation trick.**  A family of metrics jointly smooth on the *half-open*
interval `[0,T)` is jointly smooth on the *open* interval `(-ρ,ρ)` after `t = τ²`, as long as
`ρ² < T`.  This is the only place where the half-openness of `[0,T)` is used. -/
theorem cfq_jointSmooth_sqFlow (G : ℝ → Submission.Diff.SMet I M) {T ρ : ℝ}
    (hT : 0 < T) (hρ : 0 < ρ) (hρT : ρ ^ 2 < T)
    (h : Submission.Diff.JointSmooth G (Set.Ico 0 T)) :
    Submission.Diff.JointSmooth (cfq_sqFlow G) (Set.Ioo (-ρ) ρ) := by
  unfold Submission.Diff.JointSmooth
  have hsq : ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun p : ℝ × M => (p.1) ^ 2) (Set.Ioo (-ρ) ρ ×ˢ (univ : Set M)) := by
    have h1 : ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M => p.1)
        (Set.Ioo (-ρ) ρ ×ˢ (univ : Set M)) := contMDiffOn_fst
    simpa using h1.pow 2
  have hΛ : ContMDiffOn (𝓘(ℝ,ℝ).prod I) ((𝓘(ℝ,ℝ)).prod I) ∞
      (fun p : ℝ × M => (p.1 ^ 2, p.2)) (Set.Ioo (-ρ) ρ ×ˢ (univ : Set M)) :=
    hsq.prodMk contMDiffOn_snd
  have hsub : (Set.Ioo (-ρ) ρ ×ˢ (univ : Set M))
      ⊆ (fun p : ℝ × M => (p.1 ^ 2, p.2)) ⁻¹' (Set.Ico 0 T ×ˢ (univ : Set M)) := by
    intro p hp
    obtain ⟨hp1, -⟩ := hp
    obtain ⟨hlo, hhi⟩ := hp1
    refine ⟨⟨?_, ?_⟩, trivial⟩
    · nlinarith [sq_nonneg p.1]
    · nlinarith [hlo, hhi]
  have hcomp := ContMDiffOn.comp h hΛ hsub
  exact hcomp.congr (fun p hp => rfl)

/-- **Transfer from the reparametrised time.**  If `F` is continuous at `0` and agrees with `f`
after the substitution `s = τ²` on `[0,T)`, then `f` is continuous within `[0,T)` at `0`. -/
theorem cfq_continuousWithinAt_of_continuousAt_comp_sq {α : Type*} [TopologicalSpace α]
    {T : ℝ} (hT : 0 < T) {f F : ℝ → α} (hF : ContinuousAt F 0)
    (hf : ∀ s ∈ Set.Ico 0 T, f s = F (Real.sqrt s)) :
    ContinuousWithinAt f (Set.Ico 0 T) 0 := by
  have hsqrt : Filter.Tendsto Real.sqrt (𝓝[Set.Ico 0 T] 0) (𝓝 (Real.sqrt 0)) :=
    Real.continuous_sqrt.continuousAt.tendsto.mono_left inf_le_left
  rw [Real.sqrt_zero] at hsqrt
  have h1 : Filter.Tendsto (fun s : ℝ => F (Real.sqrt s)) (𝓝[Set.Ico 0 T] 0) (𝓝 (F 0)) :=
    hF.tendsto.comp hsqrt
  have h2 : f =ᶠ[𝓝[Set.Ico 0 T] 0] fun s : ℝ => F (Real.sqrt s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs using hf s hs
  have h3 : f 0 = F 0 := by rw [hf 0 ⟨le_refl 0, hT⟩, Real.sqrt_zero]
  show Filter.Tendsto f (𝓝[Set.Ico 0 T] 0) (𝓝 (f 0))
  rw [h3]
  exact h1.congr' h2.symm

/-- **Continuity of `s ↦ |Rm(G s)|²(x)` within `[0,T)` at `0`.** -/
theorem cfq_continuousWithinAt_rmNormSq_zero [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) {G : ℝ → Submission.Diff.SMet I M} {T : ℝ}
    (hflow : Submission.Diff.IsRicciFlow G T) (x : M) :
    ContinuousWithinAt (fun s ↦ Submission.Diff.rmNormSq (G s) x) (Set.Ico 0 T) 0 := by
  by_cases hT : T ≤ 0
  · rw [Set.Ico_eq_empty_iff.mpr (not_lt.mpr hT)]
    simp [ContinuousWithinAt, nhdsWithin_empty]
  · have hTpos : 0 < T := not_le.mp hT
    set ρ := Real.sqrt T / 2 with hρdef
    have hρ : 0 < ρ := by positivity
    have hρT : ρ ^ 2 < T := by
      rw [hρdef, div_pow, Real.sq_sqrt (le_of_lt hTpos)]
      nlinarith
    have hsq := cfq_jointSmooth_sqFlow (I := I) (M := M) G hTpos hρ hρT hflow.1
    have h0 : (0 : ℝ) ∈ Set.Ioo (-ρ) ρ := ⟨by linarith, hρ⟩
    have hrm := cfq_rmNormSq_jointSmoothAt (I := I) (M := M) hLC isOpen_Ioo hsq h0 x
    have hcont : ContinuousAt (fun τ : ℝ ↦ Submission.Diff.rmNormSq (cfq_sqFlow G τ) x) 0 :=
      cfq_continuousAt_of_jointSmoothAt (I := I) (M := M) hrm
    refine cfq_continuousWithinAt_of_continuousAt_comp_sq hTpos hcont ?_
    intro s hs
    show Submission.Diff.rmNormSq (G s) x
      = Submission.Diff.rmNormSq (cfq_sqFlow G (Real.sqrt s)) x
    rw [show cfq_sqFlow G (Real.sqrt s) = G ((Real.sqrt s) ^ 2) from rfl, Real.sq_sqrt hs.1]

/-! ## The field form of the Hessian -/

/-- **`hessAt` depends on its second argument only through the value.**  For a function `u` smooth at
`x`, the frozen `hessAt g u x v w` is defined with the `Classical.epsilon`-chosen extension
`smoothExt x w`; it equals the field-based expression with *any* smooth field `Z` with `Z x = w`, namely
`mvfderiv (fun y ↦ mvfderiv I u y (Z y)) x v - mvfderiv I u x (∇_v Z)`.  Equivalently, `hessAt g u x v w`
is the second covariant derivative `(∇_v du)(w)` of `u` at `x`.  Proof route: compare the two choices of
the field using the identity `X (Y f) = Y (X f) + [X, Y] f` for first and second directional derivatives
along fields (`Commons.Geometry.Manifold.VectorField.mvfderiv_second_along_fields`), the formula
`[X, Y] = ∇_X Y - ∇_Y X` for a torsion-free connection and the fact that `∇_X Y` at `x` depends only on
`X x`; alternatively use the Leibniz rule for the pairing `⟨du, Z⟩` of the covector field `du` with the
field `Z`, which gives `(∇_v du)(Z x)` directly. -/
theorem cfq_hessAt_field
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) {u : M → ℝ} (hu : ContMDiffAt I 𝓘(ℝ, ℝ) 2 u x)
    (Y Z : Π y : M, TangentSpace I y) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) :
    hessAt g u x (Y x) (Z x)
      = mvfderiv I (fun y : M ↦ mvfderiv I u y (Z y)) x (Y x)
        - mvfderiv I u x (lcOf g Z x (Y x)) := by
  classical
  haveI : IsManifold I (2 : ℕ∞ω) M :=
    IsManifold.of_le (I := I) (M := M) (m := (2 : ℕ∞ω)) (n := ∞) (by simp)
  -- `u` is `C²` at `x`, hence `C²` on an open neighbourhood `U` of `x`
  obtain ⟨U, hUopen, hxU, hUsm⟩ :=
    hu.contMDiffOn' (m := (2 : ℕ∞ω)) (n := (2 : ℕ∞ω)) (by simp)
      (by intro h; exact absurd h (by decide))
  have hUsm' : CMDiff[U] (2 : ℕ∞ω) u := by simpa using hUsm
  have hUmems : U ∈ 𝓝 x := hUopen.mem_nhds hxU
  -- within `U` the `mvfderivWithin` of a (scalar) function is its global `mvfderiv`
  have hw : ∀ (F : M → ℝ), mvfderivWithin I F U x = mvfderiv I F x :=
    fun F => by simp only [mvfderivWithin, mvfderiv, mfderivWithin_of_mem_nhds hUmems]
  have hconv : ∀ (B' : Π z : M, TangentSpace I z),
      mvfderivWithin I (fun z => mvfderivWithin I u U z (B' z)) U x
        = mvfderiv I (fun z => mvfderiv I u z (B' z)) x := by
    intro B'
    have hev : (fun z => mvfderiv I u z (B' z)) =ᶠ[𝓝[U] x]
        (fun z => mvfderivWithin I u U z (B' z)) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [mvfderivWithin, mvfderiv, mfderivWithin_of_isOpen hUopen hz]
    have hx' : (fun z => mvfderiv I u z (B' z)) x
        = (fun z => mvfderivWithin I u U z (B' z)) x := by
      simp only [mvfderivWithin, mvfderiv, mfderivWithin_of_isOpen hUopen hxU]
    have hcongr := Commons.Geometry.Manifold.VectorField.mvfderivWithin_congr_eventually
      (I := I) (s := U) (x := x) hev hx'
    rw [← hcongr, hw (fun z => mvfderiv I u z (B' z))]
  -- the commutation identity `X(Yu) − Y(Xu) = [X,Y]u` for two smooth fields, `u` only `C²` on `U`
  have key : ∀ (A B : Π y : M, TangentSpace I y), CMDiff ∞ (T% A) → CMDiff ∞ (T% B) →
      mvfderiv I (fun y => mvfderiv I u y (B y)) x (A x)
        = mvfderiv I (fun y => mvfderiv I u y (A y)) x (B x)
          + mvfderiv I u x (mlieBracket I A B x) := by
    intro A B hA hB
    have hAs : CMDiff[U] ∞ (T% A) := (contMDiffOn_univ.mpr hA).mono (subset_univ U)
    have hBs : CMDiff[U] ∞ (T% B) := (contMDiffOn_univ.mpr hB).mono (subset_univ U)
    have hxs' : x ∈ closure (interior U) := by
      rw [hUopen.interior_eq]; exact subset_closure hxU
    have hmain := Work.Diff.GE.mvfderivWithin_apply_mlieBracketWithin_two (s := U) (f := u) (X := A) (Y := B) (x := x)
      hUopen.uniqueMDiffOn hxU hxs' hUsm' hAs hBs
    have hbr : mvfderivWithin I u U x (mlieBracketWithin I A B U x)
        = mvfderiv I u x (mlieBracket I A B x) := by
      rw [hw u]
      congr 1
      rw [← mlieBracketWithin_univ, ← univ_inter U,
        mlieBracketWithin_inter (s := univ) (t := U) hUmems]
    rw [hconv B, hconv A, hbr] at hmain
    exact hmain
  -- the two fields whose values at `x` are compared
  have hW : CMDiff ∞ (T% (smoothExt x (Z x))) := smoothExt_cmdiff x (Z x)
  have hWx : smoothExt x (Z x) x = Z x := smoothExt_apply x (Z x)
  have hYm : MDiffAt (T% Y) x := hY.contMDiffAt.mdifferentiableAt (by simp)
  have hWm : MDiffAt (T% (smoothExt x (Z x))) x := hW.contMDiffAt.mdifferentiableAt (by simp)
  have hZm : MDiffAt (T% Z) x := hZ.contMDiffAt.mdifferentiableAt (by simp)
  have htors : ∀ {A B : Π y : M, TangentSpace I y},
      MDiffAt (T% A) x → MDiffAt (T% B) x →
      ((lcOf g) B x) (A x) - ((lcOf g) A x) (B x) = mlieBracket I A B x :=
    fun hA hB => (CovariantDerivative.torsion_eq_zero_iff (lcOf g)).1 (hLC g).2.1 hA hB
  have htor1 : mlieBracket I Y (smoothExt x (Z x)) x
      = ((lcOf g) (smoothExt x (Z x)) x) (Y x) - ((lcOf g) Y x) (smoothExt x (Z x) x) :=
    (htors hYm hWm).symm
  have htor2 : mlieBracket I Y Z x = ((lcOf g) Z x) (Y x) - ((lcOf g) Y x) (Z x) :=
    (htors hYm hZm).symm
  have hkey1 := key Y (smoothExt x (Z x)) hY hW
  have hkey2 := key Y Z hY hZ
  rw [hessAt, hkey1, hkey2, htor1, htor2, hWx, map_sub, map_sub]
  abel



/-! ## The tower at a point -/

/-- **The tower at a point.**  If `(t,y) ↦ u t y` is jointly smooth at `(t₀,x)` and `X` is a
`C^∞` field, then `(t,y) ↦ d_y (u t)(X y)` is jointly smooth at `(t₀,x)`.  Local form of
`Work.Diff.GE.tower_jointSmooth`, which is what is needed when `u` is known to be jointly smooth
only near `(t₀,x)`. -/
theorem cfq_tower_jointSmoothAt [T2Space M] [I.Boundaryless]
    {t₀ : ℝ} {x : M} {u : ℝ → M → ℝ}
    (hu : ContMDiffAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M ↦ u p.1 p.2) (t₀,x))
    {X : Π y : M, TangentSpace I y} (hX : CMDiff ∞ (T% X)) :
    ContMDiffAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun p : ℝ × M ↦ mvfderiv I (u p.1) p.2 (X p.2)) (t₀,x) := by
  have hVsm : CMDiff ∞ (T% (towerSection (I := I) X)) := contMDiff_towerSection (I := I) hX
  have hVat : CMDiffAt ∞ (T% (towerSection (I := I) X)) (t₀,x) := hVsm.contMDiffAt
  have hpt := Work.Diff.C.mvfderiv_contMDiffAt (I := 𝓘(ℝ,ℝ).prod I)
    (F := fun p : ℝ × M ↦ u p.1 p.2) (X := towerSection (I := I) X) hu hVat
  refine hpt.congr_of_eventuallyEq ?_
  filter_upwards [((contMDiffAt_iff_contMDiffAt_nhds (n := (2 : ℕ∞ω)) (by decide)).mp
      (hu.of_le (show (2 : ℕ∞ω) ≤ ∞ from by norm_num))).mono
      (fun p hp => hp.mdifferentiableAt (by norm_num))] with p hp
  rw [towerSection_eq_sndVec, ← mvfderiv_prod_snd (I := I) hp (X p.2)]

/-! ## The Hessian trace with the inverse Gram matrix (local form) -/

/-- **`Δu` is the contraction of the Hessian with the inverse Gram matrix**, local form: the
hypothesis on `u` is `ContMDiffAt I 𝓘(ℝ,ℝ) 2 u x` rather than global smoothness (which is what a
jointly smooth family of functions supplies at a point). -/
theorem cfq_laplAt_eq_sum_invGram [T2Space M] [I.Boundaryless]
    (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M) (u : M → ℝ) (x : M)
    (hu : ContMDiffAt I 𝓘(ℝ,ℝ) 2 u x)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (Γ : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (hΓ : ∀ i j, Γ i j = g.inner x (e i) (e j))
    (hb : Submodule.span ℝ (Set.range e) = ⊤) :
    Submission.Diff.laplAt g u x =
      ∑ i, ∑ j, (Γ⁻¹) i j * Submission.Diff.hessAt g u x (e i) (e j) := by
  classical
  letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨g.toRiemannianMetric⟩
  have hsym : ∀ v w : TangentSpace I x,
      Submission.Diff.hessAt g u x v w = Submission.Diff.hessAt g u x w v :=
    fun v w => Work.Diff.GE.hessAt_comm (I := I) (M := M) hLC g u x hu v w
  have hlap : Submission.Diff.laplAt g u x =
      ∑ i, Submission.Diff.hessAt g u x (Submission.Diff.onFrame g x i)
        (Submission.Diff.onFrame g x i) :=
    Work.Diff.GE.laplAt_eq_sum_hessAt (I := I) g u x (Submission.Diff.onFrame g x)
      (Work.Diff.GE.isONFrame_onFrame (I := I) g x) hsym
  rw [hlap]
  have hON : Orthonormal ℝ (Submission.Diff.onFrame g x) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [show Inner.inner ℝ (Submission.Diff.onFrame g x i) (Submission.Diff.onFrame g x j)
        = g.inner x (Submission.Diff.onFrame g x i) (Submission.Diff.onFrame g x j) from rfl]
    exact Work.Diff.GE.isONFrame_onFrame (I := I) g x i j
  have hadd : ∀ v₁ v₂ w : TangentSpace I x,
      Submission.Diff.hessAt g u x (v₁ + v₂) w
        = Submission.Diff.hessAt g u x v₁ w + Submission.Diff.hessAt g u x v₂ w := by
    intro v₁ v₂ w
    simp only [Submission.Diff.hessAt, map_add]
    ring
  have hsmul : ∀ (a : ℝ) (v w : TangentSpace I x),
      Submission.Diff.hessAt g u x (a • v) w = a * Submission.Diff.hessAt g u x v w := by
    intro a v w
    simp only [Submission.Diff.hessAt, map_smul, smul_eq_mul]
    ring
  have hΓeq : Γ = Matrix.gram ℝ e := by
    ext i j
    rw [hΓ i j, Matrix.gram_apply]
    rfl
  rw [hΓeq]
  exact (Work.Diff.GE.sum_invGram_mul_eq_sum_orthonormal (V := TangentSpace I x)
    (fun v w => Submission.Diff.hessAt g u x v w) hadd hsmul hsym e (Submission.Diff.onFrame g x)
    hb hON (Matrix.gram ℝ e) (fun i j => rfl)).symm

/-! ## The Christoffel symbols in the coordinate frame -/

/-- In the chart at `x`, the covariant derivative of the coordinate frame is the frame vector
whose coordinates are the chart Christoffel symbol. -/
theorem cfq_lcOf_chartFrame [T2Space M] [I.Boundaryless]
    (g : Submission.Diff.SMet I M) (x : M) {y : M} (hy : y ∈ (chartAt H x).source)
    (a b : Fin (Module.finrank ℝ E)) :
    Submission.Diff.lcOf g (cFrame (I := I) x a) y (cFrame (I := I) x b y)
      = Submission.Geodesic.frameVector (I := I) x y
          (Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x y
            (cBasis (E := E) a) (cBasis (E := E) b)) := by
  letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun z : M ↦ TangentSpace I z) := inferInstance
  have h := Submission.Geodesic.cov_frameSection_eq (I := I) (Submission.Diff.lcOf g) x y
    (cBasis (E := E) a) (cFrame (I := I) x b y) hy
  exact h

/-- Expansion of a frame vector in the coordinate frame. -/
theorem cfq_frameVector_eq_sum_frame [T2Space M] (x : M) (c : E) :
    Submission.Geodesic.frameVector (I := I) x x c
      = ∑ k : Fin (Module.finrank ℝ E),
          ((cBasis (E := E)).coord k) c • cFrame (I := I) x k x := by
  have hrepr : ∑ k : Fin (Module.finrank ℝ E),
      ((cBasis (E := E)).coord k) c • cBasis (E := E) k = c :=
    (Finset.sum_congr rfl (fun k _ => by rw [Module.Basis.coord_apply])).trans
      (Module.Basis.sum_repr (cBasis (E := E)) c)
  rw [show Submission.Geodesic.frameVector (I := I) x x c
      = (trivializationAt E (TangentSpace I) x).symmL ℝ x c from rfl]
  conv_lhs => rw [← hrepr]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul]
  rfl

/-! ## Continuity of `Δ(|Rm|²)` along a jointly smooth family -/

/-- **Continuity of `t ↦ Δ_{G t}(u t)(x)`.**  If the metric family is jointly smooth on the open
time set `J ∋ t₀` and `(t,y) ↦ u t y` is jointly smooth at `(t₀,x)`, then the Laplacian of the
slice at `x` is continuous in `t` at `t₀`. -/
theorem cfq_laplAt_continuousAt [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : Submission.Diff.JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M)
    {u : ℝ → M → ℝ}
    (hu : Work.Diff.EXT.JointSmoothAt I M (fun p : ℝ × M ↦ u p.1 p.2) t₀ x) :
    ContinuousAt (fun s : ℝ ↦ Submission.Diff.laplAt (G s) (u s) x) t₀ := by
  classical
  letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨(G t₀).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun z : M ↦ TangentSpace I z) := inferInstance
  -- globally smooth representatives of the coordinate frame fields
  have hex : ∀ k : Fin (Module.finrank ℝ E), ∃ S : Π y : M, TangentSpace I y,
      CMDiff ∞ (T% S) ∧ S =ᶠ[𝓝 x] cFrame (I := I) x k := by
    intro k
    obtain ⟨Y, hY, hYeq⟩ :=
      Submission.ChartConnection.exists_contMDiff_section_eventuallyEq_frameSection
        (I := I) (M := M) x (cBasis (E := E) k) (mem_chart_source H x)
    exact ⟨Y, hY, by simpa only [cFrame] using hYeq⟩
  let S : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y) :=
    fun k ↦ Classical.choose (hex k)
  have hSsm : ∀ k : Fin (Module.finrank ℝ E), CMDiff ∞ (T% (S k)) :=
    fun k ↦ (Classical.choose_spec (hex k)).1
  have hSeq : ∀ k : Fin (Module.finrank ℝ E), S k =ᶠ[𝓝 x] cFrame (I := I) x k :=
    fun k ↦ (Classical.choose_spec (hex k)).2
  have hSx : ∀ k : Fin (Module.finrank ℝ E), S k x = cFrame (I := I) x k x :=
    fun k ↦ (hSeq k).eq_of_nhds
  -- the slices are `C²` at `x`
  have hslice : ∀ᶠ t in 𝓝 t₀, ContMDiffAt I 𝓘(ℝ,ℝ) 2 (u t) x := by
    have h2 := (contMDiffAt_iff_contMDiffAt_nhds (n := (2 : ℕ∞ω)) (by decide)).mp
      (hu.of_le (show (2 : ℕ∞ω) ≤ ∞ from by norm_num))
    filter_upwards [(continuousAt_id.prodMk continuousAt_const).eventually h2] with t ht
    exact ht.comp x ((contMDiffAt_const (c := t)).prodMk contMDiffAt_id)
  -- the eventual identity: `laplAt` as a contraction of the field form of the Hessian
  have hslap : (fun t : ℝ ↦ Submission.Diff.laplAt (G t) (u t) x) =ᶠ[𝓝 t₀]
      (fun t : ℝ ↦ ∑ i, ∑ j, (Work.Diff.GE.GramM (I := I) G x t x)⁻¹ i j *
          (mvfderiv I (fun y : M ↦ mvfderiv I (u t) y (S j y)) x (S i x)
            - mvfderiv I (u t) x (Submission.Diff.lcOf (G t) (S j) x (S i x)))) := by
    filter_upwards [hslice] with t ht
    rw [Work.Diff.GE.cfq_laplAt_eq_sum_invGram (I := I) (M := M) hLC (G t) (u t) x ht
      (fun i ↦ cFrame (I := I) x i x) (Work.Diff.GE.GramM (I := I) G x t x) (fun i j ↦ rfl)
      (Work.Diff.GE.cfq_cFrame_span (I := I) x (mem_chart_source H x))]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← hSx i, ← hSx j,
      Work.Diff.GE.cfq_hessAt_field (I := I) (M := M) hLC (G t) x ht (S i) (S j) (hSsm i) (hSsm j)]
  -- the Gram matrix
  have hGram : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousAt (fun t : ℝ ↦ (Work.Diff.GE.GramM (I := I) G x t x)⁻¹ i j) t₀ :=
    fun i j ↦ Work.Diff.GE.cfq_continuousAt_of_jointSmoothAt (I := I) (M := M)
      (Work.Diff.GE.gramInv_jointSmooth (I := I) (M := M) hJ hG ht₀ x i j)
  -- the first term of the Hessian
  have hL1 : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousAt (fun t : ℝ ↦ mvfderiv I (fun y : M ↦ mvfderiv I (u t) y (S j y)) x (S i x))
        t₀ :=
    fun i j ↦ Work.Diff.EXT.continuousAt_mvfderiv_family (I := I) (M := M)
      (Work.Diff.GE.cfq_tower_jointSmoothAt (I := I) (M := M) hu (hSsm j)) (S i x)
  -- the second term of the Hessian: expand the Christoffel vector in the coordinate frame
  have hL2 : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousAt (fun t : ℝ ↦ mvfderiv I (u t) x (Submission.Diff.lcOf (G t) (S j) x (S i x)))
        t₀ := by
    intro i j
    have hchr : ContinuousAt (fun t : ℝ ↦ Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t))
        x x (cBasis (E := E) j) (cBasis (E := E) i)) t₀ :=
      Work.Diff.GE.cfq_continuousAt_of_jointSmoothAt (I := I) (M := M)
        (Work.Diff.GE.chrB_const_jointSmooth (I := I) (M := M) hJ hG ht₀ x j i)
    have hcoef : ∀ k : Fin (Module.finrank ℝ E),
        ContinuousAt (fun t : ℝ ↦ ((cBasis (E := E)).coord k)
          (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x x
            (cBasis (E := E) j) (cBasis (E := E) i))) t₀ :=
      fun k ↦ (LinearMap.toContinuousLinearMap ((cBasis (E := E)).coord k)).continuous.continuousAt.comp
        hchr
    have hdir : ∀ k : Fin (Module.finrank ℝ E),
        ContinuousAt (fun t : ℝ ↦ mvfderiv I (u t) x (cFrame (I := I) x k x)) t₀ :=
      fun k ↦ Work.Diff.EXT.continuousAt_mvfderiv_family (I := I) (M := M) hu
        (cFrame (I := I) x k x)
    have hVt : ∀ t : ℝ, Submission.Diff.lcOf (G t) (S j) x (S i x)
        = ∑ k, ((cBasis (E := E)).coord k)
            (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x x
              (cBasis (E := E) j) (cBasis (E := E) i)) • cFrame (I := I) x k x := by
      intro t
      have hCLM : Submission.Diff.lcOf (G t) (S j) x
          = Submission.Diff.lcOf (G t) (cFrame (I := I) x j) x :=
        Work.Diff.GE.Kato3.lcOf_congr_eventuallyEq (I := I) (M := M) (G t)
          ((hSsm j).contMDiffAt.mdifferentiableAt (by simp))
          (Submission.Geodesic.mdiffAt_frameSection (I := I) x (cBasis (E := E) j)
            (mem_chart_source H x)) (hSeq j)
      have h1 : Submission.Diff.lcOf (G t) (S j) x (S i x)
          = Submission.Diff.lcOf (G t) (cFrame (I := I) x j) x (cFrame (I := I) x i x) := by
        rw [hCLM, hSx i]
      rw [h1, Work.Diff.GE.cfq_lcOf_chartFrame (I := I) (M := M) (G t) x
        (mem_chart_source H x) j i]
      exact Work.Diff.GE.cfq_frameVector_eq_sum_frame (I := I) (M := M) x _
    have hsum : ContinuousAt (fun t : ℝ ↦ ∑ k, ((cBasis (E := E)).coord k)
          (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x x
            (cBasis (E := E) j) (cBasis (E := E) i))
          * mvfderiv I (u t) x (cFrame (I := I) x k x)) t₀ :=
      Work.Diff.GE.cfq_continuousAt_finsetSum Finset.univ (fun k _ ↦ (hcoef k).mul (hdir k))
    refine hsum.congr_of_eventuallyEq ?_
    filter_upwards with t
    rw [hVt t, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_smul, smul_eq_mul]
  -- assemble
  have hsum : ContinuousAt (fun t : ℝ ↦ ∑ i, ∑ j,
      (Work.Diff.GE.GramM (I := I) G x t x)⁻¹ i j *
        (mvfderiv I (fun y : M ↦ mvfderiv I (u t) y (S j y)) x (S i x)
          - mvfderiv I (u t) x (Submission.Diff.lcOf (G t) (S j) x (S i x)))) t₀ := by
    refine Work.Diff.GE.cfq_continuousAt_finsetSum Finset.univ (fun i _ ↦ ?_)
    refine Work.Diff.GE.cfq_continuousAt_finsetSum Finset.univ (fun j _ ↦ ?_)
    exact (hGram i j).mul ((hL1 i j).sub (hL2 i j))
  exact hsum.congr_of_eventuallyEq hslap

/-! ## Continuity in the time variable of `|∇Rm|²` -/

/-- `rmP` is linear in its first argument, in sum form. -/
theorem cfq_rmP_sum_fst [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (u : ι → TangentSpace I x)
    (b c' d : TangentSpace I x) :
    Submission.Diff.rmP g x (∑ i ∈ s, c i • u i) b c' d
      = ∑ i ∈ s, c i * Submission.Diff.rmP g x (u i) b c' d := by
  classical
  have hzero : Submission.Diff.rmP g x (0 : TangentSpace I x) b c' d = 0 := by
    simpa using Work.Diff.GE.rmP_smul_fst g hLC x (0 : ℝ) (0 : TangentSpace I x) b c' d
  induction s using Finset.induction_on with
  | empty => simp [hzero]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Work.Diff.GE.rmP_add_fst g hLC x (c i • u i) _ b c' d, ih,
        Work.Diff.GE.rmP_smul_fst g hLC x (c i) (u i) b c' d, Finset.sum_insert hi]

/-- `rmP` is linear in its second argument, in sum form. -/
theorem cfq_rmP_sum_snd [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (u : ι → TangentSpace I x)
    (a c' d : TangentSpace I x) :
    Submission.Diff.rmP g x a (∑ i ∈ s, c i • u i) c' d
      = ∑ i ∈ s, c i * Submission.Diff.rmP g x a (u i) c' d := by
  classical
  have hzero : Submission.Diff.rmP g x a (0 : TangentSpace I x) c' d = 0 := by
    simpa using Work.Diff.GE.rmP_smul_snd g hLC x (0 : ℝ) a (0 : TangentSpace I x) c' d
  induction s using Finset.induction_on with
  | empty => simp [hzero]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi,
        Work.Diff.GE.rmP_add_snd g hLC x a (c i • u i) (∑ j ∈ s, c j • u j) c' d, ih,
        Work.Diff.GE.rmP_smul_snd g hLC x (c i) a (u i) c' d, Finset.sum_insert hi]

/-- `rmP` is linear in its third argument, in sum form. -/
theorem cfq_rmP_sum_thd [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (u : ι → TangentSpace I x)
    (a b d : TangentSpace I x) :
    Submission.Diff.rmP g x a b (∑ i ∈ s, c i • u i) d
      = ∑ i ∈ s, c i * Submission.Diff.rmP g x a b (u i) d := by
  classical
  have hzero : Submission.Diff.rmP g x a b (0 : TangentSpace I x) d = 0 := by
    simpa using Work.Diff.GE.rmP_smul_thd g hLC x (0 : ℝ) a b (0 : TangentSpace I x) d
  induction s using Finset.induction_on with
  | empty => simp [hzero]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi,
        Work.Diff.GE.rmP_add_thd g hLC x a b (c i • u i) (∑ j ∈ s, c j • u j) d, ih,
        Work.Diff.GE.rmP_smul_thd g hLC x (c i) a b (u i) d, Finset.sum_insert hi]

/-- `rmP` is linear in its fourth argument, in sum form. -/
theorem cfq_rmP_sum_fth [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (u : ι → TangentSpace I x)
    (a b c' : TangentSpace I x) :
    Submission.Diff.rmP g x a b c' (∑ i ∈ s, c i • u i)
      = ∑ i ∈ s, c i * Submission.Diff.rmP g x a b c' (u i) := by
  classical
  have hzero : Submission.Diff.rmP g x a b c' (0 : TangentSpace I x) = 0 := by
    simpa using Work.Diff.GE.rmP_smul_fth g hLC x (0 : ℝ) a b c' (0 : TangentSpace I x)
  induction s using Finset.induction_on with
  | empty => simp [hzero]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi,
        Work.Diff.GE.rmP_add_fth g hLC x a b c' (c i • u i) (∑ j ∈ s, c j • u j), ih,
        Work.Diff.GE.rmP_smul_fth g hLC x (c i) a b c' (u i), Finset.sum_insert hi]

/-- The Christoffel vector `∇_{σ_m} σ_a` in the coordinate frame. -/
theorem cfq_lcOf_recon [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (x : M) (a m : Fin (Module.finrank ℝ E)) :
    (fun t : ℝ ↦ Submission.Diff.lcOf (G t) (smoothExt x (cFrame (I := I) x a x)) x
        (cFrame (I := I) x m x))
      = fun t : ℝ ↦ ∑ n, Work.Diff.EXT.reconCoef (I := I) G x
          (smoothExt x (cFrame (I := I) x m x))
          (smoothExt x (cFrame (I := I) x a x)) n t x • cFrame (I := I) x n x := by
  funext t
  have h := Work.Diff.EXT.lcOf_eq_sum_reconCoef (I := I) (M := M) G x
    (smoothExt x (cFrame (I := I) x m x))
    (smoothExt x (cFrame (I := I) x a x)) t (mem_chart_source H x)
    ((Work.Diff.GE.Gest.smoothExt_contMDiff x _).contMDiffAt)
    ((Work.Diff.GE.Gest.smoothExt_contMDiff x _).contMDiffAt)
  simpa only [smoothExt_apply, Work.Diff.EXT.fr, cFrame, Submission.Geodesic.frameSection,
    Submission.Geodesic.frameVector] using h

/-- The Christoffel vector `∇_{σ_m} σ_a` in the coordinate frame, pointwise. -/
theorem cfq_lcOf_recon_apply [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (x : M) (a m : Fin (Module.finrank ℝ E)) (t : ℝ) :
    Submission.Diff.lcOf (G t) (smoothExt x (cFrame (I := I) x a x)) x
        (cFrame (I := I) x m x)
      = ∑ n, Work.Diff.EXT.reconCoef (I := I) G x
          (smoothExt x (cFrame (I := I) x m x))
          (smoothExt x (cFrame (I := I) x a x)) n t x • cFrame (I := I) x n x := by
  have h := Work.Diff.EXT.lcOf_eq_sum_reconCoef (I := I) (M := M) G x
    (smoothExt x (cFrame (I := I) x m x))
    (smoothExt x (cFrame (I := I) x a x)) t (mem_chart_source H x)
    ((Work.Diff.GE.Gest.smoothExt_contMDiff x _).contMDiffAt)
    ((Work.Diff.GE.Gest.smoothExt_contMDiff x _).contMDiffAt)
  simpa only [smoothExt_apply, Work.Diff.EXT.fr, cFrame, Submission.Geodesic.frameSection,
    Submission.Geodesic.frameVector] using h

/-- Continuity of the connection correction term in the first slot of `rmP`. -/
theorem cfq_rmP_corr1 [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : Submission.Diff.JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M)
    (m i j k l : Fin (Module.finrank ℝ E)) :
    ContinuousAt (fun t : ℝ ↦ Submission.Diff.rmP (G t) x
      (Submission.Diff.lcOf (G t) (smoothExt x (cFrame (I := I) x i x)) x
        (cFrame (I := I) x m x))
      (cFrame (I := I) x j x) (cFrame (I := I) x k x) (cFrame (I := I) x l x)) t₀ := by
  classical
  letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨(G t₀).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun z : M ↦ TangentSpace I z) := inferInstance
  have hsum : ContinuousAt (fun t : ℝ ↦ ∑ n, Work.Diff.EXT.reconCoef (I := I) G x
      (smoothExt x (cFrame (I := I) x m x)) (smoothExt x (cFrame (I := I) x i x)) n t x
      * (Work.Diff.GE.rmC4 G x t x) n j k l) t₀ := by
    refine Work.Diff.GE.cfq_continuousAt_finsetSum Finset.univ (fun n _ ↦ ?_)
    refine (Work.Diff.GE.reconCoef_continuousAt (I := I) (M := M) hJ hG ht₀ x
      ((Work.Diff.GE.Gest.smoothExt_contMDiff x _).contMDiffAt)
      ((Work.Diff.GE.Gest.smoothExt_contMDiff x _).contMDiffAt) n).mul ?_
    exact Work.Diff.GE.cfq_continuousAt_of_jointSmoothAt (I := I) (M := M)
      (Work.Diff.GE.rmC4_jointSmooth (I := I) (M := M) hLC hJ hG ht₀ x n j k l)
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards with t
  rw [cfq_lcOf_recon_apply (I := I) (M := M) G x i m t,
    Work.Diff.GE.cfq_rmP_sum_fst (I := I) (M := M) hLC (G t) x Finset.univ
      (fun n ↦ Work.Diff.EXT.reconCoef (I := I) G x
        (smoothExt x (cFrame (I := I) x m x))
        (smoothExt x (cFrame (I := I) x i x)) n t x)
      (fun n ↦ cFrame (I := I) x n x) (cFrame (I := I) x j x) (cFrame (I := I) x k x)
      (cFrame (I := I) x l x)]
  rfl

/-- Continuity of the connection correction term in the second slot of `rmP`. -/
theorem cfq_rmP_corr2 [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : Submission.Diff.JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M)
    (m i j k l : Fin (Module.finrank ℝ E)) :
    ContinuousAt (fun t : ℝ ↦ Submission.Diff.rmP (G t) x (cFrame (I := I) x i x)
      (Submission.Diff.lcOf (G t) (smoothExt x (cFrame (I := I) x j x)) x
        (cFrame (I := I) x m x))
      (cFrame (I := I) x k x) (cFrame (I := I) x l x)) t₀ := by
  classical
  letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨(G t₀).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun z : M ↦ TangentSpace I z) := inferInstance
  have hsum : ContinuousAt (fun t : ℝ ↦ ∑ n, Work.Diff.EXT.reconCoef (I := I) G x
      (smoothExt x (cFrame (I := I) x m x)) (smoothExt x (cFrame (I := I) x j x)) n t x
      * (Work.Diff.GE.rmC4 G x t x) i n k l) t₀ := by
    refine Work.Diff.GE.cfq_continuousAt_finsetSum Finset.univ (fun n _ ↦ ?_)
    refine (Work.Diff.GE.reconCoef_continuousAt (I := I) (M := M) hJ hG ht₀ x
      ((Work.Diff.GE.Gest.smoothExt_contMDiff x _).contMDiffAt)
      ((Work.Diff.GE.Gest.smoothExt_contMDiff x _).contMDiffAt) n).mul ?_
    exact Work.Diff.GE.cfq_continuousAt_of_jointSmoothAt (I := I) (M := M)
      (Work.Diff.GE.rmC4_jointSmooth (I := I) (M := M) hLC hJ hG ht₀ x i n k l)
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards with t
  rw [cfq_lcOf_recon_apply (I := I) (M := M) G x j m t,
    Work.Diff.GE.cfq_rmP_sum_snd (I := I) (M := M) hLC (G t) x Finset.univ
      (fun n ↦ Work.Diff.EXT.reconCoef (I := I) G x
        (smoothExt x (cFrame (I := I) x m x))
        (smoothExt x (cFrame (I := I) x j x)) n t x)
      (fun n ↦ cFrame (I := I) x n x) (cFrame (I := I) x i x) (cFrame (I := I) x k x)
      (cFrame (I := I) x l x)]
  rfl

/-- Continuity of the connection correction term in the third slot of `rmP`. -/
theorem cfq_rmP_corr3 [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : Submission.Diff.JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M)
    (m i j k l : Fin (Module.finrank ℝ E)) :
    ContinuousAt (fun t : ℝ ↦ Submission.Diff.rmP (G t) x (cFrame (I := I) x i x)
      (cFrame (I := I) x j x)
      (Submission.Diff.lcOf (G t) (smoothExt x (cFrame (I := I) x k x)) x
        (cFrame (I := I) x m x))
      (cFrame (I := I) x l x)) t₀ := by
  classical
  letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨(G t₀).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun z : M ↦ TangentSpace I z) := inferInstance
  have hsum : ContinuousAt (fun t : ℝ ↦ ∑ n, Work.Diff.EXT.reconCoef (I := I) G x
      (smoothExt x (cFrame (I := I) x m x)) (smoothExt x (cFrame (I := I) x k x)) n t x
      * (Work.Diff.GE.rmC4 G x t x) i j n l) t₀ := by
    refine Work.Diff.GE.cfq_continuousAt_finsetSum Finset.univ (fun n _ ↦ ?_)
    refine (Work.Diff.GE.reconCoef_continuousAt (I := I) (M := M) hJ hG ht₀ x
      ((Work.Diff.GE.Gest.smoothExt_contMDiff x _).contMDiffAt)
      ((Work.Diff.GE.Gest.smoothExt_contMDiff x _).contMDiffAt) n).mul ?_
    exact Work.Diff.GE.cfq_continuousAt_of_jointSmoothAt (I := I) (M := M)
      (Work.Diff.GE.rmC4_jointSmooth (I := I) (M := M) hLC hJ hG ht₀ x i j n l)
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards with t
  rw [cfq_lcOf_recon_apply (I := I) (M := M) G x k m t,
    Work.Diff.GE.cfq_rmP_sum_thd (I := I) (M := M) hLC (G t) x Finset.univ
      (fun n ↦ Work.Diff.EXT.reconCoef (I := I) G x
        (smoothExt x (cFrame (I := I) x m x))
        (smoothExt x (cFrame (I := I) x k x)) n t x)
      (fun n ↦ cFrame (I := I) x n x) (cFrame (I := I) x i x) (cFrame (I := I) x j x)
      (cFrame (I := I) x l x)]
  rfl

/-- Continuity of the connection correction term in the fourth slot of `rmP`. -/
theorem cfq_rmP_corr4 [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : Submission.Diff.JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M)
    (m i j k l : Fin (Module.finrank ℝ E)) :
    ContinuousAt (fun t : ℝ ↦ Submission.Diff.rmP (G t) x (cFrame (I := I) x i x)
      (cFrame (I := I) x j x) (cFrame (I := I) x k x)
      (Submission.Diff.lcOf (G t) (smoothExt x (cFrame (I := I) x l x)) x
        (cFrame (I := I) x m x))) t₀ := by
  classical
  letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨(G t₀).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun z : M ↦ TangentSpace I z) := inferInstance
  have hsum : ContinuousAt (fun t : ℝ ↦ ∑ n, Work.Diff.EXT.reconCoef (I := I) G x
      (smoothExt x (cFrame (I := I) x m x)) (smoothExt x (cFrame (I := I) x l x)) n t x
      * (Work.Diff.GE.rmC4 G x t x) i j k n) t₀ := by
    refine Work.Diff.GE.cfq_continuousAt_finsetSum Finset.univ (fun n _ ↦ ?_)
    refine (Work.Diff.GE.reconCoef_continuousAt (I := I) (M := M) hJ hG ht₀ x
      ((Work.Diff.GE.Gest.smoothExt_contMDiff x _).contMDiffAt)
      ((Work.Diff.GE.Gest.smoothExt_contMDiff x _).contMDiffAt) n).mul ?_
    exact Work.Diff.GE.cfq_continuousAt_of_jointSmoothAt (I := I) (M := M)
      (Work.Diff.GE.rmC4_jointSmooth (I := I) (M := M) hLC hJ hG ht₀ x i j k n)
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards with t
  rw [cfq_lcOf_recon_apply (I := I) (M := M) G x l m t,
    Work.Diff.GE.cfq_rmP_sum_fth (I := I) (M := M) hLC (G t) x Finset.univ
      (fun n ↦ Work.Diff.EXT.reconCoef (I := I) G x
        (smoothExt x (cFrame (I := I) x m x))
        (smoothExt x (cFrame (I := I) x l x)) n t x)
      (fun n ↦ cFrame (I := I) x n x) (cFrame (I := I) x i x) (cFrame (I := I) x j x)
      (cFrame (I := I) x k x)]
  rfl

/-- **Continuity in `t` of `|∇Rm|²(G t)(x)`.** -/
theorem cfq_dRmNormSq_continuousAt [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : Submission.Diff.JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M) :
    ContinuousAt (fun t : ℝ ↦ Submission.Diff.dRmNormSq (G t) x) t₀ := by
  classical
  letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨(G t₀).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun z : M ↦ TangentSpace I z) := inferInstance
  have hcomp : ∀ m i j k l : Fin (Module.finrank ℝ E),
      ContinuousAt (fun t : ℝ ↦ dRmPhi (G t) x (cFrame (I := I) x m x)
        (smoothExt x (cFrame (I := I) x i x)) (smoothExt x (cFrame (I := I) x j x))
        (smoothExt x (cFrame (I := I) x k x)) (smoothExt x (cFrame (I := I) x l x))) t₀ := by
    intro m i j k l
    simp only [Work.Diff.GE.dRmPhi]
    have h1 : ContinuousAt (fun t : ℝ ↦ mvfderiv I (fun y : M ↦ Submission.Diff.rmP (G t) y
        (smoothExt x (cFrame (I := I) x i x) y) (smoothExt x (cFrame (I := I) x j x) y)
        (smoothExt x (cFrame (I := I) x k x) y) (smoothExt x (cFrame (I := I) x l x) y)) x
        (cFrame (I := I) x m x)) t₀ :=
      Work.Diff.EXT.continuousAt_mvfderiv_family (I := I) (M := M)
        (Work.Diff.GE.rmP_jointSmoothNoCompact (I := I) (M := M) hLC hJ hG ht₀ x
          (Work.Diff.GE.Gest.smoothExt_contMDiff x _) (Work.Diff.GE.Gest.smoothExt_contMDiff x _)
          (Work.Diff.GE.Gest.smoothExt_contMDiff x _) (Work.Diff.GE.Gest.smoothExt_contMDiff x _))
        (cFrame (I := I) x m x)
    have h2 : ContinuousAt (fun t : ℝ ↦ Submission.Diff.rmP (G t) x
        ((Submission.Diff.lcOf (G t) (smoothExt x (cFrame (I := I) x i x)) x)
          (cFrame (I := I) x m x))
        (smoothExt x (cFrame (I := I) x j x) x) (smoothExt x (cFrame (I := I) x k x) x)
        (smoothExt x (cFrame (I := I) x l x) x)) t₀ := by
      simpa only [smoothExt_apply] using
        cfq_rmP_corr1 (I := I) (M := M) hLC hJ hG ht₀ x m i j k l
    have h3 : ContinuousAt (fun t : ℝ ↦ Submission.Diff.rmP (G t) x
        (smoothExt x (cFrame (I := I) x i x) x)
        ((Submission.Diff.lcOf (G t) (smoothExt x (cFrame (I := I) x j x)) x)
          (cFrame (I := I) x m x))
        (smoothExt x (cFrame (I := I) x k x) x)
        (smoothExt x (cFrame (I := I) x l x) x)) t₀ := by
      simpa only [smoothExt_apply] using
        cfq_rmP_corr2 (I := I) (M := M) hLC hJ hG ht₀ x m i j k l
    have h4 : ContinuousAt (fun t : ℝ ↦ Submission.Diff.rmP (G t) x
        (smoothExt x (cFrame (I := I) x i x) x) (smoothExt x (cFrame (I := I) x j x) x)
        ((Submission.Diff.lcOf (G t) (smoothExt x (cFrame (I := I) x k x)) x)
          (cFrame (I := I) x m x))
        (smoothExt x (cFrame (I := I) x l x) x)) t₀ := by
      simpa only [smoothExt_apply] using
        cfq_rmP_corr3 (I := I) (M := M) hLC hJ hG ht₀ x m i j k l
    have h5 : ContinuousAt (fun t : ℝ ↦ Submission.Diff.rmP (G t) x
        (smoothExt x (cFrame (I := I) x i x) x) (smoothExt x (cFrame (I := I) x j x) x)
        (smoothExt x (cFrame (I := I) x k x) x)
        ((Submission.Diff.lcOf (G t) (smoothExt x (cFrame (I := I) x l x)) x)
          (cFrame (I := I) x m x))) t₀ := by
      simpa only [smoothExt_apply] using
        cfq_rmP_corr4 (I := I) (M := M) hLC hJ hG ht₀ x m i j k l
    exact (((h1.sub h2).sub h3).sub h4).sub h5
  have hev : (fun t : ℝ ↦ Submission.Diff.dRmNormSq (G t) x) =ᶠ[𝓝 t₀]
      (fun t : ℝ ↦ Work.Diff.GE.N5 (Work.Diff.GE.GramM (I := I) G x t x)
        (fun m i j k l ↦ dRmPhi (G t) x (cFrame (I := I) x m x)
          (smoothExt x (cFrame (I := I) x i x)) (smoothExt x (cFrame (I := I) x j x))
          (smoothExt x (cFrame (I := I) x k x)) (smoothExt x (cFrame (I := I) x l x)))) := by
    filter_upwards with t
    have hC : (fun m i j k l : Fin (Module.finrank ℝ E) ↦ Submission.Diff.covRm (G t) x
          (cFrame (I := I) x m x) (cFrame (I := I) x i x) (cFrame (I := I) x j x)
          (cFrame (I := I) x k x) (cFrame (I := I) x l x))
        = fun m i j k l ↦ dRmPhi (G t) x (cFrame (I := I) x m x)
            (smoothExt x (cFrame (I := I) x i x)) (smoothExt x (cFrame (I := I) x j x))
            (smoothExt x (cFrame (I := I) x k x)) (smoothExt x (cFrame (I := I) x l x)) := by
      funext m i j k l
      have h := Work.Diff.GE.Kato3.covRm_field_form (I := I) (M := M) hLC (G t) x
        (cFrame (I := I) x m x)
        (Work.Diff.GE.Gest.smoothExt_contMDiff x (cFrame (I := I) x i x))
        (Work.Diff.GE.Gest.smoothExt_contMDiff x (cFrame (I := I) x j x))
        (Work.Diff.GE.Gest.smoothExt_contMDiff x (cFrame (I := I) x k x))
        (Work.Diff.GE.Gest.smoothExt_contMDiff x (cFrame (I := I) x l x))
      simpa only [Work.Diff.GE.covRmC5, smoothExt_apply] using h
    rw [Work.Diff.GE.dRmNormSq_eq_N5_of_basis (I := I) (M := M) hLC x
      (fun i ↦ cFrame (I := I) x i x) (Work.Diff.GE.GramM (I := I) G x t x) (fun i j ↦ rfl)
      (Work.Diff.GE.cfq_cFrame_span (I := I) x (mem_chart_source H x)), hC]
  have hN5 : ContinuousAt (fun t : ℝ ↦ Work.Diff.GE.N5 (Work.Diff.GE.GramM (I := I) G x t x)
      (fun m i j k l ↦ dRmPhi (G t) x (cFrame (I := I) x m x)
        (smoothExt x (cFrame (I := I) x i x)) (smoothExt x (cFrame (I := I) x j x))
        (smoothExt x (cFrame (I := I) x k x)) (smoothExt x (cFrame (I := I) x l x)))) t₀ := by
    refine Work.Diff.GE.cfq_N5_continuousAt (n := Module.finrank ℝ E)
      (Γ := fun t : ℝ ↦ Work.Diff.GE.GramM (I := I) G x t x)
      (R := fun t : ℝ ↦ fun m i j k l ↦ dRmPhi (G t) x (cFrame (I := I) x m x)
        (smoothExt x (cFrame (I := I) x i x)) (smoothExt x (cFrame (I := I) x j x))
        (smoothExt x (cFrame (I := I) x k x)) (smoothExt x (cFrame (I := I) x l x)))
      (fun i j ↦ ?_) (fun m i j k l ↦ ?_)
    · exact Work.Diff.GE.cfq_continuousAt_of_jointSmoothAt (I := I) (M := M)
        (by simpa only [Work.Diff.GE.GramM, Work.Diff.GE.GramInv] using
          Work.Diff.GE.gramInv_jointSmooth (I := I) (M := M) hJ hG ht₀ x i j)
    · exact hcomp m i j k l
  exact hN5.congr_of_eventuallyEq hev

/-- Joint smoothness of the polynomial contraction `qPairGen` of the Gram matrix and the curvature
components in the coordinate frame. -/
theorem cfq_qPairGen_jointSmoothAt [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : Submission.Diff.JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M) :
    Work.Diff.EXT.JointSmoothAt I M (fun p : ℝ × M ↦ Work.Diff.GE.qPairGen
      (Work.Diff.GE.GramM (I := I) G x p.1 p.2) (Work.Diff.GE.rmC4 (I := I) G x p.1 p.2)) t₀ x := by
  classical
  letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨(G t₀).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun z : M ↦ TangentSpace I z) := inferInstance
  refine Work.Diff.GE.qPairGen_jointSmooth (I := I) (M := M) (n := Module.finrank ℝ E)
    (Γ := fun p : ℝ × M ↦ Work.Diff.GE.GramM (I := I) G x p.1 p.2)
    (C := fun p : ℝ × M ↦ Work.Diff.GE.rmC4 (I := I) G x p.1 p.2)
    (fun i j ↦ ?_) (fun i j k l ↦ ?_)
  · have h := Work.Diff.GE.gramInv_jointSmooth (I := I) (M := M) hJ hG ht₀ x i j
    rw [show (fun p : ℝ × M ↦ (Work.Diff.GE.GramM (I := I) G x p.1 p.2)⁻¹ i j)
        = (fun p : ℝ × M ↦ Work.Diff.GE.GramInv (I := I) G x p.1 p.2 i j) from rfl]
    exact h
  · exact Work.Diff.GE.rmC4_jointSmooth (I := I) (M := M) hLC hJ hG ht₀ x i j k l

/-- **Continuity in `t` of `⟪Rm, Q(Rm)⟫(G t)(x)`.** -/
theorem cfq_qPairAt_continuousAt [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : Submission.Diff.JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M) :
    ContinuousAt (fun t : ℝ ↦ Submission.Diff.qPairAt (G t) x) t₀ := by
  have hev : (fun t : ℝ ↦ Submission.Diff.qPairAt (G t) x) =ᶠ[𝓝 t₀]
      (fun t : ℝ ↦ Work.Diff.GE.qPairGen (Work.Diff.GE.GramM (I := I) G x t x)
        (Work.Diff.GE.rmC4 (I := I) G x t x)) := by
    filter_upwards with t
    exact Work.Diff.GE.qPairAt_eq_qPairGen_Gram (I := I) (M := M) hLC G x
      (mem_chart_source H x) t
  exact (Work.Diff.GE.cfq_continuousAt_of_jointSmoothAt (I := I) (M := M)
    (cfq_qPairGen_jointSmoothAt (I := I) (M := M) hLC hJ hG ht₀ x)).congr_of_eventuallyEq hev

end Helpers



/-- **Continuity at the initial time of the frozen curvature quantities of a Ricci flow.** -/
theorem continuous_flow_quantities
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ) (hflow : Submission.Diff.IsRicciFlow G T) (x : M) :
    ContinuousWithinAt (fun s ↦ Submission.Diff.rmNormSq (G s) x) (Set.Ico 0 T) 0 ∧
    ContinuousWithinAt (fun s ↦ Submission.Diff.laplAt (G s) (Submission.Diff.rmNormSq (G s)) x
      - 2 * Submission.Diff.dRmNormSq (G s) x + 2 * Submission.Diff.qPairAt (G s) x) (Set.Ico 0 T) 0 := by
  refine ⟨Work.Diff.GE.cfq_continuousWithinAt_rmNormSq_zero (I := I) (M := M) hLC hflow x, ?_⟩
  by_cases hT : T ≤ 0
  · rw [Set.Ico_eq_empty_iff.mpr (not_lt.mpr hT)]
    simp [ContinuousWithinAt, nhdsWithin_empty]
  · have hTpos : 0 < T := not_le.mp hT
    set ρ : ℝ := Real.sqrt T / 2 with hρdef
    have hρ : 0 < ρ := by positivity
    have hρT : ρ ^ 2 < T := by
      rw [hρdef, div_pow, Real.sq_sqrt (le_of_lt hTpos)]
      nlinarith
    have hsq := Work.Diff.GE.cfq_jointSmooth_sqFlow (I := I) (M := M) G hTpos hρ hρT hflow.1
    have h0 : (0 : ℝ) ∈ Set.Ioo (-ρ) ρ := ⟨by linarith, hρ⟩
    have hrm := Work.Diff.GE.cfq_rmNormSq_jointSmoothAt (I := I) (M := M) hLC isOpen_Ioo hsq h0 x
    have hlap : ContinuousAt (fun t : ℝ ↦ Submission.Diff.laplAt
        (Work.Diff.GE.cfq_sqFlow G t) (Submission.Diff.rmNormSq (Work.Diff.GE.cfq_sqFlow G t)) x) 0 :=
      Work.Diff.GE.cfq_laplAt_continuousAt (I := I) (M := M) hLC isOpen_Ioo hsq h0 x hrm
    have hdRm : ContinuousAt (fun t : ℝ ↦ Submission.Diff.dRmNormSq
        (Work.Diff.GE.cfq_sqFlow G t) x) 0 :=
      Work.Diff.GE.cfq_dRmNormSq_continuousAt (I := I) (M := M) hLC isOpen_Ioo hsq h0 x
    have hqP : ContinuousAt (fun t : ℝ ↦ Submission.Diff.qPairAt
        (Work.Diff.GE.cfq_sqFlow G t) x) 0 :=
      Work.Diff.GE.cfq_qPairAt_continuousAt (I := I) (M := M) hLC isOpen_Ioo hsq h0 x
    have hF : ContinuousAt (fun τ : ℝ ↦ Submission.Diff.laplAt
          (Work.Diff.GE.cfq_sqFlow G τ) (Submission.Diff.rmNormSq (Work.Diff.GE.cfq_sqFlow G τ)) x
        - 2 * Submission.Diff.dRmNormSq (Work.Diff.GE.cfq_sqFlow G τ) x
        + 2 * Submission.Diff.qPairAt (Work.Diff.GE.cfq_sqFlow G τ) x) 0 :=
      (hlap.sub ((continuousAt_const : ContinuousAt (fun _ : ℝ => (2 : ℝ)) 0).mul hdRm)).add
        ((continuousAt_const : ContinuousAt (fun _ : ℝ => (2 : ℝ)) 0).mul hqP)
    refine Work.Diff.GE.cfq_continuousWithinAt_of_continuousAt_comp_sq hTpos hF ?_
    intro s hs
    have hs' : Work.Diff.GE.cfq_sqFlow G (Real.sqrt s) = G s := by
      show G ((Real.sqrt s) ^ 2) = G s
      rw [Real.sq_sqrt hs.1]
    rw [hs']

end Work.Diff.GE
