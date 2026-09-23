import Submission.JetGap
import Submission.GapEstimate

/-!
# Two curves with the same velocity are `o(s)` apart

This is the *first order* companion of `Submission.JetGapSq.riemannianEDist_le_sq_of_same_velocity`:
the second-order estimate needs the curves to be `C^3`, whereas here only *differentiability at
`0`* is used.  It is the estimate that compares the flow of a vector field with the exponential ray
in the same direction when only the `C^1` structure of the flow is available.

* `norm_sub_le_mul_abs_of_hasDerivAt_zero` — the model-space fact: a differentiable function `g`
  with `g 0 = 0` and `g' 0 = 0` satisfies `‖g s‖ ≤ ε |s|` near `0`;
* `riemannianEDist_le_lin_of_same_velocity` — the manifold form.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartCurv
open Submission.ChartBounds
open Submission.GapEstimate
open Submission.CornerCut
open Submission.ChartConnection
open Submission.CurveField
open Submission.JetGap

namespace Submission.JetGapLin

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless]

noncomputable section

/-- **The model-space first order estimate.**  If `g` is differentiable at `0` with `g 0 = 0` and
`g' 0 = 0`, then `‖g s‖ ≤ ε |s|` for all `s` close to `0`. -/
lemma norm_sub_le_mul_abs_of_hasDerivAt_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : ℝ → F} (hg0 : g 0 = 0) (hg : HasDerivAt g 0 0) :
    ∀ ε > 0, ∀ᶠ s in 𝓝 (0:ℝ), ‖g s‖ ≤ ε * |s| := by
  intro ε hε
  have hslope : Tendsto (fun t : ℝ => t⁻¹ • (g (0 + t) - g 0)) (𝓝[≠] (0:ℝ)) (𝓝 (0:F)) :=
    hg.tendsto_slope_zero
  have hnorm : Tendsto (fun t : ℝ => |t|⁻¹ * ‖g t‖) (𝓝[≠] (0:ℝ)) (𝓝 0) := by
    have h1 : (fun t : ℝ => ‖t⁻¹ • (g (0 + t) - g 0)‖) = fun t : ℝ => |t|⁻¹ * ‖g t‖ := by
      funext t
      have h2 : g (0 + t) - g 0 = g t := by simp [hg0]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, h2]
    have h2 : Tendsto (fun t : ℝ => ‖t⁻¹ • (g (0 + t) - g 0)‖) (𝓝[≠] (0:ℝ)) (𝓝 (0:ℝ)) := by
      have h := hslope
      rw [tendsto_iff_norm_sub_tendsto_zero] at h
      simpa using h
    rwa [h1] at h2
  have hev : ∀ᶠ t in 𝓝[≠] (0:ℝ), ‖g t‖ ≤ ε * |t| := by
    filter_upwards [hnorm.eventually_lt_const hε] with t ht
    rcases eq_or_ne t 0 with h0 | h0
    · simp [h0, hg0]
    · have habs : 0 < |t| := abs_pos.mpr h0
      have h1 : ‖g t‖ = |t| * (|t|⁻¹ * ‖g t‖) := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt habs), one_mul]
      rw [h1, mul_comm ε |t|]
      exact le_of_lt (mul_lt_mul_of_pos_left ht habs)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine Metric.mem_nhds_iff.mpr ⟨δ, hδ, fun t ht => ?_⟩
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
  rcases eq_or_ne t 0 with h0 | h0
  · simp [h0, hg0]
  · exact hδ' ⟨by rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]; exact ht, h0⟩

/-- **Two curves with the same value and velocity at `0` are `o(s)` apart.** -/
theorem riemannianEDist_le_lin_of_same_velocity [Nontrivial E]
    {σ₁ σ₂ : ℝ → M} (hσ₁ : MDifferentiableAt 𝓘(ℝ) I σ₁ 0)
    (hσ₂ : MDifferentiableAt 𝓘(ℝ) I σ₂ 0)
    (hval : σ₁ 0 = σ₂ 0)
    (hvel : curveVelocity (I := I) σ₁ 0 = curveVelocity (I := I) σ₂ 0) :
    ∀ ε > 0, ∀ᶠ s in 𝓝 (0:ℝ),
      Manifold.riemannianEDist I (σ₁ s) (σ₂ s) ≤ ENNReal.ofReal (ε * |s|) := by
  intro ε hε
  classical
  set p : M := σ₁ 0 with hp
  have hsrc₁ : p ∈ (chartAt H p).source := mem_chart_source H p
  have hsrc₂ : σ₂ 0 ∈ (chartAt H p).source := by rw [← hval]; exact hsrc₁
  set r₁ : ℝ → E := fun s => (extChartAt I p) (σ₁ s) with hr₁def
  set r₂ : ℝ → E := fun s => (extChartAt I p) (σ₂ s) with hr₂def
  have hd₁ : DifferentiableAt ℝ r₁ 0 := by
    have h := (mdifferentiableAt_iff_target (I := 𝓘(ℝ)) (I' := I) (f := σ₁)).mp hσ₁
    exact h.2.differentiableAt
  have hd₂ : DifferentiableAt ℝ r₂ 0 := by
    have h := (mdifferentiableAt_iff_target (I := 𝓘(ℝ)) (I' := I) (f := σ₂)).mp hσ₂
    have h2 := h.2.differentiableAt
    have h3 : (↑(extChartAt I (σ₂ 0)) ∘ σ₂) = r₂ := by
      funext s
      show (extChartAt I (σ₂ 0)) (σ₂ s) = (extChartAt I p) (σ₂ s)
      rw [show p = σ₂ 0 from hval]
    rwa [h3] at h2
  have hdd₁ : deriv r₁ 0
      = (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p
          (curveVelocity (I := I) σ₁ 0) :=
    deriv_extChartAt_comp_eq_continuousLinearMapAt_curveVelocity (I := I)
      (x := p) (γ := σ₁) (t := 0) hσ₁ hsrc₁
  have hdd₂ : deriv r₂ 0
      = (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ (σ₂ 0)
          (curveVelocity (I := I) σ₂ 0) :=
    deriv_extChartAt_comp_eq_continuousLinearMapAt_curveVelocity (I := I)
      (x := p) (γ := σ₂) (t := 0) hσ₂ hsrc₂
  have hderiveq : deriv r₂ 0 = deriv r₁ 0 := by
    rw [hdd₂, hdd₁, ← hval]
    exact (congrArg _ hvel).symm
  -- the difference curve
  set g : ℝ → E := fun s => r₂ s - r₁ s with hgdef
  have hg0 : g 0 = 0 := by
    have h1 : r₁ 0 = (extChartAt I p) p := rfl
    have h2 : r₂ 0 = (extChartAt I p) p := by
      show (extChartAt I p) (σ₂ 0) = (extChartAt I p) p
      rw [← hval]
    simp only [hgdef, h1, h2, sub_self]
  have hgderiv : HasDerivAt g 0 0 := by
    have h := hd₂.hasDerivAt.sub hd₁.hasDerivAt
    have hz : deriv r₂ 0 - deriv r₁ 0 = 0 := by rw [hderiveq, sub_self]
    rw [hz] at h
    have hg' : (r₂ - r₁) = g := by funext s; rfl
    rwa [hg'] at h
  -- the chart metric is bounded near the centre
  obtain ⟨lam, hlam, Lam, hLam, hbnd0⟩ := exists_chartGram_bounds (I := I) p
    (K := ({p} : Set M)) isCompact_singleton ⟨p, rfl⟩
    (by intro y hy; rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hsrc₁)
  obtain ⟨U, hUnh, hUbd⟩ := exists_chartGram_le_nhds (I := I) p (c := 1) (by norm_num)
  obtain ⟨R, hR, hRsub⟩ : ∃ R : ℝ, 0 < R ∧ Metric.ball ((extChartAt I p) p) R ⊆
      (extChartAt I p).target ∩ ((extChartAt I p).symm ⁻¹' U) := by
    have htgt : (extChartAt I p) p ∈ (extChartAt I p).target := mem_extChartAt_target p
    have hcont : ContinuousAt ((extChartAt I p).symm) ((extChartAt I p) p) :=
      continuousAt_extChartAt_symm p
    have h1 : (extChartAt I p).target ∈ 𝓝 ((extChartAt I p) p) :=
      (isOpen_extChartAt_target p).mem_nhds htgt
    have hpt : ((extChartAt I p).symm) ((extChartAt I p) p) = p :=
      (extChartAt I p).left_inv (by rw [extChartAt_source]; exact hsrc₁)
    have h2 : (extChartAt I p).symm ⁻¹' U ∈ 𝓝 ((extChartAt I p) p) := by
      have hUnh' : U ∈ 𝓝 ((extChartAt I p).symm ((extChartAt I p) p)) := by rw [hpt]; exact hUnh
      exact hcont.preimage_mem_nhds hUnh'
    obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem h1 h2)
    exact ⟨R, hR, hsub⟩
  have hbound : ∀ z ∈ Metric.ball ((extChartAt I p) p) R, ∀ a : E,
      chartGram (I := I) p ((extChartAt I p).symm z) a a ≤ (2 * Lam) * ‖a‖ ^ 2 := by
    intro z hz a
    have h1 := hUbd ((extChartAt I p).symm z) (hRsub hz).2 a
    have h2 := (hbnd0 p (by simp) a).2
    calc chartGram (I := I) p ((extChartAt I p).symm z) a a
        ≤ (1 + 1) * chartGram (I := I) p p a a := h1
      _ ≤ (1 + 1) * (Lam * ‖a‖ ^ 2) := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = (2 * Lam) * ‖a‖ ^ 2 := by ring
  have hLamnn : 0 ≤ 2 * Lam := by positivity
  -- the smallness of `g`
  set e : ℝ := ε / (Real.sqrt (2 * Lam) + 1) with hedef
  have hepos : 0 < e := by rw [hedef]; positivity
  obtain ⟨ρg, hρg, hρg'⟩ : ∃ ρ > (0:ℝ), ∀ s : ℝ, |s| < ρ → ‖g s‖ ≤ e * |s| := by
    have h := norm_sub_le_mul_abs_of_hasDerivAt_zero (F := E) hg0 hgderiv e hepos
    have hmem : {s : ℝ | ‖g s‖ ≤ e * |s|} ∈ 𝓝 (0:ℝ) := h
    obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp hmem
    exact ⟨ρ, hρ, fun s hs => hsub (by rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]; exact hs)⟩
  -- the chart validity radius
  have h10 : r₁ 0 ∈ Metric.ball ((extChartAt I p) p) R := by
    rw [show r₁ 0 = (extChartAt I p) p from rfl, Metric.mem_ball, dist_self]
    exact hR
  have h20 : r₂ 0 ∈ Metric.ball ((extChartAt I p) p) R := by
    have h20' : r₂ 0 = (extChartAt I p) p := by
      show (extChartAt I p) (σ₂ 0) = (extChartAt I p) p
      rw [← hval]
    rw [h20', Metric.mem_ball, dist_self]
    exact hR
  have hcont₁ : ContinuousAt r₁ 0 := hd₁.continuousAt
  have hcont₂ : ContinuousAt r₂ 0 := hd₂.continuousAt
  obtain ⟨ρa, hρa, hρasub⟩ := exists_pos_forall_abs_lt_of_mem_nhds
    (S := {s : ℝ | r₁ s ∈ Metric.ball ((extChartAt I p) p) R})
    (hcont₁.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds h10))
  obtain ⟨ρb, hρb, hρbsub⟩ := exists_pos_forall_abs_lt_of_mem_nhds
    (S := {s : ℝ | r₂ s ∈ Metric.ball ((extChartAt I p) p) R})
    (hcont₂.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds h20))
  -- the chart source condition
  have hσ₁src : ∀ᶠ s in 𝓝 (0:ℝ), σ₁ s ∈ (chartAt H p).source :=
    hσ₁.continuousAt.preimage_mem_nhds ((chartAt H p).open_source.mem_nhds hsrc₁)
  have hσ₂src : ∀ᶠ s in 𝓝 (0:ℝ), σ₂ s ∈ (chartAt H p).source :=
    hσ₂.continuousAt.preimage_mem_nhds ((chartAt H p).open_source.mem_nhds hsrc₂)
  obtain ⟨ρa1, hρa1, hρa1sub⟩ := exists_pos_forall_abs_lt_of_mem_nhds hσ₁src
  obtain ⟨ρb1, hρb1, hρb1sub⟩ := exists_pos_forall_abs_lt_of_mem_nhds hσ₂src
  -- the chart transition
  have hleft₁ : ∀ s : ℝ, |s| < min ρa ρa1 → ((extChartAt I p).symm) (r₁ s) = σ₁ s := by
    intro s hs
    have hs2 : |s| < ρa1 := lt_of_lt_of_le hs (min_le_right _ _)
    show (extChartAt I p).symm ((extChartAt I p) (σ₁ s)) = σ₁ s
    exact (extChartAt I p).left_inv (by rw [extChartAt_source]; exact hρa1sub s hs2)
  have hleft₂ : ∀ s : ℝ, |s| < min ρb ρb1 → ((extChartAt I p).symm) (r₂ s) = σ₂ s := by
    intro s hs
    have hs2 : |s| < ρb1 := lt_of_lt_of_le hs (min_le_right _ _)
    show (extChartAt I p).symm ((extChartAt I p) (σ₂ s)) = σ₂ s
    exact (extChartAt I p).left_inv (by rw [extChartAt_source]; exact hρb1sub s hs2)
  set ρ : ℝ := min ρg (min (min ρa ρa1) (min ρb ρb1)) with hρdef
  have hρ : 0 < ρ := lt_min hρg (lt_min (lt_min hρa hρa1) (lt_min hρb hρb1))
  refine Metric.mem_nhds_iff.mpr ⟨ρ, hρ, fun s hs => ?_⟩
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
  have hsρg : |s| < ρg := lt_of_lt_of_le hs (min_le_left _ _)
  have hsρa : |s| < ρa :=
    lt_of_lt_of_le hs (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hsρb : |s| < ρb :=
    lt_of_lt_of_le hs (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hsρa1 : |s| < ρa1 :=
    lt_of_lt_of_le hs (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hsρb1 : |s| < ρb1 :=
    lt_of_lt_of_le hs (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hseg : ∀ u ∈ Icc (0:ℝ) 1, r₁ s + u • (r₂ s - r₁ s) ∈ Metric.ball ((extChartAt I p) p) R :=
    fun u hu => (convex_ball _ _).add_smul_sub_mem (hρasub s hsρa) (hρbsub s hsρb) hu
  have hgs : ‖g s‖ ≤ e * |s| := hρg' s hsρg
  have hfin := riemannianEDist_chart_le (I := I) (x₀ := p) (K := Metric.ball ((extChartAt I p) p) R)
    (Λ := 2 * Lam) hLamnn hbound (fun z hz => (hRsub hz).1) (hρasub s hsρa) hseg
  rw [hleft₁ s (lt_min hsρa hsρa1), hleft₂ s (lt_min hsρb hsρb1),
    show ‖r₂ s - r₁ s‖ = ‖g s‖ from by rw [hgdef]] at hfin
  have hge : Real.sqrt (2 * Lam) * ‖g s‖ ≤ ε * |s| := by
    have hsq : 0 ≤ Real.sqrt (2 * Lam) := Real.sqrt_nonneg _
    calc Real.sqrt (2 * Lam) * ‖g s‖
        ≤ Real.sqrt (2 * Lam) * (e * |s|) := mul_le_mul_of_nonneg_left hgs hsq
      _ = (Real.sqrt (2 * Lam) * e) * |s| := by ring
      _ ≤ ε * |s| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg s)
          rw [hedef, mul_div]
          have hpos : 0 < Real.sqrt (2 * Lam) + 1 := by linarith [hsq]
          rw [div_le_iff₀ hpos]
          nlinarith [hsq]
  exact le_trans hfin (ENNReal.ofReal_le_ofReal hge)

end

end Submission.JetGapLin
