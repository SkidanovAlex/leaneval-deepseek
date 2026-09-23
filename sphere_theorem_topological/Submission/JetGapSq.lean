import Submission.JetGap
import Submission.GapEstimate2

/-!
# Two curves with the same velocity are `O(s ^ 2)` apart

The `O(s ^ 2)` companion of `Submission.JetGap.riemannianEDist_le_cube_of_jet`: the third-order
estimate needs the covariant accelerations to agree, the second-order one only needs the position
and the velocity to agree.  It is the estimate that relates the flow of a vector field to the
geodesic ray in the same direction.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartCurv
open Submission.ChartBounds
open Submission.GapEstimate
open Submission.CornerCut
open Submission.GeodesicExtend
open Submission.CurveField
open Submission.ChartConnection
open Submission.JetGap

namespace Submission.JetGapSq

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

/-- **Two curves with the same value and velocity at `0` are `O(s ^ 2)` apart.** -/
theorem riemannianEDist_le_sq_of_same_velocity [Nontrivial E]
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) [ContMDiffCovariantDerivative cov ∞]
    {σ₁ σ₂ : ℝ → M} (hσ₁ : ContMDiffAt 𝓘(ℝ) I ∞ σ₁ 0) (hσ₂ : ContMDiffAt 𝓘(ℝ) I ∞ σ₂ 0)
    (hval : σ₁ 0 = σ₂ 0)
    (hvel : curveVelocity (I := I) σ₁ 0 = curveVelocity (I := I) σ₂ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s in 𝓝 (0:ℝ),
      Manifold.riemannianEDist I (σ₁ s) (σ₂ s) ≤ ENNReal.ofReal (C * |s| ^ 2) := by
  classical
  set p : M := σ₁ 0 with hp
  have hsrc₁ : p ∈ (chartAt H p).source := mem_chart_source H p
  have hsrc₂ : σ₂ 0 ∈ (chartAt H p).source := by rw [← hval]; exact hsrc₁
  set r₁ : ℝ → E := fun s => (extChartAt I p) (σ₁ s) with hr₁def
  set r₂ : ℝ → E := fun s => (extChartAt I p) (σ₂ s) with hr₂def
  have hr₁ : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ r₁ 0 := by
    have h := (contMDiffAt_extChartAt (I := I) (x := p) (n := ∞)).comp (0 : ℝ) hσ₁
    simpa only [hr₁def, Function.comp_def] using h
  have hr₂ : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ r₂ 0 := by
    have hc : ContMDiffAt I 𝓘(ℝ, E) ∞ (↑(extChartAt I p)) (σ₂ 0) := by
      rw [← hval]; exact contMDiffAt_extChartAt (I := I) (x := p) (n := ∞)
    have h := hc.comp (0 : ℝ) hσ₂
    simpa only [hr₂def, Function.comp_def] using h
  obtain ⟨ρc, hρc, hcd₁, hcd₂⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ContDiffOn ℝ 3 r₁ (Ioo (-ρ) ρ) ∧
      ContDiffOn ℝ 3 r₂ (Ioo (-ρ) ρ) := by
    obtain ⟨ρ₁, hρ₁, h₁⟩ := exists_pos_contDiffOn_Ioo_of_contDiffAt (F := E)
      (contMDiffAt_iff_contDiffAt.mp hr₁)
    obtain ⟨ρ₂, hρ₂, h₂⟩ := exists_pos_contDiffOn_Ioo_of_contDiffAt (F := E)
      (contMDiffAt_iff_contDiffAt.mp hr₂)
    refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, ?_, ?_⟩
    · exact h₁.mono (Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _))
    · exact h₂.mono (Ioo_subset_Ioo (neg_le_neg (min_le_right _ _)) (min_le_right _ _))
  have hmemU : Ioo (-ρc) ρc ∈ 𝓝 (0 : ℝ) :=
    IsOpen.mem_nhds isOpen_Ioo ⟨by linarith, by linarith⟩
  obtain ⟨ρe, hρe, hρesub⟩ := exists_pos_forall_abs_lt_of_mem_nhds
    (S := {s : ℝ | σ₁ s ∈ (chartAt H p).source ∧ σ₂ s ∈ (chartAt H p).source})
    (by
      have h1 : ∀ᶠ s in 𝓝 (0 : ℝ), σ₁ s ∈ (chartAt H p).source :=
        hσ₁.continuousAt.preimage_mem_nhds ((chartAt H p).open_source.mem_nhds hsrc₁)
      have h2 : ∀ᶠ s in 𝓝 (0 : ℝ), σ₂ s ∈ (chartAt H p).source :=
        hσ₂.continuousAt.preimage_mem_nhds ((chartAt H p).open_source.mem_nhds hsrc₂)
      filter_upwards [h1, h2] with s hs1 hs2
      exact ⟨hs1, hs2⟩)
  set ρ : ℝ := min ρc ρe with hρdef
  have hρ : 0 < ρ := lt_min hρc hρe
  have hρc' : ρ ≤ ρc := min_le_left _ _
  have hρe' : ρ ≤ ρe := min_le_right _ _
  have hsubc : Ioo (-ρ) ρ ⊆ Ioo (-ρc) ρc :=
    Ioo_subset_Ioo (neg_le_neg hρc') hρc'
  have hsube : Ioo (-ρ) ρ ⊆ Ioo (-ρe) ρe :=
    Ioo_subset_Ioo (neg_le_neg hρe') hρe'
  -- the first derivative towers of the two coordinate curves
  set A1 : ℝ → E := derivWithin r₁ (Ioo (-ρc) ρc) with hA1def
  set B1 : ℝ → E := derivWithin r₂ (Ioo (-ρc) ρc) with hB1def
  obtain ⟨hdA₁, -, -, -⟩ := JetGap.derivWithin_tower (f := r₁) hcd₁
  obtain ⟨hdB₁, -, -, -⟩ := JetGap.derivWithin_tower (f := r₂) hcd₂
  have hA1_0 : A1 0 = (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p
      (curveVelocity (I := I) σ₁ 0) := by
    rw [hA1def, derivWithin_of_mem_nhds hmemU]
    exact deriv_extChartAt_comp_eq_continuousLinearMapAt_curveVelocity (I := I)
      (x := p) (γ := σ₁) (t := 0) (hσ₁.mdifferentiableAt (by simp)) hsrc₁
  have hB1_0 : B1 0 = (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ (σ₂ 0)
      (curveVelocity (I := I) σ₂ 0) := by
    rw [hB1def, derivWithin_of_mem_nhds hmemU]
    exact deriv_extChartAt_comp_eq_continuousLinearMapAt_curveVelocity (I := I)
      (x := p) (γ := σ₂) (t := 0) (hσ₂.mdifferentiableAt (by simp)) hsrc₂
  have hA1B1 : A1 0 = B1 0 := by
    rw [hA1_0, hB1_0, ← hval]
    exact congrArg _ hvel
  -- the difference of the coordinate curves
  set g : ℝ → E := fun s => r₂ s - r₁ s with hgdef
  have hg3 : ContDiffOn ℝ 3 g (Ioo (-ρc) ρc) := by
    have h := hcd₂.sub hcd₁
    simpa only [hgdef, Pi.sub_apply] using h
  obtain ⟨hdg₁, hdg₂, hdg₃, hg3c⟩ := JetGap.derivWithin_tower (f := g) hg3
  set D1 : ℝ → E := derivWithin g (Ioo (-ρc) ρc) with hD1def
  set D2 : ℝ → E := derivWithin D1 (Ioo (-ρc) ρc) with hD2def
  set D3 : ℝ → E := derivWithin D2 (Ioo (-ρc) ρc) with hD3def
  have hdA₁' : ∀ s ∈ Ioo (-ρ) ρ, HasDerivAt r₁ (A1 s) s := fun s hs => by
    simpa only [hA1def] using hdA₁ s (hsubc hs)
  have hdB₁' : ∀ s ∈ Ioo (-ρ) ρ, HasDerivAt r₂ (B1 s) s := fun s hs => by
    simpa only [hB1def] using hdB₁ s (hsubc hs)
  have hdg₁r : ∀ s ∈ Ioo (-ρ) ρ, HasDerivAt g (D1 s) s := fun s hs => by
    simpa only [hD1def] using hdg₁ s (hsubc hs)
  have hdg₂r : ∀ s ∈ Ioo (-ρ) ρ, HasDerivAt D1 (D2 s) s := fun s hs => by
    simpa only [hD1def, hD2def] using hdg₂ s (hsubc hs)
  have hdg₃r : ∀ s ∈ Ioo (-ρ) ρ, HasDerivAt D2 (D3 s) s := fun s hs => by
    simpa only [hD1def, hD2def, hD3def] using hdg₃ s (hsubc hs)
  have hdr₁ : DifferentiableAt ℝ r₁ 0 :=
    (hcd₁.differentiableOn (by norm_num : (3 : WithTop ℕ∞) ≠ 0)).differentiableAt hmemU
  have hdr₂ : DifferentiableAt ℝ r₂ 0 :=
    (hcd₂.differentiableOn (by norm_num : (3 : WithTop ℕ∞) ≠ 0)).differentiableAt hmemU
  have hg0 : g 0 = 0 := by
    have h1 : r₁ 0 = (extChartAt I p) p := rfl
    have h2 : r₂ 0 = (extChartAt I p) p := by
      show (extChartAt I p) (σ₂ 0) = (extChartAt I p) p
      rw [← hval]
    simp only [hgdef, h1, h2, sub_self]
  have hD1_0 : D1 0 = deriv g 0 := by
    rw [hD1def, derivWithin_of_mem_nhds hmemU]
  have hB1_d : deriv r₂ 0 = B1 0 := by
    rw [hB1def, derivWithin_of_mem_nhds hmemU]
  have hA1_d : deriv r₁ 0 = A1 0 := by
    rw [hA1def, derivWithin_of_mem_nhds hmemU]
  have hg'0 : D1 0 = 0 := by
    rw [hD1_0]
    have h1 : deriv g 0 = deriv r₂ 0 - deriv r₁ 0 := by
      have hgg : g = r₂ - r₁ := by funext s; rfl
      rw [hgg]
      exact deriv_sub hdr₂ hdr₁
    rw [h1, hB1_d, hA1_d]
    exact sub_eq_zero.mpr hA1B1.symm
  -- the metric is bounded near `p`
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
  -- the radii of the two coordinate curves
  have h1c : ContinuousAt r₁ 0 := (hcd₁.continuousOn.continuousAt hmemU)
  have h2c : ContinuousAt r₂ 0 := (hcd₂.continuousOn.continuousAt hmemU)
  have h10 : r₁ 0 ∈ Metric.ball ((extChartAt I p) p) R := by
    have h10' : r₁ 0 = (extChartAt I p) p := rfl
    rw [h10', Metric.mem_ball, dist_self]
    exact hR
  have h20 : r₂ 0 ∈ Metric.ball ((extChartAt I p) p) R := by
    have h20' : r₂ 0 = (extChartAt I p) p := by
      show (extChartAt I p) (σ₂ 0) = (extChartAt I p) p
      rw [← hval]
    rw [h20', Metric.mem_ball, dist_self]
    exact hR
  obtain ⟨ρa, hρa, hρasub⟩ := exists_pos_forall_abs_lt_of_mem_nhds
    (S := {s : ℝ | r₁ s ∈ Metric.ball ((extChartAt I p) p) R})
    (h1c.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds h10))
  obtain ⟨ρb, hρb, hρbsub⟩ := exists_pos_forall_abs_lt_of_mem_nhds
    (S := {s : ℝ | r₂ s ∈ Metric.ball ((extChartAt I p) p) R})
    (h2c.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds h20))
  -- the effective radius
  set ρ₀ : ℝ := min (ρc / 2) (min ρ (min ρa ρb)) with hρ₀def
  have hρ₀ : 0 < ρ₀ := lt_min (by linarith) (lt_min hρ (lt_min hρa hρb))
  have hρ0c : ρ₀ ≤ ρc / 2 := min_le_left _ _
  have hρ0ρ : ρ₀ ≤ ρ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρ0a : ρ₀ ≤ ρa := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρ0b : ρ₀ ≤ ρb := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hsubρ₀ : Ioo (-ρ₀) ρ₀ ⊆ Ioo (-ρ) ρ := Ioo_subset_Ioo (neg_le_neg hρ0ρ) hρ0ρ
  have h1d : ∀ s ∈ Ioo (-ρ₀) ρ₀, HasDerivAt g (D1 s) s := fun s hs => hdg₁r s (hsubρ₀ hs)
  have h2d : ∀ s ∈ Ioo (-ρ₀) ρ₀, HasDerivAt D1 (D2 s) s := fun s hs => hdg₂r s (hsubρ₀ hs)
  have h3d : ∀ s ∈ Ioo (-ρ₀) ρ₀, HasDerivAt D2 (D3 s) s := fun s hs => hdg₃r s (hsubρ₀ hs)
  obtain ⟨M₀, hM₀, hM₀nn⟩ : ∃ M : ℝ, (∀ s ∈ Ioo (-ρ₀) ρ₀, ‖D3 s‖ ≤ M) ∧ 0 ≤ M := by
    have hD3c : ContinuousOn D3 (Ioo (-ρc) ρc) := by
      simpa only [hD1def, hD2def, hD3def] using hg3c.continuousOn
    have hsub : Icc (-ρ₀) ρ₀ ⊆ Ioo (-ρc) ρc := by
      intro s hs
      exact ⟨by linarith [hρ0c, hρc, hs.1], by linarith [hρ0c, hρc, hs.2]⟩
    obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc (hD3c.mono hsub)
    exact ⟨max M 0, fun s hs => le_trans (hM s ⟨le_of_lt hs.1, le_of_lt hs.2⟩) (le_max_left _ _),
      le_max_right _ _⟩
  have hVin : ∀ s ∈ Ioo (-ρ₀) ρ₀, r₁ s ∈ Metric.ball ((extChartAt I p) p) R := fun s hs =>
    hρasub _ (abs_lt.mpr ⟨by linarith [(abs_lt.mp (lt_of_lt_of_le (abs_lt.mpr hs) hρ0a)).1],
      by linarith [(abs_lt.mp (lt_of_lt_of_le (abs_lt.mpr hs) hρ0a)).2]⟩)
  have hUVin : ∀ s ∈ Ioo (-ρ₀) ρ₀, r₁ s + g s ∈ Metric.ball ((extChartAt I p) p) R := by
    intro s hs
    have heq : r₁ s + g s = r₂ s := by simp only [hgdef]; abel
    rw [heq]
    exact hρbsub _ (abs_lt.mpr ⟨by linarith [(abs_lt.mp (lt_of_lt_of_le (abs_lt.mpr hs) hρ0b)).1],
      by linarith [(abs_lt.mp (lt_of_lt_of_le (abs_lt.mpr hs) hρ0b)).2]⟩)
  obtain ⟨ρ', hρ'pos, hρ'le, hfin⟩ := riemannianEDist_le_sq_of_gap (I := I) (x₀ := p)
    (V := r₁) (g := g) (g' := D1) (g'' := D2) (g''' := D3)
    (K := Metric.ball ((extChartAt I p) p) R) (c := (extChartAt I p) p) (r := R)
    (Λ := 2 * Lam) (M₀ := M₀) (ρ := ρ₀) rfl (by linarith) hρ₀ hg0 hg'0
    h1d h2d h3d hM₀ hbound (fun z hz => (hRsub hz).1) hVin hUVin
  refine ⟨Real.sqrt (2 * Lam) * (M₀ / 6 * ρ₀ + ‖D2 0‖ / 2),
    mul_nonneg (Real.sqrt_nonneg _)
      (add_nonneg (mul_nonneg (div_nonneg hM₀nn (by norm_num : (0:ℝ) ≤ 6)) hρ₀.le)
        (div_nonneg (norm_nonneg (D2 0)) (by norm_num : (0:ℝ) ≤ 2))), ?_⟩
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hρ'pos] with s hs
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
  have hsI : s ∈ Ioo (-ρ) ρ := by
    have h1 : |s| < ρ := lt_of_lt_of_le (lt_of_lt_of_le hs hρ'le) hρ0ρ
    exact ⟨by linarith [(abs_lt.mp h1).1], by linarith [(abs_lt.mp h1).2]⟩
  have hp1 : ((extChartAt I p).symm) (r₁ s) = σ₁ s := by
    show (extChartAt I p).symm ((extChartAt I p) (σ₁ s)) = σ₁ s
    exact (extChartAt I p).left_inv (by rw [extChartAt_source]; exact (hρesub _ (abs_lt.mpr (hsube hsI))).1)
  have hp2 : ((extChartAt I p).symm) (r₁ s + g s) = σ₂ s := by
    have heq : r₁ s + g s = r₂ s := by simp only [hgdef]; abel
    rw [heq]
    show (extChartAt I p).symm ((extChartAt I p) (σ₂ s)) = σ₂ s
    exact (extChartAt I p).left_inv (by rw [extChartAt_source]; exact (hρesub _ (abs_lt.mpr (hsube hsI))).2)
  have h2 := hfin s hs
  rw [hp2, hp1, Manifold.riemannianEDist_comm] at h2
  exact h2.trans (le_of_eq (congrArg ENNReal.ofReal (by ring)))

end

end Submission.JetGapSq
