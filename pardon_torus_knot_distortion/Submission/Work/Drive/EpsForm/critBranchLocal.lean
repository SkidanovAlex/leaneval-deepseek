import Mathlib
import Submission.Work.Drive.EpsForm.critBranch_exists
import Submission.Work.Drive.EpsForm.tiltedSweepGenericity_holds
import Submission.Work.Drive.EpsForm.goodHeight_exists
import Submission.Work.Embedding.smooth_implicit_function_nhd

open scoped Topology

namespace Work.Drive.EpsForm

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

/-! ## An implicit-function branch which is differentiable on a whole ball

The classical implicit function theorem produces, at a nondegenerate zero `(a, b)` of `F`, a local
branch `n ↦ Y n` with `F (n, Y n) = 0`.  As stated in Mathlib the branch is only known to be
differentiable *at* the base point `a`.  The task of this section is the stronger statement used
by the sideways sweep: the branch is differentiable at *every* point of a ball around `a`.

The argument is the standard one.  Start with the Mathlib branch `Y` at `(a, b)`; it satisfies
`F (n, Y n) = 0` and is locally the unique solution near `(a, b)`.  At a point `n₁` of the ball the
point `(n₁, Y n₁)` is again a nondegenerate zero (the partial derivative is invertible nearby,
because invertibility is an open condition), so applying the implicit function theorem there
produces a second branch `Y₁` which is differentiable at `n₁`; and `Y₁` must agree with `Y` near
`n₁`, because both solve the equation inside the uniqueness region of the first application. -/

theorem iftBranchExists {E₁ E₂ G : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {F : E₁ × E₂ → G} (hF : ContDiff ℝ 1 F) {a : E₁} {b : E₂}
    (h0 : F (a, b) = 0)
    (hInv : (fderiv ℝ F (a, b) ∘L ContinuousLinearMap.inr ℝ E₁ E₂).IsInvertible) :
    ∃ (Y : E₁ → E₂) (δ ε : ℝ), 0 < δ ∧ 0 < ε ∧ Y a = b ∧
      (∀ n : E₁, ‖n - a‖ < δ → F (n, Y n) = 0) ∧
      (∀ n : E₁, ‖n - a‖ < δ → ∀ q : E₂, ‖q - b‖ < ε → F (n, q) = 0 → q = Y n) ∧
      (∀ n : E₁, ‖n - a‖ < δ → DifferentiableAt ℝ Y n) := by
  classical
  have hnz : (1 : WithTop ℕ∞) ≠ 0 := one_ne_zero
  have hct : ContDiffAt ℝ 1 F (a, b) := hF.contDiffAt
  set Y : E₁ → E₂ := hct.implicitFunction hnz hInv with hY
  have hYa : Y a = b := by rw [hY]; exact hct.implicitFunction_apply_self hnz hInv
  -- existence on a ball
  have hex : ∀ᶠ n in 𝓝 a, F (n, Y n) = 0 := by
    filter_upwards [hct.eventually_apply_implicitFunction hnz hInv] with n hn
    rw [hn, h0]
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.mem_nhds_iff.mp hex
  have key₁ : ∀ n : E₁, ‖n - a‖ < δ₁ → F (n, Y n) = 0 := by
    intro n hn
    exact hδ₁' (Metric.mem_ball.mpr (by rwa [dist_eq_norm]))
  -- uniqueness in a ball around b
  have hu : ∀ᶠ v in 𝓝 (a, b), F v = 0 ↔ Y v.1 = v.2 := by
    rw [hY]
    filter_upwards [hct.eventually_apply_eq_iff_implicitFunction hnz hInv] with v hv
    rw [← h0]; exact hv
  obtain ⟨ρ, hρ, hρ'⟩ := Metric.mem_nhds_iff.mp hu
  have key₂ : ∀ n : E₁, ∀ q : E₂, ‖n - a‖ < ρ → ‖q - b‖ < ρ → F (n, q) = 0 → Y n = q := by
    intro n q hn hq hFq
    have hmem : (n, q) ∈ Metric.ball (a, b) ρ := by
      rw [Metric.mem_ball, Prod.dist_eq, dist_eq_norm, dist_eq_norm]
      exact max_lt hn hq
    exact (hρ' hmem).mp hFq
  -- continuity of `Y` at `a`
  have hcy : ContinuousAt Y a := by
    rw [hY]
    exact (hct.hasStrictFDerivAt_implicitFunction hnz hInv).continuousAt
  -- invertibility of the partial derivative is open
  have hcontT : Continuous (fun v : E₁ × E₂ =>
      (fderiv ℝ F v) ∘L ContinuousLinearMap.inr ℝ E₁ E₂) := by
    have h1 : Continuous (fun v : E₁ × E₂ =>
        (ContinuousLinearMap.compL ℝ E₂ (E₁ × E₂) G) (fderiv ℝ F v)) :=
      (ContinuousLinearMap.compL ℝ E₂ (E₁ × E₂) G).continuous.comp (hF.continuous_fderiv hnz)
    exact h1.clm_apply continuous_const
  have hopen : ∀ᶠ v in 𝓝 (a, b),
      ((fderiv ℝ F v) ∘L ContinuousLinearMap.inr ℝ E₁ E₂).IsInvertible :=
    hcontT.continuousAt.preimage_mem_nhds
      ((Work.Embedding.isOpen_isInvertible (E := E₂) (F := G)).mem_nhds hInv)
  obtain ⟨ρ₂, hρ₂, hρ₂'⟩ := Metric.mem_nhds_iff.mp hopen
  have key₃ : ∀ n : E₁, ∀ q : E₂, ‖n - a‖ < ρ₂ → ‖q - b‖ < ρ₂ →
      ((fderiv ℝ F (n, q)) ∘L ContinuousLinearMap.inr ℝ E₁ E₂).IsInvertible := by
    intro n q hn hq
    exact hρ₂' (by
      rw [Metric.mem_ball, Prod.dist_eq, dist_eq_norm, dist_eq_norm]
      exact max_lt hn hq)
  -- the image of a small ball around `a` stays in a small ball around `b`
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.continuousAt_iff.mp hcy (min ρ ρ₂ / 2) (by positivity)
  have key₄ : ∀ n : E₁, ‖n - a‖ < δ₂ → ‖Y n - b‖ < min ρ ρ₂ / 2 := by
    intro n hn
    have h := hδ₂' (by rwa [dist_eq_norm])
    rwa [dist_eq_norm, hYa] at h
  refine ⟨Y, min δ₁ (min ρ (min ρ₂ δ₂)), min ρ ρ₂,
    lt_min hδ₁ (lt_min hρ (lt_min hρ₂ hδ₂)), lt_min hρ hρ₂, hYa, ?_, ?_, ?_⟩
  · intro n hn
    exact key₁ n (lt_of_lt_of_le hn (min_le_left _ _))
  · intro n hn q hq hFq
    have hn' : ‖n - a‖ < ρ := lt_of_lt_of_le hn (le_trans (min_le_right _ _) (min_le_left _ _))
    have hq' : ‖q - b‖ < ρ := lt_of_lt_of_le hq (min_le_left _ _)
    exact (key₂ n q hn' hq' hFq).symm
  · intro n hn
    have hnρ : ‖n - a‖ < ρ := lt_of_lt_of_le hn (le_trans (min_le_right _ _) (min_le_left _ _))
    have hnρ₂ : ‖n - a‖ < ρ₂ :=
      lt_of_lt_of_le hn (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hnδ₂ : ‖n - a‖ < δ₂ :=
      lt_of_lt_of_le hn (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
    have hyb : ‖Y n - b‖ < min ρ ρ₂ / 2 := key₄ n hnδ₂
    have hybρ : ‖Y n - b‖ < ρ := lt_of_lt_of_le hyb (by nlinarith [min_le_left ρ ρ₂, hρ])
    have hybρ₂ : ‖Y n - b‖ < ρ₂ := lt_of_lt_of_le hyb (by nlinarith [min_le_right ρ ρ₂, hρ₂])
    have hInvT : ((fderiv ℝ F (n, Y n)) ∘L ContinuousLinearMap.inr ℝ E₁ E₂).IsInvertible :=
      key₃ n (Y n) hnρ₂ hybρ₂
    have hFn : F (n, Y n) = 0 := key₁ n (lt_of_lt_of_le hn (min_le_left _ _))
    have hctn : ContDiffAt ℝ 1 F (n, Y n) := hF.contDiffAt
    set Y₁ : E₁ → E₂ := hctn.implicitFunction hnz hInvT with hY₁
    have hY₁n : Y₁ n = Y n := by rw [hY₁]; exact hctn.implicitFunction_apply_self hnz hInvT
    have hdiff₁ : DifferentiableAt ℝ Y₁ n := by
      rw [hY₁]; exact (hctn.hasStrictFDerivAt_implicitFunction hnz hInvT).differentiableAt
    have hcont₁ : ContinuousAt Y₁ n := by
      rw [hY₁]; exact (hctn.hasStrictFDerivAt_implicitFunction hnz hInvT).continuousAt
    have hagree : Y =ᶠ[𝓝 n] Y₁ := by
      have hA : ∀ᶠ m in 𝓝 n, F (m, Y₁ m) = 0 := by
        filter_upwards [hctn.eventually_apply_implicitFunction hnz hInvT] with m hm
        rw [hm, hFn]
      have hB : ∀ᶠ m in 𝓝 n, ‖m - a‖ < ρ := by
        have hpos : 0 < ρ - ‖n - a‖ := sub_pos.mpr hnρ
        filter_upwards [Metric.ball_mem_nhds n hpos] with m hm
        have hm' : ‖m - n‖ < ρ - ‖n - a‖ := by
          simpa [Metric.mem_ball, dist_eq_norm, dist_comm] using hm
        have hsub : m - a = (m - n) + (n - a) := by abel
        calc ‖m - a‖ = ‖(m - n) + (n - a)‖ := by rw [hsub]
          _ ≤ ‖m - n‖ + ‖n - a‖ := norm_add_le _ _
          _ < ρ := by linarith
      have hC : ∀ᶠ m in 𝓝 n, ‖Y₁ m - b‖ < ρ := by
        have hmem : Y₁ n ∈ Metric.ball b ρ := by
          rw [Metric.mem_ball, dist_eq_norm, hY₁n]; exact hybρ
        filter_upwards [hcont₁.eventually (Metric.isOpen_ball.mem_nhds hmem)] with m hm
        rwa [dist_eq_norm] at hm
      filter_upwards [hA, hB, hC] with m hmA hmB hmC
      exact key₂ m (Y₁ m) hmB hmC hmA
    exact (Filter.EventuallyEq.differentiableAt_iff hagree).mpr hdiff₁

/-! ## The critical-point equation of the height family -/

/-- The height `q ↦ ⟪n, par ψ q⟫` of the parametrised surface, as a function of both the direction
`n` and the parameter `q`. -/
private def gradH (ψ : Submission.Diffeo) : R3 × (ℝ × ℝ) → ℝ :=
  fun v => inner ℝ v.1 (Work.BoxShrink.Pinch.par ψ v.2)

/-- The gradient of the height in direction `n` at the parameter `q`, as a function of `(n, q)`. -/
private def gradF (ψ : Submission.Diffeo) : R3 × (ℝ × ℝ) → (ℝ × ℝ →L[ℝ] ℝ) :=
  fun v => fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v.1 (Work.BoxShrink.Pinch.par ψ q)) v.2

private lemma gradH_contDiff (ψ : Submission.Diffeo) : ContDiff ℝ 2 (gradH ψ) := by
  have h1 : ContDiff ℝ 2 (fun v : R3 × (ℝ × ℝ) => (innerSL ℝ) v.1) :=
    (ContinuousLinearMap.contDiff (innerSL ℝ) : ContDiff ℝ 2 (fun x : R3 => (innerSL ℝ) x)).comp
      contDiff_fst
  have h2 : ContDiff ℝ 2 (fun v : R3 × (ℝ × ℝ) => Work.BoxShrink.Pinch.par ψ v.2) :=
    ((Work.BoxShrink.Pinch.par_contDiff ψ).of_le (WithTop.coe_le_coe.mpr le_top)).comp contDiff_snd
  exact h1.clm_apply h2

private lemma fderiv_comp_inr {E₁ E₂ Y : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {G : E₁ × E₂ → Y} {v : E₁ × E₂} (hd : DifferentiableAt ℝ G v) :
    (fderiv ℝ G v) ∘L (ContinuousLinearMap.inr ℝ E₁ E₂)
      = fderiv ℝ (fun q : E₂ => G (v.1, q)) v.2 := by
  have h : HasFDerivAt G (fderiv ℝ G v) v := hd.hasFDerivAt
  have h2 := h.comp v.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) (E := E₁) (F := E₂) v.1 v.2)
  exact h2.fderiv.symm

private lemma gradF_eq (ψ : Submission.Diffeo) :
    gradF ψ = fun v => (fderiv ℝ (gradH ψ) v) ∘L ContinuousLinearMap.inr ℝ R3 (ℝ × ℝ) := by
  funext v
  exact (fderiv_comp_inr (G := gradH ψ) (v := v)
    ((gradH_contDiff ψ).differentiable (by norm_num) v)).symm

private lemma gradF_contDiff_one (ψ : Submission.Diffeo) : ContDiff ℝ 1 (gradF ψ) := by
  rw [gradF_eq]
  exact ((gradH_contDiff ψ).fderiv_right (m := 1) (n := 2) le_rfl).clm_comp contDiff_const

private lemma gradF_fderiv_inr (ψ : Submission.Diffeo) (n₀ : R3) (x : ℝ × ℝ) :
    (fderiv ℝ (gradF ψ) (n₀, x)) ∘L ContinuousLinearMap.inr ℝ R3 (ℝ × ℝ)
      = fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ =>
          inner ℝ n₀ (Work.BoxShrink.Pinch.par ψ q))) x := by
  have h := fderiv_comp_inr (G := gradF ψ) (v := (n₀, x))
    ((gradF_contDiff_one ψ).differentiable (by norm_num) (n₀, x))
  rw [h]
  rfl

/-! ## Local branches of the critical points of the height, smooth in the direction -/

/-- **Local branches of the critical points of the height, as the direction moves.**  At a finite
set `X` of parameters which are nondegenerate critical points of the height in direction `n₀`,
there is a radius `ε > 0` and, for every `x ∈ X`, a selection `y x` of the critical point of the
height in a nearby direction `n` (`‖n - n₀‖ < δ`), differentiable in `n`, which is the *unique*
critical point of that height within distance `ε` of `x` and which reduces to `x` at `n = n₀`. -/
theorem critBranchLocal (ψ : Submission.Diffeo) (n₀ : LeanEval.KnotTheory.PardonDistortion.R3)
    (X : Finset (ℝ × ℝ))
    (hX : ∀ x ∈ X, fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n₀ (Work.BoxShrink.Pinch.par ψ q)) x = 0 ∧
      Function.Injective
        (fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n₀ (Work.BoxShrink.Pinch.par ψ q))) x)) :
    ∃ (y : ℝ × ℝ → LeanEval.KnotTheory.PardonDistortion.R3 → ℝ × ℝ) (ε δ : ℝ),
      0 < ε ∧ 0 < δ ∧
      (∀ x ∈ X, y x n₀ = x) ∧
      (∀ x ∈ X, ∀ n : LeanEval.KnotTheory.PardonDistortion.R3, ‖n - n₀‖ < δ → DifferentiableAt ℝ (y x) n) ∧
      (∀ x ∈ X, ∀ n : LeanEval.KnotTheory.PardonDistortion.R3, ‖n - n₀‖ < δ →
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q)) (y x n) = 0) ∧
      (∀ x ∈ X, ∀ n : LeanEval.KnotTheory.PardonDistortion.R3, ‖n - n₀‖ < δ → ∀ p : ℝ × ℝ, ‖p - x‖ < ε →
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q)) p = 0 → p = y x n) := by
  classical
  have hloc : ∀ x : {x // x ∈ X}, ∃ (Y : R3 → ℝ × ℝ) (δ ε : ℝ), 0 < δ ∧ 0 < ε ∧
      Y n₀ = x.1 ∧
      (∀ n : R3, ‖n - n₀‖ < δ →
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q)) (Y n) = 0) ∧
      (∀ n : R3, ‖n - n₀‖ < δ → ∀ p : ℝ × ℝ, ‖p - x.1‖ < ε →
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q)) p = 0 → p = Y n) ∧
      (∀ n : R3, ‖n - n₀‖ < δ → DifferentiableAt ℝ Y n) := by
    intro x
    have h0 : gradF ψ (n₀, x.1) = 0 := (hX x.1 x.2).1
    have hInv : ((fderiv ℝ (gradF ψ) (n₀, x.1)) ∘L
        ContinuousLinearMap.inr ℝ R3 (ℝ × ℝ)).IsInvertible := by
      rw [gradF_fderiv_inr ψ n₀ x.1]
      exact hessian_isInvertible _ (hX x.1 x.2).2
    exact iftBranchExists (gradF_contDiff_one ψ) h0 hInv
  choose Y D E hspec using hloc
  by_cases hne : X.Nonempty
  · have hatt : X.attach.Nonempty := by
      obtain ⟨x, hx⟩ := hne
      exact ⟨⟨x, hx⟩, Finset.mem_attach X ⟨x, hx⟩⟩
    refine ⟨fun x => if h : x ∈ X then Y ⟨x, h⟩ else fun _ => x,
      X.attach.inf' hatt E, X.attach.inf' hatt D, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]; exact fun i _ => (hspec i).2.1
    · rw [Finset.lt_inf'_iff]; exact fun i _ => (hspec i).1
    · intro x hx
      simpa [dif_pos hx] using (hspec ⟨x, hx⟩).2.2.1
    · intro x hx n hn
      simpa [dif_pos hx] using (hspec ⟨x, hx⟩).2.2.2.2.2 n
        (lt_of_lt_of_le hn (Finset.inf'_le D (Finset.mem_attach X ⟨x, hx⟩)))
    · intro x hx n hn
      simpa [dif_pos hx] using (hspec ⟨x, hx⟩).2.2.2.1 n
        (lt_of_lt_of_le hn (Finset.inf'_le D (Finset.mem_attach X ⟨x, hx⟩)))
    · intro x hx n hn p hp hcrit
      simpa [dif_pos hx] using (hspec ⟨x, hx⟩).2.2.2.2.1 n
        (lt_of_lt_of_le hn (Finset.inf'_le D (Finset.mem_attach X ⟨x, hx⟩))) p
        (lt_of_lt_of_le hp (Finset.inf'_le E (Finset.mem_attach X ⟨x, hx⟩))) hcrit
  · refine ⟨fun x _ => x, 1, 1, one_pos, one_pos, ?_, ?_, ?_, ?_⟩
    · intro x hx; exact absurd ⟨x, hx⟩ hne
    · intro x hx; exact absurd ⟨x, hx⟩ hne
    · intro x hx; exact absurd ⟨x, hx⟩ hne
    · intro x hx; exact absurd ⟨x, hx⟩ hne

end

end Work.Drive.EpsForm
