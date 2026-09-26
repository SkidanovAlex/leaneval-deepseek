import Mathlib
import Submission.Work.Drive.EpsForm.goodHeight_exists
import Submission.Work.Embedding.smooth_implicit_function_nhd

namespace Work.Drive.Mono.Band

open scoped RealInnerProductSpace
open scoped _root_.Topology
open LeanEval.KnotTheory.PardonDistortion

noncomputable section

/-! ## The gradient map of the height family

The joint height `(n, q) ↦ ⟪n, par ψ q⟫` is `C²` as a function of both variables, and its partial
derivative in `q` — the *gradient map* `bandGrad ψ` — is therefore `C¹` as a function on `R3 × ℝ²`.
The critical points of the height in direction `n` are the zeros of `bandGrad ψ (n, ·)`.

The point of packaging this way is that the implicit function theorem can be applied to
`bandGrad ψ` at a nondegenerate critical point `(n₀, x)`, the partial derivative being the Hessian of
the height, which is invertible there.  Mathlib's implicit function theorem (`ContDiffAt.implicitFunction`)
provides a branch which is *differentiable* at the base point, and we need the branch to be `C¹` on
a whole neighbourhood of `n₀` (`critBranch_euclid`), so we transport the smoothness from the
implicit function at each nearby point, exactly as `Work.Drive.EpsForm.iftBranchExists` does for
`C⁰`-smoothness. -/

/-- The joint height `(n, q) ↦ ⟪n, par ψ q⟫` of the parametrised surface. -/
def bandH (ψ : Submission.Diffeo) : R3 × (ℝ × ℝ) → ℝ :=
  fun v => inner ℝ v.1 (Work.BoxShrink.Pinch.par ψ v.2)

/-- The gradient in the parameter `q` of the height in direction `n`, as a function of `(n, q)`. -/
def bandGrad (ψ : Submission.Diffeo) : R3 × (ℝ × ℝ) → (ℝ × ℝ →L[ℝ] ℝ) :=
  fun v => fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v.1 (Work.BoxShrink.Pinch.par ψ q)) v.2

lemma bandGrad_apply (ψ : Submission.Diffeo) (n : R3) (q : ℝ × ℝ) :
    bandGrad ψ (n, q) = fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n) q := rfl

lemma bandH_contDiff (ψ : Submission.Diffeo) : ContDiff ℝ 2 (bandH ψ) := by
  have h1 : ContDiff ℝ 2 (fun v : R3 × (ℝ × ℝ) => (innerSL ℝ) v.1) :=
    (ContinuousLinearMap.contDiff (innerSL ℝ) : ContDiff ℝ 2 (fun x : R3 => (innerSL ℝ) x)).comp
      contDiff_fst
  have h2 : ContDiff ℝ 2 (fun v : R3 × (ℝ × ℝ) => Work.BoxShrink.Pinch.par ψ v.2) :=
    ((Work.BoxShrink.Pinch.par_contDiff ψ).of_le (WithTop.coe_le_coe.mpr le_top)).comp contDiff_snd
  exact h1.clm_apply h2

/-- The partial derivative of a two-variable function in its second variable, as a linear map. -/
lemma fderiv_comp_inr_band {E₁ E₂ Y : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {G : E₁ × E₂ → Y} {v : E₁ × E₂} (hd : DifferentiableAt ℝ G v) :
    (fderiv ℝ G v) ∘L (ContinuousLinearMap.inr ℝ E₁ E₂)
      = fderiv ℝ (fun q : E₂ => G (v.1, q)) v.2 := by
  have h : HasFDerivAt G (fderiv ℝ G v) v := hd.hasFDerivAt
  have h2 := h.comp v.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) (E := E₁) (F := E₂) v.1 v.2)
  exact h2.fderiv.symm

lemma bandGrad_eq (ψ : Submission.Diffeo) :
    bandGrad ψ = fun v => (fderiv ℝ (bandH ψ) v) ∘L ContinuousLinearMap.inr ℝ R3 (ℝ × ℝ) := by
  funext v
  exact (fderiv_comp_inr_band (G := bandH ψ) (v := v)
    ((bandH_contDiff ψ).differentiable (by norm_num) v)).symm

lemma bandGrad_contDiff_one (ψ : Submission.Diffeo) : ContDiff ℝ 1 (bandGrad ψ) := by
  rw [bandGrad_eq]
  exact ((bandH_contDiff ψ).fderiv_right (m := 1) (n := 2) le_rfl).clm_comp contDiff_const

lemma bandGrad_fderiv_inr (ψ : Submission.Diffeo) (n₀ : R3) (x : ℝ × ℝ) :
    (fderiv ℝ (bandGrad ψ) (n₀, x)) ∘L ContinuousLinearMap.inr ℝ R3 (ℝ × ℝ)
      = fderiv ℝ (fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n₀)) x := by
  have h := fderiv_comp_inr_band (G := bandGrad ψ) (v := (n₀, x))
    ((bandGrad_contDiff_one ψ).differentiable (by norm_num) (n₀, x))
  rw [h]
  rfl

/-! ## The `C¹` branch of critical points, on a whole ball -/

/-- **Local branches of the critical points of the height, smooth on a ball.**  At a nondegenerate
critical point `x` of the height in direction `n₀` there is a ball `‖n - n₀‖ < δ` on which the
height in direction `n` has a unique critical point within distance `ε` of `x`, and this critical
point depends `C¹` on `n`.  (The statement is the ball version of the implicit function theorem for
the gradient map `bandGrad ψ`.) -/
theorem critBranch_c1 (ψ : Submission.Diffeo) (n₀ : R3) {x : ℝ × ℝ}
    (hx0 : fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n₀) x = 0)
    (hx1 : Function.Injective
      (fderiv ℝ (fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n₀)) x)) :
    ∃ (y : R3 → ℝ × ℝ) (δ ε : ℝ), 0 < δ ∧ 0 < ε ∧ y n₀ = x ∧
      (∀ n : R3, ‖n - n₀‖ < δ → fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n) (y n) = 0) ∧
      (∀ n : R3, ‖n - n₀‖ < δ → ∀ q : ℝ × ℝ, ‖q - x‖ < ε →
        fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n) q = 0 → q = y n) ∧
      (∀ n : R3, ‖n - n₀‖ < δ → ContDiffAt ℝ 1 y n) := by
  classical
  have hF : ContDiff ℝ 1 (bandGrad ψ) := bandGrad_contDiff_one ψ
  have h0 : bandGrad ψ (n₀, x) = 0 := by
    rw [bandGrad_apply]; exact hx0
  have hInv : ((fderiv ℝ (bandGrad ψ) (n₀, x)) ∘L
      ContinuousLinearMap.inr ℝ R3 (ℝ × ℝ)).IsInvertible := by
    rw [bandGrad_fderiv_inr ψ n₀ x]
    exact Work.Drive.EpsForm.hessian_isInvertible _ hx1
  have hnz : (1 : WithTop ℕ∞) ≠ 0 := one_ne_zero
  have hct : ContDiffAt ℝ 1 (bandGrad ψ) (n₀, x) := hF.contDiffAt
  set Y : R3 → ℝ × ℝ := hct.implicitFunction hnz hInv with hY
  have hYa : Y n₀ = x := by rw [hY]; exact hct.implicitFunction_apply_self hnz hInv
  -- existence of the critical point on a ball
  have hex : ∀ᶠ n in 𝓝 n₀, bandGrad ψ (n, Y n) = 0 := by
    filter_upwards [hct.eventually_apply_implicitFunction hnz hInv] with n hn
    rw [hn, h0]
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.mem_nhds_iff.mp hex
  have key₁ : ∀ n : R3, ‖n - n₀‖ < δ₁ → bandGrad ψ (n, Y n) = 0 := by
    intro n hn
    exact hδ₁' (Metric.mem_ball.mpr (by rwa [dist_eq_norm]))
  -- uniqueness in a ball
  have hu : ∀ᶠ v in 𝓝 (n₀, x), bandGrad ψ v = 0 ↔ Y v.1 = v.2 := by
    rw [hY]
    filter_upwards [hct.eventually_apply_eq_iff_implicitFunction hnz hInv] with v hv
    rw [← h0]; exact hv
  obtain ⟨ρ, hρ, hρ'⟩ := Metric.mem_nhds_iff.mp hu
  have key₂ : ∀ n : R3, ∀ q : ℝ × ℝ, ‖n - n₀‖ < ρ → ‖q - x‖ < ρ →
      bandGrad ψ (n, q) = 0 → Y n = q := by
    intro n q hn hq hFq
    have hmem : (n, q) ∈ Metric.ball (n₀, x) ρ := by
      rw [Metric.mem_ball, Prod.dist_eq, dist_eq_norm, dist_eq_norm]
      exact max_lt hn hq
    exact (hρ' hmem).mp hFq
  -- continuity of `Y` at the base point
  have hcy : ContinuousAt Y n₀ := by
    rw [hY]
    exact (hct.hasStrictFDerivAt_implicitFunction hnz hInv).continuousAt
  -- invertibility of the partial derivative is an open condition
  have hcontT : Continuous (fun v : R3 × (ℝ × ℝ) =>
      (fderiv ℝ (bandGrad ψ) v) ∘L ContinuousLinearMap.inr ℝ R3 (ℝ × ℝ)) := by
    have h1 : Continuous (fun v : R3 × (ℝ × ℝ) =>
        (ContinuousLinearMap.compL ℝ (ℝ × ℝ) (R3 × (ℝ × ℝ)) (ℝ × ℝ →L[ℝ] ℝ))
          (fderiv ℝ (bandGrad ψ) v)) :=
      (ContinuousLinearMap.compL ℝ (ℝ × ℝ) (R3 × (ℝ × ℝ)) (ℝ × ℝ →L[ℝ] ℝ)).continuous.comp
        (hF.continuous_fderiv hnz)
    exact h1.clm_apply continuous_const
  have hopen : ∀ᶠ v in 𝓝 (n₀, x),
      ((fderiv ℝ (bandGrad ψ) v) ∘L ContinuousLinearMap.inr ℝ R3 (ℝ × ℝ)).IsInvertible :=
    hcontT.continuousAt.preimage_mem_nhds
      ((Work.Embedding.isOpen_isInvertible (E := ℝ × ℝ) (F := ℝ × ℝ →L[ℝ] ℝ)).mem_nhds hInv)
  obtain ⟨ρ₂, hρ₂, hρ₂'⟩ := Metric.mem_nhds_iff.mp hopen
  have key₃ : ∀ n : R3, ∀ q : ℝ × ℝ, ‖n - n₀‖ < ρ₂ → ‖q - x‖ < ρ₂ →
      ((fderiv ℝ (bandGrad ψ) (n, q)) ∘L ContinuousLinearMap.inr ℝ R3 (ℝ × ℝ)).IsInvertible := by
    intro n q hn hq
    exact hρ₂' (by
      rw [Metric.mem_ball, Prod.dist_eq, dist_eq_norm, dist_eq_norm]
      exact max_lt hn hq)
  -- the branch stays in a small ball
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.continuousAt_iff.mp hcy (min ρ ρ₂ / 2) (by positivity)
  have key₄ : ∀ n : R3, ‖n - n₀‖ < δ₂ → ‖Y n - x‖ < min ρ ρ₂ / 2 := by
    intro n hn
    have h := hδ₂' (by rwa [dist_eq_norm])
    rwa [dist_eq_norm, hYa] at h
  refine ⟨Y, min δ₁ (min ρ (min ρ₂ δ₂)), min ρ ρ₂,
    lt_min hδ₁ (lt_min hρ (lt_min hρ₂ hδ₂)), lt_min hρ hρ₂, hYa, ?_, ?_, ?_⟩
  · intro n hn
    exact key₁ n (lt_of_lt_of_le hn (min_le_left _ _))
  · intro n hn q hq hFq
    have hn' : ‖n - n₀‖ < ρ := lt_of_lt_of_le hn (le_trans (min_le_right _ _) (min_le_left _ _))
    have hq' : ‖q - x‖ < ρ := lt_of_lt_of_le hq (min_le_left _ _)
    exact (key₂ n q hn' hq' hFq).symm
  · intro n hn
    have hnρ : ‖n - n₀‖ < ρ := lt_of_lt_of_le hn (le_trans (min_le_right _ _) (min_le_left _ _))
    have hnρ₂ : ‖n - n₀‖ < ρ₂ :=
      lt_of_lt_of_le hn (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hnδ₂ : ‖n - n₀‖ < δ₂ :=
      lt_of_lt_of_le hn (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
    have hyb : ‖Y n - x‖ < min ρ ρ₂ / 2 := key₄ n hnδ₂
    have hybρ : ‖Y n - x‖ < ρ := lt_of_lt_of_le hyb (by nlinarith [min_le_left ρ ρ₂, hρ])
    have hybρ₂ : ‖Y n - x‖ < ρ₂ := lt_of_lt_of_le hyb (by nlinarith [min_le_right ρ ρ₂, hρ₂])
    have hInvT : ((fderiv ℝ (bandGrad ψ) (n, Y n)) ∘L
        ContinuousLinearMap.inr ℝ R3 (ℝ × ℝ)).IsInvertible := key₃ n (Y n) hnρ₂ hybρ₂
    have hFn : bandGrad ψ (n, Y n) = 0 := key₁ n (lt_of_lt_of_le hn (min_le_left _ _))
    have hctn : ContDiffAt ℝ 1 (bandGrad ψ) (n, Y n) := hF.contDiffAt
    set Y₁ : R3 → ℝ × ℝ := hctn.implicitFunction hnz hInvT with hY₁
    have hY₁n : Y₁ n = Y n := by rw [hY₁]; exact hctn.implicitFunction_apply_self hnz hInvT
    have hcd₁ : ContDiffAt ℝ 1 Y₁ n := by
      rw [hY₁]; exact hctn.contDiffAt_implicitFunction hnz hInvT
    have hcont₁ : ContinuousAt Y₁ n := hcd₁.continuousAt
    have hagree : Y =ᶠ[𝓝 n] Y₁ := by
      have hA : ∀ᶠ m in 𝓝 n, bandGrad ψ (m, Y₁ m) = 0 := by
        filter_upwards [hctn.eventually_apply_implicitFunction hnz hInvT] with m hm
        rw [hm, hFn]
      have hB : ∀ᶠ m in 𝓝 n, ‖m - n₀‖ < ρ := by
        have hpos : 0 < ρ - ‖n - n₀‖ := sub_pos.mpr hnρ
        filter_upwards [Metric.ball_mem_nhds n hpos] with m hm
        have hm' : ‖m - n‖ < ρ - ‖n - n₀‖ := by
          simpa [Metric.mem_ball, dist_eq_norm, dist_comm] using hm
        have hsub : m - n₀ = (m - n) + (n - n₀) := by abel
        calc ‖m - n₀‖ = ‖(m - n) + (n - n₀)‖ := by rw [hsub]
          _ ≤ ‖m - n‖ + ‖n - n₀‖ := norm_add_le _ _
          _ < ρ := by linarith
      have hC : ∀ᶠ m in 𝓝 n, ‖Y₁ m - x‖ < ρ := by
        have hmem : Y₁ n ∈ Metric.ball x ρ := by
          rw [Metric.mem_ball, dist_eq_norm, hY₁n]; exact hybρ
        filter_upwards [hcont₁.eventually (Metric.isOpen_ball.mem_nhds hmem)] with m hm
        rwa [dist_eq_norm] at hm
      filter_upwards [hA, hB, hC] with m hmA hmB hmC
      exact key₂ m (Y₁ m) hmB hmC hmA
    exact hcd₁.congr_of_eventuallyEq hagree

end

/-- Local branches of the critical points of the height family `n ↦ ⟪n, par ψ ·⟫` at a
nondegenerate critical point `x` of the height in direction `n₀`: there is a `C¹` branch
`y : R3 → ℝ × ℝ` on a neighbourhood `U` of `n₀` with `y n₀ = x`, whose values are critical points
of the height in direction `n`, and which is the unique critical point of the height in direction
`n` in the ball of radius `r` around `x`. -/
theorem critBranch_euclid (ψ : Submission.Diffeo) (n₀ : LeanEval.KnotTheory.PardonDistortion.R3) {x : ℝ × ℝ}
    (hx0 : fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n₀) x = 0)
    (hx1 : Function.Injective
      (fderiv ℝ (fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n₀)) x)) :
    ∃ (U : Set LeanEval.KnotTheory.PardonDistortion.R3)
      (y : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ × ℝ) (r : ℝ),
      IsOpen U ∧ n₀ ∈ U ∧ 0 < r ∧ y n₀ = x ∧ ContDiffOn ℝ 1 y U ∧
      (∀ n ∈ U, fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n) (y n) = 0) ∧
      (∀ n ∈ U, ∀ p : ℝ × ℝ, ‖p - x‖ < r →
        fderiv ℝ (Work.Drive.EpsForm.heightOf ψ n) p = 0 → p = y n) := by
  obtain ⟨y, δ, ε, hδ, hε, hy0, hcrit, huniq, hcd⟩ := critBranch_c1 ψ n₀ hx0 hx1
  refine ⟨Metric.ball n₀ δ, y, ε, Metric.isOpen_ball, Metric.mem_ball_self hδ, hε, hy0, ?_, ?_, ?_⟩
  · intro n hn
    exact (hcd n (by rwa [Metric.mem_ball, dist_eq_norm] at hn)).contDiffWithinAt
  · intro n hn
    rw [Metric.mem_ball, dist_eq_norm] at hn
    exact hcrit n hn
  · intro n hn p hp hcritp
    rw [Metric.mem_ball, dist_eq_norm] at hn
    exact huniq n hn p hp hcritp

end Work.Drive.Mono.Band
