import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Interfaces.Fatou
import Submission.Work.Interfaces.FatouNarrow

/-!
# A gate Fatou coordinate is locally Lipschitz

Shishikura, §4.2: the perturbed Fatou coordinate `Φ` of the lift `F_f = liftF u σ α` of a
perturbation `f` is *Lipschitz* on every ball (with a universal constant) contained in a gate
region `Qp Ξ' α`, with a constant depending only on the universal constants of
`FatouDerivEstimate` (Lemma A.2.4(i)).

The content is `FatouDerivEstimate` (`hF.2.2.2.2.1`), which at a point `z₀` of the gate and a
radius `R` with `ball z₀ R ⊆ Q` gives

  `‖deriv Φ z₀ - 1 / v z₀‖ ≤ C₁ * (1 / R² + ‖deriv v z₀‖)`,   `v := F - id`,

while `NearTranslationOn F Q` bounds `‖v z₀ - 1‖ ≤ 1/32` (so `‖1/v z₀‖ ≤ 32/31`) and
`‖deriv v z₀‖ = ‖deriv F z₀ - 1‖ ≤ 1/32`; with `R ≥ R₁` this makes `‖deriv Φ‖` uniformly bounded by
a universal `C` (see `gate_deriv_bound` below), and the mean value theorem on the segment `[x,y]`
(with `ball z R ⊆ Q` at every point `z` of it) yields `‖Φ x - Φ y‖ ≤ C ‖x - y‖`.
-/

open Set Metric

namespace Work.Analysis.PertCrux

/-- **Pointwise bound for the derivative of a Fatou coordinate of a near-translation.**

If `F` is a near-translation on `Q` (`‖F z - (z+1)‖ ≤ 1/32`, `‖deriv F z - 1‖ ≤ 1/32`), `Φ` is a
Fatou coordinate of `F` on `Q`, and the ball of radius `R ≥ R₁` around `z` still lies in `Q`, then
`‖deriv Φ z‖ ≤ C` with universal constants `R₁, C` (those of `FatouDerivEstimate`).

Proof: apply `FatouDerivEstimate` to `v := F - id` on the ball `ball z R`.  The hypotheses of the
estimate are exactly the near-translation bounds (`‖v z' - 1‖ = ‖F z' - (z' + 1)‖ ≤ 1/32 < 1/4`)
and the Abel equation `Φ (z' + v z') = Φ (z' + (F z' - z')) = Φ (F z') = Φ z' + 1`
(`F` maps the ball into `Q` by hypothesis).  Then
`‖deriv Φ z‖ ≤ (C₁ (1/R² + 1/32) + 32/31)` using `‖1/v z‖ ≤ 32/31`, which follows from
`‖v z‖ ≥ 1 - 1/32 = 31/32`, and `1/R² ≤ 1/R₁²`. -/
theorem gate_deriv_bound (hF : MandelDim.FatouStatement) :
    ∃ R₁ C : ℝ, 0 < R₁ ∧ 0 < C ∧
      ∀ {F Φ : ℂ → ℂ} {Q : Set ℂ} {R : ℝ} {z : ℂ},
        R₁ ≤ R → MandelDim.NearTranslationOn F Q → MandelDim.IsFatouCoordOn F Φ Q →
        Metric.ball z R ⊆ Q → ‖deriv Φ z‖ ≤ C := by
  obtain ⟨R₁, C₁, _, hR₁, hC₁, _, hD⟩ := hF.2.2.2.2.1
  refine ⟨R₁, C₁ * (1 / R₁ ^ 2 + 1 / 32) + 32 / 31, hR₁, ?_, ?_⟩
  · have h1 : (0 : ℝ) < 1 / R₁ ^ 2 + 1 / 32 := by positivity
    nlinarith [mul_pos hC₁ h1]
  · intro F Φ Q R z hR hN hΦ hball
    have hRpos : 0 < R := lt_of_lt_of_le hR₁ hR
    have hzball : z ∈ Metric.ball z R := Metric.mem_ball_self hRpos
    have hzQ : z ∈ Q := hball hzball
    obtain ⟨hNdiff, hNest⟩ := hN
    obtain ⟨hΦdiff, hΦinj, hΦabel⟩ := hΦ
    have hFball : DifferentiableOn ℂ F (Metric.ball z R) := hNdiff.mono fun w hw => hball hw
    have hFz : DifferentiableAt ℂ F z :=
      (hFball z hzball).differentiableAt (Metric.ball_mem_nhds z hRpos)
    set v : ℂ → ℂ := fun w => F w - w with hv
    have hvdiff : DifferentiableOn ℂ v (Metric.ball z R) := by
      rw [hv]; exact hFball.sub differentiableOn_id
    have hsmall : ∀ w ∈ Metric.ball z R, ‖v w - 1‖ < 1 / 4 := by
      intro w hw
      have hle : ‖v w - 1‖ ≤ 1 / 32 := by
        have heq : v w - 1 = F w - (w + 1) := by rw [hv]; simp only; ring
        rw [heq]; exact (hNest w (hball hw)).1
      linarith
    have habel : ∀ w ∈ Metric.ball z R, w + v w ∈ Metric.ball z R → Φ (w + v w) = Φ w + 1 := by
      intro w hw hwv
      have hEq : w + v w = F w := by rw [hv]; simp only; ring
      have hFwQ : F w ∈ Q := hEq ▸ hball hwv
      rw [hEq]; exact hΦabel w (hball hw) hFwQ
    have hb1 : ‖deriv Φ z - 1 / v z‖ ≤ C₁ * (1 / R ^ 2 + ‖deriv v z‖) :=
      (hD Φ v z R hR (hΦdiff.mono fun w hw => hball hw)
        (hΦinj.mono fun w hw => hball hw) hvdiff hsmall habel).1
    have hderivv : ‖deriv v z‖ ≤ 1 / 32 := by
      have h1 : deriv v z = deriv F z - 1 := by
        rw [hv]
        change deriv (F - id) z = deriv F z - 1
        rw [deriv_sub hFz differentiableAt_id, deriv_id]
      rw [h1]; exact (hNest z hzQ).2
    have hvz : (31 : ℝ) / 32 ≤ ‖v z‖ := by
      have h := norm_sub_norm_le (1 : ℂ) (1 - v z)
      have h' : ‖(1 : ℂ) - (1 - v z)‖ = ‖v z‖ := by congr 1; ring
      have h'' : ‖(1 : ℂ) - v z‖ = ‖v z - 1‖ := norm_sub_rev _ _
      have hle : ‖v z - 1‖ ≤ 1 / 32 := by
        have heq : v z - 1 = F z - (z + 1) := by rw [hv]; simp only; ring
        rw [heq]; exact (hNest z hzQ).1
      rw [h', h''] at h
      simp only [norm_one] at h
      linarith
    have h1v : ‖1 / v z‖ ≤ 32 / 31 := by
      rw [norm_div, norm_one]
      have hpos : (0 : ℝ) < 31 / 32 := by norm_num
      calc (1 : ℝ) / ‖v z‖ ≤ 1 / (31 / 32) := one_div_le_one_div_of_le hpos hvz
        _ = 32 / 31 := by norm_num
    have hsq : R₁ ^ 2 ≤ R ^ 2 := by nlinarith [hR, hR₁]
    have hR1sq : 1 / R ^ 2 ≤ 1 / R₁ ^ 2 := one_div_le_one_div_of_le (pow_pos hR₁ 2) hsq
    have hmain : ‖deriv Φ z‖ ≤ C₁ * (1 / R ^ 2 + ‖deriv v z‖) + ‖1 / v z‖ := by
      have hEq : deriv Φ z = (deriv Φ z - 1 / v z) + 1 / v z := by ring
      rw [hEq]
      exact le_trans (norm_add_le _ _) (add_le_add hb1 le_rfl)
    have hstep : C₁ * (1 / R ^ 2 + ‖deriv v z‖) ≤ C₁ * (1 / R₁ ^ 2 + 1 / 32) :=
      mul_le_mul_of_nonneg_left (add_le_add hR1sq hderivv) hC₁.le
    linarith

/-- **A gate Fatou coordinate is locally Lipschitz with a universal constant.**
`FatouDerivEstimate` (a field of `FatouStatement`) applied at every point of the segment `[x,y]`
with a ball of radius `R ≥ R₁` inside the gate `Qp Ξ' α` bounds `deriv Φ` by
`1/|v| + C₁(1/R² + ‖deriv v‖)` with `v = liftF u σ α - id`; on the gate `NearTranslationL1`
gives `‖v - 1‖ ≤ 1/32` and `‖deriv v‖ ≤ 1/32`, so `‖deriv Φ‖ ≤ C` uniformly, and integrating
along the segment gives the bound below. -/
theorem gate_fatou_lipschitz (hF : MandelDim.FatouStatement) :
    ∃ R₁ C : ℝ, 0 < R₁ ∧ 0 < C ∧
      ∀ {Ξ' : ℝ} {σ α : ℂ} {u : ℂ → ℂ} {Φ : ℂ → ℂ} {R : ℝ} {x y : ℂ},
      1 + 64 * Real.pi ≤ Ξ' →
      R₁ ≤ R →
      MandelDim.QAdm (some (Ξ' : ℂ)) (some (-(Ξ' : ℂ) + 1 / α)) →
      MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qp Ξ' α) →
      MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φ (Work.Pert.Qp Ξ' α) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        Metric.closedBall ((1 - t) * x + t * y) R ⊆ Work.Pert.Qp Ξ' α) →
      ‖Φ x - Φ y‖ ≤ C * ‖x - y‖ := by
  obtain ⟨R₁, C, hR₁, hC, hbnd⟩ := gate_deriv_bound hF
  refine ⟨R₁, C, hR₁, hC, ?_⟩
  intro Ξ' σ α u Φ R x y _hΞ' hR _hAdm hNearL1 hΦ hseg
  have hNear : MandelDim.NearTranslationOn (Work.Pert.liftF u σ α) (Work.Pert.Qp Ξ' α) :=
    hNearL1.1
  have hRpos : 0 < R := lt_of_lt_of_le hR₁ hR
  -- the *open* ball of radius `R` around every point of the segment lies in the gate
  have hseg' : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Metric.ball ((1 - t) * x + t * y) R ⊆ Work.Pert.Qp Ξ' α :=
    fun t ht z hz => hseg t ht (Metric.ball_subset_closedBall hz)
  -- every point of the segment is of the form `(1 - t) * x + t * y`, `t ∈ [0,1]`
  have hparam : ∀ z ∈ segment ℝ x y, ∃ t ∈ Set.Icc (0 : ℝ) 1, z = (1 - t) * x + t * y := by
    intro z hz
    rw [segment_eq_image ℝ x y] at hz
    obtain ⟨t, ht, htz⟩ := hz
    refine ⟨t, ht, ?_⟩
    rw [← htz]
    simp only [Complex.real_smul]
    push_cast
    ring
  have key : ∀ z ∈ segment ℝ x y, DifferentiableAt ℂ Φ z ∧ ‖deriv Φ z‖ ≤ C := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := hparam z hz
    exact ⟨(hΦ.1.mono (hseg' t ht)).differentiableAt (Metric.ball_mem_nhds _ hRpos),
      hbnd hR hNear hΦ (hseg' t ht)⟩
  -- mean value theorem along the segment
  have hMVT := Convex.norm_image_sub_le_of_norm_deriv_le (f := Φ) (s := segment ℝ x y)
    (fun z hz => (key z hz).1) (fun z hz => (key z hz).2) (convex_segment x y)
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  rw [norm_sub_rev (Φ x) (Φ y), norm_sub_rev x y]
  exact hMVT

end Work.Analysis.PertCrux
