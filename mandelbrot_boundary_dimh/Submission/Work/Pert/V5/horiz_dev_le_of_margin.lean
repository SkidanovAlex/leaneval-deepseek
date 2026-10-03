import Mathlib
import Submission.Work.Pert.V5.Basics
import Submission.Work.Pert.deriv_Phi_close_on_gate
import Submission.Work.Pert.V5.dev_horiz_le

set_option linter.unusedVariables false

namespace Work.Pert.V5

theorem horiz_dev_le_of_margin {Ξ rr M Rde C₂ : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {s a b κ : ℝ}
    (hF : MandelDim.FatouStatement)
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M)
    (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hRde : 0 < Rde) (hC₂ : 0 < C₂)
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr)
    (hDE : ∀ (Φ v : ℂ → ℂ) (z : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ (Metric.ball z R) → Set.InjOn Φ (Metric.ball z R) →
      DifferentiableOn ℂ v (Metric.ball z R) → (∀ w ∈ Metric.ball z R, ‖v w - 1‖ < 1 / 4) →
      (∀ w ∈ Metric.ball z R, w + v w ∈ Metric.ball z R → Φ (w + v w) = Φ w + 1) →
      ‖deriv Φ z - 1 / v z‖ ≤ C₂ / R)
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    (hab : a ≤ b) (hκ : 0 < κ) (hκRde : Rde ≤ κ / Real.sqrt 2)
    (hmargin : ∀ ξ ∈ Set.Icc a b,
      κ ≤ min (Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (s : ℂ) * Complex.I))
               (Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (s : ℂ) * Complex.I))) :
    ‖(Φm ((b : ℂ) + (s : ℂ) * Complex.I) - ((b : ℂ) + (s : ℂ) * Complex.I))
        - (Φm ((a : ℂ) + (s : ℂ) * Complex.I) - ((a : ℂ) + (s : ℂ) * Complex.I))‖
      ≤ (C₂ * Real.sqrt 2 / κ + 1 / 31) * (b - a) := by
  -- `D w = Φm w - w` is Lipschitz along the horizontal segment at height `s`, with the constant
  -- `C₂ √2 / κ + 1/31`: at each point `w` of the segment the margin `min (mgA) (mgB)` is `≥ κ`, so
  -- the ball of radius `κ / √2 ≤ min (mgA) (mgB) / √2` around `w` lies in the gate; the derivative
  -- estimate `hDE` may be applied there with `v := liftF u σ α - id` (the vertical displacement map
  -- of the near-translation), and `‖1/v - 1‖ ≤ 1/31` because `‖v - 1‖ ≤ 1/32` on the gate.
  have hsqrt2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hRpos : 0 < κ / Real.sqrt 2 := div_pos hκ hsqrt2pos
  -- every point of the segment is in the gate
  have hmem : ∀ ξ ∈ Set.Icc a b, ((ξ : ℂ) + (s : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α := by
    intro ξ hξ
    have hm := hmargin ξ hξ
    have hA : 0 < Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (s : ℂ) * Complex.I) :=
      lt_of_lt_of_le hκ (le_trans hm (min_le_left _ _))
    have hB : 0 < Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (s : ℂ) * Complex.I) :=
      lt_of_lt_of_le hκ (le_trans hm (min_le_right _ _))
    exact (Work.Pert.V5.mem_Qm_iff_mg).mpr ⟨hA, hB⟩
  -- the ball of radius `κ / √2` around a point of the segment is inside the gate
  have hball : ∀ ξ ∈ Set.Icc a b,
      Metric.ball ((ξ : ℂ) + (s : ℂ) * Complex.I) (κ / Real.sqrt 2) ⊆ Work.Pert.Qm Ξ α := by
    intro ξ hξ
    have hw := hmem ξ hξ
    have hm := hmargin ξ hξ
    have hle : κ / Real.sqrt 2 ≤
        min (Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (s : ℂ) * Complex.I))
            (Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (s : ℂ) * Complex.I)) / Real.sqrt 2 :=
      div_le_div_of_nonneg_right hm (le_of_lt hsqrt2pos)
    exact subset_trans (Metric.ball_subset_ball hle) (Work.Pert.V5.ball_in_gate hw)
  -- the pointwise bound `‖Φm' - 1‖ ≤ C₂ √2 / κ + 1/31` on the segment
  have hderiv : ∀ ξ ∈ Set.Icc a b,
      ‖deriv Φm ((ξ : ℂ) + (s : ℂ) * Complex.I) - 1‖ ≤ C₂ * Real.sqrt 2 / κ + 1 / 31 := by
    intro ξ hξ
    set w : ℂ := (ξ : ℂ) + (s : ℂ) * Complex.I with hwdef
    have hball' := hball ξ hξ
    have hwQ : w ∈ Work.Pert.Qm Ξ α := hmem ξ hξ
    have hwball : w ∈ Metric.ball w (κ / Real.sqrt 2) := by
      rw [Metric.mem_ball]; simpa using hRpos
    set v : ℂ → ℂ := fun z => Work.Pert.liftF u σ α z - z with hvdef
    have hΦdiff : DifferentiableOn ℂ Φm (Metric.ball w (κ / Real.sqrt 2)) := hΦm.1.mono hball'
    have hΦinj : Set.InjOn Φm (Metric.ball w (κ / Real.sqrt 2)) := hΦm.2.1.mono hball'
    have hvdiff : DifferentiableOn ℂ v (Metric.ball w (κ / Real.sqrt 2)) := by
      have h1 : DifferentiableOn ℂ (fun z : ℂ => Work.Pert.liftF u σ α z - z)
          (Metric.ball w (κ / Real.sqrt 2)) :=
        (hNT.1.1.mono hball').sub differentiableOn_id
      simpa [hvdef] using h1
    have hvnear : ∀ z ∈ Metric.ball w (κ / Real.sqrt 2), ‖v z - 1‖ < 1 / 4 := by
      intro z hz
      have hzQ : z ∈ Work.Pert.Qm Ξ α := hball' hz
      have h1 : ‖v z - 1‖ ≤ 1 / 32 := by
        have heq : v z - 1 = Work.Pert.liftF u σ α z - (z + 1) := by
          simp only [hvdef]; ring
        rw [heq]; exact (hNT.1.2 z hzQ).1
      linarith
    have habel : ∀ z ∈ Metric.ball w (κ / Real.sqrt 2),
        z + v z ∈ Metric.ball w (κ / Real.sqrt 2) → Φm (z + v z) = Φm z + 1 := by
      intro z hz hzv
      have hzQ : z ∈ Work.Pert.Qm Ξ α := hball' hz
      have heq : z + v z = Work.Pert.liftF u σ α z := by simp only [hvdef]; ring
      have hFQ : Work.Pert.liftF u σ α z ∈ Work.Pert.Qm Ξ α := by
        rw [← heq]; exact hball' hzv
      have h := hΦm.2.2 z hzQ hFQ
      rwa [heq]
    have hDE' := hDE Φm v w (κ / Real.sqrt 2) hκRde hΦdiff hΦinj hvdiff hvnear habel
    have hvinv : ‖1 / v w - 1‖ ≤ 1 / 31 := by
      apply Work.Pert.V5.inv_sub_one_le_of_close
      have heq : v w - 1 = Work.Pert.liftF u σ α w - (w + 1) := by simp only [hvdef]; ring
      rw [heq]; exact (hNT.1.2 w hwQ).1
    have hCR : C₂ / (κ / Real.sqrt 2) = C₂ * Real.sqrt 2 / κ := by
      rw [div_eq_mul_one_div, one_div_div, mul_div_assoc]
    have htri : ‖deriv Φm w - 1‖ ≤
        ‖deriv Φm w - 1 / v w‖ + ‖1 / v w - 1‖ := by
      have he : deriv Φm w - 1 = (deriv Φm w - 1 / v w) + (1 / v w - 1) := by ring
      rw [he]; exact norm_add_le _ _
    rw [hCR] at hDE'
    linarith [hDE', hvinv, htri]
  -- the gate is open, so `dev_horiz_le` applies
  have hQopen : IsOpen (Work.Pert.Qm Ξ α) := by
    simpa only [Work.Pert.Qm] using
      Work.Fatou.Qreg.isOpen_Qreg (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ)))
  have hdev := Work.Pert.V5.dev_horiz_le (Φ := Φm) (Q := Work.Pert.Qm Ξ α)
    (s := s) (a := a) (b := b) (g := fun _ : ℝ => C₂ * Real.sqrt 2 / κ + 1 / 31)
    hQopen hab (fun x hx => hmem x hx) hΦm.1 (fun x hx => hderiv x hx) continuousOn_const
  have hint : (∫ x in a..b, (C₂ * Real.sqrt 2 / κ + 1 / 31 : ℝ))
      = (C₂ * Real.sqrt 2 / κ + 1 / 31) * (b - a) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  rw [hint] at hdev
  exact hdev

end Work.Pert.V5
