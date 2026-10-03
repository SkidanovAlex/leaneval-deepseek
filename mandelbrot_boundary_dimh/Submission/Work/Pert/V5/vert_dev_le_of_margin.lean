import Mathlib
import Submission.Work.Pert.V5.Basics
import Submission.Work.Pert.V5.dev_horiz_le
import Submission.Work.Pert.deriv_Phi_close_on_gate

namespace Work.Pert.V5

theorem vert_dev_le_of_margin {Ξ rr M Rde C₂ : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {a s₁ s₂ κ : ℝ}
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
    (hs : s₁ ≤ s₂) (hκ : 0 < κ) (hκRde : Rde ≤ κ / Real.sqrt 2)
    (hmargin : ∀ s ∈ Set.Icc s₁ s₂,
      κ ≤ min (Work.Pert.V5.mgA Ξ α ((a : ℂ) + (s : ℂ) * Complex.I))
               (Work.Pert.V5.mgB Ξ ((a : ℂ) + (s : ℂ) * Complex.I))) :
    ‖(Φm ((a : ℂ) + (s₂ : ℂ) * Complex.I) - ((a : ℂ) + (s₂ : ℂ) * Complex.I))
        - (Φm ((a : ℂ) + (s₁ : ℂ) * Complex.I) - ((a : ℂ) + (s₁ : ℂ) * Complex.I))‖
      ≤ (C₂ * Real.sqrt 2 / κ + 1 / 31) * (s₂ - s₁) := by
  -- ## the gate is open
  have hQopen : IsOpen (Work.Pert.Qm Ξ α) := by
    simpa only [Work.Pert.Qm] using
      Work.Fatou.Qreg.isOpen_Qreg (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ)))
  -- ## every point of the vertical segment lies in the gate
  have hmem : ∀ s ∈ Set.Icc s₁ s₂, ((a : ℂ) + (s : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α := by
    intro s hs'
    have h := hmargin s hs'
    rw [mem_Qm_iff_mg]
    exact ⟨lt_of_lt_of_le (lt_of_lt_of_le hκ h) (min_le_left _ _),
           lt_of_lt_of_le (lt_of_lt_of_le hκ h) (min_le_right _ _)⟩
  -- ## pointwise bound on the derivative deviation, from the Fatou derivative estimate `hDE`
  have hpt : ∀ s ∈ Set.Icc s₁ s₂,
      ‖deriv Φm ((a : ℂ) + (s : ℂ) * Complex.I) - 1‖
        ≤ C₂ * Real.sqrt 2 / κ + 1 / 31 := by
    intro s hs'
    set z : ℂ := (a : ℂ) + (s : ℂ) * Complex.I with hzdef
    have hzQ : z ∈ Work.Pert.Qm Ξ α := hmem s hs'
    have hzmin : κ ≤ min (mgA Ξ α z) (mgB Ξ z) := hmargin s hs'
    have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    -- the gate ball of radius `min (mgA) (mgB) / √2` sits inside the gate
    have hsub : Metric.ball z (min (mgA Ξ α z) (mgB Ξ z) / Real.sqrt 2)
        ⊆ Work.Pert.Qm Ξ α := ball_in_gate hzQ
    -- its radius is at least `Rde`, by the margin hypothesis and `hκRde`
    have hRde_le : Rde ≤ min (mgA Ξ α z) (mgB Ξ z) / Real.sqrt 2 := by
      have h1 : κ / Real.sqrt 2 ≤ min (mgA Ξ α z) (mgB Ξ z) / Real.sqrt 2 :=
        div_le_div_of_nonneg_right hzmin (le_of_lt hsqrt2)
      linarith
    have hderiv := hDE Φm (fun w => Work.Pert.liftF u σ α w - w) z
      (min (mgA Ξ α z) (mgB Ξ z) / Real.sqrt 2) hRde_le
      (hΦm.1.mono hsub) (Set.InjOn.mono hsub hΦm.2.1)
      (((hNT.1.1).mono hsub).sub differentiableOn_id)
      (fun w hw => by
        have hwQ : w ∈ Work.Pert.Qm Ξ α := hsub hw
        have h := (hNT.1.2 w hwQ).1
        have he : (Work.Pert.liftF u σ α w - w) - 1
            = Work.Pert.liftF u σ α w - (w + 1) := by ring
        rw [he]
        linarith)
      (fun w hw hw' => by
        have hwQ : w ∈ Work.Pert.Qm Ξ α := hsub hw
        have he : w + (Work.Pert.liftF u σ α w - w) = Work.Pert.liftF u σ α w := by ring
        rw [he] at hw'
        rw [he]
        exact hΦm.2.2 w hwQ (hsub hw'))
    -- `C₂ / R ≤ C₂ √2 / κ`
    have hCR : C₂ / (min (mgA Ξ α z) (mgB Ξ z) / Real.sqrt 2) ≤ C₂ * Real.sqrt 2 / κ := by
      rw [show C₂ / (min (mgA Ξ α z) (mgB Ξ z) / Real.sqrt 2)
            = C₂ * Real.sqrt 2 / min (mgA Ξ α z) (mgB Ξ z) by field_simp]
      exact div_le_div_of_nonneg_left (by positivity) hκ hzmin
    -- `‖1/(F z - z) - 1‖ ≤ 1/31`
    have hinv : ‖1 / (Work.Pert.liftF u σ α z - z) - 1‖ ≤ 1 / 31 := by
      refine inv_sub_one_le_of_close ?_
      have h := (hNT.1.2 z hzQ).1
      have he : Work.Pert.liftF u σ α z - (z + 1) = Work.Pert.liftF u σ α z - z - 1 := by ring
      rw [← he]
      exact h
    calc ‖deriv Φm z - 1‖
        = ‖(deriv Φm z - 1 / (Work.Pert.liftF u σ α z - z))
             + (1 / (Work.Pert.liftF u σ α z - z) - 1)‖ := by ring_nf
      _ ≤ ‖deriv Φm z - 1 / (Work.Pert.liftF u σ α z - z)‖
            + ‖1 / (Work.Pert.liftF u σ α z - z) - 1‖ := norm_add_le _ _
      _ ≤ C₂ * Real.sqrt 2 / κ + 1 / 31 := add_le_add (le_trans hderiv hCR) hinv
  -- ## integrate the pointwise bound along the vertical segment
  have hdev := Work.Pert.dev_vert_le (Φ := Φm) (Q := Work.Pert.Qm Ξ α) (x := a)
    (y₁ := s₁) (y₂ := s₂) (g := fun _ : ℝ => C₂ * Real.sqrt 2 / κ + 1 / 31)
    hQopen hs hmem hΦm.1 (fun s hs' => hpt s hs') continuousOn_const
  have hint : (∫ s in s₁..s₂, (C₂ * Real.sqrt 2 / κ + 1 / 31 : ℝ))
      = (C₂ * Real.sqrt 2 / κ + 1 / 31) * (s₂ - s₁) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hint] at hdev
  exact hdev

end Work.Pert.V5
