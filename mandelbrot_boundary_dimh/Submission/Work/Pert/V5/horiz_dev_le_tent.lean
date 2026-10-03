import Mathlib
import Submission.Work.Pert.V5.Basics
import Submission.Work.Pert.V5.Facts
import Submission.Work.Pert.V5.tent_integral_gate
import Submission.Work.Pert.V5.dev_horiz_le

/-!
# `Work.Pert.V5.horiz_dev_le_tent`

The **horizontal deviation bound** of the V5 layer in its *tent* form: along a horizontal segment
`x ↦ x + i s`, `x ∈ [a,b]`, lying in the gate `Qm Ξ α` with margins `√2 Rde ≤ min (mgA) (mgB)`
and `1 ≤ min (mgA) (mgB)`,

`‖D (b+is) - D (a+is)‖ ≤ 2^6 (1+Ξ) C₂ (1 + log (2 + (b-a))) + (b-a)/31`,  `D w = Φm w - w`.

There is **no hypothesis on the length** `b - a` (unlike `horiz_dev_le_gen`, whose constant
`1 + log (2+M)` needs `b - a ≤ 6 M`): the logarithm of the corridor length itself appears in the
constant, which is exactly what the tent integral

`∫_a^b dx / min (mgA) (mgB) ≤ 2 log (1 + (b-a))`   (`integral_inv_min_le` with `K = 1`)

produces.  The proof uses only three inputs:

* the Fatou derivative estimate `hDE` at the maximal admissible radius
  `R = min (mgA z) (mgB z) / √2` at each point `z` of the corridor (this is where
  `ball_in_gate` and `√2 Rde ≤ min (mgA) (mgB)` are used), giving
  `‖Φm' - 1/v‖ ≤ C₂ / R` with `v = liftF u σ α - id`;
* the near-translation hypothesis `hNT`, which gives `‖v - 1‖ ≤ 1/32` on the gate, hence
  `‖1/v - 1‖ ≤ 1/31` (`inv_sub_one_le_of_close`) — a *linear* inaccuracy `(b-a)/31`;
* the fundamental estimate `dev_horiz_le` ("displacement ≤ integral of the speed") and the tent
  bound for the integral of `1 / min (mgA) (mgB)`.

The two logarithms are absorbed by the gap between `√2 · 2` and `2^6 (1+Ξ)`.
-/

open Set Metric MeasureTheory
open scoped Topology

namespace Work.Pert.V5

set_option maxHeartbeats 1600000

noncomputable section

/-- **Arithmetic.**  `(C √2) · 2 log (1+L) ≤ 2^6 (1+Ξ) C (1 + log (2+L))` for `C > 0`, `Ξ > 0`,
`L ≥ 0`: the factor `2√2` is absorbed by `2^6`, and `log (1+L) ≤ 1 + log (2+L)`. -/
private lemma tent_log_absorb {C Ξ L : ℝ} (hC : 0 < C) (hΞ : 0 < Ξ) (hL : 0 ≤ L) :
    (C * Real.sqrt 2) * (2 * Real.log (1 + L))
      ≤ 2 ^ 6 * (1 + Ξ) * C * (1 + Real.log (2 + L)) := by
  have hs : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hlog : Real.log (1 + L) ≤ 1 + Real.log (2 + L) := by
    have h1 : Real.log (1 + L) ≤ Real.log (2 + L) :=
      Real.log_le_log (by linarith) (by linarith)
    linarith
  have hlog2 : (0 : ℝ) ≤ 1 + Real.log (2 + L) := by
    have h0 : (0 : ℝ) ≤ Real.log (2 + L) := Real.log_nonneg (by linarith)
    linarith
  have hs2 : Real.sqrt 2 * 2 ≤ 2 ^ 6 * (1 + Ξ) := by nlinarith [hs, hΞ]
  calc (C * Real.sqrt 2) * (2 * Real.log (1 + L))
      = (C * (Real.sqrt 2 * 2)) * Real.log (1 + L) := by ring
    _ ≤ (C * (Real.sqrt 2 * 2)) * (1 + Real.log (2 + L)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ (C * (2 ^ 6 * (1 + Ξ))) * (1 + Real.log (2 + L)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs2 hC.le) hlog2
    _ = 2 ^ 6 * (1 + Ξ) * C * (1 + Real.log (2 + L)) := by ring

theorem horiz_dev_le_tent {Ξ rr M Rde C₂ : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {s a b : ℝ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M)
    (hInF1 : MandelDim.InF1 α) (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
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
    (ha : (a + s * Complex.I : ℂ) ∈ Work.Pert.Qm Ξ α)
    (hb : (b + s * Complex.I : ℂ) ∈ Work.Pert.Qm Ξ α)
    (hab : a ≤ b)
    (hlo : ∀ x ∈ Set.Icc a b,
      Real.sqrt 2 * Rde ≤ min (Work.Pert.V5.mgA Ξ α ((x : ℂ) + (s : ℂ) * Complex.I))
                              (Work.Pert.V5.mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I)))
    (hpos : ∀ x ∈ Set.Icc a b,
      1 ≤ min (Work.Pert.V5.mgA Ξ α ((x : ℂ) + (s : ℂ) * Complex.I))
              (Work.Pert.V5.mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I))) :
    ‖(Φm ((b : ℂ) + (s : ℂ) * Complex.I) - ((b : ℂ) + (s : ℂ) * Complex.I))
        - (Φm ((a : ℂ) + (s : ℂ) * Complex.I) - ((a : ℂ) + (s : ℂ) * Complex.I))‖
      ≤ 2 ^ 6 * (1 + Ξ) * C₂ * (1 + Real.log (2 + (b - a))) + (b - a) / 31 := by
  have _ := hrr
  have _ := hM
  have _ := hInF1
  have _ := hα
  have _ := hσ
  have _ := hnorm
  have _ := hu
  have _ := hu2
  have _ := hτQ
  have _ := hRde
  have hΞnn : (0 : ℝ) ≤ Ξ := le_of_lt hΞ
  have hC₂pos : (0 : ℝ) < C₂ := hC₂
  have hba : (0 : ℝ) ≤ b - a := sub_nonneg.mpr hab
  -- ## the gate is open, and the segment lies in it
  have hQopen : IsOpen (Work.Pert.Qm Ξ α) := by
    simpa only [Work.Pert.Qm] using
      Work.Fatou.Qreg.isOpen_Qreg (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ)))
  have hseg : ∀ x ∈ Set.Icc a b, ((x : ℂ) + (s : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α := by
    intro x hx
    refine slice_interval (a := a) (b := b) (s := s) ha hb ?_
    rw [min_eq_left hab, max_eq_right hab]
    exact hx
  have hmpos : ∀ x ∈ Set.Icc a b,
      0 < min (mgA Ξ α ((x : ℂ) + (s : ℂ) * Complex.I))
              (mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I)) :=
    fun x hx => lt_of_lt_of_le one_pos (hpos x hx)
  -- ## continuity of the two marginals along the corridor
  have hAcont : Continuous
      (fun x : ℝ => mgA Ξ α ((x : ℂ) + (s : ℂ) * Complex.I)) := by
    simp only [mgA]; fun_prop
  have hBcont : Continuous
      (fun x : ℝ => mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I)) := by
    simp only [mgB]; fun_prop
  -- ## the pointwise derivative bound
  have hpt : ∀ x ∈ Set.Icc a b,
      ‖deriv Φm ((x : ℂ) + (s : ℂ) * Complex.I) - 1‖
        ≤ (C₂ * Real.sqrt 2)
            * (1 / min (mgA Ξ α ((x : ℂ) + (s : ℂ) * Complex.I))
                       (mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I))) + 1 / 31 := by
    intro x hx
    have hxQ : ((x : ℂ) + (s : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α := hseg x hx
    have hRde : Rde ≤ min (mgA Ξ α ((x : ℂ) + (s : ℂ) * Complex.I))
                        (mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I)) / Real.sqrt 2 := by
      rw [le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
      have h := hlo x hx
      linarith
    have hball : Metric.ball ((x : ℂ) + (s : ℂ) * Complex.I)
        (min (mgA Ξ α ((x : ℂ) + (s : ℂ) * Complex.I))
             (mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I)) / Real.sqrt 2)
        ⊆ Work.Pert.Qm Ξ α := ball_in_gate hxQ
    have hDEz : ‖deriv Φm ((x : ℂ) + (s : ℂ) * Complex.I)
        - 1 / (Work.Pert.liftF u σ α ((x : ℂ) + (s : ℂ) * Complex.I)
              - ((x : ℂ) + (s : ℂ) * Complex.I))‖
        ≤ C₂ / (min (mgA Ξ α ((x : ℂ) + (s : ℂ) * Complex.I))
                    (mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I)) / Real.sqrt 2) :=
      hDE Φm (fun w => Work.Pert.liftF u σ α w - w) ((x : ℂ) + (s : ℂ) * Complex.I)
        (min (mgA Ξ α ((x : ℂ) + (s : ℂ) * Complex.I))
             (mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I)) / Real.sqrt 2) hRde
        (hΦm.1.mono hball) (hΦm.2.1.mono hball)
        ((hNT.1.1.mono hball).sub differentiableOn_id)
        (fun w hw => by
          have h1 : ‖Work.Pert.liftF u σ α w - (w + 1)‖ ≤ 1 / 32 := (hNT.1.2 w (hball hw)).1
          have h2 : Work.Pert.liftF u σ α w - w - 1 = Work.Pert.liftF u σ α w - (w + 1) := by
            ring
          rw [h2]
          linarith)
        (fun w hw hfw => by
          have hwm : w ∈ Work.Pert.Qm Ξ α := hball hw
          have h1 : w + (Work.Pert.liftF u σ α w - w) = Work.Pert.liftF u σ α w := by ring
          have hfm : Work.Pert.liftF u σ α w ∈ Work.Pert.Qm Ξ α := by
            have h2 := hfw
            rw [h1] at h2
            exact hball h2
          have h := hΦm.2.2 w hwm hfm
          simpa only [h1] using h)
    have hv32 : ‖Work.Pert.liftF u σ α ((x : ℂ) + (s : ℂ) * Complex.I)
        - ((x : ℂ) + (s : ℂ) * Complex.I) - 1‖ ≤ 1 / 32 := by
      have h1 : ‖Work.Pert.liftF u σ α ((x : ℂ) + (s : ℂ) * Complex.I)
          - (((x : ℂ) + (s : ℂ) * Complex.I) + 1)‖ ≤ 1 / 32 := (hNT.1.2 _ hxQ).1
      have h2 : Work.Pert.liftF u σ α ((x : ℂ) + (s : ℂ) * Complex.I)
          - ((x : ℂ) + (s : ℂ) * Complex.I) - 1
          = Work.Pert.liftF u σ α ((x : ℂ) + (s : ℂ) * Complex.I)
            - (((x : ℂ) + (s : ℂ) * Complex.I) + 1) := by ring
      rw [h2]
      exact h1
    have hinv : ‖1 / (Work.Pert.liftF u σ α ((x : ℂ) + (s : ℂ) * Complex.I)
        - ((x : ℂ) + (s : ℂ) * Complex.I)) - 1‖ ≤ 1 / 31 := inv_sub_one_le_of_close hv32
    have hkey : C₂ / (min (mgA Ξ α ((x : ℂ) + (s : ℂ) * Complex.I))
                          (mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I)) / Real.sqrt 2)
        = (C₂ * Real.sqrt 2)
            * (1 / min (mgA Ξ α ((x : ℂ) + (s : ℂ) * Complex.I))
                       (mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I))) := by
      have hm0 : min (mgA Ξ α ((x : ℂ) + (s : ℂ) * Complex.I))
          (mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I)) ≠ 0 := ne_of_gt (hmpos x hx)
      have hs20 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
      field_simp
    rw [hkey] at hDEz
    have htri : ‖deriv Φm ((x : ℂ) + (s : ℂ) * Complex.I) - 1‖
        ≤ ‖deriv Φm ((x : ℂ) + (s : ℂ) * Complex.I)
            - 1 / (Work.Pert.liftF u σ α ((x : ℂ) + (s : ℂ) * Complex.I)
                  - ((x : ℂ) + (s : ℂ) * Complex.I))‖
          + ‖1 / (Work.Pert.liftF u σ α ((x : ℂ) + (s : ℂ) * Complex.I)
                  - ((x : ℂ) + (s : ℂ) * Complex.I)) - 1‖ := by
      have he : deriv Φm ((x : ℂ) + (s : ℂ) * Complex.I) - 1
          = (deriv Φm ((x : ℂ) + (s : ℂ) * Complex.I)
              - 1 / (Work.Pert.liftF u σ α ((x : ℂ) + (s : ℂ) * Complex.I)
                    - ((x : ℂ) + (s : ℂ) * Complex.I)))
            + (1 / (Work.Pert.liftF u σ α ((x : ℂ) + (s : ℂ) * Complex.I)
                    - ((x : ℂ) + (s : ℂ) * Complex.I)) - 1) := by ring
      rw [he]
      exact norm_add_le _ _
    linarith [htri, hDEz, hinv]
  -- ## the majorant is continuous on the corridor
  have hgcont : ContinuousOn (fun x : ℝ => (C₂ * Real.sqrt 2)
      * (1 / min (mgA Ξ α ((x : ℂ) + (s : ℂ) * Complex.I))
                 (mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I))) + 1 / 31) (Set.Icc a b) :=
    (ContinuousOn.mul continuousOn_const (ContinuousOn.div continuousOn_const
      (hAcont.min hBcont).continuousOn (fun x hx => ne_of_gt (hmpos x hx)))).add
      continuousOn_const
  -- ## displacement ≤ integral of the speed
  have hdev := dev_horiz_le (Φ := Φm) (Q := Work.Pert.Qm Ξ α) (s := s) (a := a) (b := b)
    (g := fun x : ℝ => (C₂ * Real.sqrt 2)
      * (1 / min (mgA Ξ α ((x : ℂ) + (s : ℂ) * Complex.I))
                 (mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I))) + 1 / 31)
    hQopen hab hseg hΦm.1 hpt hgcont
  -- ## the integral of the majorant
  have hint1 : IntervalIntegrable (fun x : ℝ => (C₂ * Real.sqrt 2)
      * (1 / min (mgA Ξ α ((x : ℂ) + (s : ℂ) * Complex.I))
                 (mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I)))) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact ContinuousOn.mul continuousOn_const (ContinuousOn.div continuousOn_const
      (hAcont.min hBcont).continuousOn (fun x hx => ne_of_gt (hmpos x hx)))
  have hsplit : ∫ x in a..b, ((C₂ * Real.sqrt 2)
        * (1 / min (mgA Ξ α ((x : ℂ) + (s : ℂ) * Complex.I))
                   (mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I))) + 1 / 31)
      = (C₂ * Real.sqrt 2)
          * (∫ x in a..b, 1 / min (mgA Ξ α ((x : ℂ) + (s : ℂ) * Complex.I))
                                   (mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I)))
        + (b - a) * (1 / 31) := by
    rw [intervalIntegral.integral_add hint1 intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
  -- ## the tent bound for `∫ dx / min (mgA) (mgB)`
  have htent : ∫ x in a..b, 1 / min (mgA Ξ α ((x : ℂ) + (s : ℂ) * Complex.I))
      (mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I)) ≤ 2 * Real.log (1 + (b - a)) := by
    have h := integral_inv_min_le (K := (1 : ℝ)) (by norm_num) hab hAcont hBcont
      (le_trans (hpos a ⟨le_rfl, hab⟩) (min_le_left _ _))
      (le_trans (hpos b ⟨hab, le_rfl⟩) (min_le_right _ _))
      (fun x hx => by rw [mgA_line, mgA_line]; ring)
      (fun x hx => by rw [mgB_line, mgB_line]; ring)
    simpa using h
  -- ## the two terms
  have hterm1 : (C₂ * Real.sqrt 2)
      * (∫ x in a..b, 1 / min (mgA Ξ α ((x : ℂ) + (s : ℂ) * Complex.I))
                               (mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I)))
      ≤ 2 ^ 6 * (1 + Ξ) * C₂ * (1 + Real.log (2 + (b - a))) := by
    have h1 := mul_le_mul_of_nonneg_left htent (by positivity : (0 : ℝ) ≤ C₂ * Real.sqrt 2)
    have h2 := tent_log_absorb hC₂pos hΞ hba
    linarith [h1, h2]
  have hterm2 : (b - a) * (1 / 31) = (b - a) / 31 := by ring
  -- ## conclusion
  have hfinal : ∫ x in a..b, ((C₂ * Real.sqrt 2)
      * (1 / min (mgA Ξ α ((x : ℂ) + (s : ℂ) * Complex.I))
                 (mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I))) + 1 / 31)
      ≤ 2 ^ 6 * (1 + Ξ) * C₂ * (1 + Real.log (2 + (b - a))) + (b - a) / 31 := by
    rw [hsplit]
    linarith [hterm1, hterm2]
  exact le_trans hdev hfinal

end

end Work.Pert.V5
