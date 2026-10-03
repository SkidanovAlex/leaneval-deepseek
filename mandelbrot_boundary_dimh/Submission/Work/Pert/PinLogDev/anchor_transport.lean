import Mathlib
import Submission.Work.Pert.dev_base_v3
import Submission.Work.Pert.Pin3.dev_deriv_le_pt
import Submission.Work.Pert.Pin3.dev_seg_const
import Submission.Work.Pert.PinLogDev.dev_vert_marg
import Submission.Work.Pert.PinLogDev.dev_horiz_marg

/-!
# `Work.Pert.PinLogDev.anchor_transport`

Transport of the pinned deviation bound `‖Φ W - W‖ ≤ K` from a point `W` of the gate `Qm Ξ α`
(with `Re W < -Ξ`, i.e. deep in the lower left wing) to the two anchors `± i Y₀` of the axis.

The hypotheses give the cleared region explicitly: both margins are `≥ √2 Rde` along the
vertical segment `{Re W} × [min (Im W) (-Y₀), max (Im W) Y₀]` and along the horizontal segments
at heights `±Y₀` over `[Re W, 0]`.  Hence

* `ball z Rde ⊆ Qm Ξ α` at every point of the L-shaped path `W → {Re W} ± i Y₀ → ± i Y₀`;
* `MandelDim.FatouDerivEstimate` (through `Work.Pert.Pin3.dev_deriv_le_pt`) turns this into
  `‖deriv Φ z - 1‖ ≤ C₂ / Rde + 1/31` there;
* the mean-value bound `Work.Pert.Pin3.dev_seg_const` integrates this along the two pieces.

The pieces themselves are `Work.Pert.PinLogDev.dev_vert_marg` and
`Work.Pert.PinLogDev.dev_horiz_marg`.
-/

namespace Work.Pert.PinLogDev

open MandelDim Complex Metric Set

noncomputable section

/-! ## The two segment parameterisations -/

/-- The point of the vertical segment from `W` to `{Re W} + i Y` at parameter `t`. -/
private lemma vert_point (W : ℂ) (Y t : ℝ) :
    W + t • (((W.re : ℂ) + (Y : ℂ) * Complex.I) - W)
      = (W.re : ℂ) + ((W.im + t * (Y - W.im) : ℝ) : ℂ) * Complex.I := by
  rw [Complex.real_smul]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      mul_one, sub_zero, add_zero, zero_add] <;>
    ring

/-- The point of the horizontal segment from `{Re W} + i Y` to `i Y` at parameter `t`. -/
private lemma horiz_point (W : ℂ) (Y t : ℝ) :
    (((W.re : ℂ) + (Y : ℂ) * Complex.I)
        + t • ((Y : ℂ) * Complex.I - ((W.re : ℂ) + (Y : ℂ) * Complex.I)))
      = ((W.re + t * (0 - W.re) : ℝ) : ℂ) + (Y : ℂ) * Complex.I := by
  rw [Work.Pert.seg_point]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
  ring_nf

/-! ## The transport -/

theorem anchor_transport (Ξ Rde C₂ : ℝ) (hΞ : 1 + 64 * Real.pi ≤ Ξ) (hRde : 0 < Rde)
    (hC₂ : 0 ≤ C₂)
    (hDE : ∀ (Φ' v : ℂ → ℂ) (z' : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ' (Metric.ball z' R) → Set.InjOn Φ' (Metric.ball z' R) →
      DifferentiableOn ℂ v (Metric.ball z' R) → (∀ z ∈ Metric.ball z' R, ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ Metric.ball z' R, z + v z ∈ Metric.ball z' R → Φ' (z + v z) = Φ' z + 1) →
      ‖deriv Φ' z' - 1 / v z'‖ ≤ C₂ / R) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
    ∀ {α : ℂ} {F Φ : ℂ → ℂ} {W : ℂ} {Y₀ K : ℝ},
      0 ≤ K → Ξ + 4 * (Rde + C₂ + 2) + 10 ≤ Y₀ →
      MandelDim.NearTranslationL1 F (Work.Pert.Qm Ξ α) →
      MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm Ξ α) →
      W ∈ Work.Pert.Qm Ξ α → W.re < -Ξ →
      (∀ y ∈ Set.Icc (min W.im (-Y₀)) (max W.im Y₀),
        Real.sqrt 2 * Rde ≤ Work.Pert.margA Ξ α ((W.re : ℂ) + (y : ℂ) * Complex.I) ∧
        Real.sqrt 2 * Rde ≤ Work.Pert.margB Ξ α ((W.re : ℂ) + (y : ℂ) * Complex.I)) →
      (∀ x ∈ Set.Icc W.re 0,
        Real.sqrt 2 * Rde ≤ Work.Pert.margA Ξ α ((x : ℂ) + (Y₀ : ℂ) * Complex.I) ∧
        Real.sqrt 2 * Rde ≤ Work.Pert.margB Ξ α ((x : ℂ) + (Y₀ : ℂ) * Complex.I) ∧
        Real.sqrt 2 * Rde ≤ Work.Pert.margA Ξ α ((x : ℂ) + (-Y₀ : ℂ) * Complex.I) ∧
        Real.sqrt 2 * Rde ≤ Work.Pert.margB Ξ α ((x : ℂ) + (-Y₀ : ℂ) * Complex.I)) →
      ‖Φ W - W‖ ≤ K →
      ‖Φ ((Y₀ : ℂ) * Complex.I) - (Y₀ : ℂ) * Complex.I‖ ≤
          K + Λ * (|W.re| + |W.im| + Y₀ + 1) ∧
      ‖Φ (-((Y₀ : ℂ) * Complex.I)) + (Y₀ : ℂ) * Complex.I‖ ≤
          K + Λ * (|W.re| + |W.im| + Y₀ + 1) := by
  have hΛnn : (0 : ℝ) ≤ C₂ / Rde + 1 / 31 := by
    have h : (0 : ℝ) ≤ C₂ / Rde := div_nonneg hC₂ hRde.le
    linarith
  refine ⟨C₂ / Rde + 1 / 31, hΛnn, ?_⟩
  intro α F Φ W Y₀ K hK hY0 hNT hΦ hW hWre hvert hhor hKW
  have hY0pos : 0 < Y₀ := by
    have h1 : (0 : ℝ) ≤ 4 * (Rde + C₂ + 2) := by positivity
    linarith [Real.pi_pos]
  have hWrle : W.re ≤ 0 := by
    have hΞ0 : 0 < Ξ := by linarith [Real.pi_pos]
    linarith
  have hmn : (-Y₀ : ℝ) ≤ Y₀ := by linarith
  -- clearance hypotheses in the form used by the two segment lemmas
  have hvertU : ∀ y ∈ Set.Icc (min W.im Y₀) (max W.im Y₀),
      Real.sqrt 2 * Rde ≤ Work.Pert.margA Ξ α ((W.re : ℂ) + (y : ℂ) * Complex.I) ∧
      Real.sqrt 2 * Rde ≤ Work.Pert.margB Ξ α ((W.re : ℂ) + (y : ℂ) * Complex.I) := by
    intro y hy
    have h1 : min W.im (-Y₀) ≤ min W.im Y₀ := by
      rw [min_comm W.im (-Y₀), min_comm W.im Y₀]
      exact min_le_min_right W.im hmn
    exact hvert y ⟨le_trans h1 hy.1, hy.2⟩
  have hvertL : ∀ y ∈ Set.Icc (min W.im (-Y₀)) (max W.im (-Y₀)),
      Real.sqrt 2 * Rde ≤ Work.Pert.margA Ξ α ((W.re : ℂ) + (y : ℂ) * Complex.I) ∧
      Real.sqrt 2 * Rde ≤ Work.Pert.margB Ξ α ((W.re : ℂ) + (y : ℂ) * Complex.I) := by
    intro y hy
    have h2 : max W.im (-Y₀) ≤ max W.im Y₀ := max_le_max_left W.im hmn
    exact hvert y ⟨hy.1, le_trans hy.2 h2⟩
  have hhorU : ∀ x ∈ Set.Icc W.re 0,
      Real.sqrt 2 * Rde ≤ Work.Pert.margA Ξ α ((x : ℂ) + (Y₀ : ℂ) * Complex.I) ∧
      Real.sqrt 2 * Rde ≤ Work.Pert.margB Ξ α ((x : ℂ) + (Y₀ : ℂ) * Complex.I) :=
    fun x hx => ⟨(hhor x hx).1, (hhor x hx).2.1⟩
  have hnegY : (((-Y₀ : ℝ)) : ℂ) = (-Y₀ : ℂ) := by push_cast; ring
  have hhorL : ∀ x ∈ Set.Icc W.re 0,
      Real.sqrt 2 * Rde ≤ Work.Pert.margA Ξ α ((x : ℂ) + (((-Y₀ : ℝ)) : ℂ) * Complex.I) ∧
      Real.sqrt 2 * Rde ≤ Work.Pert.margB Ξ α ((x : ℂ) + (((-Y₀ : ℝ)) : ℂ) * Complex.I) := by
    intro x hx
    have h := hhor x hx
    rw [hnegY]
    exact ⟨h.2.2.1, h.2.2.2⟩
  -- the vertical / horizontal segment bounds on the upper side
  have hUpV : ‖(Φ ((W.re : ℂ) + (Y₀ : ℂ) * Complex.I)
        - ((W.re : ℂ) + (Y₀ : ℂ) * Complex.I)) - (Φ W - W)‖
      ≤ (C₂ / Rde + 1 / 31) * |Y₀ - W.im| :=
    dev_vert_marg (Ξ := Ξ) (α := α) (Rde := Rde) (C₂ := C₂) (W := W) (Y := Y₀)
      hRde hDE hNT hΦ hvertU
  have hUpH : ‖(Φ ((Y₀ : ℂ) * Complex.I) - (Y₀ : ℂ) * Complex.I)
        - (Φ ((W.re : ℂ) + (Y₀ : ℂ) * Complex.I)
            - ((W.re : ℂ) + (Y₀ : ℂ) * Complex.I))‖
      ≤ (C₂ / Rde + 1 / 31) * |W.re| :=
    dev_horiz_marg (Ξ := Ξ) (α := α) (Rde := Rde) (C₂ := C₂) (a := W.re) (Y := Y₀)
      hRde hWrle hDE hNT hΦ hhorU
  -- the lower side
  have hLoV : ‖(Φ ((W.re : ℂ) + (((-Y₀ : ℝ)) : ℂ) * Complex.I)
        - ((W.re : ℂ) + (((-Y₀ : ℝ)) : ℂ) * Complex.I)) - (Φ W - W)‖
      ≤ (C₂ / Rde + 1 / 31) * |(-Y₀) - W.im| :=
    dev_vert_marg (Ξ := Ξ) (α := α) (Rde := Rde) (C₂ := C₂) (W := W) (Y := -Y₀)
      hRde hDE hNT hΦ hvertL
  have hLoH : ‖(Φ ((((-Y₀ : ℝ)) : ℂ) * Complex.I) - ((((-Y₀ : ℝ)) : ℂ) * Complex.I))
        - (Φ ((W.re : ℂ) + (((-Y₀ : ℝ)) : ℂ) * Complex.I)
            - ((W.re : ℂ) + (((-Y₀ : ℝ)) : ℂ) * Complex.I))‖
      ≤ (C₂ / Rde + 1 / 31) * |W.re| :=
    dev_horiz_marg (Ξ := Ξ) (α := α) (Rde := Rde) (C₂ := C₂) (a := W.re) (Y := -Y₀)
      hRde hWrle hDE hNT hΦ hhorL
  -- arithmetic
  have hA1 : |Y₀ - W.im| ≤ |W.im| + Y₀ := by
    rw [abs_sub_le_iff]
    refine ⟨?_, ?_⟩
    · linarith [neg_le_abs W.im]
    · linarith [le_abs_self W.im]
  have hA2 : |(-Y₀) - W.im| ≤ |W.im| + Y₀ := by
    have h : |(-Y₀) - W.im| = |Y₀ + W.im| := by
      rw [show (-Y₀) - W.im = -(Y₀ + W.im) by ring, abs_neg]
    rw [h, abs_le]
    exact ⟨by linarith [neg_le_abs W.im], by linarith [le_abs_self W.im]⟩
  have hupper : ‖Φ ((Y₀ : ℂ) * Complex.I) - (Y₀ : ℂ) * Complex.I‖
      ≤ K + (C₂ / Rde + 1 / 31) * (|W.re| + |W.im| + Y₀ + 1) := by
    have htri : ‖(Φ ((Y₀ : ℂ) * Complex.I) - (Y₀ : ℂ) * Complex.I) - (Φ W - W)‖
        ≤ (C₂ / Rde + 1 / 31) * (|W.re| + |W.im| + Y₀) := by
      have hsum : (Φ ((Y₀ : ℂ) * Complex.I) - (Y₀ : ℂ) * Complex.I) - (Φ W - W)
          = ((Φ ((Y₀ : ℂ) * Complex.I) - (Y₀ : ℂ) * Complex.I)
              - (Φ ((W.re : ℂ) + (Y₀ : ℂ) * Complex.I)
                  - ((W.re : ℂ) + (Y₀ : ℂ) * Complex.I)))
            + ((Φ ((W.re : ℂ) + (Y₀ : ℂ) * Complex.I)
                  - ((W.re : ℂ) + (Y₀ : ℂ) * Complex.I)) - (Φ W - W)) := by
        ring
      have h1 : ‖(Φ ((Y₀ : ℂ) * Complex.I) - (Y₀ : ℂ) * Complex.I) - (Φ W - W)‖
          ≤ ‖(Φ ((Y₀ : ℂ) * Complex.I) - (Y₀ : ℂ) * Complex.I)
              - (Φ ((W.re : ℂ) + (Y₀ : ℂ) * Complex.I)
                  - ((W.re : ℂ) + (Y₀ : ℂ) * Complex.I))‖
            + ‖(Φ ((W.re : ℂ) + (Y₀ : ℂ) * Complex.I)
                  - ((W.re : ℂ) + (Y₀ : ℂ) * Complex.I)) - (Φ W - W)‖ := by
        rw [hsum]; exact norm_add_le _ _
      have h2 := mul_le_mul_of_nonneg_left hA1 hΛnn
      nlinarith [h1, hUpV, hUpH, h2, abs_nonneg W.re]
    have h3 : (C₂ / Rde + 1 / 31) * (|W.re| + |W.im| + Y₀)
        ≤ (C₂ / Rde + 1 / 31) * (|W.re| + |W.im| + Y₀ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hΛnn
    have h1 : ‖Φ ((Y₀ : ℂ) * Complex.I) - (Y₀ : ℂ) * Complex.I‖
        ≤ ‖Φ W - W‖ + ‖(Φ ((Y₀ : ℂ) * Complex.I) - (Y₀ : ℂ) * Complex.I)
            - (Φ W - W)‖ := by
      have h := norm_add_le (Φ W - W)
        ((Φ ((Y₀ : ℂ) * Complex.I) - (Y₀ : ℂ) * Complex.I) - (Φ W - W))
      have he : (Φ W - W) + ((Φ ((Y₀ : ℂ) * Complex.I) - (Y₀ : ℂ) * Complex.I) - (Φ W - W))
          = Φ ((Y₀ : ℂ) * Complex.I) - (Y₀ : ℂ) * Complex.I := by ring
      rwa [he] at h
    linarith [h1, hKW, htri, h3]
  have hlower : ‖Φ (-((Y₀ : ℂ) * Complex.I)) + (Y₀ : ℂ) * Complex.I‖
      ≤ K + (C₂ / Rde + 1 / 31) * (|W.re| + |W.im| + Y₀ + 1) := by
    have hneg : (((-Y₀ : ℝ)) : ℂ) * Complex.I = -((Y₀ : ℂ) * Complex.I) := by push_cast; ring
    have hconv : Φ (-((Y₀ : ℂ) * Complex.I)) + (Y₀ : ℂ) * Complex.I
        = Φ ((((-Y₀ : ℝ)) : ℂ) * Complex.I) - ((((-Y₀ : ℝ)) : ℂ) * Complex.I) := by
      rw [hneg]; ring
    rw [hconv]
    have htri : ‖(Φ ((((-Y₀ : ℝ)) : ℂ) * Complex.I) - ((((-Y₀ : ℝ)) : ℂ) * Complex.I))
        - (Φ W - W)‖
        ≤ (C₂ / Rde + 1 / 31) * (|W.re| + |W.im| + Y₀) := by
      have hsum : (Φ ((((-Y₀ : ℝ)) : ℂ) * Complex.I) - ((((-Y₀ : ℝ)) : ℂ) * Complex.I))
            - (Φ W - W)
          = ((Φ ((((-Y₀ : ℝ)) : ℂ) * Complex.I) - ((((-Y₀ : ℝ)) : ℂ) * Complex.I))
              - (Φ ((W.re : ℂ) + (((-Y₀ : ℝ)) : ℂ) * Complex.I)
                  - ((W.re : ℂ) + (((-Y₀ : ℝ)) : ℂ) * Complex.I)))
            + ((Φ ((W.re : ℂ) + (((-Y₀ : ℝ)) : ℂ) * Complex.I)
                  - ((W.re : ℂ) + (((-Y₀ : ℝ)) : ℂ) * Complex.I)) - (Φ W - W)) := by
        ring
      have h1 : ‖(Φ ((((-Y₀ : ℝ)) : ℂ) * Complex.I) - ((((-Y₀ : ℝ)) : ℂ) * Complex.I))
            - (Φ W - W)‖
          ≤ ‖(Φ ((((-Y₀ : ℝ)) : ℂ) * Complex.I) - ((((-Y₀ : ℝ)) : ℂ) * Complex.I))
              - (Φ ((W.re : ℂ) + (((-Y₀ : ℝ)) : ℂ) * Complex.I)
                  - ((W.re : ℂ) + (((-Y₀ : ℝ)) : ℂ) * Complex.I))‖
            + ‖(Φ ((W.re : ℂ) + (((-Y₀ : ℝ)) : ℂ) * Complex.I)
                  - ((W.re : ℂ) + (((-Y₀ : ℝ)) : ℂ) * Complex.I)) - (Φ W - W)‖ := by
        rw [hsum]; exact norm_add_le _ _
      have h2 := mul_le_mul_of_nonneg_left hA2 hΛnn
      nlinarith [h1, hLoV, hLoH, h2, abs_nonneg W.re]
    have h3 : (C₂ / Rde + 1 / 31) * (|W.re| + |W.im| + Y₀)
        ≤ (C₂ / Rde + 1 / 31) * (|W.re| + |W.im| + Y₀ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hΛnn
    have h1 : ‖Φ ((((-Y₀ : ℝ)) : ℂ) * Complex.I) - ((((-Y₀ : ℝ)) : ℂ) * Complex.I)‖
        ≤ ‖Φ W - W‖ + ‖(Φ ((((-Y₀ : ℝ)) : ℂ) * Complex.I) - ((((-Y₀ : ℝ)) : ℂ) * Complex.I))
            - (Φ W - W)‖ := by
      have h := norm_add_le (Φ W - W)
        ((Φ ((((-Y₀ : ℝ)) : ℂ) * Complex.I) - ((((-Y₀ : ℝ)) : ℂ) * Complex.I)) - (Φ W - W))
      have he : (Φ W - W)
          + ((Φ ((((-Y₀ : ℝ)) : ℂ) * Complex.I) - ((((-Y₀ : ℝ)) : ℂ) * Complex.I))
            - (Φ W - W))
          = Φ ((((-Y₀ : ℝ)) : ℂ) * Complex.I) - ((((-Y₀ : ℝ)) : ℂ) * Complex.I) := by ring
      rwa [he] at h
    linarith [h1, hKW, htri, h3]
  exact ⟨hupper, hlower⟩

end

end Work.Pert.PinLogDev
