import Mathlib
import Submission.Work.Pert.V5.Window
import Submission.Work.Pert.V5.dev_horiz_le

/-!
# Elementary facts for the assembly of `Work.Pert.Phi_dev_gate_lin_v5`

This file collects the reusable pieces used by `Work.Pert.V5.Assembly`:

* `mgA_re_im`, `mgB_re_im`: the two marginals at `x + i s`, in real coordinates;
* `zo_margins`: the `hcl` ball at the pin forces both gate margins of `z₀` to exceed `2 Rde + 2`;
* `margin_of_endpoints`: along a horizontal line `x ↦ x + i s` the function
  `min (mgA) (mgB)` is a *tent* (concave), so a lower bound at the two endpoints propagates to the
  whole segment;
* `band_horiz_dev_le`: the horizontal transport of the deviation inside the band, with the explicit
  constant `1/150 + 1/31`;
* `window_horiz_dev_le`: the same on any horizontal segment lying in the window strip
  `(Ξ - Re(1/α) + 1, -Ξ - 3)`.
-/

open Set Metric Filter
open scoped Topology

namespace Work.Pert.V5

noncomputable section

/-- `mgA` at a point given by real coordinates. -/
lemma re_of_re_im (x s : ℝ) : ((x : ℂ) + (s : ℂ) * Complex.I).re = x := by
  simp

lemma im_of_re_im (x s : ℝ) : ((x : ℂ) + (s : ℂ) * Complex.I).im = s := by
  simp

lemma mgA_re_im (Ξ : ℝ) (α : ℂ) (x s : ℝ) :
    mgA Ξ α ((x : ℂ) + (s : ℂ) * Complex.I) = x - Ξ + (1 / α).re + |s + (1 / α).im| := by
  rw [mgA, re_of_re_im, im_of_re_im]

/-- `mgB` at a point given by real coordinates. -/
lemma mgB_re_im (Ξ : ℝ) (x s : ℝ) :
    mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I) = |s| - Ξ - x := by
  rw [mgB, re_of_re_im, im_of_re_im]

/-- **The ball at the pin forces big margins.**  If the closed ball of radius `2 Rde + 2` around
`z₀` lies in the gate, then both margins of `z₀` exceed `2 Rde + 2`. -/
theorem zo_margins {Ξ Rde : ℝ} {α : ℂ} {z₀ : ℂ} (hRde : 0 < Rde)
    (hcl : Metric.closedBall z₀ (2 * Rde + 2) ⊆ Work.Pert.Qm Ξ α) :
    2 * Rde + 2 < mgA Ξ α z₀ ∧ 2 * Rde + 2 < mgB Ξ z₀ := by
  have hpos : (0:ℝ) < 2 * Rde + 2 := by linarith
  have hrad : ‖(((2 * Rde + 2 : ℝ)) : ℂ)‖ = 2 * Rde + 2 := by
    have h : ‖(((2 * Rde + 2 : ℝ)) : ℂ)‖ ^ 2 = (2 * Rde + 2) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
      ring
    rw [← Real.sqrt_sq (norm_nonneg _), h, Real.sqrt_sq_eq_abs, abs_of_pos hpos]
  have hplus : z₀ + (((2 * Rde + 2 : ℝ)) : ℂ) ∈ Work.Pert.Qm Ξ α := by
    apply hcl
    rw [Metric.mem_closedBall, dist_eq_norm']
    rw [show z₀ - (z₀ + (((2 * Rde + 2 : ℝ)) : ℂ)) = -(((2 * Rde + 2 : ℝ)) : ℂ) from by ring,
      norm_neg]
    exact le_of_eq hrad
  have hminus : z₀ - (((2 * Rde + 2 : ℝ)) : ℂ) ∈ Work.Pert.Qm Ξ α := by
    apply hcl
    rw [Metric.mem_closedBall, dist_eq_norm']
    rw [show z₀ - (z₀ - (((2 * Rde + 2 : ℝ)) : ℂ)) = (((2 * Rde + 2 : ℝ)) : ℂ) from by ring]
    exact le_of_eq hrad
  have hm1 := (mem_Qm_iff_mg.mp hplus).2
  have hm2 := (mem_Qm_iff_mg.mp hminus).1
  simp only [mgB, mgA, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_zero, add_zero, sub_zero] at hm1 hm2
  constructor
  · simp only [mgA]; linarith
  · simp only [mgB]; linarith

/-- **The tent is concave**: a lower bound for `min (mgA) (mgB)` at the two endpoints of a
horizontal segment gives it on the whole segment. -/
theorem margin_of_endpoints {Ξ : ℝ} {α : ℂ} {s a b : ℝ} {m : ℝ}
    (ha : m ≤ min (mgA Ξ α ((a : ℂ) + (s : ℂ) * Complex.I))
                   (mgB Ξ ((a : ℂ) + (s : ℂ) * Complex.I)))
    (hb : m ≤ min (mgA Ξ α ((b : ℂ) + (s : ℂ) * Complex.I))
                   (mgB Ξ ((b : ℂ) + (s : ℂ) * Complex.I))) :
    ∀ x ∈ Set.Icc (min a b) (max a b),
      m ≤ min (mgA Ξ α ((x : ℂ) + (s : ℂ) * Complex.I))
              (mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I)) := by
  have hAa : m ≤ a - Ξ + (1 / α).re + |s + (1 / α).im| :=
    le_trans (le_trans ha (min_le_left _ _)) (le_of_eq (mgA_re_im Ξ α a s))
  have hBa : m ≤ |s| - Ξ - a :=
    le_trans (le_trans ha (min_le_right _ _)) (le_of_eq (mgB_re_im Ξ a s))
  have hAb : m ≤ b - Ξ + (1 / α).re + |s + (1 / α).im| :=
    le_trans (le_trans hb (min_le_left _ _)) (le_of_eq (mgA_re_im Ξ α b s))
  have hBb : m ≤ |s| - Ξ - b :=
    le_trans (le_trans hb (min_le_right _ _)) (le_of_eq (mgB_re_im Ξ b s))
  intro x hx
  rw [mgA_re_im Ξ α x s, mgB_re_im Ξ x s]
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, max_eq_right hab] at hx
    exact le_min (by linarith [hx.1, hAa]) (by linarith [hx.2, hBb])
  · rw [min_eq_right hab, max_eq_left hab] at hx
    exact le_min (by linarith [hx.1, hAb]) (by linarith [hx.2, hBa])

/-- **Horizontal transport of the deviation inside the band.**  For two abscissas `a ≤ b` of the
band `[-(Ξ+2^10+2M), -(Ξ+2^10)]` and any height `s`,
`‖D (b + i s) - D (a + i s)‖ ≤ (1/150 + 1/31) (b - a)`. -/
theorem band_horiz_dev_le {Ξ rr M : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {s a b : ℝ}
    (hF : MandelDim.FatouStatement)
    (hΞ : 0 < Ξ) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    (ha : -(Ξ + 2 ^ 10 + 2 * M) ≤ a) (ha' : a ≤ -(Ξ + 2 ^ 10))
    (hb : -(Ξ + 2 ^ 10 + 2 * M) ≤ b) (hb' : b ≤ -(Ξ + 2 ^ 10)) (hab : a ≤ b) :
    ‖(Φm (b + s * Complex.I) - (b + s * Complex.I))
        - (Φm (a + s * Complex.I) - (a + s * Complex.I))‖
      ≤ (1 / 150 + 1 / 31) * (b - a) := by
  have hQopen : IsOpen (Work.Pert.Qm Ξ α) := by
    simpa only [Work.Pert.Qm] using
      Work.Fatou.Qreg.isOpen_Qreg (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ)))
  have hseg : ∀ x ∈ Set.Icc a b, ((x : ℂ) + (s : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α :=
    fun x hx => (band_margins hΞ hM hInF1 hα hQAdm x s (le_trans ha hx.1)
      (le_trans hx.2 hb')).1
  have hpt : ∀ x ∈ Set.Icc a b,
      ‖deriv Φm ((x : ℂ) + (s : ℂ) * Complex.I) - 1‖ ≤ 1 / 150 + 1 / 31 :=
    fun x hx => band_deriv_sub_one_le (rr := rr) hF hΞ hM hInF1 hα hQAdm hNT hΦm
      (le_trans ha hx.1) (le_trans hx.2 hb')
  have hmain := dev_horiz_le (Φ := Φm) (Q := Work.Pert.Qm Ξ α) (s := s) (a := a) (b := b)
    (g := fun _ : ℝ => (1 / 150 + 1 / 31 : ℝ)) hQopen hab hseg hΦm.1 hpt continuousOn_const
  have hint : (∫ x in a..b, (1 / 150 + 1 / 31 : ℝ)) = (1 / 150 + 1 / 31) * (b - a) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hint] at hmain
  exact hmain

/-- **Horizontal transport of the deviation in the window strip.**  If the whole horizontal segment
`t ↦ t + i s`, `t ∈ [a,b]`, lies in the gate and satisfies
`(Ξ - 1/α).re + 1 < t < -Ξ - 3`, then `‖D (b + i s) - D (a + i s)‖ ≤ (1/150 + 1/31)(b - a)`. -/
theorem window_horiz_dev_le {Ξ : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {s a b : ℝ}
    (hF : MandelDim.FatouStatement)
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    (hseg : ∀ x ∈ Set.Icc a b, ((x : ℂ) + (s : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α)
    (hwin : ∀ x ∈ Set.Icc a b, ((Ξ : ℂ) - 1 / α).re + 1 < x ∧ x < -Ξ - 3)
    (hab : a ≤ b) :
    ‖(Φm (b + s * Complex.I) - (b + s * Complex.I))
        - (Φm (a + s * Complex.I) - (a + s * Complex.I))‖
      ≤ (1 / 150 + 1 / 31) * (b - a) := by
  have hQopen : IsOpen (Work.Pert.Qm Ξ α) := by
    simpa only [Work.Pert.Qm] using
      Work.Fatou.Qreg.isOpen_Qreg (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ)))
  have hpt : ∀ x ∈ Set.Icc a b,
      ‖deriv Φm ((x : ℂ) + (s : ℂ) * Complex.I) - 1‖ ≤ 1 / 150 + 1 / 31 := by
    intro x hx
    refine deriv_sub_one_le_window hF hQAdm hNT hΦm (hseg x hx) ?_ ?_
    · rw [re_of_re_im]; exact (hwin x hx).1
    · rw [re_of_re_im]; exact (by linarith [(hwin x hx).2] : x + 3 < -Ξ)
  have hmain := dev_horiz_le (Φ := Φm) (Q := Work.Pert.Qm Ξ α) (s := s) (a := a) (b := b)
    (g := fun _ : ℝ => (1 / 150 + 1 / 31 : ℝ)) hQopen hab hseg hΦm.1 hpt continuousOn_const
  have hint : (∫ x in a..b, (1 / 150 + 1 / 31 : ℝ)) = (1 / 150 + 1 / 31) * (b - a) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hint] at hmain
  exact hmain

end

end Work.Pert.V5
