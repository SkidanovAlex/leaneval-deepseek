import Mathlib
import Submission.Work.Pert.V5.Basics
import Submission.Work.Pert.V5.Facts
import Submission.Work.Pert.V5.horiz_dev_le_clear
import Submission.Work.Pert.V5.horiz_dev_le_split

/-!
# `Work.Pert.V5.horiz_dev_le_split_right`

Mirror image of `Work.Pert.V5.horiz_dev_le_split`: the horizontal transport of the deviation
`D w = Φm w - w` along a segment `[a, b]`, split at an interior point `c`, but now with the
*window* strip on the **right** piece `[c, b]` (so there the deviation is `(1/150 + 1/31)`-Lipschitz,
`window_horiz_dev_le`) and the *cleared* gate margins only on the **left** piece `[a, c]`
(`horiz_dev_le_clear`).  By the triangle inequality through `c`,

`‖D (b+is) - D (a+is)‖ ≤ (1/150 + 1/31)(b-c) + C₂ 2^6 (1+Ξ)(1+log(2+M))
                            + 2^24 (1+1/rr)(1+log(2+(c-a)))`.

As in the other split, no hypothesis is stated at `c` itself: the endpoints `a`, `b` are in the
gate and gate slices are intervals (`slice_interval`), so `[a,c] ⊆ [a,b]` is in the gate too.
-/

namespace Work.Pert.V5

set_option maxHeartbeats 2000000

theorem horiz_dev_le_split_right {Ξ rr M Rde C₂ : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {s a b c : ℝ}
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
    (ha : (a + s * Complex.I : ℂ) ∈ Work.Pert.Qm Ξ α)
    (hb : (b + s * Complex.I : ℂ) ∈ Work.Pert.Qm Ξ α)
    (hab : a ≤ b) (hac : a ≤ c) (hcb : c ≤ b)
    (hwin : ∀ ξ ∈ Set.Icc c b, ((Ξ : ℂ) - 1 / α).re + 1 < ξ ∧ ξ < -Ξ - 3)
    (hclear : ∀ ξ ∈ Set.Icc a c, ∀ k : ℤ,
      ‖α‖ * 2 ^ 10 ≤ ‖α * ((ξ : ℂ) + (s : ℂ) * Complex.I) - (k : ℂ)‖)
    (hlen : c - a ≤ 16 * (M + 2 + Ξ))
    (hlo : ∀ ξ ∈ Set.Icc a c,
      Real.sqrt 2 * Rde ≤ min (Work.Pert.V5.mgA Ξ α (ξ + s * Complex.I))
                               (Work.Pert.V5.mgB Ξ (ξ + s * Complex.I)))
    (hpos : ∀ ξ ∈ Set.Icc a c,
      1 ≤ min (Work.Pert.V5.mgA Ξ α (ξ + s * Complex.I))
              (Work.Pert.V5.mgB Ξ (ξ + s * Complex.I))) :
    ‖(Φm ((b : ℂ) + (s : ℂ) * Complex.I) - ((b : ℂ) + (s : ℂ) * Complex.I))
        - (Φm ((a : ℂ) + (s : ℂ) * Complex.I) - ((a : ℂ) + (s : ℂ) * Complex.I))‖
      ≤ (1 / 150 + 1 / 31) * (b - c)
        + C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
        + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + (c - a))) := by
  -- ## the left splitting point `c` lies in the gate, and so does the whole segment `[c,b]`
  have hcQ : ((c : ℂ) + (s : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α := by
    refine slice_interval (a := a) (b := b) (s := s) ha hb ?_
    rw [min_eq_left hab, max_eq_right hab]
    exact ⟨hac, hcb⟩
  have hseg_cb : ∀ x ∈ Set.Icc c b, ((x : ℂ) + (s : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α := by
    intro x hx
    refine slice_interval (a := a) (b := b) (s := s) ha hb ?_
    rw [min_eq_left hab, max_eq_right hab]
    exact ⟨le_trans hac hx.1, hx.2⟩
  -- ## admissibility of the window pair of vertices, from `hwin` at the two ends of `[c,b]`
  have hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) := by
    intro p hp q hq
    rw [Option.mem_some_iff] at hp hq
    subst hp
    subst hq
    have h1 : Ξ - (1 / α).re + 1 < c := by
      have h := (hwin c ⟨le_rfl, hcb⟩).1
      simpa only [Complex.sub_re, Complex.ofReal_re] using h
    have h2 : b < -Ξ - 3 := (hwin b ⟨hcb, le_rfl⟩).2
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.neg_re]
    linarith
  -- ## the two pieces
  have hwinpart := window_horiz_dev_le (Ξ := Ξ) (α := α) (σ := σ) (u := u) (Φm := Φm)
    (s := s) (a := c) (b := b) hF hQAdm hNT hΦm hseg_cb hwin hcb
  have hclearp := horiz_dev_le_clear (Ξ := Ξ) (rr := rr) (M := M) (Rde := Rde) (C₂ := C₂)
    (α := α) (σ := σ) (u := u) (Φm := Φm) (s := s) (a := a) (b := c)
    hΞ hrr hM hInF1 hα hRde hC₂ hσ hnorm hu hu2 hτQ hDE hNT hΦm ha hcQ hac
    hlen hclear hlo hpos
  -- ## triangle inequality through `c`
  have htri : ‖(Φm ((b : ℂ) + (s : ℂ) * Complex.I) - ((b : ℂ) + (s : ℂ) * Complex.I))
        - (Φm ((a : ℂ) + (s : ℂ) * Complex.I) - ((a : ℂ) + (s : ℂ) * Complex.I))‖
      ≤ ‖(Φm ((b : ℂ) + (s : ℂ) * Complex.I) - ((b : ℂ) + (s : ℂ) * Complex.I))
          - (Φm ((c : ℂ) + (s : ℂ) * Complex.I) - ((c : ℂ) + (s : ℂ) * Complex.I))‖
        + ‖(Φm ((c : ℂ) + (s : ℂ) * Complex.I) - ((c : ℂ) + (s : ℂ) * Complex.I))
          - (Φm ((a : ℂ) + (s : ℂ) * Complex.I) - ((a : ℂ) + (s : ℂ) * Complex.I))‖ := by
    have h : (Φm ((b : ℂ) + (s : ℂ) * Complex.I) - ((b : ℂ) + (s : ℂ) * Complex.I))
        - (Φm ((a : ℂ) + (s : ℂ) * Complex.I) - ((a : ℂ) + (s : ℂ) * Complex.I))
        = ((Φm ((b : ℂ) + (s : ℂ) * Complex.I) - ((b : ℂ) + (s : ℂ) * Complex.I))
            - (Φm ((c : ℂ) + (s : ℂ) * Complex.I) - ((c : ℂ) + (s : ℂ) * Complex.I)))
          + ((Φm ((c : ℂ) + (s : ℂ) * Complex.I) - ((c : ℂ) + (s : ℂ) * Complex.I))
            - (Φm ((a : ℂ) + (s : ℂ) * Complex.I) - ((a : ℂ) + (s : ℂ) * Complex.I))) := by
      ring
    rw [h]
    exact norm_add_le _ _
  -- align the logarithm's argument with the goal's `2 + (c - a)`
  rw [show (2 : ℝ) + c - a = 2 + (c - a) from by ring] at hclearp
  linarith [htri, hwinpart, hclearp]

end Work.Pert.V5
