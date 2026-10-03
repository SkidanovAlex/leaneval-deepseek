import Mathlib
import Submission.Work.Pert.V5.Facts
import Submission.Work.Pert.V5.horiz_dev_le_clear

/-!
# `Work.Pert.V5.horiz_dev_le_split`

The horizontal transport of the deviation `D w = Φm w - w` along a segment `[a, b]`, *split* at an
interior point `c`: on `[a, c]` the segment lies in the window strip (so the deviation is
`(1/150 + 1/31)`-Lipschitz, `window_horiz_dev_le`), while on `[c, b]` the gate margins only satisfy
the *cleared* separation hypotheses (`horiz_dev_le_clear`).  By the triangle inequality through `c`,

`‖D (b+is) - D (a+is)‖ ≤ (1/150 + 1/31)(c-a) + C₂ 2^6 (1+Ξ)(1+log(2+M))
                            + 2^24 (1+1/rr)(1+log(2+b-c))`.

The only point needing care is that no hypothesis is stated at `c` itself: `ha`, `hb` (the two
endpoints are in the gate) and the fact that gate slices are intervals (`slice_interval`) give the
whole segment `[a,b]`, hence in particular `[a,c]`.
-/

open Set Metric Filter
open scoped Topology

namespace Work.Pert.V5

set_option maxHeartbeats 4000000

theorem horiz_dev_le_split {Ξ rr M Rde C₂ : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {s a b c : ℝ}
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
    (hwin : ∀ ξ ∈ Set.Icc a c, ((Ξ : ℂ) - 1 / α).re + 1 < ξ ∧ ξ < -Ξ - 3)
    (hclear : ∀ ξ ∈ Set.Icc c b, ∀ k : ℤ,
      ‖α‖ * 2 ^ 10 ≤ ‖α * ((ξ : ℂ) + (s : ℂ) * Complex.I) - (k : ℂ)‖)
    (hlen : b - c ≤ 16 * (M + 2 + Ξ))
    (hlo : ∀ ξ ∈ Set.Icc c b,
      Real.sqrt 2 * Rde ≤ min (Work.Pert.V5.mgA Ξ α (ξ + s * Complex.I))
                               (Work.Pert.V5.mgB Ξ (ξ + s * Complex.I)))
    (hpos : ∀ ξ ∈ Set.Icc c b,
      1 ≤ min (Work.Pert.V5.mgA Ξ α (ξ + s * Complex.I))
              (Work.Pert.V5.mgB Ξ (ξ + s * Complex.I))) :
    ‖(Φm ((b : ℂ) + (s : ℂ) * Complex.I) - ((b : ℂ) + (s : ℂ) * Complex.I))
        - (Φm ((a : ℂ) + (s : ℂ) * Complex.I) - ((a : ℂ) + (s : ℂ) * Complex.I))‖
      ≤ (1 / 150 + 1 / 31) * (c - a)
        + C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
        + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + (b - c))) := by
  -- ## the intermediate point `c` lies in the gate, and so does the whole segment `[a,c]`
  have hcQ : ((c : ℂ) + (s : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α := by
    refine slice_interval (a := a) (b := b) (s := s) ha hb ?_
    rw [min_eq_left hab, max_eq_right hab]
    exact ⟨hac, hcb⟩
  have hseg_ac : ∀ x ∈ Set.Icc a c, ((x : ℂ) + (s : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α := by
    intro x hx
    refine slice_interval (a := a) (b := b) (s := s) ha hb ?_
    rw [min_eq_left hab, max_eq_right hab]
    exact ⟨hx.1, le_trans hx.2 hcb⟩
  -- ## admissibility of the window pair of vertices, from `hwin` at the two ends of `[a,c]`
  have hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) := by
    intro p hp q hq
    rw [Option.mem_some_iff] at hp hq
    subst hp
    subst hq
    have h1 : Ξ - (1 / α).re + 1 < a := by
      have h := (hwin a ⟨le_rfl, hac⟩).1
      simpa only [Complex.sub_re, Complex.ofReal_re] using h
    have h2 : c < -Ξ - 3 := (hwin c ⟨hac, le_rfl⟩).2
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.neg_re]
    linarith
  -- ## the two pieces
  have hwinpart := window_horiz_dev_le (Ξ := Ξ) (α := α) (σ := σ) (u := u) (Φm := Φm)
    (s := s) (a := a) (b := c) hF hQAdm hNT hΦm hseg_ac hwin hac
  have hclearp := horiz_dev_le_clear (Ξ := Ξ) (rr := rr) (M := M) (Rde := Rde) (C₂ := C₂)
    (α := α) (σ := σ) (u := u) (Φm := Φm) (s := s) (a := c) (b := b)
    hΞ hrr hM hInF1 hα hRde hC₂ hσ hnorm hu hu2 hτQ hDE hNT hΦm hcQ hb hcb
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
  -- align the logarithm's argument with the goal's `2 + (b - c)`
  rw [show (2 : ℝ) + b - c = 2 + (b - c) from by ring] at hclearp
  linarith [htri, hwinpart, hclearp]

end Work.Pert.V5
