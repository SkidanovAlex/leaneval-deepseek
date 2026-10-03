import Mathlib
import Submission.Work.Pert.V5.Basics
import Submission.Work.Pert.V5.Facts
import Submission.Work.Pert.V5.corridor_piece_bound
import Submission.Work.Pert.V5.ceil_cover_norm_le

/-!
# `Work.Pert.V5.corridor_left_cover`

The **cleared-piece cover** of the left corridor: the horizontal comparison between the band point
`q = z.re + i z₀.im` and the pin `z₀`, in the case `z.re ≤ z₀.re`, obtained by *subdividing* the
corridor into pieces of length `≤ 16 (M + 2 + Ξ)` and paying the (constant) cleared-piece bound on
each of them.

Ingredients:

* `slice_interval` (Basics): the gate slice at height `s = z₀.im` is an interval, so the whole
  corridor `[z.re, z₀.re] × {s}` is in the gate as soon as its two endpoints are;
* the two endpoints are in the gate: `q` because `mgA q ≥ √2 Rde > 0` (`hgood`) and
  `mgB q ≥ mgB z₀ > 0` (`z.re ≤ z₀.re`, `z₀ ∈ Qm`), and `z₀` because `hz₀`;
* the margins on the corridor: `mgA` is increasing and `mgB` decreasing in `Re` along a horizontal
  line, so `mgA ≥ mgA q ≥ √2 Rde` and `mgB ≥ mgB z₀ > 2 Rde + 2 ≥ √2 Rde`; the latter itself comes
  from the *clearing* hypothesis `closedBall z₀ (2 Rde + 2) ⊆ Qm`: shifting `z₀` to the right by
  `2 Rde + 2` stays in the gate, hence `mgB z₀ > 2 Rde + 2`;
* the strict margin `≥ 1` needed by `corridor_piece_bound`: at the band abscissa `z.re` one has
  `mgA (z.re + i s) ≥ 16 M ≥ 1` (`band_Qm_key_bound` bounds `Re (1/α)` from below), and `mgA` is
  increasing in `Re`;
* `ceil_cover_norm_le` + `corridor_piece_bound` then give the stated `⌈ℓ/m⌉ · P` bound.
-/

namespace Work.Pert.V5

open Set Metric

noncomputable section

/-! ## Elementary shape lemmas for the two marginals on a horizontal line -/

private lemma mgA_ofReal_line {Ξ : ℝ} {α : ℂ} (ξ s : ℝ) :
    mgA Ξ α ((ξ : ℂ) + (s : ℂ) * Complex.I)
      = ξ - Ξ + (1 / α).re + |s + (1 / α).im| := by
  simp [mgA, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]

private lemma mgB_ofReal_line {Ξ : ℝ} (ξ s : ℝ) :
    mgB Ξ ((ξ : ℂ) + (s : ℂ) * Complex.I) = |s| - Ξ - ξ := by
  simp [mgB, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]

/-- `mgA` is increasing along a horizontal line. -/
private lemma mgA_line_le {Ξ : ℝ} {α : ℂ} {s ξ η : ℝ} (h : ξ ≤ η) :
    mgA Ξ α ((ξ : ℂ) + (s : ℂ) * Complex.I)
      ≤ mgA Ξ α ((η : ℂ) + (s : ℂ) * Complex.I) := by
  rw [mgA_ofReal_line, mgA_ofReal_line]
  linarith

/-- `mgB` is decreasing along a horizontal line. -/
private lemma mgB_line_le {Ξ : ℝ} {s ξ η : ℝ} (h : ξ ≤ η) :
    mgB Ξ ((η : ℂ) + (s : ℂ) * Complex.I)
      ≤ mgB Ξ ((ξ : ℂ) + (s : ℂ) * Complex.I) := by
  rw [mgB_ofReal_line, mgB_ofReal_line]
  linarith

theorem corridor_left_cover {Ξ rr M Rde C₂ : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {z₀ : ℂ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M)
    (hRde : 0 < Rde) (hC₂ : 0 < C₂)
    (hInF1 : MandelDim.InF1 α) (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
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
    (hz₀ : z₀ ∈ Work.Pert.Qm Ξ α)
    (hcl : Metric.closedBall z₀ (2 * Rde + 2) ⊆ Work.Pert.Qm Ξ α)
    {z : ℂ} (hz : z ∈ Work.Pert.Qm Ξ α)
    (hzlo : -(Ξ + 2 ^ 10 + 2 * M) ≤ z.re) (hzhi : z.re ≤ -(Ξ + 2 ^ 10))
    (hcase : z.re ≤ z₀.re)
    (hgood : Real.sqrt 2 * Rde ≤ Work.Pert.V5.mgA Ξ α ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I))
    (hclear : ∀ ξ ∈ Set.Icc z.re z₀.re, ∀ k : ℤ,
      ‖α‖ * 2 ^ 10 ≤ ‖α * ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I) - (k : ℂ)‖) :
    ‖(Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I))
        - (Φm z₀ - z₀)‖
      ≤ ((Nat.ceil ((z₀.re - z.re) / (16 * (M + 2 + Ξ))) : ℝ))
          * (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
              + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ)))) := by
  have hsqrt2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hRde2 : (0 : ℝ) < 2 * Rde + 2 := by linarith
  have hsqRde : (0 : ℝ) < Real.sqrt 2 * Rde := mul_pos hsqrt2pos hRde
  have hsqle : Real.sqrt 2 * Rde ≤ 2 * Rde + 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2, hRde]
  -- ## the right endpoint `z₀` has `mgB > 2 Rde + 2` (the clearing hypothesis)
  have hz0ball : z₀ + (((2 * Rde + 2 : ℝ)) : ℂ) ∈ Work.Pert.Qm Ξ α := by
    apply hcl
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsub : z₀ + (((2 * Rde + 2 : ℝ)) : ℂ) - z₀ = (((2 * Rde + 2 : ℝ)) : ℂ) := by ring
    rw [hsub, Complex.norm_of_nonneg hRde2.le]
  have hmgBz0 : 2 * Rde + 2 < mgB Ξ z₀ := by
    have h := (mem_Qm_iff_mg.mp hz0ball).2
    have h1 : (z₀ + (((2 * Rde + 2 : ℝ)) : ℂ)).im = z₀.im := by simp
    have h2 : (z₀ + (((2 * Rde + 2 : ℝ)) : ℂ)).re = z₀.re + (2 * Rde + 2) := by simp
    rw [mgB, h1, h2] at h
    rw [mgB]
    linarith
  have hmgBz0' : 2 * Rde + 2 < mgB Ξ ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I) := by
    rw [Complex.re_add_im]; exact hmgBz0
  -- ## the left endpoint `q` is in the gate
  have hq_mgA : 0 < mgA Ξ α ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) :=
    lt_of_lt_of_le hsqRde hgood
  have hq_mgB : 0 < mgB Ξ ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) := by
    have h := mgB_line_le (Ξ := Ξ) (s := z₀.im) hcase
    linarith
  have hqmem : ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α :=
    mem_Qm_iff_mg.mpr ⟨hq_mgA, hq_mgB⟩
  -- ## the whole corridor lies in the gate
  have hcorr : ∀ ξ ∈ Set.Icc z.re z₀.re,
      ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α := by
    intro ξ hξ
    refine slice_interval (s := z₀.im) (a := z.re) (b := z₀.re) hqmem ?_ ?_
    · rw [Complex.re_add_im]; exact hz₀
    · rw [min_eq_left hcase, max_eq_right hcase]; exact hξ
  -- ## the two margin bounds on the corridor
  have hmgA_low : ∀ ξ ∈ Set.Icc z.re z₀.re,
      Real.sqrt 2 * Rde ≤ mgA Ξ α ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I) := by
    intro ξ hξ
    exact le_trans hgood (mgA_line_le (Ξ := Ξ) (α := α) (s := z₀.im) hξ.1)
  have hmgB_low : ∀ ξ ∈ Set.Icc z.re z₀.re,
      Real.sqrt 2 * Rde ≤ mgB Ξ ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I) := by
    intro ξ hξ
    have h := mgB_line_le (Ξ := Ξ) (s := z₀.im) hξ.2
    linarith
  have hmgA_ge : ∀ ξ ∈ Set.Icc z.re z₀.re,
      1 ≤ mgA Ξ α ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I) := by
    have hkey : 18 * M + 2 * Ξ + 2 ^ 10 ≤ (1 / α).re := band_Qm_key_bound hΞ hM hInF1 hα
    intro ξ hξ
    have hbound : 16 * M ≤ mgA Ξ α ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) := by
      rw [mgA_ofReal_line]
      have habs : (0 : ℝ) ≤ |z₀.im + (1 / α).im| := abs_nonneg _
      linarith
    have hM1 : (1 : ℝ) ≤ 16 * M := by nlinarith [hM]
    have := mgA_line_le (Ξ := Ξ) (α := α) (s := z₀.im) hξ.1
    linarith
  have hmgB_ge : ∀ ξ ∈ Set.Icc z.re z₀.re,
      1 ≤ mgB Ξ ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I) := by
    intro ξ hξ
    have h := mgB_line_le (Ξ := Ξ) (s := z₀.im) hξ.2
    linarith
  have hlo : ∀ ξ ∈ Set.Icc z.re z₀.re,
      Real.sqrt 2 * Rde ≤ min (mgA Ξ α ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I))
                                (mgB Ξ ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I)) :=
    fun ξ hξ => le_min (hmgA_low ξ hξ) (hmgB_low ξ hξ)
  have hpos : ∀ ξ ∈ Set.Icc z.re z₀.re,
      1 ≤ min (mgA Ξ α ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I))
              (mgB Ξ ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I)) :=
    fun ξ hξ => le_min (hmgA_ge ξ hξ) (hmgB_ge ξ hξ)
  -- ## the constant
  set BIG : ℝ := C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
      + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ))) with hBIGdef
  have hBIGnn : 0 ≤ BIG := by
    rw [hBIGdef]
    have h1 : (0 : ℝ) < 1 + Real.log (2 + 16 * (M + 2 + Ξ)) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + 16 * (M + 2 + Ξ) by linarith)
      linarith
    have h2 : (0 : ℝ) < 1 + Real.log (2 + M) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + M by linarith)
      linarith
    positivity
  have hmpos : (0 : ℝ) < 16 * (M + 2 + Ξ) := by linarith
  -- ## the per-piece bound
  have hpiece : ∀ x y : ℝ, z.re ≤ x → x ≤ y → y ≤ z₀.re → y - x ≤ 16 * (M + 2 + Ξ) →
      ‖(Φm ((y : ℂ) + (z₀.im : ℂ) * Complex.I) - ((y : ℂ) + (z₀.im : ℂ) * Complex.I))
        - (Φm ((x : ℂ) + (z₀.im : ℂ) * Complex.I)
            - ((x : ℂ) + (z₀.im : ℂ) * Complex.I))‖ ≤ BIG := by
    intro x y hx hxy hyc hlen
    rw [hBIGdef]
    refine corridor_piece_bound (s := z₀.im) (x := x) (y := y)
      hΞ hrr hM hRde hC₂ hInF1 hα hσ hnorm hu hu2 hτQ hDE hNT hΦm hxy hlen ?_ ?_ ?_ ?_
    · intro ξ hξ
      exact hcorr ξ ⟨le_trans hx hξ.1, le_trans hξ.2 hyc⟩
    · intro ξ hξ k
      exact hclear ξ ⟨le_trans hx hξ.1, le_trans hξ.2 hyc⟩ k
    · intro ξ hξ
      exact hlo ξ ⟨le_trans hx hξ.1, le_trans hξ.2 hyc⟩
    · intro ξ hξ
      exact hpos ξ ⟨le_trans hx hξ.1, le_trans hξ.2 hyc⟩
  -- ## assemble by the cover
  have hmain := ceil_cover_norm_le
    (f := fun ξ : ℝ => Φm ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I)
        - ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I))
    (a := z.re) (c := z₀.re) (m := 16 * (M + 2 + Ξ)) (P := BIG) hcase hmpos hBIGnn hpiece
  have hz0eq : ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I) = z₀ := Complex.re_add_im z₀
  rw [norm_sub_rev] at hmain
  simpa only [hz0eq] using hmain

end

end Work.Pert.V5
