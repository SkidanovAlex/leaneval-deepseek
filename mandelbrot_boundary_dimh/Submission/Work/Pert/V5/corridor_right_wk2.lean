import Mathlib
import Submission.Work.Pert.V5.Basics
import Submission.Work.Pert.V5.Facts
import Submission.Work.Pert.V5.Assembly2
import Submission.Work.Pert.V5.corridor_piece_bound
import Submission.Work.Pert.V5.ceil_cover_norm_le
import Submission.Work.Pert.V5.walk_data
import Submission.Work.Pert.V5.clear_lattice_band
import Submission.Work.Pert.V5.horiz_dev_le_tent_sharp
import Submission.Work.Pert.V5.horiz_dev_le_clear
import Submission.Work.Pert.V5.corridor_dev_affine
import Submission.Work.Pert.gate_walk_drift
import Submission.Work.Pert.V5.corridor_left_wk
import Submission.Work.Pert.V5.low_margin_in_window
import Submission.Work.Pert.V5.W2.Setup
import Submission.Work.Pert.V5.W2.xiB_gt_edge
import Submission.Work.Pert.V5.W2.bad_in_window
import Submission.Work.Pert.V5.W2.clear_pos
import Submission.Work.Pert.V5.W2.case1
import Submission.Work.Pert.V5.W2.case2win
import Submission.Work.Pert.V5.W2.case2esc
import Submission.Work.Pert.V5.W2.case2esc_partial

/-!
# `Work.Pert.V5.corridor_right_wk2` — the right corridor, certificate

Reusable pieces built here (all sorry-free):

* `mgA_line_mono` / `mgB_line_anti` — monotonicity of the two marginals along a horizontal line;
* `min_mg_line_le` — the tent identity on a horizontal segment;
* `band_point_mem` — a point at a band abscissa lies in the gate;
* `window_strip_mem` / `window_pointwise` / `window_seg_le` — the window strip
  `(Ξ - (1/α).re + 1, -Ξ-3)` is contained in the gate and the deviation `D = Φm - id` is
  `1/150 + 1/31`-Lipschitz there;
* `corridor_cover` — the cleared-piece cover bound (route P of the design's census) for a
  horizontal segment whose margin is `≥ √2 Rde` and `≥ 1` throughout.

The main theorem `corridor_right_wk2` is the certificate consumed by `gate_lin_asm_gen`.  Its proof
splits the corridor `[z₀.re, z.re]` at height `y₀ = z₀.im` into

* the window part `[c, z.re]`, `c := Ξ - (1/α).re + 1` (paid by the `|Im|` slot or by the
  `Kp`-slot through `window_seg_le`), and
* the part left of `c` (paid either by `corridor_cover`, whose hypotheses hold there because
  `mgA ≥ 2 Rde + 2` and `mgB ≥ √2 Rde`, or by the `F`-walk `walk_data`).
-/

namespace Work.Pert.V5

open Set Metric Filter
open scoped _root_.Topology

noncomputable section

set_option maxHeartbeats 4000000

/-! ## 0. Monotonicity of the marginals along a horizontal line -/

/-- `mgA` is monotone increasing in the abscissa along a horizontal line. -/
lemma mgA_line_mono {Ξ : ℝ} {α : ℂ} (s : ℝ) {x y : ℝ} (h : x ≤ y) :
    mgA Ξ α ((x : ℂ) + (s : ℂ) * Complex.I) ≤ mgA Ξ α ((y : ℂ) + (s : ℂ) * Complex.I) := by
  rw [mgA_re_im, mgA_re_im]; linarith

/-- `mgB` is monotone decreasing in the abscissa along a horizontal line. -/
lemma mgB_line_anti {Ξ : ℝ} (s : ℝ) {x y : ℝ} (h : x ≤ y) :
    mgB Ξ ((y : ℂ) + (s : ℂ) * Complex.I) ≤ mgB Ξ ((x : ℂ) + (s : ℂ) * Complex.I) := by
  rw [mgB_re_im, mgB_re_im]; linarith

/-- **Tent identity.**  On a horizontal segment `[a,b]`, the value of `min (mgA) (mgB)` is at
least `min (mgA a) (mgB b)` (the good margin of the *left* end in `mgA` and of the *right* end in
`mgB` propagates to the whole segment). -/
lemma min_mg_line_le {Ξ : ℝ} {α : ℂ} {s a b : ℝ} (hab : a ≤ b) {ξ : ℝ}
    (hξ : ξ ∈ Set.Icc a b) :
    min (mgA Ξ α ((a : ℂ) + (s : ℂ) * Complex.I))
        (mgB Ξ ((b : ℂ) + (s : ℂ) * Complex.I))
      ≤ min (mgA Ξ α ((ξ : ℂ) + (s : ℂ) * Complex.I))
            (mgB Ξ ((ξ : ℂ) + (s : ℂ) * Complex.I)) := by
  have h1 := mgA_line_mono (Ξ := Ξ) (α := α) s hξ.1
  have h4 := mgB_line_anti (Ξ := Ξ) s hξ.2
  have hlow : min (mgA Ξ α ((a : ℂ) + (s : ℂ) * Complex.I))
      (mgB Ξ ((b : ℂ) + (s : ℂ) * Complex.I)) ≤ mgA Ξ α ((a : ℂ) + (s : ℂ) * Complex.I) :=
    min_le_left _ _
  rcases le_total (mgA Ξ α ((ξ : ℂ) + (s : ℂ) * Complex.I))
      (mgB Ξ ((ξ : ℂ) + (s : ℂ) * Complex.I)) with h | h
  · rw [min_eq_left h]; exact le_trans hlow h1
  · rw [min_eq_right h]
    exact le_trans (min_le_right _ _) h4

/-! ## 1. Gate membership and the window strip -/

/-- A point at a band abscissa lies in the gate. -/
lemma band_point_mem {Ξ M : ℝ} {α : ℂ} (hΞ : 0 < Ξ) (hM : 2 ^ 10 ≤ M)
    (hInF1 : MandelDim.InF1 α) (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    {x s : ℝ} (hx : -(Ξ + 2 ^ 10 + 2 * M) ≤ x) (hx' : x ≤ -(Ξ + 2 ^ 10)) :
    ((x : ℂ) + (s : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α :=
  (band_margins hΞ hM hInF1 hα hQAdm x s hx hx').1

/-- **The window strip is contained in the gate.**  For `Ξ - (1/α).re + 1 < Re z < -Ξ - 3` we have
`mgA Ξ α z > 1` and `mgB Ξ z > 3`. -/
lemma window_strip_mem {Ξ : ℝ} {α : ℂ} {z : ℂ}
    (h1 : ((Ξ : ℂ) - 1 / α).re + 1 < z.re) (h2 : z.re < -Ξ - 3) :
    z ∈ Work.Pert.Qm Ξ α ∧ 1 < mgA Ξ α z ∧ 3 < mgB Ξ z := by
  have hre : ((Ξ : ℂ) - 1 / α).re = Ξ - (1 / α).re := by
    rw [Complex.sub_re, Complex.ofReal_re]
  have hA : 1 < mgA Ξ α z := by
    simp only [mgA]
    have him : (0 : ℝ) ≤ |z.im + (1 / α).im| := abs_nonneg _
    linarith
  have hB : 3 < mgB Ξ z := by
    simp only [mgB]
    have hz : z.re + Ξ < -3 := by linarith
    have him : (0 : ℝ) ≤ |z.im| := abs_nonneg _
    linarith
  exact ⟨mem_Qm_iff_mg.mpr ⟨by linarith [hA], by linarith [hB]⟩, hA, hB⟩

/-- Pointwise deviation bound in the window strip. -/
theorem window_pointwise {Ξ rr M : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {z : ℂ}
    (hF : MandelDim.FatouStatement)
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    (h1 : ((Ξ : ℂ) - 1 / α).re + 1 < z.re) (h2 : z.re < -Ξ - 3) :
    ‖deriv Φm z - 1‖ ≤ 1 / 150 + 1 / 31 :=
  deriv_sub_one_le_window hF hQAdm hNT hΦm (window_strip_mem h1 h2).1 h1 (by linarith)

/-- A horizontal segment inside the window strip: deviation bound. -/
theorem window_seg_le {Ξ rr M : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {s a b : ℝ}
    (hF : MandelDim.FatouStatement)
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    (hab : a ≤ b)
    (hwin : ∀ x ∈ Set.Icc a b, ((Ξ : ℂ) - 1 / α).re + 1 < x ∧ x < -Ξ - 3) :
    ‖(Φm ((b : ℂ) + (s : ℂ) * Complex.I) - ((b : ℂ) + (s : ℂ) * Complex.I))
        - (Φm ((a : ℂ) + (s : ℂ) * Complex.I) - ((a : ℂ) + (s : ℂ) * Complex.I))‖
      ≤ (1 / 150 + 1 / 31) * (b - a) :=
  window_horiz_dev_le (s := s) hF hQAdm hNT hΦm
    (fun x hx => (window_strip_mem (z := ((x : ℂ) + (s : ℂ) * Complex.I))
        (by simpa using (hwin x hx).1) (by simpa using (hwin x hx).2)).1)
    (fun x hx => ⟨(hwin x hx).1, by linarith [(hwin x hx).2]⟩) hab

/-- The band strip is contained in the window strip (via `band_Qm_key_bound`). -/
lemma band_re_in_window {Ξ M : ℝ} {α : ℂ} (hΞ : 0 < Ξ) (hM : 2 ^ 10 ≤ M)
    (hInF1 : MandelDim.InF1 α) (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    {x : ℝ} (hx : -(Ξ + 2 ^ 10 + 2 * M) ≤ x) (hx' : x ≤ -(Ξ + 2 ^ 10)) :
    ((Ξ : ℂ) - 1 / α).re + 1 < x ∧ x < -Ξ - 3 := by
  have hkey : 18 * M + 2 * Ξ + 2 ^ 10 ≤ (1 / α).re := band_Qm_key_bound hΞ hM hInF1 hα
  have hre : ((Ξ : ℂ) - 1 / α).re = Ξ - (1 / α).re := by
    rw [Complex.sub_re, Complex.ofReal_re]
  constructor
  · rw [hre]; linarith
  · nlinarith [show (3 : ℝ) < 2 ^ 10 by norm_num]

/-! ## 2. The cleared-piece cover bound (route P) -/

/-- **Route P** (cleared-piece cover) for an arbitrary horizontal segment at height `s`: if the
segment lies in the gate, its margin is `≥ √2 Rde` and `≥ 1` throughout, and the lattice clearance
holds, then the deviation is at most
`⌈(c-a)/(16(M+2+Ξ))⌉ · (C₂ 2^6 (1+Ξ) (1+log(2+M)) + 2^24 (1+1/rr) (1+log(2+16(M+2+Ξ))))`. -/
theorem corridor_cover {Ξ rr M Rde C₂ : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {s a c : ℝ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M)
    (hRde : 0 < Rde) (hC₂ : 0 < C₂)
    (hInF1 : MandelDim.InF1 α) (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
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
    (hac : a ≤ c)
    (hgate : ∀ ξ ∈ Set.Icc a c, ((ξ : ℂ) + (s : ℂ) * Complex.I) ∈ Work.Pert.Qm Ξ α)
    (hclear : ∀ ξ ∈ Set.Icc a c, ∀ k : ℤ,
      ‖α‖ * 2 ^ 10 ≤ ‖α * ((ξ : ℂ) + (s : ℂ) * Complex.I) - (k : ℂ)‖)
    (hlo : ∀ ξ ∈ Set.Icc a c,
      Real.sqrt 2 * Rde ≤ min (mgA Ξ α ((ξ : ℂ) + (s : ℂ) * Complex.I))
                              (mgB Ξ ((ξ : ℂ) + (s : ℂ) * Complex.I)))
    (hpos : ∀ ξ ∈ Set.Icc a c,
      1 ≤ min (mgA Ξ α ((ξ : ℂ) + (s : ℂ) * Complex.I))
              (mgB Ξ ((ξ : ℂ) + (s : ℂ) * Complex.I))) :
    ‖(Φm ((c : ℂ) + (s : ℂ) * Complex.I) - ((c : ℂ) + (s : ℂ) * Complex.I))
        - (Φm ((a : ℂ) + (s : ℂ) * Complex.I) - ((a : ℂ) + (s : ℂ) * Complex.I))‖
      ≤ ((Nat.ceil ((c - a) / (16 * (M + 2 + Ξ))) : ℝ))
          * (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
              + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ)))) := by
  set BIG : ℝ := C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
      + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ))) with hBIG
  have hBIGnn : 0 ≤ BIG := by
    rw [hBIG]
    have h1 : (0 : ℝ) < 1 + Real.log (2 + M) := by
      have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 + M by linarith)
      linarith
    have h2 : (0 : ℝ) < 1 + Real.log (2 + 16 * (M + 2 + Ξ)) := by
      have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 + 16 * (M + 2 + Ξ) by linarith)
      linarith
    have h3 : (0 : ℝ) < 1 + 1 / rr := by positivity
    positivity
  have hm : (0 : ℝ) < 16 * (M + 2 + Ξ) := by linarith
  have hpiece : ∀ x y : ℝ, a ≤ x → x ≤ y → y ≤ c → y - x ≤ 16 * (M + 2 + Ξ) →
      ‖(Φm ((y : ℂ) + (s : ℂ) * Complex.I) - ((y : ℂ) + (s : ℂ) * Complex.I))
        - (Φm ((x : ℂ) + (s : ℂ) * Complex.I) - ((x : ℂ) + (s : ℂ) * Complex.I))‖ ≤ BIG := by
    intro x y hax hxy hyc hlen
    rw [hBIG]
    exact corridor_piece_bound (s := s) (x := x) (y := y)
      hΞ hrr hM hRde hC₂ hInF1 hα hσ hnorm hu hu2 hτQ hDE hNT hΦm hxy hlen
      (fun ξ hξ => hgate ξ ⟨le_trans hax hξ.1, le_trans hξ.2 hyc⟩)
      (fun ξ hξ k => hclear ξ ⟨le_trans hax hξ.1, le_trans hξ.2 hyc⟩ k)
      (fun ξ hξ => hlo ξ ⟨le_trans hax hξ.1, le_trans hξ.2 hyc⟩)
      (fun ξ hξ => hpos ξ ⟨le_trans hax hξ.1, le_trans hξ.2 hyc⟩)
  exact ceil_cover_norm_le
    (f := fun ξ : ℝ => Φm ((ξ : ℂ) + (s : ℂ) * Complex.I) - ((ξ : ℂ) + (s : ℂ) * Complex.I))
    (a := a) (c := c) (m := 16 * (M + 2 + Ξ)) (P := BIG) hac hm hBIGnn hpiece

/-! ## 3. The low-margin part of the corridor is in the window (corollary of the
delegated lemma `Work.Pert.V5.low_margin_in_window`). -/

/-- **Every point of `[z₀.re, Ξ - (1/α).re + 1]` has `min (mgA) (mgB) ≥ √2 Rde`.**  The `mgA` part
is `mgA ≥ mgA z₀ > 2Rde + 2` (`zo_margins`, monotonicity); the `mgB` part is the contrapositive of
`low_margin_in_window`. -/
lemma left_part_margins {Ξ M Rde : ℝ} {α : ℂ} {z₀ : ℂ} {ξ : ℝ}
    (hΞ : 0 < Ξ) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ))) (hRde : 0 < Rde)
    (hcl : Metric.closedBall z₀ (2 * Rde + 2) ⊆ Work.Pert.Qm Ξ α)
    (hξlo : z₀.re ≤ ξ)
    (hξc : ξ ≤ ((Ξ : ℂ) - 1 / α).re + 1) :
    Real.sqrt 2 * Rde ≤ min (mgA Ξ α ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I))
                            (mgB Ξ ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I)) := by
  have hA := (Work.Pert.V5.zo_margins hRde hcl).1
  have hAmono := mgA_line_mono (Ξ := Ξ) (α := α) z₀.im hξlo
  have hsqrt : Real.sqrt 2 * Rde < 2 * Rde + 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2, hRde]
  have hmgA : Real.sqrt 2 * Rde ≤ mgA Ξ α ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I) := by
    have h2 : mgA Ξ α ((z₀.re : ℂ) + (z₀.im : ℂ) * Complex.I) = mgA Ξ α z₀ := by
      rw [Complex.re_add_im]
    rw [h2] at hAmono
    linarith
  have hmgB : Real.sqrt 2 * Rde ≤ mgB Ξ ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I) := by
    by_contra hcon
    push_neg at hcon
    have := Work.Pert.V5.low_margin_in_window (Ξ := Ξ) (M := M) (Rde := Rde) (α := α) (z₀ := z₀)
      (ξ := ξ) hΞ hM hInF1 hα hRde hcl hξlo hcon
    linarith
  exact le_min hmgA hmgB

/-- The `(N)`-conjunct with `N = 1` (from `P_le_B_pin` and the pin relation `pin_le`). -/
lemma N1_conjunct {Ξ rr M Kp Rde C₂ : ℝ} {α : ℂ} {z₀ : ℂ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M) (hKp : 0 ≤ Kp)
    (hRde : 0 < Rde) (hC₂ : 0 < C₂)
    (hcl : Metric.closedBall z₀ (2 * Rde + 2) ⊆ Work.Pert.Qm Ξ α)
    (hpinbd : ‖z₀ + (((M : ℝ)) : ℂ)‖ ≤ Kp * (1 + Real.log (2 + M))) :
    ((1 : ℕ) : ℝ) * (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
          + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ))))
      ≤ C₂ * 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
        + 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
        + Kp * 2 ^ 38 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) := by
  have hpin := pin_le hpinbd (zo_margins hRde hcl).2
  simpa using P_le_B_pin hΞ hrr hM hKp hRde hC₂ hpin

theorem corridor_right_wk2 {Ξ rr M Kp Rde C₂ : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {z₀ : ℂ}
    (hF : MandelDim.FatouStatement)
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M) (hKp : 0 ≤ Kp)
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
    (hpinbd : ‖z₀ + (((M : ℝ)) : ℂ)‖ ≤ Kp * (1 + Real.log (2 + M)))
    {z : ℂ} (hz : z ∈ Work.Pert.Qm Ξ α)
    (hzlo : -(Ξ + 2 ^ 10 + 2 * M) ≤ z.re) (hzhi : z.re ≤ -(Ξ + 2 ^ 10))
    (ht : 4 * Rde ≤ |z.im|) (hcase : z₀.re ≤ z.re) :
    ∃ (N : ℕ) (W : ℝ),
      W + (1 / 150 + 1 / 31) * |z.im|
        ≤ |z.im| / 8 + Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) ∧
      (N : ℝ) * (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
            + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ))))
        ≤ C₂ * 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
          + 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
          + Kp * 2 ^ 38 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) ∧
      ‖(Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I))
          - (Φm z₀ - z₀)‖
        ≤ W + (N : ℝ) * (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
            + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ)))) := by
  by_cases hshort : z.re - z₀.re ≤ 16 * (M + 2 + Ξ)
  · -- ===== Case 1: short corridor: one route-P piece + the window piece =====
    have hdev := Work.Pert.V5.W2.case1 hF hΞ hrr hM hKp hRde hC₂ hInF1 hα hQAdm hσ hnorm
      hu hu2 hτQ hDE hNT hΦm hz₀ hcl hpinbd hz hzlo hzhi ht hcase hshort
    refine ⟨1, (1 / 150 + 1 / 31) * Real.sqrt 2 * Rde, ?_, ?_, ?_⟩
    · have h1 := rw_slot_bad hRde ht
      have h2 : (0 : ℝ) ≤ Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) := by
        have hL : (0 : ℝ) ≤ 1 + Real.log (2 + M) := by
          have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + M by linarith)
          linarith
        have hK : (0 : ℝ) ≤ 1 + Ξ + 1 / Ξ + 1 / rr := by
          have h1 : (0 : ℝ) ≤ 1 / Ξ := div_nonneg zero_le_one (le_of_lt hΞ)
          have h2 : (0 : ℝ) ≤ 1 / rr := div_nonneg zero_le_one (le_of_lt hrr)
          linarith
        positivity
      linarith
    · exact N1_conjunct hΞ hrr hM hKp hRde hC₂ hcl hpinbd
    · simpa using hdev
  · push_neg at hshort
    by_cases hwin : ((Ξ : ℂ) - 1 / α).re + 2 < z₀.re
    · -- ===== Case 2a: the whole corridor is inside the window strip =====
      obtain ⟨hd1, hd2⟩ := Work.Pert.V5.W2.case2win hF hΞ hrr hM hKp hRde hC₂ hInF1 hα hQAdm
        hσ hnorm hu hu2 hτQ hDE hNT hΦm hz₀ hcl hpinbd hz hzlo hzhi ht hcase hshort hwin
      refine ⟨0, (1 / 150 + 1 / 31) * (z.re - z₀.re), ?_, ?_, ?_⟩
      · have h3 : (1 / 150 + 1 / 31) * |z.im| ≤ |z.im| / 8 := by
          have hc : (1 / 150 + 1 / 31 : ℝ) ≤ 1 / 8 := by norm_num
          nlinarith [abs_nonneg z.im]
        linarith
      · have hL : (0 : ℝ) ≤ 1 + Real.log (2 + M) := by
          have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + M by linarith)
          linarith
        have hK : (0 : ℝ) ≤ 1 + Ξ + 1 / Ξ + 1 / rr := by
          have h1 : (0 : ℝ) ≤ 1 / Ξ := div_nonneg zero_le_one (le_of_lt hΞ)
          have h2 : (0 : ℝ) ≤ 1 / rr := div_nonneg zero_le_one (le_of_lt hrr)
          linarith
        have h2' : (0 : ℝ) ≤ C₂ := le_of_lt hC₂
        have h40 : (0 : ℝ) ≤ 2 ^ 40 := by norm_num
        have h38 : (0 : ℝ) ≤ 2 ^ 38 := by norm_num
        have hgoal : (0 : ℝ) ≤ C₂ * 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
            + 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
            + Kp * 2 ^ 38 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) := by
          have h1 : (0 : ℝ) ≤ C₂ * 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) := by
            have := mul_nonneg (mul_nonneg (mul_nonneg h2' h40) hK) hL
            simpa [mul_assoc] using this
          have h2 : (0 : ℝ) ≤ 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) := by
            have := mul_nonneg (mul_nonneg h40 hK) hL
            simpa [mul_assoc] using this
          have h3 : (0 : ℝ) ≤ Kp * 2 ^ 38 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) := by
            have := mul_nonneg (mul_nonneg (mul_nonneg hKp h38) hK) hL
            simpa [mul_assoc] using this
          linarith
        simpa using hgoal
      · simpa using hd1
    · push_neg at hwin
      -- ===== Case 2b: the corridor escapes the window to the left =====
      by_cases hroom : (17 / 16 : ℝ) * (z.re - z₀.re + 1) + 1 ≤ Work.Pert.V5.mgB Ξ z₀
      · obtain ⟨W, hW1, hW2⟩ := Work.Pert.V5.W2.case2esc hF hΞ hrr hM hKp hRde hC₂ hInF1 hα
          hQAdm hσ hnorm hu hu2 hτQ hDE hNT hΦm hz₀ hcl hpinbd hz hzlo hzhi ht hcase
          hshort hwin hroom
        refine ⟨1, W, ?_, ?_, ?_⟩
        · linarith
        · exact N1_conjunct hΞ hrr hM hKp hRde hC₂ hcl hpinbd
        · simpa using hW2
      · push_neg at hroom
        obtain ⟨W, hW1, hW2⟩ := Work.Pert.V5.W2.case2esc_partial hF hΞ hrr hM hKp hRde hC₂
          hInF1 hα hQAdm hσ hnorm hu hu2 hτQ hDE hNT hΦm hz₀ hcl hpinbd hz hzlo hzhi ht
          hcase hshort hwin hroom
        refine ⟨1, W, ?_, ?_, ?_⟩
        · linarith
        · exact N1_conjunct hΞ hrr hM hKp hRde hC₂ hcl hpinbd
        · simpa using hW2

end

end Work.Pert.V5
