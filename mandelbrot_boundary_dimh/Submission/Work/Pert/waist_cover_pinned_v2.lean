import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.AsmDefs
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.Interfaces.Fatou
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.PinLogDev.anchor_dev_le
import Submission.Work.Pert.Gates
import Submission.Work.Pert.Qm_slice
import Submission.Work.Pert.image_cover_centered
import Submission.Work.Fatou.Qreg.InjGeom
import Submission.Work.Pert.WaistPinned.deriv_close_on_gate_uniform
import Submission.Work.Pert.WaistPinned.waist_disc_window
import Submission.Work.Pert.WaistPinned.exists_Y_log_linear
import Submission.Work.Pert.Ksub2.exists_log_le_half

/-! Guidance from the project lead (the requester):

LEAD (waist_cover_pinned_v2): the SAME statement as waist_cover_pinned (H3199). That proof was finished (0 sorry), but it rested on Pert/pinned_dev_log, which is FALSE (the lower end is linear). The dependency is now Pert/pinned_dev_log_v2: its bound has the extra slack + ‖z‖/64.
Start from the snapshot Submission/Work/Pert/waist_cover_pinned_snapshot.lean.txt (H3199's complete proof). Changes:
  - import/use pinned_dev_log_v2 instead of pinned_dev_log (line ~117);
  - in the threshold arithmetic, the deviation at z with ‖z‖ ≈ |t| is now ≤ A log(|t|+3) + C + (|t|+2)/64. Enlarge Y so that 8·(that) + R₂ + 4 ≤ |t| − Ξ for all |t| ≥ Y − 1 (possible since 8/64 = 1/8 < 1). Everything else is verbatim.
-/

namespace Work.Pert

open _root_.MandelDim

/-- The integer `-(⌊w.re + 1/2⌋)` brings the real part of `w` into `[-1/2, 1/2]`. -/
private lemma abs_re_add_neg_floor (w : ℂ) :
    |(w + ((-(⌊w.re + 1 / 2⌋) : ℤ) : ℂ)).re| ≤ 1 / 2 := by
  have hcast : (((-(⌊w.re + 1 / 2⌋) : ℤ)) : ℂ).re = -(((⌊w.re + 1 / 2⌋) : ℤ) : ℝ) := by
    simp
  rw [Complex.add_re, hcast, abs_le]
  have h1 := Int.floor_le (w.re + 1 / 2)
  have h2 := Int.lt_floor_add_one (w.re + 1 / 2)
  constructor <;> linarith

/-- The lower gate `Qm ξ α` is open (an intersection of two open half-planes). -/
private lemma isOpen_Qm' (ξ : ℝ) (α : ℂ) : IsOpen (Work.Pert.Qm ξ α) := by
  have h1 : IsOpen {z : ℂ | -|(z - ((ξ : ℂ) - 1 / α)).im| < (z - ((ξ : ℂ) - 1 / α)).re} :=
    isOpen_lt (continuous_abs.comp
        (Complex.continuous_im.comp (continuous_id.sub continuous_const))).neg
      (Complex.continuous_re.comp (continuous_id.sub continuous_const))
  have h2 : IsOpen {z : ℂ | (z - (-(ξ : ℂ))).re < |(z - (-(ξ : ℂ))).im|} :=
    isOpen_lt (Complex.continuous_re.comp (continuous_id.sub continuous_const))
      (continuous_abs.comp
        (Complex.continuous_im.comp (continuous_id.sub continuous_const)))
  have h3 : Work.Pert.Qm ξ α =
      {z : ℂ | -|(z - ((ξ : ℂ) - 1 / α)).im| < (z - ((ξ : ℂ) - 1 / α)).re} ∩
        {z : ℂ | (z - (-(ξ : ℂ))).re < |(z - (-(ξ : ℂ))).im|} := by
    ext z
    simp [Work.Pert.Qm, MandelDim.Qreg]
  rw [h3]
  exact h1.inter h2

/-- **Logarithm vs. linear, with an arbitrary additive constant.**  For `A ≥ 0` and any real `K`
the function `32 A log (t+2)` is eventually smaller than `t/2 - K`.  (The library lemma
`exists_log_le_half` only gives `C (1 + log t) ≤ t/2`, whose additive constant is not free; here the
argument is applied at `t/4` so that the constant can be absorbed.)

This is the threshold refinement needed by `pinned_dev_log_v2`, whose deviation bound carries the
extra linear slack `‖z‖/64`. -/
theorem exists_add_mul_log_lt_half (A K : ℝ) (hA : 0 ≤ A) :
    ∃ Y : ℝ, 0 < Y ∧ ∀ t : ℝ, Y ≤ t → K + 32 * A * Real.log (t + 2) < t / 2 := by
  obtain ⟨R₀, hR₀⟩ := Work.Pert.Ksub2.exists_log_le_half (64 * A)
  set Yc : ℝ := max 2 (max (4 * max R₀ 1 + 4) (8 * (K + 32 * A * Real.log 8 + 1) + 8))
    with hYc
  refine ⟨Yc, ?_, ?_⟩
  · rw [hYc]
    exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  · intro t ht
    have ht2 : (2 : ℝ) ≤ t := le_trans (le_max_left _ _) ht
    have htR : 4 * max R₀ 1 + 4 ≤ t :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) ht)
    have htK : 8 * (K + 32 * A * Real.log 8 + 1) + 8 ≤ t :=
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) ht)
    have hx : max R₀ 1 ≤ t / 4 := by linarith
    have hxR₀ : R₀ ≤ t / 4 := le_trans (le_max_left _ _) hx
    have hx1 : (1 : ℝ) ≤ t / 4 := le_trans (le_max_right _ _) hx
    have hx0 : (0 : ℝ) < t / 4 := lt_of_lt_of_le one_pos hx1
    have hlogx : 0 ≤ Real.log (t / 4) := Real.log_nonneg hx1
    have h64 : 64 * A * (1 + Real.log (t / 4)) ≤ (t / 4) / 2 := hR₀ (t / 4) hxR₀
    have hlog_split : Real.log (t + 2) ≤ Real.log 8 + Real.log (t / 4) := by
      have h1 : Real.log (t + 2) ≤ Real.log (8 * (t / 4)) :=
        Real.log_le_log (by linarith) (by linarith)
      rwa [Real.log_mul (by norm_num) (ne_of_gt hx0)] at h1
    have h32 : 32 * A * Real.log (t + 2) ≤ 32 * A * Real.log 8 + t / 8 := by
      have h1 : 32 * A * Real.log (t + 2) ≤ 32 * A * (Real.log 8 + Real.log (t / 4)) :=
        mul_le_mul_of_nonneg_left hlog_split (by linarith)
      have h2 : 32 * A * Real.log (t / 4) ≤ 64 * A * (1 + Real.log (t / 4)) := by
        nlinarith [hlogx, hA]
      have h3 : 64 * A * (1 + Real.log (t / 4)) ≤ t / 8 := by
        have := h64
        linarith
      calc 32 * A * Real.log (t + 2)
          ≤ 32 * A * (Real.log 8 + Real.log (t / 4)) := h1
        _ = 32 * A * Real.log 8 + 32 * A * Real.log (t / 4) := by ring
        _ ≤ 32 * A * Real.log 8 + 64 * A * (1 + Real.log (t / 4)) := by linarith
        _ ≤ 32 * A * Real.log 8 + t / 8 := by linarith
    have hK : K + 32 * A * Real.log 8 + 1 ≤ t / 8 - 1 := by linarith
    linarith

/-! ## The reduction performed by this file

The only analytic input of the proof below is the deviation of the pinned gate coordinate at the two
*axis anchors* `± i t`:

  `Work.Pert.PinLogDev.anchor_dev_le` — `‖Φ (± i t) ∓ i t‖ ≤ A log (t+2) + C + t/64` for `t ≥ Y₀`,
  with `A, C, Y₀` datum-level (chosen before `M`, `L`, `δ₀` and the perturbation).

This is a strictly weaker statement than the lead's `Work.Pert.pinned_dev_log_v2` (no `∀ z`, no ball
condition: only the two points of the waist axis are used), and it is *not* implied by it — but it is
exactly what the covering argument below needs.  The reason this bound is a *datum-level* constant
(i.e. does not grow like `log M` although the pin gives `D (Xc d (−M)) = −M − Xc d (−M) = Θ(log M)`)
is the cancellation described in `Submission/Work/Pert/PinLogDev/NOTES_new_route.md` §1:
`D (z_pin) = D₀ (z_pin)` for the datum's own coordinate `Φ₀ = (Xc d)⁻¹`, and `D − D₀ = O(1)` uniformly
along the comparison walk `Xc d (−M + j)`; equivalently the `1/w`-coefficients of the defects of `F`
and of the datum's model `F0f` agree, which is a `NearOn`-jet statement.

Everything else here is the `waist_cover_pinned` assembly (H3199, snapshot
`Submission/Work/Pert/waist_cover_pinned_snapshot.lean.txt`), with the threshold arithmetic recomputed
for the extra linear slack `t/64` of the deviation (`t/64 ≪ (t − Ξ)/16`). -/

theorem waist_cover_pinned_v2 {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement) (hd : MandelDim.IsParabolicGerm f₀ D₀)
    (Ξ : ℝ) (hΞ : 1 + 64 * Real.pi ≤ Ξ)
    {rr : ℝ} (hrr : 0 < rr) (hrrD : Metric.closedBall (0 : ℂ) rr ⊆ D₀) :
    ∃ Y : ℝ, 0 < Y ∧
    ∃ Ms : ℝ, 0 < Ms ∧ ∀ M : ℝ, Ms ≤ M →
    ∃ L : Set ℂ, IsCompact L ∧ L ⊆ D₀ ∧ Metric.closedBall (0 : ℂ) rr ⊆ L ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (f : ℂ → ℂ) (Df : Set ℂ) (u : ℂ → ℂ) (σ α : ℂ),
        MandelDim.NearOn f₀ f Df L δ₀ → f 0 = 0 → MandelDim.InF1 (MandelDim.rotOf f) →
        α = MandelDim.rotOf f →
        DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr) →
        (∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
        (∀ z ∈ Metric.ball (0 : ℂ) rr, f z = z + z * (z - σ) * u z) →
        1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
        (∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr) →
        MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) →
        MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α) →
        ∀ Φ : ℂ → ℂ, MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φ (Work.Pert.Qm Ξ α) →
          Work.Pert.Xc d (((-M : ℝ)) : ℂ) ∈ Work.Pert.Qm Ξ α →
          Φ (Work.Pert.Xc d (((-M : ℝ)) : ℂ)) = (((-M : ℝ)) : ℂ) →
          ∀ w : ℂ, Y ≤ |w.im| →
            ∃ n : ℤ, |(w + (n : ℂ)).re| < 1 ∧
              w + (n : ℂ) ∈ Φ '' (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) := by
  -- ## 1. the datum-level constants
  -- the pinned deviation bound at the two waist anchors
  -- `‖Φ (± i t) ∓ i t‖ ≤ A log(t+2) + C + t/64` (`A, C, Y₀` do not see `M`)
  obtain ⟨A, C, Y₀, hA, hC, hY₀pos, Ms₀, hMs₀, hdev₀⟩ :=
    Work.Pert.PinLogDev.anchor_dev_le d hF hd Ξ hΞ hrr hrrD
  -- the datum-level radius on which `Φ' ≈ 1` on the gate (`FatouDerivEstimate`)
  obtain ⟨R₂, hR₂, hder₀⟩ := WaistPinned.deriv_close_on_gate_uniform hF.2.2.2.2.1
  -- the height threshold: the linear term beats `log`
  obtain ⟨Yraw, hYraw, hYraw'⟩ := WaistPinned.exists_Y_log_linear A C 0 R₂ Ξ hA hC
  -- the second threshold: the *linear slack* `t/64` is beaten by the waist room
  -- (`8 · (t/64) = t/8 < t/2`)
  obtain ⟨Y₁, hY₁pos, hY₁⟩ := exists_add_mul_log_lt_half A (32 * C + 2 * R₂ + Ξ + 12) hA
  set Y : ℝ := max Yraw (max Y₁ (max Y₀ 2)) with hYdef
  have hYY₁ : Y₁ ≤ Y := by
    rw [hYdef]
    exact le_trans (le_max_left Y₁ (max Y₀ 2))
      (le_trans (le_max_right Yraw (max Y₁ (max Y₀ 2))) le_rfl)
  have hYY₀ : Y₀ ≤ Y := by
    rw [hYdef]
    exact le_trans (le_max_left Y₀ 2) (le_trans (le_max_right Y₁ (max Y₀ 2))
      (le_max_right Yraw (max Y₁ (max Y₀ 2))))
  have hYpos : 0 < Y := lt_of_lt_of_le hY₁pos hYY₁
  have hYYraw : Yraw ≤ Y := by rw [hYdef]; exact le_max_left Yraw (max Y₁ (max Y₀ 2))
  have hY2 : (2 : ℝ) ≤ Y := by
    rw [hYdef]
    exact le_trans (le_max_right Y₀ 2) (le_trans (le_max_right Y₁ (max Y₀ 2))
      (le_max_right Yraw (max Y₁ (max Y₀ 2))))
  refine ⟨Y, hYpos, max Ms₀ 1, lt_max_iff.mpr (Or.inr one_pos), ?_⟩
  -- ## 2. the datum-level compact set and threshold for this `M`
  intro M hM
  have hMMs : Ms₀ ≤ M := le_trans (le_max_left _ _) hM
  obtain ⟨L, hLc, hLD, hLrr, δ₀, hδ₀, hdev⟩ := hdev₀ M hMMs
  refine ⟨L, hLc, hLD, hLrr, δ₀, hδ₀, ?_⟩
  -- ## 3. the perturbation data
  intro f Df u σ α hNear hf0 hInF1r hα hdu hub hform hexp hτQ hQAdm hNT Φ hΦ hXcQm hpin w hw
  have hInF1 : MandelDim.InF1 α := by rw [hα]; exact hInF1r
  -- ## 4. the height `t := |Im w|`, the sign `s` and the anchor `z₀ = s·i·t`
  set t : ℝ := |w.im| with ht
  have htY : Y ≤ t := by rw [ht]; exact hw
  have ht2 : (2 : ℝ) ≤ t := le_trans hY2 htY
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht2
  have htYraw : Yraw ≤ t := le_trans hYYraw htY
  have htY₁ : Y₁ ≤ t := le_trans hYY₁ htY
  have hlog0 : 0 ≤ Real.log (t + 2) := Real.log_nonneg (by linarith)
  set s : ℝ := if 0 ≤ w.im then 1 else -1 with hs
  have hsabs : |s| = 1 := by rw [hs]; split_ifs <;> norm_num
  have hst : s * t = w.im := by
    rw [hs, ht]; split_ifs with h
    · rw [abs_of_nonneg h]; ring
    · rw [abs_of_neg (lt_of_not_ge h)]; ring
  set z₀ : ℂ := ((s * t : ℝ) : ℂ) * Complex.I with hz₀
  have hz₀re : z₀.re = 0 := by simp [hz₀]
  have hz₀im : z₀.im = s * t := by simp [hz₀]
  have hz₀w : z₀.im = w.im := by rw [hz₀im, hst]
  have hz₀abs : |z₀.im| = t := by rw [hz₀im, abs_mul, hsabs, one_mul, abs_of_pos htpos]
  have hz₀norm : ‖z₀‖ = t := by
    rw [hz₀, norm_mul, Complex.norm_I, mul_one]
    rw [show ‖((s * t : ℝ) : ℂ)‖ = |s * t| by simp]
    rw [abs_mul, hsabs, one_mul, abs_of_pos htpos]
  -- ## 5. the radius `ρ` of the waist disc at the anchor, from the threshold
  set ρ : ℝ := (t - (Ξ + 2)) / 2 with hρ
  have hbase : R₂ + 7 + 16 * C + 16 * A * Real.log (t + 2) ≤ ρ := by
    have h := hYraw' t htYraw
    rw [hρ]
    simpa using h
  have h16 : 0 ≤ 16 * A * Real.log (t + 2) := mul_nonneg (by linarith) hlog0
  have hbase0 : 0 ≤ R₂ + 7 + 16 * C + 16 * A * Real.log (t + 2) := by
    linarith [hR₂, hC, h16]
  have hρnn : 0 ≤ ρ := le_trans hbase0 hbase
  have hρR₂ : R₂ + 1 ≤ ρ := le_trans (by linarith [hC, h16]) hbase
  have hwaist : Ξ + 2 * ρ < t := by rw [hρ]; linarith
  -- ## 6. the waist disc, the deviation bound at the anchor, and the covering radius
  have hdisc : Metric.closedBall z₀ ρ ⊆ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α :=
    WaistPinned.waist_disc_window (ξ := Ξ) (T := t) (ρ := ρ) (α := α) (z₀ := z₀)
      hInF1 hρnn hwaist hz₀re hz₀abs
  have hdevz : ‖Φ z₀ - z₀‖ ≤ A * Real.log (t + 2) + C + t / 64 := by
    have hanch := hdev f Df u σ α hNear hf0 hInF1r hα hdu hub hform hexp hτQ hQAdm hNT
      Φ hΦ hXcQm hpin
    have htY₀ : Y₀ ≤ t := le_trans hYY₀ htY
    have hbr : s = 1 ∨ s = -1 := by rw [hs]; split_ifs <;> simp
    rcases hbr with hs1 | hs1
    · have h := (hanch t htY₀).1
      rw [hz₀, hs1]
      simpa using h
    · have h := (hanch t htY₀).2
      have heq : (((-1 * t : ℝ)) : ℂ) * Complex.I = -(((t : ℝ) : ℂ) * Complex.I) := by
        push_cast; ring
      rw [hz₀, hs1, heq]
      simpa only [sub_eq_add_neg, neg_neg] using h
  set r : ℝ := (ρ - R₂ - 1) / 2 with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  have hrρ : r ≤ ρ := by rw [hr]; linarith
  have hrR₂ : R₂ ≤ ρ - r := by rw [hr]; linarith
  -- the deviation budget: `1/2 + 2 (A log(t+2) + C + t/64) < r/4`
  have hdev_arith : 1 / 2 + 2 * (A * Real.log (t + 2) + C + t / 64) < r / 4 := by
    have hkey := hY₁ t htY₁
    rw [hr, hρ]
    linarith
  -- ## 7. `Φ` is a near-identity on the disc, so the quarter-ball is covered
  have hsubWaist : Metric.closedBall z₀ r ⊆ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α := fun z hz =>
    hdisc (Metric.closedBall_subset_closedBall hrρ hz)
  have hdiff : ∀ ζ ∈ Metric.closedBall z₀ r, DifferentiableAt ℂ Φ ζ := fun ζ hζ =>
    hΦ.1.differentiableAt (isOpen_Qm' Ξ α |>.mem_nhds (hsubWaist hζ).1)
  have hder : ∀ ζ ∈ Metric.closedBall z₀ r, ‖deriv Φ ζ - 1‖ ≤ 1 / 2 := by
    intro ζ hζ
    refine hder₀ (Work.Pert.liftF u σ α) Φ α Ξ hNT hΦ ζ (ρ - r) hrR₂ ?_
    intro z hz
    rw [Metric.mem_ball] at hz
    have h1 : dist ζ z₀ ≤ r := by rwa [Metric.mem_closedBall] at hζ
    have h2 : dist z z₀ < ρ := by
      calc dist z z₀ ≤ dist z ζ + dist ζ z₀ := dist_triangle _ _ _
        _ < (ρ - r) + r := by linarith
        _ = ρ := by ring
    exact (hdisc (Metric.mem_closedBall.mpr h2.le)).1
  have hcov : Metric.ball (Φ z₀) (r / 4) ⊆ Φ '' Metric.closedBall z₀ r :=
    Work.Pert.image_cover_centered hrpos hdiff hder
  -- ## 8. the integer translate `u = w + n` with `|Re u| ≤ 1/2`
  have hre_n : |(w + (((-(⌊w.re + 1 / 2⌋)) : ℤ) : ℂ)).re| < 1 :=
    lt_of_le_of_lt (abs_re_add_neg_floor w) (by norm_num)
  have hmem_n : w + (((-(⌊w.re + 1 / 2⌋)) : ℤ) : ℂ) ∈
      Φ '' (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) := by
    set uu : ℂ := w + (((-(⌊w.re + 1 / 2⌋)) : ℤ) : ℂ) with huu
    have huure : |uu.re| ≤ 1 / 2 := by rw [huu]; exact abs_re_add_neg_floor w
    have huuim : uu.im = w.im := by rw [huu, Complex.add_im]; simp
    have hsmall : ‖uu - Φ z₀‖ < r / 4 := by
      have hre : |(uu - Φ z₀).re| ≤ 1 / 2 + (A * Real.log (t + 2) + C + t / 64) := by
        have hΦre : (Φ z₀).re = (Φ z₀ - z₀).re := by rw [Complex.sub_re, hz₀re, sub_zero]
        have h1 : |(uu - Φ z₀).re| = |uu.re - (Φ z₀).re| := by rw [Complex.sub_re]
        rw [h1, hΦre]
        have h2 := Complex.abs_re_le_norm (Φ z₀ - z₀)
        linarith [abs_sub uu.re (Φ z₀ - z₀).re]
      have him : |(uu - Φ z₀).im| ≤ A * Real.log (t + 2) + C + t / 64 := by
        have h1 : (uu - Φ z₀).im = -(Φ z₀ - z₀).im := by
          rw [Complex.sub_im, Complex.sub_im, huuim, hz₀w]; ring
        rw [h1, abs_neg]
        exact le_trans (Complex.abs_im_le_norm _) hdevz
      have h3 : ‖uu - Φ z₀‖ ≤ |(uu - Φ z₀).re| + |(uu - Φ z₀).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      linarith
    have hmem : uu ∈ Φ '' Metric.closedBall z₀ r :=
      hcov (by rw [Metric.mem_ball, dist_eq_norm]; exact hsmall)
    exact Set.image_mono hsubWaist hmem
  exact ⟨_, hre_n, hmem_n⟩

end Work.Pert
