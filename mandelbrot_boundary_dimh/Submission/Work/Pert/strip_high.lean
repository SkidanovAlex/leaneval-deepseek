import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.image_cover_centered
import Submission.Work.Pert.deriv_Phi_close_on_gate
import Submission.Work.Pert.cone_subset_Qm
import Submission.Work.Pert.closedBall_subset_Qm
import Submission.Work.Pert.deriv_sub_id_le_on_cone
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.Interfaces.Parabolic

/-!
# PERT · `strip_high`: level-0 coverage of the half-strips by `Φm '' (Qm ξ₁ α)`

For a Fatou coordinate `Φ` of a near-translation `F` on the gate `Qm ξ₁ α` (the lower gate of
Shishikura §4.2), the image `Φ '' (Qm ξ₁ α)` contains the whole half-strip
`{|Re uu| ≤ 1, Y ≤ |Im uu|}` for a threshold `Y` depending only on the data (`F`, `Φ`, `ξ₁`, `α`).

The argument is purely local: **no** end asymptotics (`FatouEnds`), no pinning, no `FatouUnique`.

* **(deviation bound)**  On the deep cone `{|Re z| ≤ |Im z|/2}` of the gate the derivative of
  `dev := Φ - id` satisfies `‖dev' z‖ ≤ C₂ / |z.im| + 1/31`: the `1/R`-estimate of Shishikura
  A.2.4(i) (`MandelDim.FatouDerivEstimate`, second conjunct) applied on the ball of radius
  `|z.im|/8`, whose inradius grows linearly, plus the crude `1/31 = (1/32)/(31/32)` coming from the
  near-translation defect.  The constant term `1/31` is harmless: on the convex set
  `S = {T ≤ |Im w|, |Re w| ≤ |Im w|/2}` the mean value inequality gives
  `‖dev z - dev z₀‖ ≤ M‖z - z₀‖` with `M := C₂/T + 1/31`, and `T ≥ 1024 C₂` makes `M ≤ 1/24`.
  With `z₀ = ±iT` and `‖z - z₀‖ ≤ (3/2)|Im z| + T` this yields the bound
  `‖Φ z - z‖ ≤ C + |z.im|/16` (`dev_le_on_cone`) with the *sharp* coefficient `1/16`.
* **(covering)**  For `uu` with `|Re uu| ≤ 1` and `|Im uu|` large apply
  `Work.Pert.image_cover_centered` with centre `z₀ := uu` and radius `r := 4‖Φ uu - uu‖ + 1`:
  `uu ∈ ball (Φ uu) (r/4) ⊆ Φ '' closedBall uu r`, the derivative is `≈ 1` on that disk
  (`deriv_Phi_close_on_gate`), and `closedBall uu r ⊆ Qm ξ₁ α` because `r ≤ |Im uu|/3`
  (`closedBall_subset_Qm`).  This is `gate_strip_cover`, and `strip_high` is its assembly.
-/

namespace Work.Pert

open MandelDim Complex Set Metric Filter

noncomputable section

/-! ## The gate is open -/

/-- The gate `Qm ξ₁ α` is open (an intersection of open half planes). -/
theorem isOpen_Qm (ξ₁ : ℝ) (α : ℂ) : IsOpen (Qm ξ₁ α) := by
  have h1 : IsOpen {z : ℂ | -|(z - ((ξ₁ : ℂ) - 1 / α)).im| < (z - ((ξ₁ : ℂ) - 1 / α)).re} :=
    isOpen_lt (continuous_abs.comp
        (Complex.continuous_im.comp (continuous_id.sub continuous_const))).neg
      (Complex.continuous_re.comp (continuous_id.sub continuous_const))
  have h2 : IsOpen {z : ℂ | (z - (-(ξ₁ : ℂ))).re < |(z - (-(ξ₁ : ℂ))).im|} :=
    isOpen_lt (Complex.continuous_re.comp (continuous_id.sub continuous_const))
      (continuous_abs.comp (Complex.continuous_im.comp (continuous_id.sub continuous_const)))
  have h3 : Qm ξ₁ α =
      {z : ℂ | -|(z - ((ξ₁ : ℂ) - 1 / α)).im| < (z - ((ξ₁ : ℂ) - 1 / α)).re} ∩
        {z : ℂ | (z - (-(ξ₁ : ℂ))).re < |(z - (-(ξ₁ : ℂ))).im|} := by
    ext z
    simp [Qm, MandelDim.Qreg]
  rw [h3]
  exact h1.inter h2

/-! ## Convexity of the two arms of the deep cone -/

private lemma convex_cone_up {T : ℝ} :
    Convex ℝ {w : ℂ | T ≤ w.im ∧ |w.re| ≤ w.im / 2} := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hxim : (a • x + b • y).im = a * x.im + b * y.im := by simp [Complex.add_im]
  have hxre : (a • x + b • y).re = a * x.re + b * y.re := by simp [Complex.add_re]
  refine ⟨by
    rw [hxim]
    have h1 : a * T ≤ a * x.im := mul_le_mul_of_nonneg_left hx1 ha
    have h2 : b * T ≤ b * y.im := mul_le_mul_of_nonneg_left hy1 hb
    have h3 : a * T + b * T = T := by rw [← add_mul, hab, one_mul]
    linarith, ?_⟩
  rw [hxre, hxim]
  calc |a * x.re + b * y.re| ≤ |a * x.re| + |b * y.re| := abs_add_le _ _
    _ = a * |x.re| + b * |y.re| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * (x.im / 2) + b * (y.im / 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hx2 ha) (mul_le_mul_of_nonneg_left hy2 hb)
    _ = (a * x.im + b * y.im) / 2 := by ring

private lemma convex_cone_dn {T : ℝ} :
    Convex ℝ {w : ℂ | w.im ≤ -T ∧ |w.re| ≤ -w.im / 2} := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hxim : (a • x + b • y).im = a * x.im + b * y.im := by simp [Complex.add_im]
  have hxre : (a • x + b • y).re = a * x.re + b * y.re := by simp [Complex.add_re]
  refine ⟨by
    rw [hxim]
    have h1 : a * x.im ≤ a * (-T) := mul_le_mul_of_nonneg_left hx1 ha
    have h2 : b * y.im ≤ b * (-T) := mul_le_mul_of_nonneg_left hy1 hb
    have h3 : a * (-T) + b * (-T) = -T := by rw [← add_mul, hab, one_mul]
    linarith, ?_⟩
  rw [hxre, hxim]
  calc |a * x.re + b * y.re| ≤ |a * x.re| + |b * y.re| := abs_add_le _ _
    _ = a * |x.re| + b * |y.re| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * (-x.im / 2) + b * (-y.im / 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hx2 ha) (mul_le_mul_of_nonneg_left hy2 hb)
    _ = -(a * x.im + b * y.im) / 2 := by ring

/-! ## The deviation bound on the deep cone -/

theorem dev_le_on_cone (hDE : MandelDim.FatouDerivEstimate) {F Φ : ℂ → ℂ} {ξ₁ : ℝ} {α : ℂ}
    (hNT : MandelDim.NearTranslationL1 F (Qm ξ₁ α))
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Qm ξ₁ α)) :
    ∃ C T : ℝ, 0 ≤ C ∧ 0 < T ∧ ∀ z : ℂ, T ≤ |z.im| → |z.re| ≤ |z.im| / 2 →
      ‖Φ z - z‖ ≤ C + |z.im| / 16 := by
  obtain ⟨C₂, T₂, hC₂, hT₂, hder⟩ := deriv_sub_id_le_on_cone hDE hNT hΦ
  obtain ⟨Tg, hTg, hcone⟩ := cone_subset_Qm (ξ₁ := ξ₁) (α := α)
  set T : ℝ := max (max T₂ (max Tg 1)) (1024 * C₂ + 1) with hTdef
  have hTpos : 0 < T := by
    rw [hTdef]
    exact lt_max_iff.mpr (Or.inl (lt_max_iff.mpr (Or.inl hT₂)))
  have hTgeT₂ : T₂ ≤ T := by
    rw [hTdef]; exact le_trans (le_max_left T₂ _) (le_max_left _ _)
  have hTgeTg : Tg ≤ T := by
    rw [hTdef]
    exact le_trans (le_trans (le_max_left Tg 1) (le_max_right T₂ _)) (le_max_left _ _)
  have hTge1 : (1 : ℝ) ≤ T := by
    rw [hTdef]
    exact le_trans (le_trans (le_max_right Tg 1) (le_max_right T₂ _)) (le_max_left _ _)
  have hTgeC : 1024 * C₂ + 1 ≤ T := by
    rw [hTdef]; exact le_max_right _ _
  have hM : C₂ / T + 1 / 31 ≤ 1 / 24 := by
    have h1 : C₂ / T ≤ 1 / 1024 := by
      rw [div_le_iff₀ hTpos]
      nlinarith [hC₂.le, hTgeC]
    linarith
  have hMnonneg : 0 ≤ C₂ / T + 1 / 31 := by positivity
  refine ⟨max (‖Φ (T * Complex.I) - T * Complex.I‖)
      (‖Φ (-(T * Complex.I)) + T * Complex.I‖) + (C₂ / T + 1 / 31) * T + 1, T, ?_, hTpos, ?_⟩
  · have h0 : 0 ≤ max (‖Φ (T * Complex.I) - T * Complex.I‖)
        (‖Φ (-(T * Complex.I)) + T * Complex.I‖) :=
      le_trans (norm_nonneg _) (le_max_left _ _)
    nlinarith [h0, mul_nonneg hMnonneg hTpos.le]
  intro z hTz hrez
  have hderM : ∀ w : ℂ, T ≤ |w.im| → |w.re| ≤ |w.im| / 2 →
      ‖deriv (fun v : ℂ => Φ v - v) w‖ ≤ C₂ / T + 1 / 31 := by
    intro w hw hwr
    have h1 := hder w (le_trans hTgeT₂ hw) hwr
    have h2 : C₂ / |w.im| ≤ C₂ / T := div_le_div_of_nonneg_left hC₂.le hTpos hw
    linarith
  have hΦdiff : ∀ w : ℂ, T ≤ |w.im| → |w.re| ≤ |w.im| / 2 → DifferentiableAt ℂ Φ w := by
    intro w hw hwr
    have hwQ : w ∈ Qm ξ₁ α := hcone w (le_trans hTgeTg hw) hwr
    exact hΦ.1.differentiableAt ((isOpen_Qm ξ₁ α).mem_nhds hwQ)
  have hkey : ∀ z : ℂ, T ≤ |z.im| → |z.re| ≤ |z.im| / 2 →
      ‖Φ z - z‖ ≤ max (‖Φ (T * Complex.I) - T * Complex.I‖)
        (‖Φ (-(T * Complex.I)) + T * Complex.I‖) + (C₂ / T + 1 / 31) * T + 1
        + |z.im| / 16 := by
    intro z hTz hrez
    have hMim : (C₂ / T + 1 / 31) * |z.im| ≤ |z.im| / 24 :=
      le_trans (mul_le_mul_of_nonneg_right hM (abs_nonneg z.im)) (le_of_eq (by ring))
    have hMim3 : (3 / 2) * ((C₂ / T + 1 / 31) * |z.im|) ≤ |z.im| / 16 := by
      have h := mul_le_mul_of_nonneg_left hMim (by norm_num : (0 : ℝ) ≤ 3 / 2)
      linarith
    have hexp : (C₂ / T + 1 / 31) * ((3 / 2) * |z.im| + T)
        = (3 / 2) * ((C₂ / T + 1 / 31) * |z.im|) + (C₂ / T + 1 / 31) * T := by ring
    rcases lt_or_ge (0 : ℝ) z.im with hz0 | hzle
    · -- the upper arm
      have hzim : |z.im| = z.im := abs_of_nonneg hz0.le
      have hS : z ∈ {w : ℂ | T ≤ w.im ∧ |w.re| ≤ w.im / 2} :=
        ⟨by rwa [hzim] at hTz, by rwa [hzim] at hrez⟩
      have hS₀ : (T * Complex.I) ∈ {w : ℂ | T ≤ w.im ∧ |w.re| ≤ w.im / 2} := by
        have him : (T * Complex.I).im = T := by simp
        have hre : (T * Complex.I).re = 0 := by simp
        refine ⟨by rw [him], ?_⟩
        rw [hre, abs_zero, him]
        linarith
      have hwT : ∀ w ∈ {w : ℂ | T ≤ w.im ∧ |w.re| ≤ w.im / 2}, T ≤ |w.im| := by
        intro w hw
        rw [abs_of_pos (lt_of_lt_of_le hTpos hw.1)]
        exact hw.1
      have hwr : ∀ w ∈ {w : ℂ | T ≤ w.im ∧ |w.re| ≤ w.im / 2}, |w.re| ≤ |w.im| / 2 := by
        intro w hw
        rw [abs_of_pos (lt_of_lt_of_le hTpos hw.1)]
        exact hw.2
      have hMVT := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun v : ℂ => Φ v - v)
        (s := {w : ℂ | T ≤ w.im ∧ |w.re| ≤ w.im / 2}) (C := C₂ / T + 1 / 31)
        (fun w hw => (hΦdiff w (hwT w hw) (hwr w hw)).sub differentiableAt_id)
        (fun w hw => hderM w (hwT w hw) (hwr w hw))
        (convex_cone_up (T := T)) hS₀ hS
      have hzig : ‖z - T * Complex.I‖ ≤ (3 / 2) * |z.im| + T := by
        have h1 : ‖z - T * Complex.I‖ ≤ ‖z‖ + ‖T * Complex.I‖ := norm_sub_le _ _
        have h2 : ‖T * Complex.I‖ = T := by
          rw [norm_mul, Complex.norm_I, mul_one]
          simp [abs_of_pos hTpos]
        have h3 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        rw [h2] at h1
        rw [hzim] at hrez
        linarith
      have hsplit : ‖Φ z - z‖ ≤
          ‖Φ (T * Complex.I) - T * Complex.I‖
            + ‖Φ z - z - (Φ (T * Complex.I) - T * Complex.I)‖ := by
        have he : Φ z - z = (Φ (T * Complex.I) - T * Complex.I)
            + (Φ z - z - (Φ (T * Complex.I) - T * Complex.I)) := by ring
        calc ‖Φ z - z‖ = ‖(Φ (T * Complex.I) - T * Complex.I)
                + (Φ z - z - (Φ (T * Complex.I) - T * Complex.I))‖ := congrArg norm he
          _ ≤ ‖Φ (T * Complex.I) - T * Complex.I‖
                + ‖Φ z - z - (Φ (T * Complex.I) - T * Complex.I)‖ :=
              norm_add_le (Φ (T * Complex.I) - T * Complex.I)
                (Φ z - z - (Φ (T * Complex.I) - T * Complex.I))
      have hmain' : ‖Φ z - z - (Φ (T * Complex.I) - T * Complex.I)‖
          ≤ (3 / 2) * ((C₂ / T + 1 / 31) * |z.im|) + (C₂ / T + 1 / 31) * T := by
        have hmain := le_trans hMVT (mul_le_mul_of_nonneg_left hzig hMnonneg)
        rwa [hexp] at hmain
      have hble : ‖Φ (T * Complex.I) - T * Complex.I‖ ≤
          max (‖Φ (T * Complex.I) - T * Complex.I‖)
            (‖Φ (-(T * Complex.I)) + T * Complex.I‖) := le_max_left _ _
      linarith [hsplit, hmain', hMim3, hble, mul_nonneg hMnonneg hTpos.le]
    · -- the lower arm
      have hzim : |z.im| = -z.im := abs_of_nonpos hzle
      have hzneg : z.im < 0 := by rw [hzim] at hTz; linarith
      have hS : z ∈ {w : ℂ | w.im ≤ -T ∧ |w.re| ≤ -w.im / 2} :=
        ⟨by rw [hzim] at hTz; linarith, by rw [hzim] at hrez; exact hrez⟩
      have hS₀ : (-(T * Complex.I)) ∈ {w : ℂ | w.im ≤ -T ∧ |w.re| ≤ -w.im / 2} := by
        have him : (-(T * Complex.I) : ℂ).im = -T := by simp
        have hre : (-(T * Complex.I) : ℂ).re = 0 := by simp
        refine ⟨by rw [him], ?_⟩
        rw [hre, abs_zero, him]
        linarith
      have hwT : ∀ w ∈ {w : ℂ | w.im ≤ -T ∧ |w.re| ≤ -w.im / 2}, T ≤ |w.im| := by
        intro w hw
        have hwneg : w.im < 0 := by linarith [hw.1, hTpos]
        rw [abs_of_neg hwneg]
        linarith [hw.1]
      have hwr : ∀ w ∈ {w : ℂ | w.im ≤ -T ∧ |w.re| ≤ -w.im / 2}, |w.re| ≤ |w.im| / 2 := by
        intro w hw
        have hwneg : w.im < 0 := by linarith [hw.1, hTpos]
        rw [abs_of_neg hwneg]
        exact hw.2
      have hMVT := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun v : ℂ => Φ v - v)
        (s := {w : ℂ | w.im ≤ -T ∧ |w.re| ≤ -w.im / 2}) (C := C₂ / T + 1 / 31)
        (fun w hw => (hΦdiff w (hwT w hw) (hwr w hw)).sub differentiableAt_id)
        (fun w hw => hderM w (hwT w hw) (hwr w hw))
        (convex_cone_dn (T := T)) hS₀ hS
      have hzig : ‖z - (-(T * Complex.I))‖ ≤ (3 / 2) * |z.im| + T := by
        have h1 : ‖z - (-(T * Complex.I))‖ ≤ ‖z‖ + ‖(T * Complex.I)‖ := by
          have h := norm_sub_le z (-(T * Complex.I))
          simpa using h
        have h2 : ‖T * Complex.I‖ = T := by
          rw [norm_mul, Complex.norm_I, mul_one]
          simp [abs_of_pos hTpos]
        have h3 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        rw [h2] at h1
        rw [hzim] at hrez
        linarith
      have hsplit : ‖Φ z - z‖ ≤
          ‖Φ (-(T * Complex.I)) + T * Complex.I‖
            + ‖Φ z - z - (Φ (-(T * Complex.I)) - (-(T * Complex.I)))‖ := by
        have he : Φ z - z = (Φ (-(T * Complex.I)) + T * Complex.I)
            + (Φ z - z - (Φ (-(T * Complex.I)) - (-(T * Complex.I)))) := by ring
        calc ‖Φ z - z‖ = ‖(Φ (-(T * Complex.I)) + T * Complex.I)
                + (Φ z - z - (Φ (-(T * Complex.I)) - (-(T * Complex.I))))‖ := congrArg norm he
          _ ≤ ‖Φ (-(T * Complex.I)) + T * Complex.I‖
                + ‖Φ z - z - (Φ (-(T * Complex.I)) - (-(T * Complex.I)))‖ :=
              norm_add_le (Φ (-(T * Complex.I)) + T * Complex.I)
                (Φ z - z - (Φ (-(T * Complex.I)) - (-(T * Complex.I))))
      have hmain' : ‖Φ z - z - (Φ (-(T * Complex.I)) - (-(T * Complex.I)))‖
          ≤ (3 / 2) * ((C₂ / T + 1 / 31) * |z.im|) + (C₂ / T + 1 / 31) * T := by
        have hmain := le_trans hMVT (mul_le_mul_of_nonneg_left hzig hMnonneg)
        rwa [hexp] at hmain
      have hble : ‖Φ (-(T * Complex.I)) + T * Complex.I‖ ≤
          max (‖Φ (T * Complex.I) - T * Complex.I‖)
            (‖Φ (-(T * Complex.I)) + T * Complex.I‖) := le_max_right _ _
      linarith [hsplit, hmain', hMim3, hble, mul_nonneg hMnonneg hTpos.le]
  exact hkey z hTz hrez

/-! ## Covering the half-strips -/

theorem gate_strip_cover (hDE : MandelDim.FatouDerivEstimate) {F Φ : ℂ → ℂ} {ξ₁ : ℝ} {α : ℂ}
    (hNT : MandelDim.NearTranslationL1 F (Qm ξ₁ α))
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Qm ξ₁ α)) :
    ∃ Y : ℝ, 0 < Y ∧ ∀ uu : ℂ, |uu.re| ≤ 1 → Y ≤ |uu.im| → uu ∈ Φ '' Qm ξ₁ α := by
  obtain ⟨C, T, hC, hT, hdev⟩ := dev_le_on_cone hDE hNT hΦ
  obtain ⟨R₂, hR₂, hclose⟩ := deriv_Phi_close_on_gate hDE hNT hΦ
  obtain ⟨Tg, hTg, hgeo⟩ := closedBall_subset_Qm (ξ₁ := ξ₁) (α := α)
  set Y : ℝ := 100 * (C + T + Tg + R₂ + 1) + 1000 with hYdef
  have hYpos : 0 < Y := by rw [hYdef]; linarith [hC, hT, hTg, hR₂]
  refine ⟨Y, hYpos, ?_⟩
  intro uu hreu himu
  have hH : Y ≤ |uu.im| := himu
  have hbase : 100 * (C + T + Tg + R₂ + 1) ≤ |uu.im| := by linarith
  have hH2 : 2 ≤ |uu.im| := by linarith [hbase, hC, hT, hTg, hR₂]
  have hHu : T ≤ |uu.im| := by linarith [hbase, hC, hTg, hR₂]
  have hreim : |uu.re| ≤ |uu.im| / 2 := by linarith
  have hdev_uu : ‖Φ uu - uu‖ ≤ C + |uu.im| / 16 := hdev uu hHu hreim
  set r : ℝ := 4 * (C + |uu.im| / 16) + 1 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; nlinarith [hC, abs_nonneg uu.im]
  have hlt : ‖Φ uu - uu‖ < r / 4 := by rw [hrdef]; linarith [hdev_uu]
  have hmem : uu ∈ Metric.ball (Φ uu) (r / 4) := by
    rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
    exact hlt
  have hTgr : Tg + 3 * r + 1 ≤ |uu.im| := by
    rw [hrdef]; nlinarith [hbase, hC, hT, hTg, hR₂, abs_nonneg uu.im]
  have hballQ : Metric.closedBall uu r ⊆ Qm ξ₁ α := hgeo uu 1 r hrpos.le hreu hTgr
  have hdiff : ∀ ζ ∈ Metric.closedBall uu r, DifferentiableAt ℂ Φ ζ := fun ζ hζ =>
    hΦ.1.differentiableAt ((isOpen_Qm ξ₁ α).mem_nhds (hballQ hζ))
  have hderiv : ∀ ζ ∈ Metric.closedBall uu r, ‖deriv Φ ζ - 1‖ ≤ 1 / 2 := by
    intro ζ hζ
    rw [Metric.mem_closedBall, dist_eq_norm] at hζ
    have hζre : |ζ.re| ≤ 1 + r := by
      have h1 : |ζ.re - uu.re| ≤ r := by
        have h := Complex.abs_re_le_norm (ζ - uu)
        rw [Complex.sub_re] at h
        exact le_trans h hζ
      have h5 : |ζ.re| ≤ |ζ.re - uu.re| + |uu.re| := by
        have he : ζ.re = (ζ.re - uu.re) + uu.re := by ring
        calc |ζ.re| = |(ζ.re - uu.re) + uu.re| := congrArg abs he
          _ ≤ |ζ.re - uu.re| + |uu.re| := abs_add_le (ζ.re - uu.re) uu.re
      linarith
    have hζim : |uu.im| - r ≤ |ζ.im| := by
      have h1 : |ζ.im - uu.im| ≤ r := by
        have h := Complex.abs_im_le_norm (ζ - uu)
        rw [Complex.sub_im] at h
        exact le_trans h hζ
      have h1' : |uu.im - ζ.im| ≤ r := by rwa [abs_sub_comm] at h1
      have h2 : |uu.im| ≤ |ζ.im| + r := by
        have h5 : |uu.im| ≤ |uu.im - ζ.im| + |ζ.im| := by
          have he : uu.im = (uu.im - ζ.im) + ζ.im := by ring
          calc |uu.im| = |(uu.im - ζ.im) + ζ.im| := congrArg abs he
            _ ≤ |uu.im - ζ.im| + |ζ.im| := abs_add_le (uu.im - ζ.im) ζ.im
        linarith
      linarith
    have hTg2 : Tg + 3 * R₂ + (1 + r) ≤ |ζ.im| := by
      nlinarith [hbase, hC, hT, hTg, hR₂, hrdef, hζim, abs_nonneg uu.im]
    exact hclose ζ R₂ le_rfl
      (Metric.ball_subset_closedBall.trans (hgeo ζ (1 + r) R₂ hR₂.le hζre hTg2))
  have hcov := image_cover_centered (Φ := Φ) (z₀ := uu) (r := r) hrpos hdiff hderiv
  obtain ⟨ζ, hζ, hζeq⟩ := hcov hmem
  exact ⟨ζ, hballQ hζ, hζeq⟩

/-! ## The theorem -/

theorem strip_high {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement) (hd : MandelDim.IsParabolicGerm f₀ D₀) :
    ∃ L : Set ℂ, IsCompact L ∧ L ⊆ D₀ ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (f : ℂ → ℂ) (Df : Set ℂ) (ξ₁ rr : ℝ) (u : ℂ → ℂ) (σ α : ℂ),
        MandelDim.NearOn f₀ f Df L δ₀ → f 0 = 0 → MandelDim.InF1 (MandelDim.rotOf f) →
        α = MandelDim.rotOf f → 0 < rr →
        DifferentiableOn ℂ u (Metric.ball 0 rr) →
        (∀ z ∈ Metric.ball 0 rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
        (∀ z ∈ Metric.ball 0 rr, f z = z + z * (z - σ) * u z) →
        1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
        (∀ z ∈ Work.Pert.Qm ξ₁ α, Work.Pert.tauC σ α z ∈ Metric.ball 0 rr) →
        MandelDim.QAdm (some ((ξ₁ : ℂ) - 1 / α)) (some (-(ξ₁ : ℂ))) →
        MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm ξ₁ α) →
        ∃ Y : ℝ, 0 < Y ∧ ∃ Φm : ℂ → ℂ,
          MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm ξ₁ α) ∧
          ∀ uu : ℂ, |uu.re| ≤ 1 → Y ≤ |uu.im| → uu ∈ Φm '' (Work.Pert.Qm ξ₁ α) := by
  refine ⟨{0}, isCompact_singleton, ?_, 1, one_pos, ?_⟩
  · exact Set.singleton_subset_iff.mpr hd.2.1
  · intro f Df ξ₁ rr u σ α hNear hf0 hInF1 hα hr hDiff hu hfid hu0 htau hQAdm hNT
    obtain ⟨Φm, hΦm, -⟩ := hF.1 (some ((ξ₁ : ℂ) - 1 / α)) (some (-(ξ₁ : ℂ)))
      (Work.Pert.liftF u σ α) hQAdm hNT.1
    obtain ⟨Y, hY, hcov⟩ := gate_strip_cover (ξ₁ := ξ₁) (α := α)
      (F := Work.Pert.liftF u σ α) (Φ := Φm) hF.2.2.2.2.1 hNT hΦm
    exact ⟨Y, hY, Φm, hΦm, hcov⟩

end

end Work.Pert
