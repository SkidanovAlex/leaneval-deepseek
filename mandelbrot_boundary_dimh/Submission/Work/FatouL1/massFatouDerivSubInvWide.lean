import Mathlib
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.FatouCH.fatouDerivEstimate
import Submission.Work.FatouL1.strip_in_Qreg
import Submission.Work.FatouL1.massFatouDerivSubInv
import Submission.Work.FatouL1.ball_subset_Qreg_chan19

/-!
# `Work.FatouL1.massFatouDerivSubInvWide`

Same as `Work.FatouL1.massFatouDerivSubInv` (line mass of the defect `Φ' - 1/(F - id)` bounded
uniformly on the vertical lines of a strip), with the strip widened from
`x₀ - 1/4 < Re < x₀ + 63/32` to `x₀ - 1/4 < Re < x₀ + 19/8`.

The proof is the same argument with `19/8` in place of `63/32` everywhere: the constant `chanK` of
the channel geometry has enough slack that the ball `ball z ((|Im z| - chanK)/4) ⊆ Qreg b₁ b₂`
is still available on the wider strip (that is the lemma
`Work.FatouL1.ball_subset_Qreg_chan19`), and the rest of the estimate uses only the two endpoints
of the strip. -/

open Set MeasureTheory Filter Metric
open scoped Topology

namespace Work.FatouL1

noncomputable section

variable {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}

private lemma isOpen_Qreg' (b₁ b₂ : Option ℂ) : IsOpen (MandelDim.Qreg b₁ b₂) := by
  have h1 : ∀ a : ℂ, IsOpen {z : ℂ | -|(z - a).im| < (z - a).re} := fun a =>
    isOpen_lt (by fun_prop) (by fun_prop)
  have h2 : ∀ b : ℂ, IsOpen {z : ℂ | (z - b).re < |(z - b).im|} := fun b =>
    isOpen_lt (by fun_prop) (by fun_prop)
  rcases b₁ with _ | a <;> rcases b₂ with _ | b
  · have h : MandelDim.Qreg none none = Set.univ := by ext z; simp [MandelDim.Qreg]
    rw [h]; exact isOpen_univ
  · have h : MandelDim.Qreg none (some b) = {z : ℂ | (z - b).re < |(z - b).im|} := by
      ext z; simp [MandelDim.Qreg]
    rw [h]; exact h2 b
  · have h : MandelDim.Qreg (some a) none = {z : ℂ | -|(z - a).im| < (z - a).re} := by
      ext z; simp [MandelDim.Qreg]
    rw [h]; exact h1 a
  · have h : MandelDim.Qreg (some a) (some b)
        = {z : ℂ | -|(z - a).im| < (z - a).re} ∩ {z : ℂ | (z - b).re < |(z - b).im|} := by
      ext z; simp [MandelDim.Qreg]
    rw [h]; exact (h1 a).inter (h2 b)

/-! ## Elementary `abs`-bookkeeping for the geometry -/

private lemma abs_le_abs_add' {u v : ℝ} : |v| ≤ |u| + |v - u| := by
  have h : v = u + (v - u) := by ring
  conv_lhs => rw [h]
  exact abs_add_le u (v - u)

private lemma sub_abs_le {u v ρ : ℝ} (h : |u - v| < ρ) : |v| - ρ ≤ |u| := by
  have h1 : |v| ≤ |u| + |u - v| := by
    have := abs_le_abs_add' (u := u) (v := v)
    rwa [abs_sub_comm v u] at this
  linarith

private lemma abs_sub_le_abs_sub_add {u v c : ℝ} : |u - c| ≤ |u - v| + |v - c| := by
  simpa [Real.dist_eq] using dist_triangle u v c

/-! ## The geometric input: an explicit ball inside the channel -/


lemma rightV_le_chanK19 (b₁ b₂ : Option ℂ) (x₀ : ℝ) :
    -rightV b₂ x₀ ≤ chanK b₁ b₂ x₀ - (x₀ + 19 / 8) := by
  have h1 := abs_nonneg x₀
  have h2 := abs_nonneg (leftV b₁ x₀)
  have h3 := abs_nonneg (rightV b₂ x₀)
  have ha := neg_le_abs (rightV b₂ x₀)
  have hx := le_abs_self x₀
  have hx' := neg_le_abs x₀
  rw [chanK]; linarith


set_option linter.unusedVariables false in
/-- **The line mass of `Φ' - 1/(F - id)` is finite on the strip `x₀ - 1/4 < Re < x₀ + 19/8`.**
See the module docstring for the proof. -/
theorem massFatouDerivSubInvWide {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}
    (hadm : MandelDim.QAdm b₁ b₂) (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re)
    {Φ : ℂ → ℂ} (hΦ : MandelDim.IsFatouCoordOn F Φ (MandelDim.Qreg b₁ b₂)) :
    ∃ m : ℝ, ∀ x ∈ Set.Ioo (x₀ - 1 / 4) (x₀ + 19 / 8),
      ∫⁻ y : ℝ, ENNReal.ofReal
        ‖deriv Φ ((x : ℂ) + y * Complex.I) -
          (F ((x : ℂ) + y * Complex.I) - ((x : ℂ) + y * Complex.I))⁻¹‖ ≤ ENNReal.ofReal m := by
  obtain ⟨R₁, C₁, C₂, hR₁, hC₁, hC₂, hest⟩ := Work.FatouCH.fatouDerivEstimate
  have hQopen : IsOpen (MandelDim.Qreg b₁ b₂) := isOpen_Qreg' b₁ b₂
  have hdF : DifferentiableOn ℂ F (MandelDim.Qreg b₁ b₂) := hF.1.1
  -- the vertex constants are dominated by `chanK`
  have hK₁ : ∀ a ∈ b₁, a.re + |a.im| ≤ chanK b₁ b₂ x₀ + (x₀ - 1 / 4) := by
    intro a ha
    rw [← leftV_mem (x₀ := x₀) ha]
    exact leftV_le_chanK b₁ b₂ x₀
  have hK₂ : ∀ b ∈ b₂, |b.im| - b.re ≤ chanK b₁ b₂ x₀ - (x₀ + 19 / 8) := by
    intro b hb
    have h := rightV_mem (x₀ := x₀) hb
    have he : |b.im| - b.re = -rightV b₂ x₀ := by rw [h]; ring
    rw [he]
    exact rightV_le_chanK19 b₁ b₂ x₀
  have hKpos : 0 < chanK b₁ b₂ x₀ := chanK_pos b₁ b₂ x₀
  have hMpos : 0 < chanM R₁ b₁ b₂ x₀ := chanM_pos hR₁ b₁ b₂ x₀
  -- every vertical line of the closed strip lies in `Q`
  have hmem_line : ∀ x ∈ Set.Icc (x₀ - 1 / 4) (x₀ + 19 / 8), ∀ y : ℝ,
      ((x : ℂ) + y * Complex.I) ∈ MandelDim.Qreg b₁ b₂ := by
    intro x hx y
    refine mem_Qreg_of_re (fun a ha => ?_) (fun b hb => ?_)
    · have := h₁ a ha; linarith [hx.1]
    · have := h₂ b hb; linarith [hx.2]
  -- the compact box
  have hbox_eq : {z : ℂ | x₀ - 1 / 4 ≤ z.re ∧ z.re ≤ x₀ + 19 / 8 ∧
        |z.im| ≤ chanM R₁ b₁ b₂ x₀}
      = Set.Icc (x₀ - 1 / 4) (x₀ + 19 / 8) ×ℂ
        Set.Icc (-(chanM R₁ b₁ b₂ x₀)) (chanM R₁ b₁ b₂ x₀) := by
    ext z
    simp only [Set.mem_ofPred_eq, Complex.mem_reProdIm, Set.mem_Icc, abs_le]
    tauto
  have hbox_compact : IsCompact {z : ℂ | x₀ - 1 / 4 ≤ z.re ∧ z.re ≤ x₀ + 19 / 8 ∧
      |z.im| ≤ chanM R₁ b₁ b₂ x₀} := by
    rw [hbox_eq]
    exact (isCompact_Icc.reProdIm isCompact_Icc)
  have hbox_sub : {z : ℂ | x₀ - 1 / 4 ≤ z.re ∧ z.re ≤ x₀ + 19 / 8 ∧
      |z.im| ≤ chanM R₁ b₁ b₂ x₀} ⊆ MandelDim.Qreg b₁ b₂ := by
    intro z hz
    have h := hmem_line z.re ⟨hz.1, hz.2.1⟩ z.im
    rwa [Complex.re_add_im] at h
  -- `F - id` does not vanish on `Q`
  have hvne : ∀ z ∈ MandelDim.Qreg b₁ b₂, F z - z ≠ 0 := by
    intro z hz h0
    have h := (hF.1.2 z hz).1
    have hz' : F z = z := sub_eq_zero.mp h0
    have h1 : F z - (z + 1) = -1 := by rw [hz']; ring
    rw [h1, norm_neg, norm_one] at h
    norm_num at h
  -- the defect is holomorphic on `Q`
  have hdiff : DifferentiableOn ℂ (fatouDefect F Φ) (MandelDim.Qreg b₁ b₂) := by
    have h1 : DifferentiableOn ℂ (fun z : ℂ => deriv Φ z) (MandelDim.Qreg b₁ b₂) :=
      hΦ.1.deriv hQopen
    have h2 : DifferentiableOn ℂ (fun z : ℂ => (F z - z)⁻¹) (MandelDim.Qreg b₁ b₂) :=
      (hdF.sub differentiableOn_id).inv hvne
    show DifferentiableOn ℂ (fun z : ℂ => deriv Φ z - (F z - z)⁻¹) (MandelDim.Qreg b₁ b₂)
    exact h1.sub h2
  -- boundedness on the compact box
  obtain ⟨N₀, hN₀⟩ :=
    hbox_compact.exists_bound_of_continuousOn (hdiff.continuousOn.mono hbox_sub)
  set N : ℝ := max N₀ 0 with hNdef
  have hN : ∀ z ∈ {z : ℂ | x₀ - 1 / 4 ≤ z.re ∧ z.re ≤ x₀ + 19 / 8 ∧
      |z.im| ≤ chanM R₁ b₁ b₂ x₀}, ‖fatouDefect F Φ z‖ ≤ N :=
    fun z hz => le_trans (hN₀ z hz) (le_max_left _ _)
  have hN0 : 0 ≤ N := le_max_right _ _
  -- the pointwise decay high up
  have hdecay : ∀ x ∈ Set.Ioo (x₀ - 1 / 4) (x₀ + 19 / 8), ∀ y : ℝ,
      chanM R₁ b₁ b₂ x₀ ≤ |y| →
      ‖fatouDefect F Φ ((x : ℂ) + y * Complex.I)‖ ≤
        C₁ * (64 / y ^ 2 + ‖deriv F ((x : ℂ) + y * Complex.I) - 1‖) := by
    intro x hx y hy
    set z : ℂ := (x : ℂ) + y * Complex.I with hzdef
    have hzre : z.re = x := by simp [hzdef]
    have hzim : z.im = y := by simp [hzdef]
    have hzmem : z ∈ MandelDim.Qreg b₁ b₂ := by
      have h := hmem_line x ⟨hx.1.le, hx.2.le⟩ y
      rwa [← hzdef] at h
    set ρ : ℝ := (|z.im| - chanK b₁ b₂ x₀) / 4 with hρdef
    have h1M : 4 * R₁ + chanK b₁ b₂ x₀ + 8 ≤ |y| := by
      have h := hy; rw [chanM] at h; linarith [hKpos]
    have h2M : 2 * chanK b₁ b₂ x₀ ≤ |y| := by
      have h := hy; rw [chanM] at h; linarith [hR₁]
    have hρR₁ : R₁ ≤ ρ := by
      rw [hρdef, hzim]; linarith [hKpos]
    have hρ8 : |y| / 8 ≤ ρ := by
      rw [hρdef, hzim]; linarith [hKpos]
    have hball : Metric.ball z ρ ⊆ MandelDim.Qreg b₁ b₂ :=
      ball_subset_Qreg_chan19 (K := chanK b₁ b₂ x₀) hK₁ hK₂
        (by rw [hzre]; exact hx.1.le) (by rw [hzre]; exact hx.2.le)
        (by rw [hzim]; linarith [hKpos])
    have hρpos : 0 < ρ := lt_of_lt_of_le hR₁ hρR₁
    have hFz : DifferentiableAt ℂ F z := hdF.differentiableAt (hQopen.mem_nhds hzmem)
    have hestz := (hest Φ (fun w : ℂ => F w - w) z ρ hρR₁
      (hΦ.1.mono hball) (hΦ.2.1.mono hball)
      ((hdF.mono hball).sub differentiableOn_id)
      (fun w hw => by
        have hwQ : w ∈ MandelDim.Qreg b₁ b₂ := hball hw
        have h := (hF.1.2 w hwQ).1
        have he : F w - (w + 1) = (F w - w) - 1 := by ring
        rw [he] at h
        linarith)
      (fun w hw hwF => by
        have hwQ : w ∈ MandelDim.Qreg b₁ b₂ := hball hw
        have h1 : w + (F w - w) = F w := by ring
        rw [h1] at hwF ⊢
        exact hΦ.2.2 w hwQ (hball hwF))).1
    have hderiv : deriv (fun w : ℂ => F w - w) z = deriv F z - 1 := by
      have h1 : (fun w : ℂ => F w - w) = (F - id : ℂ → ℂ) := by funext w; simp
      rw [h1, deriv_sub hFz differentiableAt_id]
      simp
    rw [hderiv] at hestz
    have hbound : ‖fatouDefect F Φ z‖ ≤ C₁ * (1 / ρ ^ 2 + ‖deriv F z - 1‖) := by
      simpa [fatouDefect, one_div] using hestz
    have hρ2 : 1 / ρ ^ 2 ≤ 64 / y ^ 2 := by
      have hyne : y ≠ 0 := by
        intro h0
        have h : chanM R₁ b₁ b₂ x₀ ≤ 0 := by simpa [h0] using hy
        linarith
      have hsq : y ^ 2 / 64 ≤ ρ ^ 2 := by
        have h8 : (|y| / 8) ^ 2 ≤ ρ ^ 2 := by nlinarith [hρ8, hρpos.le, abs_nonneg y]
        have h9 : (|y| / 8) ^ 2 = y ^ 2 / 64 := by
          rw [div_pow, sq_abs]; norm_num
        linarith
      have h64 : (0 : ℝ) < y ^ 2 / 64 := by positivity
      calc 1 / ρ ^ 2 ≤ 1 / (y ^ 2 / 64) := one_div_le_one_div_of_le h64 hsq
        _ = 64 / y ^ 2 := by field_simp
    calc ‖fatouDefect F Φ ((x : ℂ) + y * Complex.I)‖ = ‖fatouDefect F Φ z‖ := by rw [hzdef]
      _ ≤ C₁ * (1 / ρ ^ 2 + ‖deriv F z - 1‖) := hbound
      _ ≤ C₁ * (64 / y ^ 2 + ‖deriv F ((x : ℂ) + y * Complex.I) - 1‖) := by
          have hde : deriv F z = deriv F ((x : ℂ) + y * Complex.I) := by rw [hzdef]
          rw [hde]
          apply mul_le_mul_of_nonneg_left _ hC₁.le
          linarith [hρ2]
  have hB₀ : 0 ≤ C₁ * 64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * Real.pi + C₁ / 64 := by
    have hM2 : (0 : ℝ) ≤ (chanM R₁ b₁ b₂ x₀) ^ 2 := sq_nonneg _
    have hinvM : (0 : ℝ) ≤ 1 / (chanM R₁ b₁ b₂ x₀) ^ 2 := div_nonneg zero_le_one hM2
    have hfac : (0 : ℝ) ≤ 1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2 := by linarith
    have hprod : (0 : ℝ) ≤ C₁ * 64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * Real.pi :=
      mul_nonneg (mul_nonneg (mul_nonneg hC₁.le (by norm_num)) hfac) Real.pi_pos.le
    have hlast : (0 : ℝ) ≤ C₁ / 64 := div_nonneg hC₁.le (by norm_num)
    linarith
  set m : ℝ := N * (2 * chanM R₁ b₁ b₂ x₀) +
      (C₁ * 64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * Real.pi + C₁ / 64) with hmdef
  refine ⟨m, ?_⟩
  intro x hx
  change ∫⁻ y : ℝ, ENNReal.ofReal ‖fatouDefect F Φ ((x : ℂ) + y * Complex.I)‖ ≤
    ENNReal.ofReal m
  have hxIcc : x ∈ Set.Icc (x₀ - 1 / 4) (x₀ + 19 / 8) := ⟨hx.1.le, hx.2.le⟩
  have hA₀ : 0 ≤ N * (2 * chanM R₁ b₁ b₂ x₀) := by
    apply mul_nonneg hN0; linarith [hMpos]
  -- the compact part
  have hcomp : ∫⁻ y in Set.Icc (-(chanM R₁ b₁ b₂ x₀)) (chanM R₁ b₁ b₂ x₀),
        ENNReal.ofReal ‖fatouDefect F Φ ((x : ℂ) + y * Complex.I)‖ ≤
      ENNReal.ofReal (N * (2 * chanM R₁ b₁ b₂ x₀)) := by
    have hpt : ∀ y ∈ Set.Icc (-(chanM R₁ b₁ b₂ x₀)) (chanM R₁ b₁ b₂ x₀),
        ENNReal.ofReal ‖fatouDefect F Φ ((x : ℂ) + y * Complex.I)‖ ≤ ENNReal.ofReal N := by
      intro y hy
      apply ENNReal.ofReal_le_ofReal
      apply hN
      refine ⟨?_, ?_, ?_⟩
      · simpa using hx.1.le
      · simpa using hx.2.le
      · rw [show ((x : ℂ) + y * Complex.I).im = y by simp, abs_le]
        exact ⟨hy.1, hy.2⟩
    refine le_trans (setLIntegral_mono' measurableSet_Icc hpt) ?_
    rw [setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul hN0]
    rw [show N * (chanM R₁ b₁ b₂ x₀ - -(chanM R₁ b₁ b₂ x₀))
        = N * (2 * chanM R₁ b₁ b₂ x₀) by ring]
  -- the tail
  have hdecay_x : ∀ y : ℝ, chanM R₁ b₁ b₂ x₀ ≤ |y| →
      ‖fatouDefect F Φ ((x : ℂ) + y * Complex.I)‖ ≤
        C₁ * (64 / y ^ 2 + ‖deriv F ((x : ℂ) + y * Complex.I) - 1‖) :=
    fun y hy => hdecay x hx y hy
  have htail : ∫⁻ y in (Set.Icc (-(chanM R₁ b₁ b₂ x₀)) (chanM R₁ b₁ b₂ x₀))ᶜ,
        ENNReal.ofReal ‖fatouDefect F Φ ((x : ℂ) + y * Complex.I)‖ ≤
      ENNReal.ofReal (C₁ * 64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * Real.pi + C₁ / 64) := by
    set s : Set ℝ := Set.Icc (-(chanM R₁ b₁ b₂ x₀)) (chanM R₁ b₁ b₂ x₀) with hsdef
    have hpt : ∀ y ∈ sᶜ,
        ENNReal.ofReal ‖fatouDefect F Φ ((x : ℂ) + y * Complex.I)‖ ≤
          ENNReal.ofReal (C₁ * 64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * (1 + y ^ 2)⁻¹) +
          ENNReal.ofReal (C₁ * ‖deriv F ((x : ℂ) + y * Complex.I) - 1‖) := by
      intro y hy
      have hyabs : chanM R₁ b₁ b₂ x₀ < |y| := by
        rw [hsdef, Set.mem_compl_iff, Set.mem_Icc, not_and_or] at hy
        rcases hy with h | h
        · rw [not_le] at h
          rw [abs_of_neg (by linarith [hMpos])]
          linarith
        · rw [not_le] at h
          rw [abs_of_pos (by linarith [hMpos])]
          linarith
      have hyne : y ≠ 0 := by
        intro h0
        have h : chanM R₁ b₁ b₂ x₀ ≤ 0 := by simpa [h0] using hyabs.le
        linarith [hMpos]
      have hy2 : (0 : ℝ) < y ^ 2 := by positivity
      have hnum : 64 / y ^ 2 ≤ 64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * (1 + y ^ 2)⁻¹ := by
        have hcore : 1 / y ^ 2 ≤ (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * (1 + y ^ 2)⁻¹ := by
          have hx1 : (0 : ℝ) < 1 + y ^ 2 := by positivity
          have key : (1 : ℝ) + y ^ 2 ≤ (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * y ^ 2 := by
            have h4 : (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * y ^ 2
                = y ^ 2 + y ^ 2 / (chanM R₁ b₁ b₂ x₀) ^ 2 := by ring
            rw [h4]
            have h3 : (chanM R₁ b₁ b₂ x₀) ^ 2 < y ^ 2 := by
              nlinarith [hyabs, abs_nonneg y, sq_abs y, hMpos]
            have h1 : 1 ≤ y ^ 2 / (chanM R₁ b₁ b₂ x₀) ^ 2 := by
              rw [le_div_iff₀ (by positivity : (0 : ℝ) < (chanM R₁ b₁ b₂ x₀) ^ 2)]
              linarith
            linarith
          rw [← div_eq_mul_inv, div_le_iff₀ hy2, div_mul_eq_mul_div,
            le_div_iff₀ hx1]
          linarith
        calc 64 / y ^ 2 = 64 * (1 / y ^ 2) := by ring
          _ ≤ 64 * ((1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * (1 + y ^ 2)⁻¹) :=
              mul_le_mul_of_nonneg_left hcore (by norm_num)
          _ = 64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * (1 + y ^ 2)⁻¹ := by ring
      have hA := hdecay_x y hyabs.le
      have hA' : ‖fatouDefect F Φ ((x : ℂ) + y * Complex.I)‖ ≤
          C₁ * (64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * (1 + y ^ 2)⁻¹ +
            ‖deriv F ((x : ℂ) + y * Complex.I) - 1‖) := by
        refine le_trans hA ?_
        apply mul_le_mul_of_nonneg_left _ hC₁.le
        linarith [hnum]
      have h₁₀ : 0 ≤ C₁ * 64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * (1 + y ^ 2)⁻¹ := by
        have hfac : (0 : ℝ) ≤ 1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2 := by
          have hM2 : (0 : ℝ) ≤ (chanM R₁ b₁ b₂ x₀) ^ 2 := sq_nonneg _
          have hinvM : (0 : ℝ) ≤ 1 / (chanM R₁ b₁ b₂ x₀) ^ 2 := div_nonneg zero_le_one hM2
          linarith
        have hprod : (0 : ℝ) ≤ C₁ * 64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) :=
          mul_nonneg (mul_nonneg hC₁.le (by norm_num)) hfac
        have hinv : (0 : ℝ) ≤ (1 + y ^ 2)⁻¹ := inv_nonneg.mpr (by positivity)
        exact mul_nonneg hprod hinv
      have h₂₀ : 0 ≤ C₁ * ‖deriv F ((x : ℂ) + y * Complex.I) - 1‖ :=
        mul_nonneg hC₁.le (norm_nonneg _)
      calc ENNReal.ofReal ‖fatouDefect F Φ ((x : ℂ) + y * Complex.I)‖
          ≤ ENNReal.ofReal (C₁ * (64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * (1 + y ^ 2)⁻¹ +
              ‖deriv F ((x : ℂ) + y * Complex.I) - 1‖)) := ENNReal.ofReal_le_ofReal hA'
        _ = ENNReal.ofReal (C₁ * 64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * (1 + y ^ 2)⁻¹ +
              C₁ * ‖deriv F ((x : ℂ) + y * Complex.I) - 1‖) := by
              congr 1; ring
        _ = ENNReal.ofReal (C₁ * 64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * (1 + y ^ 2)⁻¹) +
              ENNReal.ofReal (C₁ * ‖deriv F ((x : ℂ) + y * Complex.I) - 1‖) :=
              ENNReal.ofReal_add h₁₀ h₂₀
    have hg₁meas : Measurable (fun y : ℝ =>
        ENNReal.ofReal (C₁ * 64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * (1 + y ^ 2)⁻¹)) := by
      have hcont1 : Continuous fun y : ℝ => (1 + y ^ 2 : ℝ)⁻¹ :=
        (continuous_const.add (continuous_id.pow 2)).inv₀
          (fun y => ne_of_gt (by positivity : (0 : ℝ) < 1 + y ^ 2))
      exact ((continuous_const.mul hcont1).measurable).ennreal_ofReal
    have hmono : ∫⁻ y in sᶜ, ENNReal.ofReal ‖fatouDefect F Φ ((x : ℂ) + y * Complex.I)‖
        ≤ ∫⁻ y in sᶜ,
            (ENNReal.ofReal (C₁ * 64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * (1 + y ^ 2)⁻¹) +
              ENNReal.ofReal (C₁ * ‖deriv F ((x : ℂ) + y * Complex.I) - 1‖)) :=
      setLIntegral_mono' (μ := volume) (hsdef ▸ measurableSet_Icc).compl hpt
    have hadd : ∫⁻ y in sᶜ,
          (ENNReal.ofReal (C₁ * 64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * (1 + y ^ 2)⁻¹) +
            ENNReal.ofReal (C₁ * ‖deriv F ((x : ℂ) + y * Complex.I) - 1‖))
        = (∫⁻ y in sᶜ, ENNReal.ofReal (C₁ * 64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * (1 + y ^ 2)⁻¹)) +
          (∫⁻ y in sᶜ, ENNReal.ofReal (C₁ * ‖deriv F ((x : ℂ) + y * Complex.I) - 1‖)) :=
      lintegral_add_left (μ := volume.restrict sᶜ) hg₁meas _
    have hb₁ : ∫⁻ y in sᶜ,
          ENNReal.ofReal (C₁ * 64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * (1 + y ^ 2)⁻¹) ≤
        ENNReal.ofReal (C₁ * 64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * Real.pi) := by
      have h1 : (∫⁻ y in sᶜ,
            ENNReal.ofReal (C₁ * 64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * (1 + y ^ 2)⁻¹)) ≤
          ∫⁻ y : ℝ, ENNReal.ofReal (C₁ * 64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * (1 + y ^ 2)⁻¹) := by
        have h0 := lintegral_mono_set (μ := volume) (s := sᶜ) (t := Set.univ)
          (f := fun y : ℝ =>
            ENNReal.ofReal (C₁ * 64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * (1 + y ^ 2)⁻¹))
          (subset_univ sᶜ)
        rwa [Measure.restrict_univ] at h0
      have hfac : (0 : ℝ) ≤ 1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2 := by
        have hM2 : (0 : ℝ) ≤ (chanM R₁ b₁ b₂ x₀) ^ 2 := sq_nonneg _
        have hinvM : (0 : ℝ) ≤ 1 / (chanM R₁ b₁ b₂ x₀) ^ 2 := div_nonneg zero_le_one hM2
        linarith
      have hInt : Integrable (fun y : ℝ =>
          C₁ * 64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * (1 + y ^ 2)⁻¹) volume :=
        integrable_inv_one_add_sq.const_mul _
      have hae : 0 ≤ᵐ[volume] (fun y : ℝ =>
          C₁ * 64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * (1 + y ^ 2)⁻¹) :=
        Filter.Eventually.of_forall fun y =>
          mul_nonneg (mul_nonneg (mul_nonneg hC₁.le (by norm_num)) hfac)
            (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ 1 + y ^ 2))
      refine le_trans h1 ?_
      rw [← ofReal_integral_eq_lintegral_ofReal hInt hae]
      apply ENNReal.ofReal_le_ofReal
      rw [integral_const_mul, integral_univ_inv_one_add_sq]
    have hb₂ : ∫⁻ y in sᶜ, ENNReal.ofReal (C₁ * ‖deriv F ((x : ℂ) + y * Complex.I) - 1‖) ≤
        ENNReal.ofReal (C₁ / 64) := by
      have h1 : (∫⁻ y in sᶜ, ENNReal.ofReal (C₁ * ‖deriv F ((x : ℂ) + y * Complex.I) - 1‖)) ≤
          ∫⁻ y : ℝ, ENNReal.ofReal (C₁ * ‖deriv F ((x : ℂ) + y * Complex.I) - 1‖) := by
        have h0 := lintegral_mono_set (μ := volume) (s := sᶜ) (t := Set.univ)
          (f := fun y : ℝ => ENNReal.ofReal (C₁ * ‖deriv F ((x : ℂ) + y * Complex.I) - 1‖))
          (subset_univ sᶜ)
        rwa [Measure.restrict_univ] at h0
      refine le_trans h1 ?_
      have h2 : ∫⁻ y : ℝ, ENNReal.ofReal (C₁ * ‖deriv F ((x : ℂ) + y * Complex.I) - 1‖)
          = ENNReal.ofReal C₁ *
            ∫⁻ y : ℝ, ENNReal.ofReal ‖deriv F ((x : ℂ) + y * Complex.I) - 1‖ := by
        rw [← lintegral_const_mul' (ENNReal.ofReal C₁) _ ENNReal.ofReal_ne_top]
        apply lintegral_congr
        intro y
        rw [ENNReal.ofReal_mul hC₁.le]
      rw [h2]
      calc ENNReal.ofReal C₁ * ∫⁻ y : ℝ, ENNReal.ofReal ‖deriv F ((x : ℂ) + y * Complex.I) - 1‖
          ≤ ENNReal.ofReal C₁ * ENNReal.ofReal (1 / 64) :=
            mul_le_mul_right (hF.2 x (fun y => hmem_line x hxIcc y)) _
        _ = ENNReal.ofReal (C₁ / 64) := by
            rw [← ENNReal.ofReal_mul hC₁.le]; ring_nf
    have hB₀₁ : (0 : ℝ) ≤ C₁ * 64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * Real.pi := by
      have hfac : (0 : ℝ) ≤ 1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2 := by
        have hM2 : (0 : ℝ) ≤ (chanM R₁ b₁ b₂ x₀) ^ 2 := sq_nonneg _
        have hinvM : (0 : ℝ) ≤ 1 / (chanM R₁ b₁ b₂ x₀) ^ 2 := div_nonneg zero_le_one hM2
        linarith
      exact mul_nonneg (mul_nonneg (mul_nonneg hC₁.le (by norm_num)) hfac) Real.pi_pos.le
    calc ∫⁻ y in sᶜ, ENNReal.ofReal ‖fatouDefect F Φ ((x : ℂ) + y * Complex.I)‖
        = (∫⁻ y in sᶜ, ENNReal.ofReal ‖fatouDefect F Φ ((x : ℂ) + y * Complex.I)‖) := rfl
      _ ≤ ∫⁻ y in sᶜ,
            (ENNReal.ofReal (C₁ * 64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * (1 + y ^ 2)⁻¹) +
              ENNReal.ofReal (C₁ * ‖deriv F ((x : ℂ) + y * Complex.I) - 1‖)) := hmono
      _ = (∫⁻ y in sᶜ, ENNReal.ofReal (C₁ * 64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * (1 + y ^ 2)⁻¹)) +
            (∫⁻ y in sᶜ, ENNReal.ofReal (C₁ * ‖deriv F ((x : ℂ) + y * Complex.I) - 1‖)) := hadd
      _ ≤ ENNReal.ofReal (C₁ * 64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * Real.pi) +
            ENNReal.ofReal (C₁ / 64) := add_le_add hb₁ hb₂
      _ = ENNReal.ofReal (C₁ * 64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * Real.pi + C₁ / 64) := by
            rw [ENNReal.ofReal_add hB₀₁ (by positivity : (0 : ℝ) ≤ C₁ / 64)]
  have hsplit := lintegral_add_compl (μ := volume)
    (f := fun y : ℝ => ENNReal.ofReal ‖fatouDefect F Φ ((x : ℂ) + y * Complex.I)‖)
    (A := Set.Icc (-(chanM R₁ b₁ b₂ x₀)) (chanM R₁ b₁ b₂ x₀))
    (measurableSet_Icc)
  calc ∫⁻ y : ℝ, ENNReal.ofReal ‖fatouDefect F Φ ((x : ℂ) + y * Complex.I)‖
      = (∫⁻ y in Set.Icc (-(chanM R₁ b₁ b₂ x₀)) (chanM R₁ b₁ b₂ x₀),
          ENNReal.ofReal ‖fatouDefect F Φ ((x : ℂ) + y * Complex.I)‖) +
        (∫⁻ y in (Set.Icc (-(chanM R₁ b₁ b₂ x₀)) (chanM R₁ b₁ b₂ x₀))ᶜ,
          ENNReal.ofReal ‖fatouDefect F Φ ((x : ℂ) + y * Complex.I)‖) := hsplit.symm
    _ ≤ ENNReal.ofReal (N * (2 * chanM R₁ b₁ b₂ x₀)) +
        ENNReal.ofReal (C₁ * 64 * (1 + 1 / (chanM R₁ b₁ b₂ x₀) ^ 2) * Real.pi + C₁ / 64) :=
        add_le_add hcomp htail
    _ = ENNReal.ofReal m := by
        rw [hmdef, ENNReal.ofReal_add hA₀ hB₀]

end

end Work.FatouL1
