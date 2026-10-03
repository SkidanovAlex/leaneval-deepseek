import Submission.Work.Fatou.Smooth

/-!
# Elementary values and the equivariance of `devH`

`devH x₀ F ζ = x₀ + ζ + χ(Re ζ)·eps F (x₀+ζ-1)` (see `Submission/Work/Fatou/Setup.lean`) is the
interpolation between the identity and `F`.  Here we record the two branches
(`devH ζ = x₀+ζ` for `Re ζ ≤ 1/8`, `devH ζ = F(x₀+ζ-1)` for `7/8 ≤ Re ζ ≤ 9/8`), the
equivariance `devH (ζ+1) = F (devH ζ)` on the central strip `|Re ζ| ≤ 1/8` (which makes the
transition maps of the surface equal to `F` and `F⁻¹`), and the estimates showing that `devH`
maps the strip `Σ = (-1/8, 9/8) + iℝ` into `Qreg b₁ b₂`.
-/

namespace Work.Fatou

open MandelDim Filter Set
open scoped Topology

noncomputable section

/-! ### Elementary real-part estimates -/

theorem abs_re_sub_le {z w : ℂ} {c : ℝ} (h : ‖z - w‖ ≤ c) : |z.re - w.re| ≤ c := by
  have h' := Complex.abs_re_le_norm (z - w)
  rw [Complex.sub_re] at h'
  linarith

theorem abs_im_sub_le {z w : ℂ} {c : ℝ} (h : ‖z - w‖ ≤ c) : |z.im - w.im| ≤ c := by
  have h' := Complex.abs_im_le_norm (z - w)
  rw [Complex.sub_im] at h'
  linarith

theorem norm_ofReal_cast (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := RCLike.norm_ofReal r

/-! ### The two branches of `devH` -/

theorem devH_of_le_one_eighth {x₀ : ℝ} {F : ℂ → ℂ} {ζ : ℂ} (h : ζ.re ≤ 1 / 8) :
    devH x₀ F ζ = (x₀ : ℂ) + ζ := by
  have h0 : ((smoothstep ζ.re : ℝ) : ℂ) = 0 := by
    rw [smoothstep_eq_zero_of_le h]; norm_num
  rw [devH_apply, h0, zero_mul, add_zero]

theorem devH_of_ge {x₀ : ℝ} {F : ℂ → ℂ} {ζ : ℂ} (h1 : 7 / 8 ≤ ζ.re) (h2 : ζ.re ≤ 9 / 8) :
    devH x₀ F ζ = F ((x₀ : ℂ) + ζ - 1) := by
  have h0 : ((smoothstep ζ.re : ℝ) : ℂ) = 1 := by
    rw [smoothstep_eq_one_of_mem h1 h2]; norm_num
  rw [devH_apply, h0, eps_apply, one_mul]
  ring_nf

theorem devH_of_ge_fifteen {x₀ : ℝ} {F : ℂ → ℂ} {ζ : ℂ} (h : 15 / 8 ≤ ζ.re) :
    devH x₀ F ζ = (x₀ : ℂ) + ζ := by
  have h0 : ((smoothstep ζ.re : ℝ) : ℂ) = 0 := by
    rw [smoothstep_eq_zero_of_ge h]; norm_num
  rw [devH_apply, h0, zero_mul, add_zero]

/-- The equivariance of `devH`: it intertwines `ζ ↦ ζ+1` with `F` on the central strip. -/
theorem devH_add_one {x₀ : ℝ} {F : ℂ → ℂ} {ζ : ℂ} (h1 : -(1 / 8) ≤ ζ.re) (h2 : ζ.re ≤ 1 / 8) :
    devH x₀ F (ζ + 1) = F (devH x₀ F ζ) := by
  rw [devH_of_le_one_eighth h2]
  have hr : (ζ + 1).re = ζ.re + 1 := by simp
  have hge : 7 / 8 ≤ (ζ + 1).re := by rw [hr]; linarith
  have hle : (ζ + 1).re ≤ 9 / 8 := by rw [hr]; linarith
  rw [devH_of_ge hge hle]
  congr 1
  ring

/-- `devH` is within `1/32` of the translation `ζ ↦ x₀+ζ` on `1/8 ≤ Re ζ ≤ 15/8`. -/
theorem devH_sub_le {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} (hadm : QAdm b₁ b₂)
    (hF : NearTranslationOn F (Qreg b₁ b₂)) {ζ : ℂ}
    (h1 : (1 / 8 : ℝ) ≤ ζ.re) (h2 : ζ.re ≤ 15 / 8) :
    ‖devH (xOf b₁ b₂) F ζ - ((xOf b₁ b₂ : ℂ) + ζ)‖ ≤ 1 / 32 := by
  have hmem : (xOf b₁ b₂ : ℂ) + ζ - 1 ∈ Qreg b₁ b₂ := xOf_add_mem_Qreg hadm h1 h2
  have hb := (hF.2 ((xOf b₁ b₂ : ℂ) + ζ - 1) hmem).1
  have hdev : devH (xOf b₁ b₂) F ζ - ((xOf b₁ b₂ : ℂ) + ζ) =
      ((smoothstep ζ.re : ℝ) : ℂ) * eps F ((xOf b₁ b₂ : ℂ) + ζ - 1) := by
    rw [devH_apply]; ring
  rw [hdev, norm_mul, norm_ofReal_cast]
  have hχ : |smoothstep ζ.re| ≤ 1 := by
    have h := smoothstep_mem_Icc ζ.re
    rw [abs_le]; exact ⟨by linarith [h.1], h.2⟩
  have heps : ‖eps F ((xOf b₁ b₂ : ℂ) + ζ - 1)‖ ≤ 1 / 32 := by
    rw [eps_apply]; exact hb
  calc |smoothstep ζ.re| * ‖eps F ((xOf b₁ b₂ : ℂ) + ζ - 1)‖ ≤ 1 * (1 / 32) :=
        mul_le_mul hχ heps (norm_nonneg _) (by norm_num)
    _ = 1 / 32 := by norm_num

/-! ### `devH` maps `Σ` into `Qreg` -/

/-- The vertical strip `x₀ ± 1/8` widened by `7/4` on the right is contained in `Qreg`. -/
theorem strip_wide_subset_Qreg {b₁ b₂ : Option ℂ} (h : QAdm b₁ b₂) :
    {z : ℂ | xOf b₁ b₂ - 1 / 8 ≤ z.re ∧ z.re ≤ xOf b₁ b₂ + 7 / 4} ⊆ Qreg b₁ b₂ := by
  apply subset_trans _ (vertStrip_subset_Qreg b₁ b₂)
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have := xOf_sub_left h a ha; linarith
  · have := xOf_lt_right h b hb; linarith

/-- The real part of `devH ζ` for `ζ ∈ Σ`. -/
theorem devH_re_mem {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} (hadm : QAdm b₁ b₂)
    (hF : NearTranslationOn F (Qreg b₁ b₂)) {ζ : ℂ} (hζ : ζ ∈ Sigma) :
    xOf b₁ b₂ - 1 / 8 ≤ (devH (xOf b₁ b₂) F ζ).re ∧
      (devH (xOf b₁ b₂) F ζ).re ≤ xOf b₁ b₂ + 7 / 4 := by
  obtain ⟨hlo, hhi⟩ := hζ
  have hre : ((xOf b₁ b₂ : ℂ) + ζ).re = xOf b₁ b₂ + ζ.re := by simp
  rcases le_or_gt ζ.re (1 / 8) with h | h
  · rw [devH_of_le_one_eighth h, Complex.add_re, Complex.ofReal_re]
    constructor <;> linarith
  rcases le_or_gt ζ.re (7 / 8) with h2 | h2
  · have hd := devH_sub_le hadm hF h.le (by linarith)
    have h' := abs_re_sub_le (z := devH (xOf b₁ b₂) F ζ) (w := (xOf b₁ b₂ : ℂ) + ζ) hd
    rw [hre, abs_le] at h'
    constructor <;> linarith
  · have hle : ζ.re ≤ 9 / 8 := le_of_lt hhi
    rw [devH_of_ge (le_of_lt h2) hle]
    have hw : (xOf b₁ b₂ : ℂ) + ζ - 1 ∈ Qreg b₁ b₂ :=
      xOf_add_mem_Qreg hadm (by linarith) (by linarith)
    have hb := (hF.2 ((xOf b₁ b₂ : ℂ) + ζ - 1) hw).1
    have h' := abs_re_sub_le (z := F ((xOf b₁ b₂ : ℂ) + ζ - 1))
      (w := ((xOf b₁ b₂ : ℂ) + ζ - 1) + 1) hb
    rw [Complex.add_re, Complex.sub_re, Complex.add_re,
      Complex.one_re, Complex.ofReal_re, abs_le] at h'
    constructor <;> linarith

/-- On `Σ`, `devH` takes its values in `Qreg`. -/
theorem devH_mem_Qreg {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} (hadm : QAdm b₁ b₂)
    (hF : NearTranslationOn F (Qreg b₁ b₂)) {ζ : ℂ} (hζ : ζ ∈ Sigma) :
    devH (xOf b₁ b₂) F ζ ∈ Qreg b₁ b₂ :=
  strip_wide_subset_Qreg hadm (devH_re_mem hadm hF hζ)

end

end Work.Fatou
