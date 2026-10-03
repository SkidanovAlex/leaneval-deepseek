import Mathlib
import Submission.Work.FatouL1.wideStripDefs
import Submission.Work.FatouL1.geom
import Submission.Work.FatouL1.strip_in_Qreg
import Submission.Work.FatouL1.primitiveOnStrip
import Submission.Work.FatouL1.pointwiseDerivBound
import Submission.Work.FatouL1.fatouDerivSetup

/-!
# FATOU-L1: the working regions for the second-derivative bound on the wide strip

The target `Work.FatouL1.fatouSecondDerivWideBound` asks for

`∃ Φ, IsFatouCoordOn F Φ (Qreg b₁ b₂) ∧ ∀ z ∈ wStrip x₀, ‖iteratedDeriv 2 Φ z‖ ≤ 1/100`

under `QAdm b₁ b₂`, `NearTranslationL1 F (Qreg b₁ b₂)`, `h₁ : a.re + 1 < x₀` for `a ∈ b₁` and
`h₂ : x₀ + 3 < b.re` for `b ∈ b₂`.

The regions used below (all vertical strips, with `A = x₀ - 1`, `B = x₀ + 2`):

* `wsQ x₀ = (x₀ - 1, x₀ + 3)`: the strip known to lie in `Qreg b₁ b₂` (and even its *closure*
  does, by `mem_Qreg_of_re_point`), where the cocycle/Taylor/FTC identities are applied and where
  the a priori bounds for `Φ'`, `Φ''` are established;
* `wsPi x₀ = (A + 1/2, B + 1/2) = (x₀ - 1/2, x₀ + 5/2)`: the `π`-region, on which the
  Cauchy–Heine solver controls `Φ''` in terms of the mass of `fatouM = Δ₁ (Φ' - 1)` on the lines
  of `(A,B)`; it contains the target strip `wStrip x₀`.

The line `Re = x` is in `Qreg` exactly when `x` is strictly between the real parts of the
vertices, so the mass hypothesis of `NearTranslationL1` is available on the lines of `(A,B)`
(which is a subset of `(x₀ - 1, x₀ + 3)`).
-/

open MandelDim Set MeasureTheory
open scoped Topology ENNReal

namespace Work.FatouL1

set_option linter.unusedVariables false

noncomputable section

variable {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}

/-! ## The regions -/

/-- Left end of the Cauchy–Heine (unit shift) strip: `A = x₀ - 1`. -/
def wsA (x₀ : ℝ) : ℝ := x₀ - 1

/-- Right end of the Cauchy–Heine (unit shift) strip: `B = x₀ + 2`. -/
def wsB (x₀ : ℝ) : ℝ := x₀ + 2

/-- The `π`-region `Π = (A + 1/2, B + 1/2) = (x₀ - 1/2, x₀ + 5/2)`. -/
def wsPi (x₀ : ℝ) : Set ℂ := strip (x₀ - 1 / 2) (x₀ + 5 / 2)

/-- The convex strip `(x₀ - 1, x₀ + 3)`, contained in `Qreg b₁ b₂` together with its closure. -/
def wsQ (x₀ : ℝ) : Set ℂ := strip (x₀ - 1) (x₀ + 3)

/-! ## Elementary region arithmetic -/

lemma wsA_eq (x₀ : ℝ) : wsA x₀ = x₀ - 1 := rfl

lemma wsB_eq (x₀ : ℝ) : wsB x₀ = x₀ + 2 := rfl

lemma wsA_lt_wsB (x₀ : ℝ) : wsA x₀ < wsB x₀ := by simp only [wsA, wsB]; linarith

lemma wsB_sub_wsA (x₀ : ℝ) : 2 < wsB x₀ - wsA x₀ := by simp only [wsA, wsB]; norm_num

lemma wsPi_eq_shift (x₀ : ℝ) : wsPi x₀ = strip (wsA x₀ + 1 / 2) (wsB x₀ + 1 / 2) := by
  ext z
  simp only [wsPi, mem_strip, wsA, wsB]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

lemma wsQ_eq (x₀ : ℝ) : wsQ x₀ = strip (x₀ - 1) (x₀ + 3) := rfl

lemma wsPi_isOpen (x₀ : ℝ) : IsOpen (wsPi x₀) := strip_isOpen

lemma wsQ_isOpen (x₀ : ℝ) : IsOpen (wsQ x₀) := strip_isOpen

lemma wsPi_convex (x₀ : ℝ) : Convex ℝ (wsPi x₀) := by
  have h : wsPi x₀ = Complex.reLm ⁻¹' Set.Ioo (x₀ - 1 / 2) (x₀ + 5 / 2) := by
    ext z; simp [wsPi, strip]
  rw [h]
  exact (convex_Ioo _ _).linear_preimage Complex.reLm

lemma wsQ_convex (x₀ : ℝ) : Convex ℝ (wsQ x₀) := by
  have h : wsQ x₀ = Complex.reLm ⁻¹' Set.Ioo (x₀ - 1) (x₀ + 3) := by ext z; simp [wsQ, strip]
  rw [h]
  exact (convex_Ioo _ _).linear_preimage Complex.reLm

lemma wStrip_subset_wsPi (x₀ : ℝ) : wStrip x₀ ⊆ wsPi x₀ := by
  intro z hz
  rw [mem_wStrip] at hz
  exact ⟨by linarith [hz.1], by linarith [hz.2]⟩

lemma wsPi_subset_wsQ (x₀ : ℝ) : wsPi x₀ ⊆ wsQ x₀ := by
  intro z hz
  exact ⟨by linarith [hz.1], by linarith [hz.2]⟩

/-! ## `Qreg` membership -/

/-- **Pointwise real-part criterion for `Qreg`.**  A point all of whose real comparisons with the
vertices are strict lies in `Qreg b₁ b₂`: the first condition of `Qreg` becomes
`Re (z - a) > 0` and the second `Re (z - b) < 0`. -/
lemma mem_Qreg_of_re_point {b₁ b₂ : Option ℂ} {z : ℂ}
    (h₁ : ∀ a ∈ b₁, a.re < z.re) (h₂ : ∀ b ∈ b₂, z.re < b.re) :
    z ∈ MandelDim.Qreg b₁ b₂ := by
  refine ⟨?_, ?_⟩
  · intro a ha
    have h := h₁ a ha
    have hre : (z - a).re = z.re - a.re := Complex.sub_re z a
    rw [hre]
    calc -|(z - a).im| ≤ 0 := neg_nonpos.mpr (abs_nonneg _)
      _ < z.re - a.re := by linarith
  · intro b hb
    have h := h₂ b hb
    have hre : (z - b).re = z.re - b.re := Complex.sub_re z b
    rw [hre]
    calc z.re - b.re < 0 := by linarith
      _ ≤ |(z - b).im| := abs_nonneg _

/-- A point with `x₀ - 1 ≤ Re z ≤ x₀ + 3` lies in `Qreg b₁ b₂`. -/
lemma mem_Qreg_of_re_closed (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re)
    {z : ℂ} (hz₁ : x₀ - 1 ≤ z.re) (hz₂ : z.re ≤ x₀ + 3) : z ∈ MandelDim.Qreg b₁ b₂ := by
  refine mem_Qreg_of_re_point ?_ ?_
  · intro a ha; have := h₁ a ha; linarith
  · intro b hb; have := h₂ b hb; linarith

/-- The strip `(x₀ - 1, x₀ + 3)` lies in `Qreg b₁ b₂`. -/
lemma wsQ_subset_Qreg (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) :
    wsQ x₀ ⊆ MandelDim.Qreg b₁ b₂ :=
  fun _ hz => mem_Qreg_of_re_closed h₁ h₂ (le_of_lt hz.1) (le_of_lt hz.2)

/-- Membership in `Qreg` from real-part bounds alone. -/
lemma mem_Qreg_of_re_strip (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re)
    {z : ℂ} (hz₁ : x₀ - 1 < z.re) (hz₂ : z.re < x₀ + 3) : z ∈ MandelDim.Qreg b₁ b₂ :=
  wsQ_subset_Qreg h₁ h₂ ⟨hz₁, hz₂⟩

lemma wsPi_subset_Qreg (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) :
    wsPi x₀ ⊆ MandelDim.Qreg b₁ b₂ :=
  (wsPi_subset_wsQ x₀).trans (wsQ_subset_Qreg h₁ h₂)

lemma wStrip_subset_Qreg' (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) :
    wStrip x₀ ⊆ MandelDim.Qreg b₁ b₂ :=
  (wStrip_subset_wsPi x₀).trans (wsPi_subset_Qreg h₁ h₂)

/-- Points of the shift strip `(A,B)` lie in `Qreg`. -/
lemma mem_Qreg_of_ws_strip (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re)
    {z : ℂ} (hz₁ : wsA x₀ < z.re) (hz₂ : z.re < wsB x₀) : z ∈ MandelDim.Qreg b₁ b₂ := by
  refine mem_Qreg_of_re_strip h₁ h₂ ?_ ?_
  · simp only [wsA] at hz₁; linarith
  · simp only [wsB] at hz₂; linarith

/-! ## The pointwise bound for `F' - 1` on the `π`-region -/

/-- **`‖F' - 1‖ ≤ 1/150` on the `π`-region.**  On the interval `(-1/2, 5/2)` the Cauchy bracket
`1/(t + 1) + 1/(3 - t)` of `pointwiseDerivBound` is at most `16/7` (its minimum is at `t = 1`),
so the pointwise bound `(1/64)/(2π)·(16/7) = 1/(56π) ≤ 1/150` holds there. -/
theorem wDerivSubOne_le (hadm : MandelDim.QAdm b₁ b₂)
    (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) {z : ℂ}
    (hz₁ : x₀ - 1 / 2 < z.re) (hz₂ : z.re < x₀ + 5 / 2) : ‖deriv F z - 1‖ ≤ 1 / 150 := by
  have hz₁' : x₀ - 1 < z.re := by linarith
  have hz₂' : z.re < x₀ + 3 := by linarith
  have h := pointwiseDerivBound (b₁ := b₁) (b₂ := b₂) (F := F) (x₀ := x₀)
    hadm hF h₁ h₂ z hz₁' hz₂'
  have hden₁ : 0 < z.re - (x₀ - 1) := by linarith
  have hden₂ : 0 < x₀ + 3 - z.re := by linarith
  -- the bracket is `4/((t+1)(3-t))` with `t = Re z - x₀`, and `(t+1)(3-t) ≥ 7/4`
  have hbracket : 1 / (z.re - (x₀ - 1)) + 1 / (x₀ + 3 - z.re) ≤ 16 / 7 := by
    have hquad : ((z.re - x₀) - 1) ^ 2 ≤ (3 / 2) ^ 2 := by
      have h1 : -(1 / 2 : ℝ) ≤ z.re - x₀ := by linarith
      have h2 : z.re - x₀ ≤ 5 / 2 := by linarith
      nlinarith
    have hprod : 7 / 4 ≤ (z.re - (x₀ - 1)) * (x₀ + 3 - z.re) := by
      have hexp : (z.re - (x₀ - 1)) * (x₀ + 3 - z.re)
          = 3 + 2 * (z.re - x₀) - (z.re - x₀) ^ 2 := by ring
      rw [hexp]
      nlinarith [hquad]
    have hpos : 0 < (z.re - (x₀ - 1)) * (x₀ + 3 - z.re) := mul_pos hden₁ hden₂
    rw [div_add_div _ _ (ne_of_gt hden₁) (ne_of_gt hden₂), div_le_iff₀ hpos]
    have hnum : (x₀ + 3 - z.re) + (z.re - (x₀ - 1)) = 4 := by ring
    nlinarith [hprod, hnum]
  have hpi := Real.pi_gt_three
  have h64 : ‖deriv F z - 1‖ ≤ (1 / 64) / (2 * Real.pi) * (16 / 7) :=
    h.trans (mul_le_mul_of_nonneg_left hbracket (by positivity))
  have hb : (1 / 64) / (2 * Real.pi) * (16 / 7) ≤ 1 / 150 := by
    have hp : 0 < Real.pi := Real.pi_pos
    have hkey : (1 / 64) / (2 * Real.pi) * (16 / 7) = 1 / (56 * Real.pi) := by
      field_simp; ring
    rw [hkey, one_div, one_div]
    exact (inv_le_inv₀ (by positivity : (0:ℝ) < 56 * Real.pi) (by norm_num : (0:ℝ) < 150)).mpr
      (by nlinarith)
  linarith

/-- **`‖F' - 1‖ ≤ 1/136` on `(x₀ - 5/8, x₀ + 5/2)`.**  On that interval the Cauchy bracket of
`pointwiseDerivBound` is at most `256/87` (its maximum is attained at `t = -5/8`), so the bound
`(1/64)/(2π)·(256/87) = 2/(87π) ≤ 1/136` holds there (using `π > 3.1415`). -/
theorem wDerivSubOne_le_136 (hadm : MandelDim.QAdm b₁ b₂)
    (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) {z : ℂ}
    (hz₁ : x₀ - 5 / 8 < z.re) (hz₂ : z.re < x₀ + 5 / 2) : ‖deriv F z - 1‖ ≤ 1 / 136 := by
  have hz₁' : x₀ - 1 < z.re := by linarith
  have hz₂' : z.re < x₀ + 3 := by linarith
  have h := pointwiseDerivBound (b₁ := b₁) (b₂ := b₂) (F := F) (x₀ := x₀)
    hadm hF h₁ h₂ z hz₁' hz₂'
  have hden₁ : 0 < z.re - (x₀ - 1) := by linarith
  have hden₂ : 0 < x₀ + 3 - z.re := by linarith
  have hbracket : 1 / (z.re - (x₀ - 1)) + 1 / (x₀ + 3 - z.re) ≤ 256 / 87 := by
    have hquad : ((z.re - x₀) - 1) ^ 2 ≤ (13 / 8) ^ 2 := by
      have h1 : -(5 / 8 : ℝ) < z.re - x₀ := by linarith
      have h2 : z.re - x₀ < 5 / 2 := by linarith
      nlinarith
    have hprod : 87 / 64 ≤ (z.re - (x₀ - 1)) * (x₀ + 3 - z.re) := by
      have hexp : (z.re - (x₀ - 1)) * (x₀ + 3 - z.re)
          = 3 + 2 * (z.re - x₀) - (z.re - x₀) ^ 2 := by ring
      rw [hexp]
      nlinarith [hquad]
    have hpos : 0 < (z.re - (x₀ - 1)) * (x₀ + 3 - z.re) := mul_pos hden₁ hden₂
    rw [div_add_div _ _ (ne_of_gt hden₁) (ne_of_gt hden₂), div_le_iff₀ hpos]
    have hnum : (x₀ + 3 - z.re) + (z.re - (x₀ - 1)) = 4 := by ring
    nlinarith [hprod, hnum]
  have hb : (1 / 64) / (2 * Real.pi) * (256 / 87) ≤ 1 / 136 := by
    have hp : 0 < Real.pi := Real.pi_pos
    have hkey : (1 / 64) / (2 * Real.pi) * (256 / 87) = 2 / (87 * Real.pi) := by
      field_simp; ring
    rw [hkey, div_le_iff₀ (by positivity : (0:ℝ) < 87 * Real.pi)]
    nlinarith [Real.pi_gt_d4]
  calc ‖deriv F z - 1‖ ≤ (1 / 64) / (2 * Real.pi) * (256 / 87) :=
        h.trans (mul_le_mul_of_nonneg_left hbracket (by positivity))
    _ ≤ 1 / 136 := hb


end

end Work.FatouL1
