import Mathlib
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.FatouCH.fatouDerivEstimate
import Submission.Work.FatouL1.strip_in_Qreg

/-!
# `Work.FatouL1.massFatouDerivSubInv`

For a near-translation `F` on Shishikura's region `𝒬 = Qreg b₁ b₂` with the `L¹` line-mass
hypothesis (`MandelDim.NearTranslationL1`), *any* Fatou coordinate `Φ` of `F` on `𝒬`
(`MandelDim.IsFatouCoordOn`: holomorphic, injective, Abel relation `Φ (F z) = Φ z + 1`) and a
vertical line of the strip `x₀ - 1/4 < Re < x₀ + 63/32` (where `x₀` sits `1` to the right of the
vertices of `b₁` and `3` to the left of those of `b₂`), the *mass* of the defect

`Φ'  - 1/(F - id)`

on that line is finite, uniformly in the line: there is `m` with

`∫⁻ y, ‖Φ' (x + iy) - (F (x + iy) - (x + iy))⁻¹‖ dy ≤ m`

for every `x ∈ (x₀ - 1/4, x₀ + 63/32)`.

The proof is a direct application of Shishikura's Lemma A.2.4(i) in the quantitative form proved in
`Work.FatouCH.fatouDerivEstimate`, whose *first* conjunct reads

`‖Φ' z - 1/v z‖ ≤ C₁ (1/R² + ‖v' z‖)`

on any ball `ball z R ⊆ 𝒬` of radius `R ≥ R₁` (with `v = F - id`, so `‖v' z‖ = ‖F' z - 1‖`).
Two facts make this integrable along a vertical line `Re = x` of the strip:

* deep in the channel the ball `ball z R` may be taken of radius `R ≈ |Im z|`: the point `z` is at
  distance `≳ (|Im z| - K)/2` from the two cone boundaries of `𝒬`, where `K` is an explicit
  constant of the data (`chanK`), so `1/R² ≲ 1/y²` is integrable;
* `‖F' - 1‖` is controlled in `L¹` by the hypothesis (`∫⁻ y, ‖F' (x+iy) - 1‖ ≤ 1/64`).

On the bounded part of the line (`|y| ≤ M`) the integrand is bounded by an arbitrary finite
constant `N`, which exists because `Φ'` and `(F - id)⁻¹` are holomorphic on the open set `𝒬`, which
contains a neighbourhood of the compact set `{x₀ - 1/4 ≤ Re ≤ x₀ + 63/32, |Im| ≤ M}`
(here the fact that the conclusion is stated for a *fixed* `Φ` matters: `N` may depend on `Φ`).
-/

open Set MeasureTheory Filter Metric
open scoped Topology

namespace Work.FatouL1

noncomputable section

variable {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}

/-- The defect `Φ' - (F - id)⁻¹` of a Fatou coordinate whose line mass we bound. -/
def fatouDefect (F Φ : ℂ → ℂ) (z : ℂ) : ℂ := deriv Φ z - (F z - z)⁻¹

/-- `Qreg b₁ b₂` is open (it is cut out by strict inequalities between continuous functions). -/
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

/-- The constant attached to the left vertex: `Re a + |Im a|` for the (at most one) vertex `a`
of `b₁`, and a harmless placeholder if `b₁ = none`. -/
def leftV (b₁ : Option ℂ) (x₀ : ℝ) : ℝ := (b₁.map (fun a : ℂ => a.re + |a.im|)).getD (-x₀)

/-- The constant attached to the right vertex: `Re b - |Im b|` for the (at most one) vertex `b`
of `b₂`, and a harmless placeholder if `b₂ = none`. -/
def rightV (b₂ : Option ℂ) (x₀ : ℝ) : ℝ := (b₂.map (fun b : ℂ => b.re - |b.im|)).getD (x₀ + 4)

/-- A constant dominating the two vertex constants, `|x₀|` and a safety margin. -/
def chanK (b₁ b₂ : Option ℂ) (x₀ : ℝ) : ℝ :=
  4 * (|x₀| + |leftV b₁ x₀| + |rightV b₂ x₀| + 8)

/-- The height threshold above which the "deep in the channel" ball is available. -/
def chanM (R₁ : ℝ) (b₁ b₂ : Option ℂ) (x₀ : ℝ) : ℝ :=
  4 * R₁ + 2 * chanK b₁ b₂ x₀ + 8

lemma leftV_mem {b₁ : Option ℂ} {x₀ : ℝ} {a : ℂ} (ha : a ∈ b₁) :
    leftV b₁ x₀ = a.re + |a.im| := by
  rw [Option.mem_def] at ha
  rw [leftV, ha]
  simp

lemma rightV_mem {b₂ : Option ℂ} {x₀ : ℝ} {b : ℂ} (hb : b ∈ b₂) :
    rightV b₂ x₀ = b.re - |b.im| := by
  rw [Option.mem_def] at hb
  rw [rightV, hb]
  simp

lemma chanK_pos (b₁ b₂ : Option ℂ) (x₀ : ℝ) : 0 < chanK b₁ b₂ x₀ := by
  have h1 := abs_nonneg x₀
  have h2 := abs_nonneg (leftV b₁ x₀)
  have h3 := abs_nonneg (rightV b₂ x₀)
  rw [chanK]; linarith

lemma chanM_pos {R₁ : ℝ} (hR₁ : 0 < R₁) (b₁ b₂ : Option ℂ) (x₀ : ℝ) :
    0 < chanM R₁ b₁ b₂ x₀ := by
  have h := chanK_pos b₁ b₂ x₀
  rw [chanM]; linarith

lemma leftV_le_chanK (b₁ b₂ : Option ℂ) (x₀ : ℝ) :
    leftV b₁ x₀ ≤ chanK b₁ b₂ x₀ + (x₀ - 1 / 4) := by
  have h1 := abs_nonneg x₀
  have h2 := abs_nonneg (leftV b₁ x₀)
  have h3 := abs_nonneg (rightV b₂ x₀)
  have ha := le_abs_self (leftV b₁ x₀)
  have hx := neg_le_abs x₀
  have hx' := le_abs_self x₀
  rw [chanK]; linarith

lemma rightV_le_chanK (b₁ b₂ : Option ℂ) (x₀ : ℝ) :
    -rightV b₂ x₀ ≤ chanK b₁ b₂ x₀ - (x₀ + 63 / 32) := by
  have h1 := abs_nonneg x₀
  have h2 := abs_nonneg (leftV b₁ x₀)
  have h3 := abs_nonneg (rightV b₂ x₀)
  have ha := neg_le_abs (rightV b₂ x₀)
  have hx := le_abs_self x₀
  have hx' := neg_le_abs x₀
  rw [chanK]; linarith

/-- **The ball around a point of the strip, deep in the channel, lies in `Qreg b₁ b₂`.**
If `K` dominates the vertex constants (`a.re + |a.im| ≤ K + x₀ - 1/4` for `a ∈ b₁` and
`|b.im| - b.re ≤ K - x₀ - 63/32` for `b ∈ b₂`), then for a point `z` of the strip
`x₀ - 1/4 ≤ Re ≤ x₀ + 63/32` with `|Im z| ≥ K` the ball of radius `(|Im z| - K)/4` about `z` is
contained in `Qreg b₁ b₂`.

Indeed, `Re z - a.re + |Im z - a.im| ≥ |Im z| - K = 4ρ` (which is at least `2ρ` since `ρ ≥ 0`)
makes the left cone condition hold on the whole ball, and symmetrically
`Re b - Re z + |Im z - b.im| ≥ 4ρ` makes the right cone condition hold. -/
theorem ball_subset_Qreg_chan {K : ℝ}
    (hK₁ : ∀ a ∈ b₁, a.re + |a.im| ≤ K + (x₀ - 1 / 4))
    (hK₂ : ∀ b ∈ b₂, |b.im| - b.re ≤ K - (x₀ + 63 / 32))
    {z : ℂ} (hz₁ : x₀ - 1 / 4 ≤ z.re) (hz₂ : z.re ≤ x₀ + 63 / 32) (hz₃ : K ≤ |z.im|) :
    Metric.ball z ((|z.im| - K) / 4) ⊆ MandelDim.Qreg b₁ b₂ := by
  set ρ : ℝ := (|z.im| - K) / 4 with hρ
  have hρ0 : 0 ≤ ρ := by rw [hρ]; linarith
  intro w hw
  have hdist : ‖w - z‖ < ρ := by
    rw [Metric.mem_ball, dist_eq_norm] at hw
    rw [hρ]; exact hw
  have hwre_lo : z.re - ρ < w.re := by
    have h := Complex.abs_re_le_norm (w - z)
    rw [Complex.sub_re] at h
    have h2 := lt_of_le_of_lt h hdist
    have h3 := (abs_lt.mp h2).1
    linarith
  have hwre_hi : w.re < z.re + ρ := by
    have h := Complex.abs_re_le_norm (w - z)
    rw [Complex.sub_re] at h
    have h2 := lt_of_le_of_lt h hdist
    have h3 := (abs_lt.mp h2).2
    linarith
  have hwim_lo : |z.im| - ρ ≤ |w.im| := by
    have h2 : |w.im - z.im| < ρ := by
      have h := Complex.abs_im_le_norm (w - z)
      rw [Complex.sub_im] at h
      exact lt_of_le_of_lt h hdist
    exact sub_abs_le h2
  have him_gap : ∀ c : ℝ, |z.im - c| - ρ ≤ |w.im - c| := by
    intro c
    have h5 : |z.im - c| ≤ |z.im - w.im| + |w.im - c| := abs_sub_le_abs_sub_add
    have h6 : |z.im - w.im| < ρ := by
      have h9 : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm (w - z)
      rw [Complex.sub_im] at h9
      rw [abs_sub_comm]
      linarith
    linarith
  rw [MandelDim.Qreg]
  constructor
  · intro a ha
    have hKa := hK₁ a ha
    have hkey : -|z.im| + |a.im| + ρ ≤ z.re - ρ - a.re := by
      have h4 : 4 * ρ ≤ z.re - a.re + |z.im| - |a.im| := by
        rw [hρ]; linarith
      linarith
    have h1 : z.re - ρ - a.re < (w - a).re := by
      have h2 : (w - a).re = w.re - a.re := Complex.sub_re w a
      rw [h2]; linarith
    have h3 : -|(w - a).im| ≤ -|z.im| + |a.im| + ρ := by
      have him : (w - a).im = w.im - a.im := Complex.sub_im w a
      have h4 := him_gap a.im
      have h8 : |z.im| - |a.im| ≤ |z.im - a.im| := by
        have := abs_sub_abs_le_abs_sub z.im a.im
        linarith [le_abs_self (|z.im| - |a.im|)]
      rw [him]
      linarith
    linarith
  · intro b hb
    have hKb := hK₂ b hb
    have hkey : z.re + ρ - b.re ≤ |z.im| - |b.im| - ρ := by
      have h4 : 4 * ρ ≤ b.re - z.re + |z.im| - |b.im| := by
        rw [hρ]; linarith
      linarith
    have h1 : (w - b).re < z.re + ρ - b.re := by
      have h2 : (w - b).re = w.re - b.re := Complex.sub_re w b
      rw [h2]; linarith
    have h3 : |z.im| - |b.im| - ρ ≤ |(w - b).im| := by
      have him : (w - b).im = w.im - b.im := Complex.sub_im w b
      have h4 := him_gap b.im
      have h8 : |z.im| - |b.im| ≤ |z.im - b.im| := by
        have := abs_sub_abs_le_abs_sub z.im b.im
        linarith [le_abs_self (|z.im| - |b.im|)]
      rw [him]
      linarith
    linarith

set_option linter.unusedVariables false in
/-- **The line mass of `Φ' - 1/(F - id)` is finite on the strip `x₀ - 1/4 < Re < x₀ + 63/32`.**
See the module docstring for the proof. -/
theorem massFatouDerivSubInv {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}
    (hadm : MandelDim.QAdm b₁ b₂) (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re)
    {Φ : ℂ → ℂ} (hΦ : MandelDim.IsFatouCoordOn F Φ (MandelDim.Qreg b₁ b₂)) :
    ∃ m : ℝ, ∀ x ∈ Set.Ioo (x₀ - 1 / 4) (x₀ + 63 / 32),
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
  have hK₂ : ∀ b ∈ b₂, |b.im| - b.re ≤ chanK b₁ b₂ x₀ - (x₀ + 63 / 32) := by
    intro b hb
    have h := rightV_mem (x₀ := x₀) hb
    have he : |b.im| - b.re = -rightV b₂ x₀ := by rw [h]; ring
    rw [he]
    exact rightV_le_chanK b₁ b₂ x₀
  have hKpos : 0 < chanK b₁ b₂ x₀ := chanK_pos b₁ b₂ x₀
  have hMpos : 0 < chanM R₁ b₁ b₂ x₀ := chanM_pos hR₁ b₁ b₂ x₀
  -- every vertical line of the closed strip lies in `Q`
  have hmem_line : ∀ x ∈ Set.Icc (x₀ - 1 / 4) (x₀ + 63 / 32), ∀ y : ℝ,
      ((x : ℂ) + y * Complex.I) ∈ MandelDim.Qreg b₁ b₂ := by
    intro x hx y
    refine mem_Qreg_of_re (fun a ha => ?_) (fun b hb => ?_)
    · have := h₁ a ha; linarith [hx.1]
    · have := h₂ b hb; linarith [hx.2]
  -- the compact box
  have hbox_eq : {z : ℂ | x₀ - 1 / 4 ≤ z.re ∧ z.re ≤ x₀ + 63 / 32 ∧
        |z.im| ≤ chanM R₁ b₁ b₂ x₀}
      = Set.Icc (x₀ - 1 / 4) (x₀ + 63 / 32) ×ℂ
        Set.Icc (-(chanM R₁ b₁ b₂ x₀)) (chanM R₁ b₁ b₂ x₀) := by
    ext z
    simp only [Set.mem_ofPred_eq, Complex.mem_reProdIm, Set.mem_Icc, abs_le]
    tauto
  have hbox_compact : IsCompact {z : ℂ | x₀ - 1 / 4 ≤ z.re ∧ z.re ≤ x₀ + 63 / 32 ∧
      |z.im| ≤ chanM R₁ b₁ b₂ x₀} := by
    rw [hbox_eq]
    exact (isCompact_Icc.reProdIm isCompact_Icc)
  have hbox_sub : {z : ℂ | x₀ - 1 / 4 ≤ z.re ∧ z.re ≤ x₀ + 63 / 32 ∧
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
  have hN : ∀ z ∈ {z : ℂ | x₀ - 1 / 4 ≤ z.re ∧ z.re ≤ x₀ + 63 / 32 ∧
      |z.im| ≤ chanM R₁ b₁ b₂ x₀}, ‖fatouDefect F Φ z‖ ≤ N :=
    fun z hz => le_trans (hN₀ z hz) (le_max_left _ _)
  have hN0 : 0 ≤ N := le_max_right _ _
  -- the pointwise decay high up
  have hdecay : ∀ x ∈ Set.Ioo (x₀ - 1 / 4) (x₀ + 63 / 32), ∀ y : ℝ,
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
      ball_subset_Qreg_chan (K := chanK b₁ b₂ x₀) hK₁ hK₂
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
  have hxIcc : x ∈ Set.Icc (x₀ - 1 / 4) (x₀ + 63 / 32) := ⟨hx.1.le, hx.2.le⟩
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
