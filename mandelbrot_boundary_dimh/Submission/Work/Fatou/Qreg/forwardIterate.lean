import Mathlib
import Submission.Work.Fatou.Qreg.Setup
import Submission.Work.Interfaces.Fatou

/-!
# Forward iteration in `𝒬(b₁,b₂)`: the first crossing of the line `Re = x₀`

Shishikura, Prop. A.2.1(i) (forward half).  If `z ∈ 𝒬(b₁,b₂)` with `Re z < x₀`, where `x₀` is
`1` to the right of `b₁` and `3` to the left of `b₂`, then the orbit of `z` under a
near-translation `F` stays in `𝒬` and reaches the half-plane `Re ≥ x₀` for the first time at
some `k ≥ 1`.

The geometric content is that one step of `F` moves the point by `1` in the horizontal
direction: the left (`b₁`) cone condition is preserved unconditionally (`b1_step`), while the
right (`b₂`) cone condition survives because `Re w < x₀ < Re b₂ - 3` leaves a margin much
larger than the `1/32` error (`b2_step`).  Hence the orbit can only leave the region by crossing
`Re = x₀`, and since `Re` increases by at least `31/32` per step it does cross, and the first
crossing time exists by well-ordering.
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Work.Fatou.Qreg

open Set Metric Complex
open scoped Topology

noncomputable section

variable {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}

/-- One step of `F` preserves the `b₂`-part of `𝒬` when `Re w < x₀ < Re b₂ - 3`: the quantity
`Re (w - b) - |Im (w - b)|` is `< -3` at `w` and increases by at most `17/16`, hence stays
negative. -/
lemma b2_step {w : ℂ} (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) (hw : w.re < x₀)
    (hε : ‖F w - (w + 1)‖ ≤ (1 / 32 : ℝ)) :
    ∀ b ∈ b₂, (F w - b).re < |(F w - b).im| := by
  intro b hb
  have hb' := h₂ b hb
  have hε' : ‖F w - w - 1‖ ≤ (1 / 32 : ℝ) := by
    simpa only [show F w - w - 1 = F w - (w + 1) by ring] using hε
  have hre : (w - b).re < -3 := by simp only [Complex.sub_re]; linarith
  have hεre : (F w - w - 1).re ≤ (1 / 32 : ℝ) := by
    have h := (abs_le.mp (le_trans (Complex.abs_re_le_norm (F w - w - 1)) hε')).2
    linarith
  have heq : (F w - b).re = (w - b).re + 1 + (F w - w - 1).re := by
    simp only [Complex.sub_re, Complex.one_re]; ring
  have hneg : (F w - b).re < 0 := by rw [heq]; linarith
  exact lt_of_lt_of_le hneg (abs_nonneg _)

/-- One step of `F` maps `𝒬 ∩ {Re < x₀}` into `𝒬`, and it increases `Re` by at least `31/32`. -/
lemma step_mem (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re)
    (hF : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂))
    {w : ℂ} (hw : w ∈ MandelDim.Qreg b₁ b₂) (hwx : w.re < x₀) :
    F w ∈ MandelDim.Qreg b₁ b₂ ∧ w.re + 31 / 32 ≤ (F w).re := by
  have hε := (hF.2 w hw).1
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro a ha
    exact b1_step (hw.1 a ha) hε
  · exact b2_step h₂ hwx hε
  · exact (re_step_bounds hε).1

theorem forwardIterate {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re)
    (hF : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂))
    {z : ℂ} (hz : z ∈ MandelDim.Qreg b₁ b₂) (hzx : z.re < x₀) :
    ∃ k : ℕ, 0 < k ∧ (∀ j ≤ k, F^[j] z ∈ MandelDim.Qreg b₁ b₂) ∧
      x₀ ≤ (F^[k] z).re ∧ ∀ j < k, (F^[j] z).re < x₀ := by
  classical
  -- The set of times at which the orbit has reached the half-plane `Re ≥ x₀` is nonempty:
  -- otherwise the orbit would stay in `𝒬` forever and have `Re` tending to `+∞`.
  have hne : ∃ n : ℕ, x₀ ≤ (F^[n] z).re := by
    by_contra hcon
    push Not at hcon
    have hmain : ∀ n : ℕ, F^[n] z ∈ MandelDim.Qreg b₁ b₂ ∧
        z.re + n * (31 / 32) ≤ (F^[n] z).re := by
      intro n
      induction n with
      | zero => exact ⟨by simpa using hz, by simp⟩
      | succ n ih =>
        obtain ⟨hmem, hre⟩ := ih
        have hlt : (F^[n] z).re < x₀ := hcon n
        obtain ⟨hmem', hre'⟩ := step_mem h₂ hF hmem hlt
        refine ⟨?_, ?_⟩
        · rwa [Function.iterate_succ_apply']
        · rw [Function.iterate_succ_apply']
          push_cast
          linarith
    obtain ⟨n, hn⟩ := exists_nat_gt ((x₀ - z.re) * 32 / 31)
    have h31 : (0 : ℝ) < 31 / 32 := by norm_num
    have hltn : x₀ - z.re < (n : ℝ) * (31 / 32) := by
      have h := mul_lt_mul_of_pos_right hn h31
      have he : ((x₀ - z.re) * 32 / 31) * (31 / 32) = (x₀ - z.re) := by ring
      rw [he] at h
      exact h
    have hfin := (hmain n).2
    have hcon' := hcon n
    linarith
  -- The first such time.
  obtain ⟨k, hkspec, hkmin⟩ : ∃ k : ℕ, x₀ ≤ (F^[k] z).re ∧
      ∀ j < k, (F^[j] z).re < x₀ :=
    ⟨Nat.find hne, Nat.find_spec hne, fun j hj => not_le.mp (Nat.find_min hne hj)⟩
  have hkpos : 0 < k := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    rw [h0] at hkspec
    simp only [Function.iterate_zero_apply] at hkspec
    linarith
  -- Up to time `k` the orbit never leaves `𝒬`.
  have hmem : ∀ j ≤ k, F^[j] z ∈ MandelDim.Qreg b₁ b₂ := by
    intro j hj
    induction j with
    | zero => simpa using hz
    | succ j ih =>
      have hlt : (F^[j] z).re < x₀ := hkmin j (Nat.lt_of_succ_le hj)
      have hmemj : F^[j] z ∈ MandelDim.Qreg b₁ b₂ := ih (Nat.le_of_succ_le hj)
      have hstep := (step_mem h₂ hF hmemj hlt).1
      rw [Function.iterate_succ_apply']
      exact hstep
  exact ⟨k, hkpos, hmem, hkspec, hkmin⟩

end

end Work.Fatou.Qreg
