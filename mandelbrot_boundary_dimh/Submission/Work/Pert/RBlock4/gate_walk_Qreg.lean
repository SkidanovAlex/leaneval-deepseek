import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.gate_walk_legal

/-!
# PERT · `Work.Pert.RBlock4.gate_walk_Qreg`: a walk of prescribed length inside `Qreg`

The general form (no lower-gate bookkeeping) of `Work.Pert.gate_walk_legal`: if `F` is a
near-translation by `1` with error `‖F w - (w + 1)‖ ≤ 1/32` on the region
`Q = Qreg (some a) (some b)` (the intersection of the cone with vertex `a` opening to the left and
the cone with vertex `b` opening to the right), then writing

`marg₁ w = Re (w - a) + |Im (w - a)|`,  `marg₂ w = |Im (w - b)| - Re (w - b)`

(`marg₁ w > 0`, `marg₂ w > 0` is exactly `w ∈ Q`), one step of `F` gives

* `marg₁ (F w) ≥ marg₁ w + 1 - 2‖ε w‖ ≥ marg₁ w + 30/32` (the `a`-condition improves);
* `marg₂ (F w) ≥ marg₂ w - 1 - 2‖ε w‖ ≥ marg₂ w - 17/16` (the `b`-condition degrades slowly).

Hence the walk `z, F z, F² z, …` stays inside `Q` as long as its room to the *upper* boundary
`marg₂` stays positive, and `marg₂ (F^j z) ≥ marg₂ z - (17/16) j ≥ (17/16)(m - j) + 1 > 0` for
`j ≤ m` as soon as `marg₂ z ≥ (17/16) m + 1` — which is exactly `hroom`.
-/

namespace Work.Pert.RBlock4

set_option linter.unusedSimpArgs false

open MandelDim Complex Set Metric

noncomputable section

/-- The `a`-margin of `w`: `Re (w - a) + |Im (w - a)|`; its positivity is the `a`-condition of
`Qreg`. -/
private def marg1 (a w : ℂ) : ℝ := (w - a).re + |(w - a).im|

/-- The `b`-margin of `w`: `|Im (w - b)| - Re (w - b)`; its positivity is the `b`-condition of
`Qreg`. -/
private def marg2 (b w : ℂ) : ℝ := |(w - b).im| - (w - b).re

/-- Membership in `Qreg (some a) (some b)` is exactly positivity of the two cone margins. -/
private lemma mem_Qreg_iff {a b z : ℂ} :
    z ∈ MandelDim.Qreg (some a) (some b) ↔ 0 < marg1 a z ∧ 0 < marg2 b z := by
  have h := (show z ∈ MandelDim.Qreg (some a) (some b) ↔
      -|(z - a).im| < (z - a).re ∧ (z - b).re < |(z - b).im| from by
    simp only [MandelDim.Qreg, Set.mem_ofPred_eq, Option.mem_some_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1 a rfl, h2 b rfl⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun b' hb => by rw [← hb]; exact h1, fun b' hb => by rw [← hb]; exact h2⟩)
  rw [h]
  simp only [marg1, marg2]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- One step of a near-translation increases the `a`-margin by at least `30/32`. -/
private lemma marg1_step {F : ℂ → ℂ} {w a : ℂ}
    (h : ‖F w - (w + 1)‖ ≤ (1 / 32 : ℝ)) : marg1 a w + 30 / 32 ≤ marg1 a (F w) := by
  set ε : ℂ := F w - w - 1 with hεdef
  have hε : ‖ε‖ ≤ (1 / 32 : ℝ) := by
    rw [hεdef]; rwa [show F w - (w + 1) = F w - w - 1 by ring] at h
  have hre : (F w - a).re = (w - a).re + 1 + ε.re := by
    rw [hεdef]; simp only [Complex.sub_re, Complex.add_re, Complex.one_re]; ring
  have him : (F w - a).im = (w - a).im + ε.im := by
    rw [hεdef]; simp only [Complex.sub_im, Complex.add_im, Complex.one_im]; ring
  have h1 : (w - a).re + 1 - ‖ε‖ ≤ (F w - a).re := by
    rw [hre]
    have := (abs_le.mp (Complex.abs_re_le_norm ε)).1
    linarith
  have h2 : |(w - a).im| - ‖ε‖ ≤ |(F w - a).im| := by
    rw [him]
    have h3 : |ε.im| ≤ ‖ε‖ := Complex.abs_im_le_norm ε
    have h4 := abs_sub_abs_le_abs_sub (w - a).im (-ε.im)
    rw [abs_neg] at h4
    have h5 : (w - a).im - -ε.im = (w - a).im + ε.im := by ring
    rw [h5] at h4
    linarith
  simp only [marg1]
  linarith

/-- One step of a near-translation decreases the `b`-margin by at most `17/16`. -/
private lemma marg2_step {F : ℂ → ℂ} {w b : ℂ}
    (h : ‖F w - (w + 1)‖ ≤ (1 / 32 : ℝ)) : marg2 b w - 17 / 16 ≤ marg2 b (F w) := by
  set ε : ℂ := F w - w - 1 with hεdef
  have hε : ‖ε‖ ≤ (1 / 32 : ℝ) := by
    rw [hεdef]; rwa [show F w - (w + 1) = F w - w - 1 by ring] at h
  have hre : (F w - b).re = (w - b).re + 1 + ε.re := by
    rw [hεdef]; simp only [Complex.sub_re, Complex.add_re, Complex.one_re]; ring
  have him : (F w - b).im = (w - b).im + ε.im := by
    rw [hεdef]; simp only [Complex.sub_im, Complex.add_im, Complex.one_im]; ring
  have h1 : ε.re ≤ ‖ε‖ := (abs_le.mp (Complex.abs_re_le_norm ε)).2
  have h2 : |(w - b).im| - ‖ε‖ ≤ |(F w - b).im| := by
    rw [him]
    have h3 : |ε.im| ≤ ‖ε‖ := Complex.abs_im_le_norm ε
    have h4 := abs_sub_abs_le_abs_sub (w - b).im (-ε.im)
    rw [abs_neg] at h4
    have h5 : (w - b).im - -ε.im = (w - b).im + ε.im := by ring
    rw [h5] at h4
    linarith
  simp only [marg2]
  linarith

/-- **A walk of prescribed length inside `Qreg (some a) (some b)`.** -/
theorem gate_walk_Qreg {a b : ℂ} {F : ℂ → ℂ} {z : ℂ} {m : ℕ}
    (hstep : ∀ w ∈ MandelDim.Qreg (some a) (some b), ‖F w - (w + 1)‖ ≤ 1 / 32)
    (hz : z ∈ MandelDim.Qreg (some a) (some b))
    (hroom : (17 / 16 : ℝ) * (m : ℝ) + 1 ≤ |(z - b).im| - (z - b).re) :
    ∀ j : ℕ, j ≤ m → F^[j] z ∈ MandelDim.Qreg (some a) (some b) := by
  have hz' := mem_Qreg_iff.mp hz
  have hroom' : (17 / 16 : ℝ) * (m : ℝ) + 1 ≤ marg2 b z := by
    simpa only [marg2] using hroom
  -- the invariant: membership, positivity of `marg₁`, and the room to the upper boundary
  have key : ∀ j : ℕ, j ≤ m →
      F^[j] z ∈ MandelDim.Qreg (some a) (some b) ∧ 0 < marg1 a (F^[j] z) ∧
        (17 / 16 : ℝ) * (m : ℝ) + 1 ≤ marg2 b (F^[j] z) + (17 / 16 : ℝ) * (j : ℝ) := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨hz, hz'.1, by simpa using hroom'⟩
    | succ j ih =>
      intro hj
      have hjm : j ≤ m := by omega
      obtain ⟨hmem, hm1, hm2⟩ := ih hjm
      have hε := hstep (F^[j] z) hmem
      have h1 := marg1_step (F := F) (w := F^[j] z) (a := a) hε
      have h2 := marg2_step (F := F) (w := F^[j] z) (b := b) hε
      have hjle : (j : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast (by omega : j + 1 ≤ m)
      -- the point is still inside the gate: `marg₂` is still `≥ 1 > 0`
      have hpos : 0 < marg2 b (F (F^[j] z)) := by
        have h3 : (17 / 16 : ℝ) * ((j : ℝ) + 1) ≤ (17 / 16 : ℝ) * (m : ℝ) :=
          mul_le_mul_of_nonneg_left hjle (by norm_num)
        linarith
      have hmem' : F (F^[j] z) ∈ MandelDim.Qreg (some a) (some b) :=
        mem_Qreg_iff.mpr ⟨by linarith, hpos⟩
      rw [Function.iterate_succ_apply']
      exact ⟨hmem', by linarith, by push_cast; linarith⟩
  intro j hj
  exact (key j hj).1

end

end Work.Pert.RBlock4
