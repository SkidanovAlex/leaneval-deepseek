import Mathlib
import Submission.Work.Pert.Setup

namespace Work.Pert

/-!
# `Work.Pert.walk_gate_mono`

Monotonicity of the "gate walk" used in the perturbation estimate of Shishikura §4.2.

A step `w (j+1) - w j` which is `1/32`-close to `1` advances the real part by at least
`31/32`, moves the imaginary part by at most `1/32`, and decreases the quantity
`|w.im| - w.re` by at least `15/16`.  Chaining the steps over `j ≤ n` gives the stated
linear bounds.
-/

/-- If `‖z - 1‖ ≤ 1/32` then `z.re ≥ 31/32`. -/
private lemma norm_sub_one_re {z : ℂ} (h : ‖z - 1‖ ≤ (1 : ℝ) / 32) : 31 / 32 ≤ z.re := by
  have hh : |(z - 1).re| ≤ (1 : ℝ) / 32 := le_trans (Complex.abs_re_le_norm _) h
  have h2 := (abs_le.mp hh).1
  rw [Complex.sub_re, Complex.one_re] at h2
  linarith

/-- If `‖z - 1‖ ≤ 1/32` then `|z.im| ≤ 1/32`. -/
private lemma norm_sub_one_im {z : ℂ} (h : ‖z - 1‖ ≤ (1 : ℝ) / 32) : |z.im| ≤ 1 / 32 := by
  have hh : |(z - 1).im| ≤ (1 : ℝ) / 32 := le_trans (Complex.abs_im_le_norm _) h
  rw [Complex.sub_im, Complex.one_im] at hh
  simpa using hh

theorem walk_gate_mono {Ξ : ℝ} {w : ℕ → ℂ} {n : ℕ}
    (hstep : ∀ j < n, ‖w (j + 1) - (w j + 1)‖ ≤ 1 / 32) :
    (∀ j < n, (w j).re + 31 / 32 ≤ (w (j + 1)).re) ∧
      (∀ j < n, |(w (j + 1)).im - (w j).im| ≤ 1 / 32) ∧
      (∀ j < n, |(w (j + 1)).im| - (w (j + 1)).re - Ξ ≤ |(w j).im| - (w j).re - Ξ - 15 / 16) ∧
      (∀ j ≤ n, |(w j).im| - (w j).re - Ξ ≤ |(w 0).im| - (w 0).re - Ξ - 15 * (j : ℝ) / 16) ∧
      (∀ j ≤ n, (w 0).re + 31 * (j : ℝ) / 32 ≤ (w j).re) ∧
      (∀ j ≤ n, |(w j).im - (w 0).im| ≤ (j : ℝ) / 32) := by
  -- Rewrite the hypothesis as closeness of the increment `w (j+1) - w j` to `1`.
  have hstep' : ∀ j < n, ‖(w (j + 1) - w j) - 1‖ ≤ 1 / 32 := by
    intro j hj
    have he : w (j + 1) - (w j + 1) = (w (j + 1) - w j) - 1 := by ring
    simpa only [he] using hstep j hj
  -- Step 1: real part advances by at least `31/32`.
  have hre : ∀ j < n, (w j).re + 31 / 32 ≤ (w (j + 1)).re := by
    intro j hj
    have h1 := norm_sub_one_re (hstep' j hj)
    have hd : (w (j + 1) - w j).re = (w (j + 1)).re - (w j).re := Complex.sub_re _ _
    linarith
  -- Step 2: imaginary part moves by at most `1/32`.
  have him : ∀ j < n, |(w (j + 1)).im - (w j).im| ≤ 1 / 32 := by
    intro j hj
    have h1 := norm_sub_one_im (hstep' j hj)
    have hd : (w (j + 1) - w j).im = (w (j + 1)).im - (w j).im := Complex.sub_im _ _
    rw [hd] at h1
    exact h1
  -- Step 3: the quantity `|w.im| - w.re` decreases by at least `15/16`.
  have hphi : ∀ j < n,
      |(w (j + 1)).im| - (w (j + 1)).re - Ξ ≤ |(w j).im| - (w j).re - Ξ - 15 / 16 := by
    intro j hj
    have h1 : |(w (j + 1)).im| - |(w j).im| ≤ 1 / 32 := by
      have h := abs_sub_abs_le_abs_sub (w (j + 1)).im (w j).im
      have h2 := him j hj
      linarith
    have h3 := hre j hj
    linarith
  -- Step 4: telescoping of `|w.im| - w.re`.
  have hbound : ∀ j ≤ n,
      |(w j).im| - (w j).re - Ξ ≤ |(w 0).im| - (w 0).re - Ξ - 15 * (j : ℝ) / 16 := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ k ih =>
        intro hk1
        have hk : k < n := Nat.lt_of_succ_le hk1
        have ihk := ih (le_of_lt hk)
        have hs := hphi k hk
        have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
        calc |(w (k + 1)).im| - (w (k + 1)).re - Ξ
            ≤ |(w k).im| - (w k).re - Ξ - 15 / 16 := hs
          _ ≤ (|(w 0).im| - (w 0).re - Ξ - 15 * (k : ℝ) / 16) - 15 / 16 := by linarith
          _ = |(w 0).im| - (w 0).re - Ξ - 15 * ((k + 1 : ℕ) : ℝ) / 16 := by
                rw [hcast]; ring
  -- Step 5: telescoping of the real part.
  have hrebound : ∀ j ≤ n, (w 0).re + 31 * (j : ℝ) / 32 ≤ (w j).re := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ k ih =>
        intro hk1
        have hk : k < n := Nat.lt_of_succ_le hk1
        have ihk := ih (le_of_lt hk)
        have hs := hre k hk
        have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
        calc (w 0).re + 31 * ((k + 1 : ℕ) : ℝ) / 32
            = (w 0).re + 31 * (k : ℝ) / 32 + 31 / 32 := by rw [hcast]; ring
          _ ≤ (w k).re + 31 / 32 := by linarith
          _ ≤ (w (k + 1)).re := hs
  -- Step 6: telescoping of the imaginary part.
  have himbound : ∀ j ≤ n, |(w j).im - (w 0).im| ≤ (j : ℝ) / 32 := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ k ih =>
        intro hk1
        have hk : k < n := Nat.lt_of_succ_le hk1
        have ihk := ih (le_of_lt hk)
        have hs := him k hk
        have hsplit : |(w (k + 1)).im - (w 0).im|
            ≤ |(w (k + 1)).im - (w k).im| + |(w k).im - (w 0).im| := by
          have he : (w (k + 1)).im - (w 0).im
              = ((w (k + 1)).im - (w k).im) + ((w k).im - (w 0).im) := by ring
          rw [he]
          exact abs_add_le _ _
        have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
        calc |(w (k + 1)).im - (w 0).im| ≤ 1 / 32 + (k : ℝ) / 32 := by linarith
          _ = ((k + 1 : ℕ) : ℝ) / 32 := by rw [hcast]; ring
  exact ⟨hre, him, hphi, hbound, hrebound, himbound⟩

end Work.Pert
