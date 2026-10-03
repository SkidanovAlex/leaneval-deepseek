import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.walk_gate_mono

namespace Work.Pert.GateDriftRate

/-!
# `Work.Pert.GateDriftRate.walk_gate_H_im_drift`

Two *chained* (i.e. two-sided, arbitrary start `i`) consequences of the gate-walk step bound
`‖w (j+1) - (w j + 1)‖ ≤ 1/32`:

* the imaginary parts drift by at most `1/32` per step, so `|Im w j - Im w i| ≤ (j-i)/32`;
* the "gate height" `|Im w| - Re w` *decreases* by at least `15/16` per step (the real part
  advances by at least `31/32` while `|Im|` can change by at most `1/32`), so
  `(|Im w j| - Re w j) ≤ (|Im w i| - Re w i) - 15 (j-i)/16`.

Both are obtained by telescoping the per-step estimates of `Work.Pert.walk_gate_mono`.
-/

theorem walk_gate_H_im_drift {Ξ : ℝ} {w : ℕ → ℂ} {n : ℕ}
    (hstep : ∀ j < n, ‖w (j + 1) - (w j + 1)‖ ≤ 1 / 32) :
    (∀ i j : ℕ, i ≤ j → j ≤ n → |(w j).im - (w i).im| ≤ ((j - i : ℕ) : ℝ) / 32) ∧
      (∀ i j : ℕ, i ≤ j → j ≤ n →
        |(w j).im| - (w j).re - Ξ ≤
          (|(w i).im| - (w i).re - Ξ) - 15 * ((j - i : ℕ) : ℝ) / 16) := by
  -- Per-step estimates from `walk_gate_mono`.
  obtain ⟨-, him, hphi, -, -, -⟩ :=
    Work.Pert.walk_gate_mono (Ξ := Ξ) (w := w) (n := n) hstep
  -- Imaginary part: telescope the `1/32` increments.
  have key1 : ∀ m i : ℕ, i + m ≤ n → |(w (i + m)).im - (w i).im| ≤ (m : ℝ) / 32 := by
    intro m
    induction m with
    | zero =>
        intro i _
        simp
    | succ k ih =>
        intro i hle
        have hik : i + k ≤ n := by omega
        have hklt : i + k < n := by omega
        have ihk := ih i hik
        have hs := him (i + k) hklt
        have hidx : i + (k + 1) = (i + k) + 1 := by omega
        have hsplit : |(w ((i + k) + 1)).im - (w i).im|
            ≤ |(w ((i + k) + 1)).im - (w (i + k)).im| + |(w (i + k)).im - (w i).im| := by
          have he : (w ((i + k) + 1)).im - (w i).im
              = ((w ((i + k) + 1)).im - (w (i + k)).im)
                + ((w (i + k)).im - (w i).im) := by ring
          rw [he]
          exact abs_add_le _ _
        have hm : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
        rw [hidx]
        calc |(w ((i + k) + 1)).im - (w i).im|
            ≤ 1 / 32 + (k : ℝ) / 32 := by linarith
          _ = ((k + 1 : ℕ) : ℝ) / 32 := by rw [hm]; ring
  -- Gate height: telescope the `-15/16` decrements.
  have key2 : ∀ m i : ℕ, i + m ≤ n →
      |(w (i + m)).im| - (w (i + m)).re - Ξ ≤
        (|(w i).im| - (w i).re - Ξ) - 15 * (m : ℝ) / 16 := by
    intro m
    induction m with
    | zero =>
        intro i _
        simp
    | succ k ih =>
        intro i hle
        have hik : i + k ≤ n := by omega
        have hklt : i + k < n := by omega
        have ihk := ih i hik
        have hs := hphi (i + k) hklt
        have hidx : i + (k + 1) = (i + k) + 1 := by omega
        have hm : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
        rw [hidx]
        calc |(w ((i + k) + 1)).im| - (w ((i + k) + 1)).re - Ξ
            ≤ |(w (i + k)).im| - (w (i + k)).re - Ξ - 15 / 16 := hs
          _ ≤ (|(w i).im| - (w i).re - Ξ - 15 * (k : ℝ) / 16) - 15 / 16 := by linarith
          _ = (|(w i).im| - (w i).re - Ξ) - 15 * ((k + 1 : ℕ) : ℝ) / 16 := by
                rw [hm]; ring
  refine ⟨?_, ?_⟩
  · intro i j hij hjn
    have h := key1 (j - i) i (by rw [Nat.add_sub_of_le hij]; exact hjn)
    rw [Nat.add_sub_of_le hij] at h
    exact h
  · intro i j hij hjn
    have h := key2 (j - i) i (by rw [Nat.add_sub_of_le hij]; exact hjn)
    rw [Nat.add_sub_of_le hij] at h
    exact h

end Work.Pert.GateDriftRate
