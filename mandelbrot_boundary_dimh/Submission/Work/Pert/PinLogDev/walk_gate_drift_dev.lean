import Mathlib
import Submission.Work.Pert.dev_base_v3
import Submission.Work.Pert.PinAux.dev_axis_transport

namespace Work.Pert.PinLogDev

open MandelDim Complex Set Metric

noncomputable section

/-!
# `Work.Pert.PinLogDev.walk_gate_drift_dev`

The **drift of a legal walk** in the lower gate `Qm Ξ α`, together with the *change of the
deviation* `Dev Φ = Φ - id` of a gate Fatou coordinate along that walk.

This is the quantitative core of the "walk" route to `anchor_dev_le` (see `NOTES_new_route.md`
§2): starting from a point `w₀` with `Re w₀ = 0` and `|Im w₀| = β` where `32 (β - Ξ) ≥ 34 n + 32`,
one may iterate a near-translation `F` (`‖F w - (w+1)‖ ≤ 1/32` on the gate, an *arbitrary* such
`F`, not necessarily a `liftF`) exactly `n` times while staying inside the gate, and the orbit
drifts by at most `1/32` per step relative to the exact translation by `1`.

The mechanism is purely elementary:

* the two linear margins of the gate (`Work.Pert.margA`, `Work.Pert.margB`) move by exactly one
  unit per step up to `‖F w - (w+1)‖`: the `A`-margin **increases** by at least `30/32` and the
  `B`-margin **decreases** by at most `17/16`;
* the room `margB Ξ α w₀ = |w₀.im| - Ξ - w₀.re = β - Ξ` of the starting point dominates
  `(17/16) n + 1` by hypothesis `hn`, so the `B`-margin stays `≥ 1 > 0` for the first `n` steps
  (and the `A`-margin only grows);
* telescoping the defect `F w - (w + 1)` gives
  `F^[n] w₀ - (w₀ + n) = ∑_{j<n} (F (F^[j] w₀) - (F^[j] w₀ + 1))`, a sum of `n` terms each of
  norm `≤ 1/32`, which yields the three metric bounds and — via the Abel equation
  `Φ (F^[n] w₀) = Φ w₀ + n` (`Work.Pert.abel_iter`) — also the bound on `Dev`.
-/

/-- Elementary real inequality: `|x| - |y| ≤ |x + y|`. -/
private lemma abs_add_ge_abs_sub (x y : ℝ) : |x| - |y| ≤ |x + y| := by
  have h : |x| ≤ |x + y| + |y| := by
    calc |x| = |(x + y) + (-y)| := by ring_nf
      _ ≤ |x + y| + |-y| := abs_add_le _ _
      _ = |x + y| + |y| := by rw [abs_neg]
  linarith

/-- One step of a near-translation increases the `A`-margin by at least `30/32`. -/
private lemma margA_step {Ξ : ℝ} {α : ℂ} {F : ℂ → ℂ} {w : ℂ}
    (h : ‖F w - (w + 1)‖ ≤ (1 / 32 : ℝ)) :
    Work.Pert.margA Ξ α w + 30 / 32 ≤ Work.Pert.margA Ξ α (F w) := by
  set ε : ℂ := F w - w - 1 with hεdef
  have hε : ‖ε‖ ≤ (1 / 32 : ℝ) := by
    rw [hεdef]; rwa [show F w - (w + 1) = F w - w - 1 by ring] at h
  have hFw : F w = w + 1 + ε := by rw [hεdef]; ring
  have hre : (F w).re = w.re + 1 + ε.re := by rw [hFw]; simp
  have him : (F w).im = w.im + ε.im := by rw [hFw]; simp
  have h1 : -‖ε‖ ≤ ε.re := (abs_le.mp (Complex.abs_re_le_norm ε)).1
  have h2 : |w.im + (1 / α).im| - ‖ε‖ ≤ |w.im + ε.im + (1 / α).im| := by
    have h3 : w.im + ε.im + (1 / α).im = (w.im + (1 / α).im) + ε.im := by ring
    rw [h3]
    have h4 : |ε.im| ≤ ‖ε‖ := Complex.abs_im_le_norm ε
    have h5 := abs_add_ge_abs_sub (w.im + (1 / α).im) ε.im
    linarith
  simp only [Work.Pert.margA]
  rw [hre, him]
  linarith

/-- One step of a near-translation decreases the `B`-margin by at most `17/16`. -/
private lemma margB_step {Ξ : ℝ} {α : ℂ} {F : ℂ → ℂ} {w : ℂ}
    (h : ‖F w - (w + 1)‖ ≤ (1 / 32 : ℝ)) :
    Work.Pert.margB Ξ α w - 17 / 16 ≤ Work.Pert.margB Ξ α (F w) := by
  set ε : ℂ := F w - w - 1 with hεdef
  have hε : ‖ε‖ ≤ (1 / 32 : ℝ) := by
    rw [hεdef]; rwa [show F w - (w + 1) = F w - w - 1 by ring] at h
  have hFw : F w = w + 1 + ε := by rw [hεdef]; ring
  have hre : (F w).re = w.re + 1 + ε.re := by rw [hFw]; simp
  have him : (F w).im = w.im + ε.im := by rw [hFw]; simp
  have h1 : ε.re ≤ ‖ε‖ := (abs_le.mp (Complex.abs_re_le_norm ε)).2
  have h2 : |w.im| - ‖ε‖ ≤ |w.im + ε.im| := by
    have h4 : |ε.im| ≤ ‖ε‖ := Complex.abs_im_le_norm ε
    have h5 := abs_add_ge_abs_sub w.im ε.im
    linarith
  simp only [Work.Pert.margB]
  rw [hre, him]
  linarith

theorem walk_gate_drift_dev {F Φ : ℂ → ℂ} {Ξ : ℝ} {α : ℂ} {w₀ : ℂ} {β : ℝ} {n : ℕ}
    (hCre : Ξ + 4 ≤ (1 / α).re) (hβ : 0 < β) (hre : w₀.re = 0) (him : |w₀.im| = β)
    (hn : 34 * (n : ℝ) + 32 ≤ 32 * (β - Ξ))
    (hw0 : w₀ ∈ Work.Pert.Qm Ξ α)
    (hF : ∀ w ∈ Work.Pert.Qm Ξ α, ‖F w - (w + 1)‖ ≤ 1 / 32)
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm Ξ α)) :
    (∀ j : ℕ, j ≤ n → F^[j] w₀ ∈ Work.Pert.Qm Ξ α) ∧
    (∀ j : ℕ, j ≤ n → 31 * (j : ℝ) / 32 ≤ (F^[j] w₀).re) ∧
    (∀ j : ℕ, j ≤ n → (F^[j] w₀).re ≤ 33 * (j : ℝ) / 32) ∧
    (∀ j : ℕ, j ≤ n → |(F^[j] w₀).im - w₀.im| ≤ (j : ℝ) / 32) ∧
    ‖Work.Pert.PinAux.Dev Φ (F^[n] w₀) - Work.Pert.PinAux.Dev Φ w₀‖ ≤ (n : ℝ) / 32 := by
  have _ := hCre
  have _ := hβ
  -- ## the room of the starting point
  have hB0 : Work.Pert.margB Ξ α w₀ = β - Ξ := by
    simp only [Work.Pert.margB, him, hre]
    ring
  have hroom : (17 / 16 : ℝ) * (n : ℝ) + 1 ≤ Work.Pert.margB Ξ α w₀ := by
    rw [hB0]
    nlinarith [hn]
  -- ## legality of the walk, by induction on the two margins
  have key : ∀ j : ℕ, j ≤ n →
      F^[j] w₀ ∈ Work.Pert.Qm Ξ α ∧
        (17 / 16 : ℝ) * (n : ℝ) + 1 ≤
          Work.Pert.margB Ξ α (F^[j] w₀) + (17 / 16 : ℝ) * (j : ℝ) := by
    intro j
    induction j with
    | zero => intro _; exact ⟨hw0, by simpa using hroom⟩
    | succ k ih =>
      intro hk
      have hk' : k ≤ n := by omega
      obtain ⟨hmem, hB⟩ := ih hk'
      have hd : ‖F (F^[k] w₀) - (F^[k] w₀ + 1)‖ ≤ (1 / 32 : ℝ) := hF _ hmem
      have hApos : 0 < Work.Pert.margA Ξ α (F^[k] w₀) :=
        ((Work.Pert.mem_Qm_iff_marg Ξ α _).mp hmem).1
      have hAstep := margA_step (Ξ := Ξ) (α := α) (F := F) (w := F^[k] w₀) hd
      have hBstep := margB_step (Ξ := Ξ) (α := α) (F := F) (w := F^[k] w₀) hd
      have hmemF : F (F^[k] w₀) ∈ Work.Pert.Qm Ξ α := by
        have hkn : (k : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hk
        refine (Work.Pert.mem_Qm_iff_marg Ξ α _).mpr ⟨by linarith, ?_⟩
        nlinarith [hB, hBstep, hkn]
      rw [Function.iterate_succ_apply']
      refine ⟨hmemF, ?_⟩
      push_cast
      linarith
  have hwalk : ∀ j : ℕ, j ≤ n → F^[j] w₀ ∈ Work.Pert.Qm Ξ α := fun j hj => (key j hj).1
  -- ## telescoping the defect
  have htel : ∀ j : ℕ, F^[j] w₀ - (w₀ + (j : ℂ)) =
      ∑ i ∈ Finset.range j, (F (F^[i] w₀) - (F^[i] w₀ + 1)) := by
    intro j
    induction j with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', Finset.sum_range_succ, ← ih]
      push_cast
      ring
  -- ## the drift bound
  have hbound : ∀ j : ℕ, j ≤ n → ‖F^[j] w₀ - (w₀ + (j : ℂ))‖ ≤ (j : ℝ) / 32 := by
    intro j hj
    rw [htel j]
    calc ‖∑ i ∈ Finset.range j, (F (F^[i] w₀) - (F^[i] w₀ + 1))‖
        ≤ ∑ i ∈ Finset.range j, ‖F (F^[i] w₀) - (F^[i] w₀ + 1)‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range j, (1 / 32 : ℝ) := by
          refine Finset.sum_le_sum fun i hi => ?_
          exact hF _ (hwalk i (le_trans (le_of_lt (Finset.mem_range.mp hi)) hj))
      _ = (j : ℝ) / 32 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  -- ## the real-part bound
  have hdev : ∀ j : ℕ, j ≤ n → |(F^[j] w₀).re - (j : ℝ)| ≤ (j : ℝ) / 32 := by
    intro j hj
    have h1 : |(F^[j] w₀ - (w₀ + (j : ℂ))).re| ≤ ‖F^[j] w₀ - (w₀ + (j : ℂ))‖ :=
      Complex.abs_re_le_norm _
    have h2 : (F^[j] w₀ - (w₀ + (j : ℂ))).re = (F^[j] w₀).re - (j : ℝ) := by
      simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, hre]
      ring
    rw [h2] at h1
    exact le_trans h1 (hbound j hj)
  -- ## the imaginary-part bound
  have himdev : ∀ j : ℕ, j ≤ n → |(F^[j] w₀).im - w₀.im| ≤ (j : ℝ) / 32 := by
    intro j hj
    have h1 : |(F^[j] w₀ - (w₀ + (j : ℂ))).im| ≤ ‖F^[j] w₀ - (w₀ + (j : ℂ))‖ :=
      Complex.abs_im_le_norm _
    have h2 : (F^[j] w₀ - (w₀ + (j : ℂ))).im = (F^[j] w₀).im - w₀.im := by
      simp only [Complex.sub_im, Complex.add_im, Complex.natCast_im]
      ring
    rw [h2] at h1
    exact le_trans h1 (hbound j hj)
  -- ## the deviation bound, through the Abel equation
  have habel : Φ (F^[n] w₀) = Φ w₀ + (n : ℂ) :=
    Work.Pert.abel_iter (F := F) (Φ := Φ) (Q := Work.Pert.Qm Ξ α) (n := n) (ζ := w₀)
      hwalk hΦ.2.2
  have hdevn : ‖Work.Pert.PinAux.Dev Φ (F^[n] w₀) - Work.Pert.PinAux.Dev Φ w₀‖ ≤
      (n : ℝ) / 32 := by
    have h : Work.Pert.PinAux.Dev Φ (F^[n] w₀) - Work.Pert.PinAux.Dev Φ w₀
        = -(F^[n] w₀ - (w₀ + (n : ℂ))) := by
      simp only [Work.Pert.PinAux.Dev]
      rw [habel]
      ring
    rw [h, norm_neg]
    exact hbound n le_rfl
  refine ⟨hwalk, ?_, ?_, himdev, hdevn⟩
  · intro j hj
    have h := (abs_le.mp (hdev j hj)).1
    linarith
  · intro j hj
    have h := (abs_le.mp (hdev j hj)).2
    linarith

end

end Work.Pert.PinLogDev
