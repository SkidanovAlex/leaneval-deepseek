import Mathlib
import Submission.Work.Step2.Defs

/-!
# `Work.Step2.closedBox_subset_closure_PBox`

The closed box `{y | boxNorm c σ y ≤ s}` is contained in the closure of the *open* box
`PBox s c σ = {y | boxNorm c σ y < s}` (`s > 0`).  Since the box norm is the gauge of the box, the
two sets are the closed, respectively open, box with the same centre/side lengths, and the closed
box is exactly the closure of the open one.

The proof is the obvious one: the box norm is positively homogeneous along the homothety with
centre `c`, and it vanishes at `c`; so every point `y` of the closed box can be pushed slightly
towards the centre, `z = c + (1 - δ) • (y - c)`, landing strictly inside the open box while staying
arbitrarily close to `y`.

The two helper lemmas are the analytic content: `boxNorm_smul_sub` (positive homogeneity of the box
norm under the homothety centred at `c`) and `abs_coord_sub_le_of_boxNorm_le` (the box norm controls
each coordinate; this is the `≤`-form of `Submission.mem_PBox_iff`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Step2

noncomputable section

/-- **Positive homogeneity of the box norm under the homothety centred at `c`.** -/
theorem boxNorm_smul_sub (c : R3) (σ : Equiv.Perm (Fin 3)) (y : R3) {t : ℝ} (ht : 0 ≤ t) :
    Submission.boxNorm c σ (c + t • (y - c)) = t * Submission.boxNorm c σ y := by
  have hkey : ∀ i : Fin 3, |(c + t • (y - c)) (σ i) - c (σ i)| = t * |y (σ i) - c (σ i)| := by
    intro i
    have h1 : (c + t • (y - c)) (σ i) - c (σ i) = t * (y (σ i) - c (σ i)) := by simp
    rw [h1, abs_mul, abs_of_nonneg ht]
  have h2 : ∀ i : Fin 3, |(c + t • (y - c)) (σ i) - c (σ i)| / Submission.boxSide i
      = t * (|y (σ i) - c (σ i)| / Submission.boxSide i) := by
    intro i; rw [hkey i, mul_div_assoc]
  simp only [Submission.boxNorm, h2]
  rw [mul_max_of_nonneg _ _ ht, mul_max_of_nonneg _ _ ht]

/-- **The box norm bounds each coordinate**: `|y (σ i) - c (σ i)| ≤ boxSide i * s` whenever
`boxNorm c σ y ≤ s`.  This is the `≤`-form of `Submission.mem_PBox_iff`. -/
theorem abs_coord_sub_le_of_boxNorm_le {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {y : R3}
    (h : Submission.boxNorm c σ y ≤ s) (i : Fin 3) :
    |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s := by
  have h' := h
  simp only [Submission.boxNorm] at h'
  rw [max_le_iff, max_le_iff] at h'
  have hi : |y (σ i) - c (σ i)| / Submission.boxSide i ≤ s := by
    fin_cases i
    · exact h'.1.1
    · exact h'.1.2
    · exact h'.2
  rw [div_le_iff₀ (Submission.boxSide_pos i)] at hi
  linarith [hi]

theorem closedBox_subset_closure_PBox {s : ℝ} (hs : 0 < s) (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) : {y : LeanEval.KnotTheory.PardonDistortion.R3 | Submission.boxNorm c σ y ≤ s} ⊆ closure (Submission.PBox s c σ) := by
  intro y hy
  have hy0 : Submission.boxNorm c σ y ≤ s := hy
  rw [Metric.mem_closure_iff]
  intro ε hε
  -- a small shrinking towards the centre, small enough for the distance bound
  have hδ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ δ ≤ ε / (2 * (‖y - c‖ + 1)) :=
    ⟨min (1 / 2) (ε / (2 * (‖y - c‖ + 1))), lt_min (by norm_num) (by positivity),
      min_le_left _ _, min_le_right _ _⟩
  obtain ⟨δ, hδpos, hδle, hδle'⟩ := hδ
  have hδlt : 1 - δ < 1 := by linarith
  have hδnn : (0 : ℝ) ≤ 1 - δ := by linarith
  refine ⟨c + (1 - δ) • (y - c), ?_, ?_⟩
  · -- the shrunken point lies in the open box
    rw [Submission.mem_PBox]
    intro i
    have hcz : (c + (1 - δ) • (y - c)) (σ i) - c (σ i)
        = (1 - δ) * (y (σ i) - c (σ i)) := by simp
    rw [hcz, abs_mul, abs_of_nonneg hδnn]
    calc (1 - δ) * |y (σ i) - c (σ i)| ≤ (1 - δ) * (Submission.boxSide i * s) :=
          mul_le_mul_of_nonneg_left (abs_coord_sub_le_of_boxNorm_le hy0 i) hδnn
      _ < Submission.boxSide i * s := by
          have hbs : 0 < Submission.boxSide i * s := mul_pos (Submission.boxSide_pos i) hs
          calc (1 - δ) * (Submission.boxSide i * s)
              < 1 * (Submission.boxSide i * s) := mul_lt_mul_of_pos_right hδlt hbs
            _ = Submission.boxSide i * s := one_mul _
  · -- and it is close to `y`: the displacement is `δ • (y - c)`
    rw [dist_eq_norm]
    have hzy : (c + (1 - δ) • (y - c)) - y = -(δ • (y - c)) := by
      ext i; simp; ring
    rw [norm_sub_rev, hzy, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (le_of_lt hδpos)]
    have hn : (0 : ℝ) ≤ ‖y - c‖ := norm_nonneg _
    have hquot : ‖y - c‖ / (2 * (‖y - c‖ + 1)) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    calc δ * ‖y - c‖ ≤ (ε / (2 * (‖y - c‖ + 1))) * ‖y - c‖ :=
          mul_le_mul_of_nonneg_right hδle' hn
      _ = ε * (‖y - c‖ / (2 * (‖y - c‖ + 1))) := by ring
      _ ≤ ε * (1 / 2) := mul_le_mul_of_nonneg_left hquot (le_of_lt hε)
      _ < ε := by linarith

end

end Work.Step2
