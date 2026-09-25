/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The logarithmic chart in one coordinate of `ℂⁿ`

This file defines the local coordinates used by the Seeley extension theorem for a polydisc pair
`pd n ρ 1 ⊂ pd n ρ 2` (`Work/NN/Final/exists_extension.lean`).

In the `i`-th coordinate the chart is `z ↦ (u, t)` with

* `u = z i / ‖z i‖` — the *argument* of `z i` as a unit complex number (no branch cut!),
  smoothly replaced by `0` when `‖z i‖ ≤ ρ i / 8`;
* `t = log (ρ i / ‖z i‖)` — the *logarithm of the modulus*, smoothly clamped (to `log 4`) near
  `z i = 0`; note `t > -log 2` whenever `‖z i‖ < 2 * ρ i`, so the polydisc `pd n ρ 2` maps into the
  slab `{-log 2 < t}`;

and the inverse chart is `(x, t) ↦ x` with the `i`-th coordinate replaced by `ρ i * exp (-t) * x i`.
The basic identity `expChart ρ i (chartPoint ρ i z) = z` holds as soon as `ρ i / 3 ≤ ‖z i‖`
(which contains the region on which the pieces of the extension are supported).
-/
import Mathlib

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Final

/-! ## Smooth cutoffs on `ℝ` -/

/-- The standard smooth step: `0` on `(-∞, 0]`, `1` on `[1, ∞)`. -/
noncomputable def smoothCut (x : ℝ) : ℝ := Real.smoothTransition x

lemma smoothCut_contDiff : ContDiff ℝ (⊤ : ℕ∞) smoothCut :=
  Real.smoothTransition.contDiff

lemma smoothCut_of_nonpos {x : ℝ} (h : x ≤ 0) : smoothCut x = 0 :=
  Real.smoothTransition.zero_of_nonpos h

lemma smoothCut_of_one_le {x : ℝ} (h : 1 ≤ x) : smoothCut x = 1 :=
  Real.smoothTransition.one_of_one_le h

lemma smoothCut_nonneg (x : ℝ) : 0 ≤ smoothCut x := Real.smoothTransition.nonneg x

lemma smoothCut_le_one (x : ℝ) : smoothCut x ≤ 1 := Real.smoothTransition.le_one x

/-- A smooth "radial step" on `[0, ∞)`: `0` on `[0, a]`, `1` on `[b, ∞)` (for `a < b`). -/
noncomputable def radialStep (a b : ℝ) (r : ℝ) : ℝ := smoothCut ((r - a) / (b - a))

lemma radialStep_of_le {a b r : ℝ} (hab : a < b) (h : r ≤ a) : radialStep a b r = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

lemma radialStep_of_ge {a b r : ℝ} (hab : a < b) (h : b ≤ r) : radialStep a b r = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  rw [one_le_div (by linarith : (0:ℝ) < b - a)]
  linarith

/-! ## The logarithmic chart in one coordinate -/

variable {n : ℕ}

/-- The "angular" coordinate of the logarithmic chart in the `i`-th coordinate: it equals
`z i / ‖z i‖` for `ρ i / 3 ≤ ‖z i‖` and vanishes for `‖z i‖ ≤ ρ i / 8`. -/
noncomputable def chartU (ρ : Fin n → ℝ) (i : Fin n) (z : Fin n → ℂ) : ℂ :=
  (radialStep (ρ i / 8) (ρ i / 3) ‖z i‖ : ℂ) * (z i / (‖z i‖ : ℂ))

/-- The "logarithmic modulus" coordinate of the chart in the `i`-th coordinate: it equals
`log (ρ i / ‖z i‖)` for `ρ i / 4 ≤ ‖z i‖` and is smoothly clamped (to `log 4`) near `0`. -/
noncomputable def chartT (ρ : Fin n → ℝ) (i : Fin n) (z : Fin n → ℂ) : ℝ :=
  (1 - radialStep (ρ i / 8) (ρ i / 4) ‖z i‖) * Real.log 4
    + radialStep (ρ i / 8) (ρ i / 4) ‖z i‖ * (Real.log (ρ i) - Real.log ‖z i‖)

/-- The logarithmic chart in the `i`-th coordinate, as a map into `ℂⁿ × ℝ`. -/
noncomputable def chartPoint (ρ : Fin n → ℝ) (i : Fin n) (z : Fin n → ℂ) :
    (Fin n → ℂ) × ℝ :=
  (Function.update z i (chartU ρ i z), chartT ρ i z)

/-- The inverse chart in the `i`-th coordinate: `(x, t) ↦ x` with the `i`-th coordinate replaced
by `ρ i * exp (-t) * x i`. -/
noncomputable def expChart (ρ : Fin n → ℝ) (i : Fin n) (p : (Fin n → ℂ) × ℝ) :
    Fin n → ℂ :=
  Function.update p.1 i (ρ i * Complex.exp (-(p.2)) * p.1 i)

@[simp] lemma chartPoint_fst (ρ : Fin n → ℝ) (i : Fin n) (z : Fin n → ℂ) :
    (chartPoint ρ i z).1 = Function.update z i (chartU ρ i z) := rfl

@[simp] lemma chartPoint_snd (ρ : Fin n → ℝ) (i : Fin n) (z : Fin n → ℂ) :
    (chartPoint ρ i z).2 = chartT ρ i z := rfl

lemma chartPoint_fst_apply_of_ne {ρ : Fin n → ℝ} {i j : Fin n} (h : j ≠ i) (z : Fin n → ℂ) :
    (chartPoint ρ i z).1 j = z j := by
  simp [chartPoint, Function.update_of_ne h]

/-- **The chart identity.**  On `{ρ i / 3 ≤ ‖z i‖}` the chart and its inverse are inverse to each
other: `expChart ρ i (chartPoint ρ i z) = z`. -/
theorem expChart_chartPoint {ρ : Fin n → ℝ} {i : Fin n} (hρ : 0 < ρ i) {z : Fin n → ℂ}
    (hz : ρ i / 3 ≤ ‖z i‖) : expChart ρ i (chartPoint ρ i z) = z := by
  have hlt1 : ρ i / 8 < ρ i / 3 := by linarith
  have hlt2 : ρ i / 8 < ρ i / 4 := by linarith
  have hstep1 : radialStep (ρ i / 8) (ρ i / 3) ‖z i‖ = 1 := radialStep_of_ge hlt1 hz
  have hstep2 : radialStep (ρ i / 8) (ρ i / 4) ‖z i‖ = 1 :=
    radialStep_of_ge hlt2 (by linarith)
  have hnorm_pos : 0 < ‖z i‖ := by
    have h : 0 < ρ i / 3 := by positivity
    have h' : (0 : ℝ) ≤ ‖z i‖ := norm_nonneg _
    linarith
  have hnorm_ne : (‖z i‖ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hnorm_pos
  have hU : chartU ρ i z = z i / (‖z i‖ : ℂ) := by simp [chartU, hstep1]
  have hT : chartT ρ i z = Real.log (ρ i) - Real.log ‖z i‖ := by simp [chartT, hstep2]
  have hlog : -(Real.log (ρ i) - Real.log ‖z i‖) = Real.log (‖z i‖ / ρ i) := by
    rw [Real.log_div (ne_of_gt hnorm_pos) (ne_of_gt hρ)]; ring
  have hexp : Complex.exp (-(chartT ρ i z)) = ((‖z i‖ / ρ i : ℝ) : ℂ) := by
    have h1 : -(↑(chartT ρ i z) : ℂ) = ((Real.log (‖z i‖ / ρ i) : ℝ) : ℂ) := by
      rw [show (chartT ρ i z : ℝ) = Real.log (ρ i) - Real.log ‖z i‖ from hT,
        ← Complex.ofReal_neg]
      exact congrArg _ hlog
    rw [h1, ← Complex.ofReal_exp, Real.exp_log (by positivity)]
  have h2 : (ρ i : ℂ) * ((‖z i‖ / ρ i : ℝ) : ℂ) = ((‖z i‖ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hρ)]
  have h3 : chartU ρ i z * (‖z i‖ : ℂ) = z i := by
    rw [hU, div_mul_cancel₀ _ hnorm_ne]
  have hmain : (ρ i : ℂ) * Complex.exp (-(chartT ρ i z)) * chartU ρ i z = z i := by
    calc (ρ i : ℂ) * Complex.exp (-(chartT ρ i z)) * chartU ρ i z
        = (ρ i : ℂ) * ((‖z i‖ / ρ i : ℝ) : ℂ) * chartU ρ i z := by rw [hexp]
      _ = ((‖z i‖ : ℝ) : ℂ) * chartU ρ i z := by rw [h2]
      _ = chartU ρ i z * (‖z i‖ : ℂ) := by ring
      _ = z i := h3
  unfold expChart chartPoint
  simp only [Function.update_self, hmain]
  rw [Function.update_idem]
  funext j
  by_cases hj : j = i
  · subst hj; rw [Function.update_self]
  · rw [Function.update_of_ne hj]

end Work.NN.Final
