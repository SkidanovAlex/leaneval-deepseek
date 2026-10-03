import Mathlib
import Submission.VarPrep

/-!
# Raising the clamp point of a variational norm costs three times the last increment

For `r ≥ 1`, a sequence `a : ℕ → ℂ` and `n₀ ≥ 1`,

`‖k ↦ a (min k n₀)‖_{Vʳ} ≤ ‖k ↦ a (min k (n₀ - 1))‖_{Vʳ} + 3 ‖a n₀ - a (n₀ - 1)‖`.

The clamped families `b k = a (min k n₀)` and `c k = a (min k (n₀ - 1))` agree on `k ≤ n₀ - 1`;
for `k ≥ n₀` both are constant, with values `a n₀` resp. `a (n₀ - 1)`.  Hence

`b = c + g`,   `g k = if k < n₀ then 0 else (a n₀ - a (n₀ - 1))`,

and the claim follows from subadditivity of the variational norm together with the bound
`‖g‖_{Vʳ} ≤ 3 ‖a n₀ - a (n₀ - 1)‖`: `g` is the sequence obtained by *prepending `n₀` zeros* to
the constant family `v`, so `variationalNorm_prependZeros_le` gives
`‖g‖_{Vʳ} ≤ 3 ‖v‖_{Vʳ} = 3 ‖v‖` (`variationalNorm_const_le`).
-/

namespace Work.KMTAreas.A7Rescue

open scoped ENNReal NNReal

/-- The variational norm of a constant family `n ↦ c` is at most `‖c‖`: the variation part
vanishes (all increments are zero) and the supremum part is `‖c‖`. -/
private lemma variationalNorm_const_le {r : ℝ≥0} (hr : 1 ≤ r) (c : ℂ) :
    PointwiseErgodicTheorems.variationalNorm r (fun _ : ℕ => c) ≤ ‖c‖ₑ := by
  have hvar : Submission.PointwiseErgodicTheorems.varPart r (fun _ : ℕ => c) ≤ 0 := by
    refine iSup_le (fun J => iSup_le (fun N => iSup_le (fun hN => ?_)))
    have h := Submission.PointwiseErgodicTheorems.norm_toLp_le_sum_norm hr
      (fun _ : Fin J => c - c)
    have h0 : ‖WithLp.toLp r (fun _ : Fin J => c - c)‖ ≤ 0 := by simpa using h
    simpa using ENNReal.ofReal_le_ofReal h0
  calc PointwiseErgodicTheorems.variationalNorm r (fun _ : ℕ => c)
      = (⨆ n : ℕ, ‖(fun _ : ℕ => c) n‖ₑ)
          + Submission.PointwiseErgodicTheorems.varPart r (fun _ : ℕ => c) :=
        Submission.PointwiseErgodicTheorems.variationalNorm_eq_add r _
    _ ≤ ‖c‖ₑ + 0 := add_le_add (le_of_eq (by simp)) hvar
    _ = ‖c‖ₑ := add_zero _

theorem variationalNorm_pad_mono_change {r : NNReal} (hr : 1 ≤ r) (a : ℕ → ℂ) {n₀ : ℕ} (hn₀ : 1 ≤ n₀) :
    PointwiseErgodicTheorems.variationalNorm r (fun k => a (min k n₀))
      ≤ PointwiseErgodicTheorems.variationalNorm r (fun k => a (min k (n₀ - 1)))
        + 3 * ‖a n₀ - a (n₀ - 1)‖ₑ := by
  set b : ℕ → ℂ := fun k => a (min k n₀) with hb
  set c : ℕ → ℂ := fun k => a (min k (n₀ - 1)) with hc
  set v : ℂ := a n₀ - a (n₀ - 1) with hv
  set g : ℕ → ℂ := fun k => if k < n₀ then 0 else v with hg
  have hbc : b = c + g := by
    funext k
    by_cases hk : k < n₀
    · have h1 : min k n₀ = k := min_eq_left hk.le
      have h2 : min k (n₀ - 1) = k := min_eq_left (by omega)
      simp only [hb, hc, hv, hg, h1, h2, Pi.add_apply, if_pos hk, add_zero]
    · have hk' : n₀ ≤ k := le_of_not_gt hk
      have h1 : min k n₀ = n₀ := min_eq_right hk'
      have h2 : min k (n₀ - 1) = n₀ - 1 := min_eq_right (by omega)
      simp only [hb, hc, hv, hg, h1, h2, Pi.add_apply, if_neg hk]
      ring
  have hg_le : PointwiseErgodicTheorems.variationalNorm r g ≤ 3 * ‖v‖ₑ := by
    have h1 : PointwiseErgodicTheorems.variationalNorm r g
        ≤ 3 * PointwiseErgodicTheorems.variationalNorm r (fun _ : ℕ => v) := by
      rw [hg]
      exact Submission.PointwiseErgodicTheorems.variationalNorm_prependZeros_le hr n₀
        (fun _ : ℕ => v)
    exact h1.trans (mul_le_mul' le_rfl (variationalNorm_const_le hr v))
  calc PointwiseErgodicTheorems.variationalNorm r b
      = PointwiseErgodicTheorems.variationalNorm r (c + g) := by rw [hbc]
    _ ≤ PointwiseErgodicTheorems.variationalNorm r c
          + PointwiseErgodicTheorems.variationalNorm r g :=
        Submission.PointwiseErgodicTheorems.variationalNorm_add_le hr c g
    _ ≤ PointwiseErgodicTheorems.variationalNorm r c + 3 * ‖v‖ₑ :=
        add_le_add le_rfl hg_le
    _ = PointwiseErgodicTheorems.variationalNorm r (fun k => a (min k (n₀ - 1)))
          + 3 * ‖a n₀ - a (n₀ - 1)‖ₑ := by rw [hc, hv]

end Work.KMTAreas.A7Rescue
