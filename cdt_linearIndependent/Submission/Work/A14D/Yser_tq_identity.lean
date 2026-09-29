import Mathlib
import Submission.Work.A14D.BU_defs

/-!
# `Yser_tq_identity`

`Yser f w = Σ_k a_k (yC w)^k` is the value at `y = yC w` of the `y`-series `f = Σ a_k y^k`,
and `tq i f = Σ_n a_{n+i} y^n = (f − Σ_{n<i} a_n y^n)/y^i` (the formal `i`-fold Taylor
remainder).  Hence, whenever the coefficient bound `‖a_k‖ R^k ≤ C` holds and `‖yC w‖ < R`
so that everything converges,

`Yser (tq i f) w · (yC w)^i = Yser f w − Σ_{n<i} a_n (yC w)^n`,

which is the identity used to identify the integral slots `∫ (f − jet_i)/y^{i+1}`.
-/

namespace Work.A14D

open Complex Metric

noncomputable section

/-- Splitting a convergent power series at `i`: the tail `Σ_n c_{n+i} y^n`, after
multiplication by `y^i`, is the full sum minus the first `i` terms. -/
lemma tsum_shift_mul_pow (c : ℕ → ℂ) (y : ℂ) (i : ℕ)
    (h : Summable (fun k => c k * y ^ k)) :
    (∑' n : ℕ, c (n + i) * y ^ n) * y ^ i
      = (∑' k : ℕ, c k * y ^ k) - ∑ n ∈ Finset.range i, c n * y ^ n := by
  have hshift : HasSum (fun n => (fun k => c k * y ^ k) (n + i))
      ((∑' k : ℕ, c k * y ^ k) - ∑ n ∈ Finset.range i, c n * y ^ n) :=
    (hasSum_nat_add_iff (f := fun k => c k * y ^ k) i).mpr
      (by rw [sub_add_cancel]; exact h.hasSum)
  calc (∑' n : ℕ, c (n + i) * y ^ n) * y ^ i
      = (∑' n : ℕ, (c (n + i) * y ^ n) * y ^ i) := by rw [← tsum_mul_right]
    _ = (∑' n : ℕ, c (n + i) * y ^ (n + i)) := by
          apply tsum_congr; intro n; rw [mul_assoc, ← pow_add]
    _ = (∑' k : ℕ, c k * y ^ k) - ∑ n ∈ Finset.range i, c n * y ^ n := hshift.tsum_eq

/-- The coefficient bound `‖a_k‖ R^k ≤ C` with `‖yC w‖ < R` makes the series
`Σ a_k (yC w)^k` (absolutely) summable. -/
lemma summable_coeff_mul_pow (f : PowerSeries ℚ) {C R : ℝ} (hR : 0 < R)
    (hf : ∀ k : ℕ, ‖((PowerSeries.coeff k f : ℚ) : ℂ)‖ * R ^ k ≤ C) {w : ℂ}
    (hw : ‖Work.A14D.yC w‖ < R) :
    Summable (fun k : ℕ => ((PowerSeries.coeff k f : ℚ) : ℂ) * (Work.A14D.yC w) ^ k) := by
  have hr : ‖Work.A14D.yC w‖ / R < 1 := by
    rw [div_lt_one hR]; exact hw
  have hgeom : Summable (fun k : ℕ => C * (‖Work.A14D.yC w‖ / R) ^ k) := by
    refine (summable_geometric_of_norm_lt_one ?_).mul_left C
    rw [Real.norm_of_nonneg (div_nonneg (norm_nonneg _) hR.le)]
    exact hr
  refine Summable.of_norm_bounded hgeom (fun k => ?_)
  rw [norm_mul, norm_pow]
  have hRk : (0:ℝ) < R ^ k := pow_pos hR k
  have hbound : ‖((PowerSeries.coeff k f : ℚ) : ℂ)‖ ≤ C / R ^ k :=
    (le_div_iff₀ hRk).mpr (hf k)
  calc ‖((PowerSeries.coeff k f : ℚ) : ℂ)‖ * ‖Work.A14D.yC w‖ ^ k
      ≤ (C / R ^ k) * ‖Work.A14D.yC w‖ ^ k :=
        mul_le_mul_of_nonneg_right hbound (pow_nonneg (norm_nonneg _) k)
    _ = C * (‖Work.A14D.yC w‖ / R) ^ k := by rw [div_pow]; ring

/-- The coefficient identity `[y^n] (tq i f) = [y^{n+i}] f`. -/
lemma coeff_tq (f : PowerSeries ℚ) (i n : ℕ) :
    PowerSeries.coeff n (Submission.CDTPlan.tq i f) = PowerSeries.coeff (n + i) f :=
  PowerSeries.coeff_mk n _

theorem Yser_tq_identity (f : PowerSeries ℚ) {C R : ℝ} (hC : 0 < C) (hR : 0 < R)
    (hf : ∀ k : ℕ, ‖((PowerSeries.coeff k f : ℚ) : ℂ)‖ * R ^ k ≤ C) (i : ℕ) {w : ℂ}
    (hw : ‖Work.A14D.yC w‖ < R) :
    Work.A14D.Yser (Submission.CDTPlan.tq i f) w * (Work.A14D.yC w) ^ i
      = Work.A14D.Yser f w
        - ∑ n ∈ Finset.range i, ((PowerSeries.coeff n f : ℚ) : ℂ) * (Work.A14D.yC w) ^ n := by
  have hsum : Summable
      (fun k : ℕ => ((PowerSeries.coeff k f : ℚ) : ℂ) * (Work.A14D.yC w) ^ k) :=
    summable_coeff_mul_pow f hR hf hw
  have key := tsum_shift_mul_pow (fun k => ((PowerSeries.coeff k f : ℚ) : ℂ)) (Work.A14D.yC w)
    i hsum
  have hL : Work.A14D.Yser (Submission.CDTPlan.tq i f) w
      = ∑' n : ℕ, ((PowerSeries.coeff (n + i) f : ℚ) : ℂ) * (Work.A14D.yC w) ^ n := by
    simp only [Work.A14D.Yser, Submission.CDTPlan.tq, PowerSeries.coeff_mk]
  have hR' : Work.A14D.Yser f w
      = ∑' k : ℕ, ((PowerSeries.coeff k f : ℚ) : ℂ) * (Work.A14D.yC w) ^ k := rfl
  rw [hL, hR']
  exact key

end

end Work.A14D
