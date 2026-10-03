import Mathlib
import Submission.Work.Horn.fatouQ_defs
import Submission.Work.Horn.petal_facts

/-!
# Elementary estimates behind the Hölder bound for the approximate Fatou coordinate

This file collects the shared, elementary ingredients of `Xfun_holder`:

* two real-variable lemmas on how fractional powers and logarithms behave on `[M, ∞)`
  (`abs_log_le_rpow`, `rpow_le_rpow_add_one`, `rpow_div_le`, `rpow_nat_pow_eq`);
* the complex estimate `‖log z‖ ≤ |log ‖z‖| + π`;
* the elementary consequences of the chart identity `chartQ q a (zBranch q a j w) = w`:
  the inverse chart satisfies `z ^ q = c / w`, hence `‖z⁻¹‖ ^ q = ‖w‖ / ‖c‖` and `c ≠ 0`.

Everything is proved from the definitions of `Work.Horn.Flower` / `Work.Horn.FatouQ` alone.
-/

namespace Work.Horn.FatouQ

open Work.Horn.Flower

noncomputable section

/-! ## Real-variable lemmas -/

/-- For `r ≥ M > 0` the logarithm grows at most like `2 * r ^ (1/2)`, the remaining
unboundedness being only downward, where it is controlled by `|log M|`. -/
lemma abs_log_le_rpow {M r : ℝ} (hM : 0 < M) (hr : M ≤ r) :
    |Real.log r| ≤ 2 * r ^ ((1 : ℝ) / 2) + |Real.log M| := by
  have hr0 : 0 ≤ r := le_trans hM.le hr
  rcases le_or_gt 1 r with h | h
  · have hlog : 0 ≤ Real.log r := Real.log_nonneg h
    rw [abs_of_nonneg hlog]
    have h1 : Real.log r ≤ r ^ ((1 : ℝ) / 2) / (1 / 2 : ℝ) :=
      Real.log_le_rpow_div hr0 (by norm_num)
    have h2 : r ^ ((1 : ℝ) / 2) / (1 / 2 : ℝ) = 2 * r ^ ((1 : ℝ) / 2) := by ring
    have h3 : 0 ≤ |Real.log M| := abs_nonneg _
    linarith
  · have hlog : Real.log r ≤ 0 := Real.log_nonpos hr0 h.le
    rw [abs_of_nonpos hlog]
    have hMlog : Real.log M ≤ Real.log r := Real.log_le_log hM hr
    have h2 : -Real.log r ≤ -Real.log M := by linarith
    have h3 : -Real.log M ≤ |Real.log M| := neg_le_abs _
    have h4 : 0 ≤ 2 * r ^ ((1 : ℝ) / 2) := by
      have := Real.rpow_nonneg hr0 ((1 : ℝ) / 2); linarith
    linarith

/-- `r ^ s ≤ r ^ θ + 1` for `0 ≤ s ≤ θ ≤ 1` and `r ≥ 0`. -/
lemma rpow_le_rpow_add_one {s θ r : ℝ} (hs : 0 ≤ s) (hsθ : s ≤ θ) (hθ : θ ≤ 1)
    (hr : 0 ≤ r) : r ^ s ≤ r ^ θ + 1 := by
  rcases le_or_gt 1 r with h | h
  · have h1 : r ^ s ≤ r ^ θ := Real.rpow_le_rpow_of_exponent_le h hsθ
    have h2 : 0 ≤ r ^ θ := Real.rpow_nonneg hr θ
    linarith
  · have h1 : r ^ s ≤ 1 := Real.rpow_le_one hr h.le hs
    have h2 : 0 ≤ r ^ θ := Real.rpow_nonneg hr θ
    linarith

/-- Scaling by a fixed positive `D` costs only a multiplicative constant: for `0 ≤ s ≤ θ ≤ 1`
there is `K ≥ 0` with `(r / D) ^ s ≤ K * (r ^ θ + 1)` for every `r ≥ 0`. -/
lemma rpow_div_le (D θ : ℝ) (hD : 0 < D) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (s r : ℝ), 0 ≤ s → s ≤ θ → 0 ≤ r →
      (r / D) ^ s ≤ K * (r ^ θ + 1) := by
  refine ⟨max 1 (D ^ (-θ)), le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro s r hs hsθ hr
  have hsplit : (r / D) ^ s = r ^ s * D ^ (-s) := by
    rw [Real.div_rpow hr hD.le, div_eq_mul_inv, ← Real.rpow_neg hD.le]
  rw [hsplit]
  have hDinv : D ^ (-s) ≤ max 1 (D ^ (-θ)) := by
    rcases le_or_gt 1 D with h | h
    · have h1 : D ^ (-s) ≤ D ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h (neg_nonpos.mpr hs)
      rw [Real.rpow_zero] at h1
      exact le_trans h1 (le_max_left _ _)
    · have h1 : D ^ (-s) ≤ D ^ (-θ) :=
        Real.rpow_le_rpow_of_exponent_ge hD h.le (neg_le_neg hsθ)
      exact le_trans h1 (le_max_right _ _)
  have h1 : r ^ s ≤ r ^ θ + 1 := rpow_le_rpow_add_one hs hsθ hθ1 hr
  have h3 : 0 ≤ D ^ (-s) := Real.rpow_nonneg hD.le _
  have h5 : 0 ≤ max 1 (D ^ (-θ)) := le_trans zero_le_one (le_max_left _ _)
  have h6 : 0 ≤ r ^ θ + 1 := by positivity
  calc r ^ s * D ^ (-s) ≤ (r ^ θ + 1) * max 1 (D ^ (-θ)) := mul_le_mul h1 hDinv h3 h6
    _ = max 1 (D ^ (-θ)) * (r ^ θ + 1) := by ring

/-- `r ^ (q - i) = (r ^ q) ^ ((q - i) / q)` for `r ≥ 0`, `0 < q`, `i ≤ q`. -/
lemma rpow_nat_pow_eq {r : ℝ} (hr : 0 ≤ r) {q i : ℕ} (hq : 0 < q) (hi : i ≤ q) :
    r ^ (q - i) = (r ^ q) ^ (((q - i : ℕ) : ℝ) / (q : ℝ)) := by
  rw [← Real.rpow_natCast r (q - i), ← Real.rpow_natCast r q, ← Real.rpow_mul hr]
  congr 1
  have hqi : ((q - i : ℕ) : ℝ) = (q : ℝ) - (i : ℝ) := by
    push_cast [Nat.cast_sub hi]; ring
  rw [hqi]
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  field_simp

/-! ## A complex logarithm estimate -/

/-- `‖log z‖ ≤ |log ‖z‖| + π` (principal branch; junk at `0` is harmless). -/
lemma norm_log_le (z : ℂ) : ‖Complex.log z‖ ≤ |Real.log ‖z‖| + Real.pi := by
  calc ‖Complex.log z‖ ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |Real.log ‖z‖| + |z.arg| := by rw [Complex.log_re, Complex.log_im]
    _ ≤ |Real.log ‖z‖| + Real.pi := by linarith [Complex.abs_arg_le_pi z]

/-! ## Consequences of the chart identity -/

/-- The inverse chart is nonzero as soon as the chart identity holds at a point of the open
right half plane. -/
lemma zBranch_ne_zero_of_chart {q : ℕ} {a : ℂ} {M : ℝ} (j : Fin q) {w : ℂ}
    (hM : 0 < M) (hw : M < w.re) (h : chartQ q a (zBranch q a j w) = w) :
    zBranch q a j w ≠ 0 := by
  intro h0
  have hw0 : w ≠ 0 := fun hw' => by rw [hw'] at hw; simp at hw; linarith
  have hq : 0 < q := j.pos
  rw [chartQ, h0, zero_pow hq.ne', div_zero] at h
  exact hw0 h.symm

/-- The chart identity `w = c / z ^ q` inverts to `z ^ q = c / w`. -/
lemma zBranch_pow_of_chart {q : ℕ} {a : ℂ} {M : ℝ} (j : Fin q) {w : ℂ}
    (hM : 0 < M) (hw : M < w.re) (h : chartQ q a (zBranch q a j w) = w) :
    (zBranch q a j w) ^ q = cc q a / w := by
  have hw0 : w ≠ 0 := fun hw' => by rw [hw'] at hw; simp at hw; linarith
  have hz0 : zBranch q a j w ≠ 0 := zBranch_ne_zero_of_chart j hM hw h
  have hzq : (zBranch q a j w) ^ q ≠ 0 := pow_ne_zero q hz0
  have h1 : cc q a = w * (zBranch q a j w) ^ q :=
    (div_eq_iff hzq).mp (by rw [← chartQ]; exact h)
  rw [eq_div_iff hw0, mul_comm]
  exact h1.symm

/-- The chart constant is nonzero whenever the chart identity holds. -/
lemma cc_ne_zero_of_chart {q : ℕ} {a : ℂ} {M : ℝ} (j : Fin q) {w : ℂ}
    (hM : 0 < M) (hw : M < w.re) (h : chartQ q a (zBranch q a j w) = w) :
    cc q a ≠ 0 := by
  have hzq := zBranch_pow_of_chart j hM hw h
  have hz0 : zBranch q a j w ≠ 0 := zBranch_ne_zero_of_chart j hM hw h
  intro h0
  rw [h0, zero_div] at hzq
  exact pow_ne_zero q hz0 hzq

/-- Consequently `‖z⁻¹‖ ^ q = ‖w‖ / ‖c‖`. -/
lemma norm_inv_zBranch_pow {q : ℕ} {a : ℂ} {M : ℝ} (j : Fin q) {w : ℂ}
    (hM : 0 < M) (hw : M < w.re) (h : chartQ q a (zBranch q a j w) = w) :
    ‖(zBranch q a j w)⁻¹‖ ^ q = ‖w‖ / ‖cc q a‖ := by
  have hzq := zBranch_pow_of_chart j hM hw h
  have hnp : ‖zBranch q a j w‖ ^ q = ‖cc q a‖ / ‖w‖ := by
    rw [← norm_pow, hzq, norm_div]
  rw [norm_inv, inv_pow, hnp, inv_div]

end

end Work.Horn.FatouQ
