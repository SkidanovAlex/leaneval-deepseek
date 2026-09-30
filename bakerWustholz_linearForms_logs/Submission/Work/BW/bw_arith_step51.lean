import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW_Step51.bw_step51_part2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-! ### BW step 51 (arithmetic of §13/§14)

Two independent numerical facts are assembled here:

* `bw_ph_le` (proved in this file): the integer `h = ⌊H + v log 2⌋` satisfies
  `h ≤ (n+1) H max(2^v/c, 1)`, the "`h`-bound" that sizes the auxiliary polynomial;
* `Work.BW_Step51.bw_step51_part2` (proved by a colleague): the multiplicative
  comparison `9·2^r·S·D ≤ κ'·H·∏σ`, which is a constant-matching computation
  reducing to `h ≤ (n+1) H max(2^v/c, 1)`. -/

/-- The floor bound for `h = ph H v = ⌊H + v log 2⌋` used in BW §13:

`⌊H + v log 2⌋ ≤ (n+1) · H · max (2^v / c, 1)`

under the standing hypotheses `exp 1 ≤ c` and `log c < n H`.

The proof splits on whether `2^v ≤ c`: if so then `v log 2 ≤ log c < n H` and the
bound is `(n+1)H`; otherwise `c ≤ 2^v`, and since `x ↦ log x / x` is antitone on
`[exp 1, ∞)` (Mathlib's `Real.log_div_self_antitoneOn`) we have
`log c / c ≥ log(2^v)/2^v`, whence
`v log 2 ≤ n H (2^v/c) ≤ H((n+1)(2^v/c) - 1)`. -/
lemma bw_ph_le (n v : ℕ) (c H : ℝ) (_hn : 1 ≤ n)
    (hH : 0 < H) (hcr : Real.exp 1 ≤ c) (hlogc : Real.log c < (n : ℝ) * H) :
    (ph H v : ℝ) ≤ (n + 1) * H * max ((2 : ℝ) ^ v / c) 1 := by
  have hcpos : 0 < c := lt_of_lt_of_le (Real.exp_pos 1) hcr
  have hfloor : (ph H v : ℝ) ≤ H + (v : ℝ) * Real.log 2 := by
    rw [ph]
    apply Nat.floor_le
    positivity
  suffices hsuff : H + (v : ℝ) * Real.log 2 ≤ ((n : ℝ) + 1) * H * max ((2 : ℝ) ^ v / c) 1 by
    linarith
  by_cases hcase : (2 : ℝ) ^ v / c ≤ 1
  · -- Case A: `2^v ≤ c`, the maximum equals `1`.
    have hmax : max ((2 : ℝ) ^ v / c) 1 = 1 := max_eq_right hcase
    rw [hmax, mul_one]
    have h2v_le_c : (2 : ℝ) ^ v ≤ c := by
      have h := (div_le_iff₀ hcpos).mp hcase
      linarith
    have hlogle : Real.log ((2 : ℝ) ^ v) ≤ Real.log c :=
      Real.log_le_log (by positivity) h2v_le_c
    rw [Real.log_pow] at hlogle
    nlinarith [hlogc, hlogle, hH]
  · -- Case B: `c ≤ 2^v`, the maximum equals `2^v / c`.
    replace hcase : 1 < (2 : ℝ) ^ v / c := not_le.mp hcase
    have hmax : max ((2 : ℝ) ^ v / c) 1 = (2 : ℝ) ^ v / c := max_eq_left (le_of_lt hcase)
    rw [hmax, ← Real.log_pow]
    set s : ℝ := (2 : ℝ) ^ v with hs
    have hs_pos : 0 < s := by rw [hs]; positivity
    have hc_le_s : c ≤ s := by
      have h : 1 * c < s := by rw [hs]; exact (lt_div_iff₀ hcpos).mp hcase
      linarith
    have hexp_le_s : Real.exp 1 ≤ s := le_trans hcr hc_le_s
    have hmono : Real.log s / s ≤ Real.log c / c :=
      Real.log_div_self_antitoneOn hcr hexp_le_s hc_le_s
    have h1 : Real.log s ≤ Real.log c * (s / c) := by
      have h := mul_le_mul_of_nonneg_right hmono hs_pos.le
      rw [div_mul_cancel₀ (Real.log s) hs_pos.ne'] at h
      rwa [div_mul_eq_mul_div, mul_div_assoc] at h
    have h2 : Real.log s < H * ((n : ℝ) * (s / c)) := by
      have hsc_pos : 0 < s / c := div_pos hs_pos hcpos
      have h := mul_lt_mul_of_pos_right hlogc hsc_pos
      nlinarith [h1, h]
    have hge1 : 1 ≤ s / c := le_of_lt hcase
    have key : (n : ℝ) * (s / c) ≤ ((n : ℝ) + 1) * (s / c) - 1 := by nlinarith [hge1]
    have h3 : H * ((n : ℝ) * (s / c)) ≤ H * (((n : ℝ) + 1) * (s / c) - 1) :=
      mul_le_mul_of_nonneg_left key hH.le
    have h4 : Real.log s < H * (((n : ℝ) + 1) * (s / c) - 1) := lt_of_lt_of_le h2 h3
    nlinarith [h4]

theorem bw_arith_step51 (n d r v : ℕ) (c H : ℝ) (σ : Fin r → ℝ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (hr : 1 ≤ r) (hH : 0 < H) (hcr : Real.exp 1 ≤ c) (hlogc : Real.log c < n * H)
    (hσ : ∀ j, 0 < σ j) :
    (ph H v : ℝ) ≤ (n + 1) * H * max (2 ^ v / c) 1 ∧
    9 * 2 ^ r * (pS r d (ph H v) : ℝ) * pD r d σ ≤ kappa' n d r v c * H * ∏ j, σ j := by
  have hp : (ph H v : ℝ) ≤ (n + 1) * H * max ((2 : ℝ) ^ v / c) 1 :=
    bw_ph_le n v c H hn hH hcr hlogc
  exact ⟨hp, Work.BW_Step51.bw_step51_part2 n d r v c H σ hr hd hσ hp⟩

end Work.BW
