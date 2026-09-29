import Mathlib
import Submission.Work.Resample.buQWdefs
import Submission.Work.Resample.buNeumannArith

/-!
# `Work.Resample.buQWnloop`: two elementary size bounds for the loop parameters

`egN p α s t = ⌈ps/(α²(t-s))⌉` is the number of Neumann rounds and
`egM p α = ⌊√p/(2α)⌋ + 1` is the Gaussian window half-width.

Under the paper's hypothesis `θ = t/s - 1 ≥ p/α⁴` (together with `2 ≤ s`, `s < t`, `α ≥ 2`,
`p ≥ 100`, `α² < p`) we prove

* `egN p α s t ≤ α² + 1`;
* `(egN+1)(egM+1)(s+1) ≤ 16 (t+1)(√p+1)(α+1)`.

The first bound comes from `ps ≤ α⁴(t-s)` (i.e. `α⁴ ≥ p/θ`), the second only from
`t > s`, `α² < p` and the first bound: `2α(egM+1) = 2α⌊√p/(2α)⌋ + 4α ≤ √p + 4α`,
`(α²+2)(√p+4α) ≤ 32α(√p+1)(α+1)` (since `4α ≤ 15√p` as `α ≤ √p`), and `s < t`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

/-- **First bound**: `egN p α s t ≤ α² + 1`.

From `θ ≥ p/α⁴` we get `p·s ≤ α⁴·(t-s)`, hence
`(p·s - 1)/(α²(t-s)) < α² + 1` because `α⁴ ≤ α²(α²+1)`. -/
theorem buQWnloop_egN_le (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1) :
    egN p α s t ≤ α ^ 2 + 1 := by
  have hs0 : 0 < s := by omega
  have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs0
  have hsub : ((t - s : ℕ) : ℝ) = (t : ℝ) - (s : ℝ) := Nat.cast_sub (le_of_lt hst)
  -- multiply `hθ` by `s > 0`
  have hθs : ((p : ℝ) / (α : ℝ) ^ 4) * (s : ℝ) ≤ ((t - s : ℕ) : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hθ (le_of_lt hspos)
    rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hspos), one_mul] at h
    rwa [← hsub] at h
  have hA4pos : (0 : ℝ) < (α : ℝ) ^ 4 := by positivity
  -- multiply by `α⁴ > 0`
  have hpsR : (p : ℝ) * (s : ℝ) ≤ ((t - s : ℕ) : ℝ) * (α : ℝ) ^ 4 := by
    have h := mul_le_mul_of_nonneg_right hθs (le_of_lt hA4pos)
    have h1 : ((p : ℝ) / (α : ℝ) ^ 4 * (s : ℝ)) * (α : ℝ) ^ 4 = (p : ℝ) * (s : ℝ) := by
      field_simp
    rwa [h1] at h
  have hps : p * s ≤ α ^ 4 * (t - s) := by
    have hh : ((p * s : ℕ) : ℝ) ≤ ((α ^ 4 * (t - s) : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hh
  have hDpos : 0 < α ^ 2 * (t - s) := by
    have h1 : 0 < t - s := by omega
    positivity
  have hlt : p * s - 1 < (α ^ 2 + 1) * (α ^ 2 * (t - s)) := by
    have hps1 : 1 ≤ p * s := by
      have h1 : 0 < p := by omega
      have : 0 < p * s := Nat.mul_pos h1 hs0
      omega
    have h1 : p * s - 1 < α ^ 4 * (t - s) := by omega
    have h2 : α ^ 4 * (t - s) ≤ (α ^ 2 + 1) * (α ^ 2 * (t - s)) := by
      have h3 : α ^ 2 * α ^ 2 ≤ (α ^ 2 + 1) * α ^ 2 := Nat.mul_le_mul_right _ (Nat.le_succ _)
      have h4 := Nat.mul_le_mul_right (t - s) h3
      calc α ^ 4 * (t - s) = α ^ 2 * α ^ 2 * (t - s) := by ring
        _ ≤ (α ^ 2 + 1) * α ^ 2 * (t - s) := h4
        _ = (α ^ 2 + 1) * (α ^ 2 * (t - s)) := by ring
    omega
  have hNle : (p * s - 1) / (α ^ 2 * (t - s)) ≤ α ^ 2 := by
    have h : (p * s - 1) / (α ^ 2 * (t - s)) < α ^ 2 + 1 :=
      (Nat.div_lt_iff_lt_mul hDpos).mpr hlt
    omega
  show egN p α s t ≤ α ^ 2 + 1
  rw [egN]
  omega

/-- **Second bound**: `(egN+1)(egM+1)(s+1) ≤ 16 (t+1)(√p+1)(α+1)`.

Uses only `s < t`, `α ≤ √p` (from `α² < p`) and `egN ≤ α² + 1`.  Everything is multipled by
`2α` so that the integer division `√p/(2α)` can be bounded by `2α(⌊√p/(2α)⌋+1) ≤ √p + 4α`. -/
theorem buQWnloop_prod (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (hαp : α ^ 2 < p) (hN : egN p α s t ≤ α ^ 2 + 1) :
    (egN p α s t + 1) * (egM p α + 1) * (s + 1) ≤
      16 * (t + 1) * (Nat.sqrt p + 1) * (α + 1) := by
  -- `α ≤ √p`
  have hAleP : α ≤ Nat.sqrt p := by
    rw [Nat.le_sqrt]
    calc α * α = α ^ 2 := by ring
      _ ≤ p := le_of_lt hαp
  -- `2α(egM+1) ≤ √p + 4α`, since `egM+1 = ⌊√p/(2α)⌋ + 2`
  have hM : 2 * α * (egM p α + 1) ≤ Nat.sqrt p + 4 * α := by
    have hdiv : 2 * α * (Nat.sqrt p / (2 * α)) ≤ Nat.sqrt p := Nat.mul_div_le _ _
    rw [egM]
    calc 2 * α * (Nat.sqrt p / (2 * α) + 1 + 1)
        = 2 * α * (Nat.sqrt p / (2 * α)) + 4 * α := by ring
      _ ≤ Nat.sqrt p + 4 * α := by omega
  -- `(α²+2)(√p+4α) ≤ 32α(√p+1)(α+1)`
  have hD : (α ^ 2 + 2) * (Nat.sqrt p + 4 * α) ≤ 32 * α * (Nat.sqrt p + 1) * (α + 1) := by
    have h4 : 4 * α ≤ 15 * Nat.sqrt p := by omega
    have h2 : 2 ≤ α ^ 2 := by nlinarith
    nlinarith [h4, hAleP, h2, Nat.zero_le α]
  have hA : egN p α s t + 1 ≤ α ^ 2 + 2 := by omega
  have hE : s + 1 ≤ t + 1 := by omega
  have hkey : 2 * α * ((egN p α s t + 1) * (egM p α + 1) * (s + 1))
      ≤ 2 * α * (16 * (t + 1) * (Nat.sqrt p + 1) * (α + 1)) := by
    have h1 : (egN p α s t + 1) * (2 * α * (egM p α + 1))
        ≤ (α ^ 2 + 2) * (Nat.sqrt p + 4 * α) := Nat.mul_le_mul hA hM
    have h2 : (egN p α s t + 1) * (2 * α * (egM p α + 1)) * (s + 1)
        ≤ (α ^ 2 + 2) * (Nat.sqrt p + 4 * α) * (t + 1) := Nat.mul_le_mul h1 hE
    have h3 : (α ^ 2 + 2) * (Nat.sqrt p + 4 * α) * (t + 1)
        ≤ 32 * α * (Nat.sqrt p + 1) * (α + 1) * (t + 1) :=
      Nat.mul_le_mul_right (t + 1) hD
    calc 2 * α * ((egN p α s t + 1) * (egM p α + 1) * (s + 1))
        = (egN p α s t + 1) * (2 * α * (egM p α + 1)) * (s + 1) := by ring
      _ ≤ (α ^ 2 + 2) * (Nat.sqrt p + 4 * α) * (t + 1) := h2
      _ ≤ 32 * α * (Nat.sqrt p + 1) * (α + 1) * (t + 1) := h3
      _ = 2 * α * (16 * (t + 1) * (Nat.sqrt p + 1) * (α + 1)) := by ring
  exact Nat.le_of_mul_le_mul_left hkey (by omega)

theorem buQWnloop (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (hαp : α ^ 2 < p) (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1) :
    Work.Resample.egN p α s t ≤ α ^ 2 + 1 ∧
    (Work.Resample.egN p α s t + 1) * (Work.Resample.egM p α + 1) * (s + 1) ≤
      16 * (t + 1) * (Nat.sqrt p + 1) * (α + 1) :=
  ⟨buQWnloop_egN_le p α s t hs hst hα hp hθ,
   buQWnloop_prod p α s t hs hst hα hp hαp (buQWnloop_egN_le p α s t hs hst hα hp hθ)⟩

end Work.Resample
