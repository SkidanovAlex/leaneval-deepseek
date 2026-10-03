import Mathlib

/-!
# The waist walk: the real parts of `α · w` of two waist points differ by at most `66`

A walk `w : ℕ → ℂ` which is a `1/32`-approximate translation (`‖w (j+1) - (w j + 1)‖ ≤ 1/32`) and
an `α` with `‖α‖ / 16 ≤ |α.im|` (so `α` is not too close to being real) are given.  At two indices
`j, j' ≤ n` where the walk is in the *waist* `|Im (α w)| < 1`, the real parts `Re (α w j)` and
`Re (α w j')` differ by at most `66`.

The mechanism is the following.  Per step,
`Δᵣₑ = Re (α w (k+1)) - Re (α w k) = α.re + εₖ`,
`Δᵢₘ = Im (α w (k+1)) - Im (α w k) = α.im + ηₖ`
with `|εₖ|, |ηₖ| ≤ ‖α‖ / 32`.  Since `|α.im| ≥ ‖α‖ / 16 > ‖α‖ / 32`, every `Δᵢₘ` has the sign of
`α.im`, so `Im (α w ·)` is *strictly monotone* along the walk and `|Im (α w j') - Im (α w j)|` is the
sum of the `|Δᵢₘ| ≥ ‖α‖ / 16 - ‖α‖ / 32 = ‖α‖ / 32`.  The waist hypothesis at both ends (each
`|Im (α w)| < 1`) bounds that total variation by `2`, hence the number of steps satisfies
`(j' - j) ‖α‖ < 64`, while `|Δᵣₑ| ≤ |α.re| + ‖α‖ / 32 ≤ (33/32) ‖α‖` per step.  Altogether
`|Re (α w j) - Re (α w j')| ≤ (j' - j)(33/32) ‖α‖ < (33/32)·64 = 66`.
-/

namespace Work.Pert.GateDriftRate

namespace WaistWalk

/-- Telescoping count bound: if every step of `f` over the index range `[j, j')` is at least `c`,
then `f` grows by at least `(j' - j) * c` across that range. -/
lemma card_mul_le_of_step {f : ℕ → ℝ} {c : ℝ} {j j' : ℕ} (hjj : j ≤ j')
    (h : ∀ k, j ≤ k → k < j' → c ≤ f (k + 1) - f k) :
    ((j' - j : ℕ) : ℝ) * c ≤ f j' - f j := by
  have h1 : ∑ k ∈ Finset.Ico j j', c ≤ ∑ k ∈ Finset.Ico j j', (f (k + 1) - f k) :=
    Finset.sum_le_sum fun k hk => h k (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at h1
  rw [Finset.sum_Ico_sub f hjj] at h1
  exact h1

/-- Per-step estimate for an approximate translation.  The real and imaginary parts of
`α * w (k+1) - α * w k` differ from `α.re` and `α.im` by at most `‖α‖ / 32`. -/
lemma step_re_im_bound {α : ℂ} {w : ℕ → ℂ} {n k : ℕ} (hk : k < n)
    (hstep : ∀ j < n, ‖w (j + 1) - (w j + 1)‖ ≤ 1 / 32) :
    |(α * w (k + 1)).re - (α * w k).re - α.re| ≤ ‖α‖ / 32 ∧
    |(α * w (k + 1)).im - (α * w k).im - α.im| ≤ ‖α‖ / 32 := by
  have hdec : α * w (k + 1) - α * w k - α = α * (w (k + 1) - (w k + 1)) := by ring
  have hnorm : ‖α * (w (k + 1) - (w k + 1))‖ ≤ ‖α‖ / 32 := by
    rw [norm_mul]
    calc ‖α‖ * ‖w (k + 1) - (w k + 1)‖ ≤ ‖α‖ * (1 / 32) :=
          mul_le_mul_of_nonneg_left (hstep k hk) (norm_nonneg α)
      _ = ‖α‖ / 32 := by ring
  constructor
  · have hthis : (α * w (k + 1)).re - (α * w k).re - α.re
        = (α * (w (k + 1) - (w k + 1))).re := by
      rw [← hdec]; simp [Complex.sub_re]
    rw [hthis]
    exact le_trans (Complex.abs_re_le_norm _) hnorm
  · have hthis : (α * w (k + 1)).im - (α * w k).im - α.im
        = (α * (w (k + 1) - (w k + 1))).im := by
      rw [← hdec]; simp [Complex.sub_im]
    rw [hthis]
    exact le_trans (Complex.abs_im_le_norm _) hnorm

end WaistWalk

open WaistWalk

theorem waist_walk_re {α : ℂ} {w : ℕ → ℂ} {n : ℕ}
    (hstep : ∀ j < n, ‖w (j + 1) - (w j + 1)‖ ≤ 1 / 32)
    (hR : ‖α‖ / 16 ≤ |α.im|)
    (j j' : ℕ) (hj : j ≤ n) (hj' : j' ≤ n)
    (hjw : |(α * w j).im| < 1) (hj'w : |(α * w j').im| < 1) :
    |(α * w j).re - (α * w j').re| ≤ 66 := by
  -- it suffices to treat the case `j ≤ j'`, since the statement (and the hypotheses) are symmetric
  suffices hmain : ∀ a b : ℕ, a ≤ n → b ≤ n → a ≤ b →
      |(α * w a).im| < 1 → |(α * w b).im| < 1 →
      |(α * w a).re - (α * w b).re| ≤ 66 by
    rcases le_total j j' with h | h
    · exact hmain j j' hj hj' h hjw hj'w
    · have h' := hmain j' j hj' hj h hj'w hjw
      rwa [abs_sub_comm] at h'
  intro a b ha hb hab haw hbw
  have hstepk : ∀ k < n, |(α * w (k + 1)).re - (α * w k).re - α.re| ≤ ‖α‖ / 32 ∧
      |(α * w (k + 1)).im - (α * w k).im - α.im| ≤ ‖α‖ / 32 :=
    fun k hk => step_re_im_bound (α := α) (w := w) (n := n) hk hstep
  -- ## 0.  the sign of `α.im`, and monotonicity of `Im (α w ·)`
  set s : ℝ := if 0 ≤ α.im then 1 else -1 with hsdef
  have hs_abs : |s| = 1 := by rw [hsdef]; split <;> norm_num
  have hs_im : s * α.im = |α.im| := by
    rw [hsdef]; split
    · rename_i h; rw [one_mul, abs_of_nonneg h]
    · rename_i h; rw [not_le] at h; rw [neg_one_mul, abs_of_neg h]
  have hs_ge : ∀ x : ℝ, -|x| ≤ s * x := by
    intro x
    have h1 : -|s * x| ≤ s * x := neg_abs_le (s * x)
    calc -|x| = -|s * x| := by rw [abs_mul, hs_abs, one_mul]
      _ ≤ s * x := h1
  -- each step increases the signed imaginary part by at least `‖α‖ / 32`
  have hψstep : ∀ k < n, ‖α‖ / 32 ≤ s * (α * w (k + 1)).im - s * (α * w k).im := by
    intro k hk
    have hΔ := (hstepk k hk).2
    have hid : s * (α * w (k + 1)).im - s * (α * w k).im
        = s * α.im + s * ((α * w (k + 1)).im - (α * w k).im - α.im) := by ring
    rw [hid, hs_im]
    have hge := hs_ge ((α * w (k + 1)).im - (α * w k).im - α.im)
    linarith [hΔ, hge, hR]
  -- ## 1.  the number of steps is bounded: `(j' - j) ‖α‖ < 64`
  have hcount : ((b - a : ℕ) : ℝ) * (‖α‖ / 32) ≤ s * (α * w b).im - s * (α * w a).im :=
    card_mul_le_of_step hab (f := fun k => s * (α * w k).im) (c := ‖α‖ / 32)
      (fun k hk1 hk2 => hψstep k (lt_of_lt_of_le hk2 hb))
  have hsdiff : s * (α * w b).im - s * (α * w a).im ≤ |(α * w b).im - (α * w a).im| := by
    have h1 : s * (α * w b).im - s * (α * w a).im = s * ((α * w b).im - (α * w a).im) := by ring
    rw [h1]
    calc s * ((α * w b).im - (α * w a).im) ≤ |s * ((α * w b).im - (α * w a).im)| := le_abs_self _
      _ = |(α * w b).im - (α * w a).im| := by rw [abs_mul, hs_abs, one_mul]
  have him2 : |(α * w b).im - (α * w a).im| < 2 := by
    calc |(α * w b).im - (α * w a).im| ≤ |(α * w b).im| + |(α * w a).im| := abs_sub _ _
      _ < 2 := by linarith
  have hbma : ((b - a : ℕ) : ℝ) * ‖α‖ < 64 := by
    have h1 : ((b - a : ℕ) : ℝ) * (‖α‖ / 32) < 2 :=
      lt_of_le_of_lt hcount (lt_of_le_of_lt hsdiff him2)
    have h2 : ((b - a : ℕ) : ℝ) * ‖α‖ = 32 * (((b - a : ℕ) : ℝ) * (‖α‖ / 32)) := by ring
    linarith [h1, h2]
  -- ## 2.  the real part drifts by at most `(33/32) ‖α‖` per step
  have hre_step : ∀ k < n, |(α * w (k + 1)).re - (α * w k).re| ≤ |α.re| + ‖α‖ / 32 := by
    intro k hk
    have hΔ := (hstepk k hk).1
    rw [abs_le] at hΔ ⊢
    constructor <;> linarith [hΔ.1, hΔ.2, neg_abs_le α.re, le_abs_self α.re]
  have hre : |(α * w a).re - (α * w b).re| ≤ ((b - a : ℕ) : ℝ) * (|α.re| + ‖α‖ / 32) := by
    have htel : ∑ k ∈ Finset.Ico a b, ((α * w (k + 1)).re - (α * w k).re)
        = (α * w b).re - (α * w a).re := by
      rw [Finset.sum_Ico_sub (fun k => (α * w k).re) hab]
    calc |(α * w a).re - (α * w b).re|
        = |(α * w b).re - (α * w a).re| := abs_sub_comm _ _
      _ = |∑ k ∈ Finset.Ico a b, ((α * w (k + 1)).re - (α * w k).re)| := by rw [htel]
      _ ≤ ∑ k ∈ Finset.Ico a b, |(α * w (k + 1)).re - (α * w k).re| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Ico a b, (|α.re| + ‖α‖ / 32) :=
            Finset.sum_le_sum fun k hk => hre_step k (lt_of_lt_of_le (Finset.mem_Ico.mp hk).2 hb)
      _ = ((b - a : ℕ) : ℝ) * (|α.re| + ‖α‖ / 32) := by
            rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have hC : |α.re| + ‖α‖ / 32 ≤ (33 / 32) * ‖α‖ := by
    have h := Complex.abs_re_le_norm α
    linarith
  have hmid : |(α * w a).re - (α * w b).re| ≤ (33 / 32) * (((b - a : ℕ) : ℝ) * ‖α‖) := by
    calc |(α * w a).re - (α * w b).re| ≤ ((b - a : ℕ) : ℝ) * (|α.re| + ‖α‖ / 32) := hre
      _ ≤ ((b - a : ℕ) : ℝ) * ((33 / 32) * ‖α‖) := mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg _)
      _ = (33 / 32) * (((b - a : ℕ) : ℝ) * ‖α‖) := by ring
  linarith [hmid, hbma]

end Work.Pert.GateDriftRate
