import Mathlib
import Submission.Work.BMF.vke_defs
import Submission.Work.BMF.kdr_defs
import Submission.Work.BMF.meanValue_polySum_J
import Submission.Work.BMF.J_mono_X
import Submission.Work.BMF.vmvt_uniform
import Submission.Work.BMF.vke_H_pos

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open MeasureTheory Set
open scoped BigOperators
open LeanEval.NumberTheory.VinogradovMeanValue

noncomputable section

/-- The exponent produced by the uniform Vinogradov mean value estimate at `(k', r') = (k-1, r)`
equals the exponent displayed in `Work.BMF.vke_Mval`: the only point is the cast identity
`((k-1 : ℕ) : ℝ) + 1 = (k : ℝ)` (valid since `vkK N t ≥ 2`), together with the definitional
unfoldings of `vkS` and `vkEta`. -/
lemma vke_exp_eq (N t : ℝ) (hN : 2 ≤ N) (hNt : N ≤ t) :
    2 * (((vkK N t - 1 : ℕ) : ℝ) * ((vkR N t : ℕ) : ℝ))
      - ((vkK N t - 1 : ℕ) : ℝ) * (((vkK N t - 1 : ℕ) : ℝ) + 1) / 2
      + ((vkK N t - 1 : ℕ) : ℝ) ^ 2 / 2 * (1 - 1 / ((vkK N t - 1 : ℕ) : ℝ)) ^ (vkR N t)
    = 2 * ((vkS N t : ℕ) : ℝ) - (((vkK N t - 1 : ℕ) : ℝ)) * ((vkK N t : ℕ) : ℝ) / 2 +
        vkEta N t := by
  have hk : 1 ≤ vkK N t := by have := vkK_ge_six hN hNt; omega
  have h1 : ((vkK N t - 1 : ℕ) : ℝ) + 1 = ((vkK N t : ℕ) : ℝ) := by
    rw [show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num, ← Nat.cast_add, Nat.sub_add_cancel hk]
  simp only [vkS, vkEta]
  push_cast
  rw [h1]

/-- The mean-value exponent `2s - (k-1)k/2 + η` is nonnegative.  Since `vkR N t ≥ 4k log k` and
`log k ≥ 1` for `k = vkK N t ≥ 6`, we have `2 r ≥ k`, hence `2s = 2(k-1)r ≥ (k-1)k/2`; and
`η = ((k-1)²/2)(1 - 1/(k-1))^r ≥ 0`. -/
lemma vke_exponent_nonneg (N t : ℝ) (hN : 2 ≤ N) (hNt : N ≤ t) :
    0 ≤ 2 * ((vkS N t : ℕ) : ℝ) - (((vkK N t - 1 : ℕ) : ℝ)) * ((vkK N t : ℕ) : ℝ) / 2 +
        vkEta N t := by
  have hk6r : (6 : ℝ) ≤ ((vkK N t : ℕ) : ℝ) := by exact_mod_cast (vkK_ge_six hN hNt)
  have hkpos : (0 : ℝ) < ((vkK N t : ℕ) : ℝ) := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log ((vkK N t : ℕ) : ℝ) := by
    have hexp : Real.exp 1 ≤ ((vkK N t : ℕ) : ℝ) := by
      have := Real.exp_one_lt_d9
      linarith
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hr2 : ((vkK N t : ℕ) : ℝ) ≤ 2 * ((vkR N t : ℕ) : ℝ) := by
    have h1 := vkR_ge (N := N) (t := t)
    have h2 : ((vkK N t : ℕ) : ℝ) ≤
        8 * (((vkK N t : ℕ) : ℝ) * Real.log ((vkK N t : ℕ) : ℝ)) := by
      nlinarith [hlog1, hkpos]
    nlinarith [h1, h2]
  have hsub : 1 ≤ vkK N t := by have := vkK_ge_six hN hNt; omega
  have hs : ((vkS N t : ℕ) : ℝ) = (((vkK N t - 1 : ℕ) : ℝ)) * ((vkR N t : ℕ) : ℝ) := by
    rw [vkS, Nat.cast_mul]
  have heta : 0 ≤ vkEta N t := by
    have hmpos : (0 : ℝ) < ((vkK N t - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hsub]; push_cast; linarith
    rw [vkEta]
    refine mul_nonneg (by positivity) (pow_nonneg ?_ _)
    rw [sub_nonneg, div_le_one hmpos]
    have h1 : (1 : ℝ) ≤ (((vkK N t - 1 : ℕ)) : ℝ) := by
      rw [Nat.cast_sub hsub]; push_cast; linarith
    linarith
  have hmain : 0 ≤ 2 * (((vkK N t - 1 : ℕ) : ℝ) * ((vkR N t : ℕ) : ℝ))
      - (((vkK N t - 1 : ℕ) : ℝ)) * ((vkK N t : ℕ) : ℝ) / 2 := by
    have hkm1 : (0 : ℝ) ≤ ((vkK N t - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hsub]; push_cast; linarith
    have hfac : 2 * (((vkK N t - 1 : ℕ) : ℝ) * ((vkR N t : ℕ) : ℝ))
        - (((vkK N t - 1 : ℕ) : ℝ)) * ((vkK N t : ℕ) : ℝ) / 2
        = ((vkK N t - 1 : ℕ) : ℝ) * (2 * ((vkR N t : ℕ) : ℝ) - ((vkK N t : ℕ) : ℝ) / 2) := by
      ring
    rw [hfac]
    exact mul_nonneg hkm1 (by linarith)
  rw [hs]
  linarith

/-- Degenerate branch: if the Weyl shift satisfies `⌊H⌋₊ = 0` then `x ≤ H < 1`, so `⌊x⌋₊ = 0`,
the box Weyl sum is the empty sum `0`, and the moment integral vanishes. -/
lemma vke_floorH_integral_zero (N t x : ℝ) (hx : x ≤ vkH N t) (hfl : ⌊vkH N t⌋₊ = 0) :
    (∫ α in unitBox (vkK N t - 1),
        ‖polySum (vkK N t - 1) α x‖ ^ (2 * ((vkS N t : ℕ) : ℝ))) = 0 := by
  have hfx : ⌊x⌋₊ = 0 := le_antisymm ((Nat.floor_mono hx).trans_eq hfl) (Nat.zero_le _)
  have hk2 : 1 ≤ vkK N t - 1 := by
    have : 2 ≤ vkK N t := by rw [vkK]; omega
    omega
  have hr1 : 1 ≤ vkR N t := by rw [vkR]; omega
  have hs1 : 1 ≤ vkS N t := by
    rw [vkS]
    calc (1 : ℕ) = 1 * 1 := by ring
      _ ≤ (vkK N t - 1) * vkR N t := Nat.mul_le_mul hk2 hr1
  have hsne : 2 * ((vkS N t : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (vkS N t : ℕ) := by exact_mod_cast (by omega : 0 < vkS N t)
    positivity
  have hzero : (fun α : Fin (vkK N t - 1) → ℝ =>
      ‖polySum (vkK N t - 1) α x‖ ^ (2 * ((vkS N t : ℕ) : ℝ))) = fun _ => 0 := by
    funext α
    have hp : polySum (vkK N t - 1) α x = 0 := by
      rw [polySum, hfx]
      simp
    rw [hp, norm_zero]
    exact Real.zero_rpow hsne
  rw [hzero]
  simp

/-- **The box-integral bound feeding the Weyl reduction.**  There is a constant `C₁ > 0` such that
for `2 ≤ N ≤ t` the `2s`-th moment over `[0,1]^{k-1}` of the box Weyl sum of degree `k-1` is
bounded, uniformly for `0 ≤ x ≤ H`, by `exp (C₁ (k-1)² r² (1 + log((k-1)r))) · H^{2s - (k-1)k/2 + η}`,
where `s = (k-1) r` and `η = ((k-1)²/2)(1 - 1/(k-1))^r`.

Route.  `Work.BMF.meanValue_polySum_J` identifies the moment with `J s (k-1) ⌊x⌋₊`; monotonicity in
the range (`Work.BMF.J_mono_X`, with `⌊x⌋₊ ≤ ⌊H⌋₊` since `x ≤ H`) bounds that by `J s (k-1) ⌊H⌋₊`;
the uniform Vinogradov mean value estimate `Work.BMF.vmvt_uniform`, whose constant `C₁` is the one
produced here, at `(k', r') = (k-1, r)` (with `k-1 ≥ 2`, `r ≥ 1`, `⌊H⌋₊ ≥ 1`, from
`Work.BMF.vkK_ge_six`) bounds the latter by `exp (C₁ (k-1)² r² (1 + log((k-1)r))) ⌊H⌋₊^{2s - (k-1)k/2 + η}`;
and `⌊H⌋₊ ≤ H` together with `2s - (k-1)k/2 + η ≥ 0` (from `r ≥ k/4` and `η ≥ 0`, cf.
`Work.BMF.vkR_ge`) allows replacing `⌊H⌋₊` by `H`.  Note `k'(k'+1)/2 = (k-1)k/2`, matching the
exponent in `vmvt_uniform`.  If `⌊H⌋₊ = 0` the Weyl sum is empty and the bound is trivial. -/
theorem vke_Mval :
    ∃ C1 : ℝ, 0 < C1 ∧ ∀ (N t : ℝ), 2 ≤ N → N ≤ t → ∀ x : ℝ, 0 ≤ x → x ≤ vkH N t →
      (∫ α in unitBox (vkK N t - 1),
          ‖polySum (vkK N t - 1) α x‖ ^ (2 * ((vkS N t : ℕ) : ℝ)))
        ≤ Real.exp (C1 * (((vkK N t - 1 : ℕ) : ℝ))^2 * ((vkR N t : ℕ) : ℝ)^2 *
              (1 + Real.log ((((vkK N t - 1 : ℕ) : ℝ)) * ((vkR N t : ℕ) : ℝ))))
          * (vkH N t) ^ (2 * ((vkS N t : ℕ) : ℝ)
              - (((vkK N t - 1 : ℕ) : ℝ)) * ((vkK N t : ℕ) : ℝ) / 2 + vkEta N t) := by
  obtain ⟨C1, hC1pos, hvmvt⟩ := vmvt_uniform
  refine ⟨C1, hC1pos, ?_⟩
  intro N t hN hNt x hx0 hxH
  by_cases hfl : ⌊vkH N t⌋₊ = 0
  · rw [vke_floorH_integral_zero N t x hxH hfl]
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (vke_H_pos N t hN hNt).le _)
  · have hP : 1 ≤ ⌊vkH N t⌋₊ := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hfl)
    have hk2 : 2 ≤ vkK N t - 1 := by have := vkK_ge_six hN hNt; omega
    have hr1 : 1 ≤ vkR N t := by rw [vkR]; omega
    have hvm := hvmvt (vkK N t - 1) (vkR N t) ⌊vkH N t⌋₊ hk2 hr1 hP
    have hmean : (∫ α in unitBox (vkK N t - 1),
          ‖polySum (vkK N t - 1) α x‖ ^ (2 * ((vkS N t : ℕ) : ℝ)))
        = J (vkS N t) (vkK N t - 1) ⌊x⌋₊ := by
      rw [← meanValue_polySum_J (vkS N t) (vkK N t - 1) ⌊x⌋₊]
      apply integral_congr_ae
      filter_upwards with α
      simp only [polySum, Nat.floor_natCast]
    calc (∫ α in unitBox (vkK N t - 1),
            ‖polySum (vkK N t - 1) α x‖ ^ (2 * ((vkS N t : ℕ) : ℝ)))
        = J (vkS N t) (vkK N t - 1) ⌊x⌋₊ := hmean
      _ ≤ J (vkS N t) (vkK N t - 1) ⌊vkH N t⌋₊ := J_mono_X _ _ (Nat.floor_mono hxH)
      _ ≤ Real.exp (C1 * (((vkK N t - 1 : ℕ) : ℝ))^2 * ((vkR N t : ℕ) : ℝ)^2 *
              (1 + Real.log ((((vkK N t - 1 : ℕ) : ℝ)) * ((vkR N t : ℕ) : ℝ))))
            * (⌊vkH N t⌋₊ : ℝ) ^ (2 * (((vkK N t - 1 : ℕ) : ℝ) * ((vkR N t : ℕ) : ℝ))
              - ((vkK N t - 1 : ℕ) : ℝ) * (((vkK N t - 1 : ℕ) : ℝ) + 1) / 2
              + ((vkK N t - 1 : ℕ) : ℝ) ^ 2 / 2 *
                (1 - 1 / ((vkK N t - 1 : ℕ) : ℝ)) ^ (vkR N t)) := hvm
      _ ≤ Real.exp (C1 * (((vkK N t - 1 : ℕ) : ℝ))^2 * ((vkR N t : ℕ) : ℝ)^2 *
              (1 + Real.log ((((vkK N t - 1 : ℕ) : ℝ)) * ((vkR N t : ℕ) : ℝ))))
            * (vkH N t) ^ (2 * ((vkS N t : ℕ) : ℝ)
              - (((vkK N t - 1 : ℕ) : ℝ)) * ((vkK N t : ℕ) : ℝ) / 2 + vkEta N t) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        rw [vke_exp_eq N t hN hNt]
        exact Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (vke_H_pos N t hN hNt).le)
          (vke_exponent_nonneg N t hN hNt)

end

end Work.BMF
