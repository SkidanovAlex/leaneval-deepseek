/-
# `Submission.Work.FIArea7.modeLen_bounds`

The two-sided bound for the mode length of the §17 bridge,

  `modeLen Pa X = ⌈θ⁻¹⌉ · X · ⌈log(N+2)⌉⁶`  (`Submission/Work/FIArea7/Bridge17Defs.lean`),

in the regime in which the bridge uses it: `x ≥ x₀` and `X ≤ (log N)^{nuU}`.

* **lower**: `θ⁻¹·X·(log(N+2))⁶ ≤ modeLen Pa X`.  This is `Nat.le_ceil` twice; no hypothesis on
  `Pa` beyond those already carried by `Params` (`θ > 0`, `N ≥ 1`) is needed, and no threshold.

* **upper**: `modeLen Pa X ≤ (log N)^{2A'+nuU+7}`.  Here `θ = (log x)^{-A'}` with
  `A' ≥ 2A + 2²⁰ ≥ 1`, and (4.6) gives `N > x^{1/4+η} > x^{1/4}`, so `log x < 4 log N`.  Hence
  * `⌈θ⁻¹⌉ ≤ 2 θ⁻¹ = 2 (log x)^{A'} ≤ 2 (4 log N)^{A'} ≤ 2 (log N)^{2A'}`, using `4 ≤ log N`;
  * `⌈log(N+2)⌉⁶ ≤ (2 log(N+2))⁶ ≤ (4 log N)⁶`, since `N ≥ 1` gives `N + 2 ≤ 3N` and
    `log 3 ≤ 1 ≤ log N` (the lemma `log_add_two_le_two_log`);
  * `X ≤ (log N)^{nuU}` by hypothesis.

  So `modeLen ≤ 2¹³ (log N)^{2A'} (log N)^{nuU} (log N)⁶ = 2¹³ (log N)^{2A'+nuU+6}`, and
  `2¹³ ≤ log N` finishes.  Everything reduces to `log N ≥ 8192`, which `log x ≥ 40000` and
  `log N > log x / 4` supply: the threshold is `x₀ = exp 40000`, uniform in `η, A, A', B, θ, …`.

The three real-arithmetic inputs are proved below as standalone lemmas
(`ceil_mul_ceil_pow_le`, `log_add_two_le_two_log`, `rpow_polylog_core`), and `nuU ≥ 0` for the
exponent `nuU = 3·sigmaChoice Asave + 4` (`FITop4/Areas6.lean`).
-/
import Mathlib
import Submission.Work.FIArea7.Bridge17Defs

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The exponent `nuU = 3·sigmaChoice Asave + 4` of the area-7 cap `X ≤ (log N)^{nuU}` is
non-negative (in fact `≈ 3·10⁹`). -/
lemma nuU_nonneg : (0 : ℝ) ≤ Work.FITop4.nuU := by
  unfold Work.FITop4.nuU Work.FITop4.sigmaChoice Work.FITop4.Aprime Work.FITop4.Asave
  norm_num

/-- **The `⌈·⌉` comparison of the lower bound.**  For `a, b ≥ 0` the product `a·X·b^k` is at most
`⌈a⌉·X·⌈b⌉^k`. -/
lemma ceil_mul_ceil_pow_le (a b : ℝ) (X k : ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * (X : ℝ) * b ^ k ≤ ((Nat.ceil a * X * Nat.ceil b ^ k : ℕ) : ℝ) := by
  push_cast
  gcongr
  · exact Nat.le_ceil a
  · exact Nat.le_ceil b

/-- For real `N ≥ 2`, `log (N + 2) ≤ 2 log N` (because `N + 2 ≤ N·N`). -/
lemma log_add_two_le_two_log {N : ℝ} (hN : 2 ≤ N) :
    Real.log (N + 2) ≤ 2 * Real.log N := by
  have hNpos : 0 < N := by linarith
  have hsq : N + 2 ≤ N ^ 2 := by nlinarith
  calc Real.log (N + 2) ≤ Real.log (N ^ 2) :=
        Real.log_le_log (by linarith) hsq
    _ = 2 * Real.log N := by rw [Real.log_pow]; norm_num

/-- **The real-power comparison of the upper bound.**  If `C ≥ 0`, `C ≤ t`, `1 ≤ s ≤ 4t`,
`t ≥ 4`, `β ≥ 0` and `ν ≥ 0`, then `C·s^β·t^{ν+6} ≤ t^{2β+ν+7}`: indeed
`s^β ≤ (4t)^β = 4^β t^β ≤ t^β t^β = t^{2β}` (as `t ≥ 4`), and `C ≤ t` supplies one more factor
`t`, while `t^{2β}·t^{ν+6} = t^{2β+ν+6}`. -/
lemma rpow_polylog_core {C s t β ν : ℝ} (hC0 : 0 ≤ C) (hC : C ≤ t) (hs : 1 ≤ s)
    (ht : 4 ≤ t) (hsle : s ≤ 4 * t) (hβ : 0 ≤ β) (hν : 0 ≤ ν) :
    C * s ^ β * t ^ (ν + 6) ≤ t ^ (2 * β + ν + 7) := by
  have ht0 : 0 < t := by linarith
  have hs0 : 0 ≤ s := by linarith
  have ht0' : 0 ≤ t := le_of_lt ht0
  have hsβ : s ^ β ≤ t ^ (2 * β) := by
    have h1 : s ^ β ≤ (4 * t) ^ β := Real.rpow_le_rpow hs0 hsle hβ
    have h2 : (4 * t) ^ β = 4 ^ β * t ^ β := Real.mul_rpow (by norm_num) ht0'
    have h3 : 4 ^ β ≤ t ^ β := Real.rpow_le_rpow (by norm_num) ht hβ
    have h4 : t ^ β * t ^ β = t ^ (2 * β) := by
      rw [← Real.rpow_add ht0]
      congr 1
      ring
    calc s ^ β ≤ 4 ^ β * t ^ β := by rw [← h2]; exact h1
      _ ≤ t ^ β * t ^ β := mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg ht0' β)
      _ = t ^ (2 * β) := h4
  have hCt : C * s ^ β ≤ t * t ^ (2 * β) :=
    le_trans (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hs0 β))
      (mul_le_mul_of_nonneg_left hsβ ht0')
  have hfin : t * t ^ (2 * β) * t ^ (ν + 6) = t ^ (2 * β + ν + 7) := by
    have e1 : t * t ^ (2 * β) = t ^ ((1 : ℝ) + 2 * β) := by
      rw [Real.rpow_add ht0 (1 : ℝ) (2 * β), Real.rpow_one]
    have e2 : t ^ ((1 : ℝ) + 2 * β) * t ^ (ν + 6) = t ^ (((1 : ℝ) + 2 * β) + (ν + 6)) :=
      (Real.rpow_add ht0 _ _).symm
    have e3 : ((1 : ℝ) + 2 * β) + (ν + 6) = 2 * β + ν + 7 := by ring
    rw [e1, e2, e3]
  calc C * s ^ β * t ^ (ν + 6) = (C * s ^ β) * t ^ (ν + 6) := by ring
    _ ≤ (t * t ^ (2 * β)) * t ^ (ν + 6) :=
        mul_le_mul_of_nonneg_right hCt (Real.rpow_nonneg ht0' (ν + 6))
    _ = t ^ (2 * β + ν + 7) := hfin

/-- **The two-sided bound for the mode length.**  Both inequalities hold from `x ≥ exp 40000`
(then `log x ≥ 40000`, and `N > x^{1/4+η} > x^{1/4}` gives `log N > log x / 4 ≥ 10000`) and
`X ≤ (log N)^{nuU}`. -/
theorem modeLen_bounds : ∃ x0 : ℝ, ∀ (Pa : Work.FITop.Params) (X : ℕ),
    x0 ≤ (Pa.x : ℝ) → 1 ≤ X → (X : ℝ) ≤ (Real.log Pa.N) ^ Work.FITop4.nuU →
    Pa.θ⁻¹ * (X : ℝ) * (Real.log (Pa.N + 2)) ^ 6 ≤ (Work.FIArea7.modeLen Pa X : ℝ) ∧
    (Work.FIArea7.modeLen Pa X : ℝ) ≤ (Real.log Pa.N) ^ (2 * Pa.A' + Work.FITop4.nuU + 7) := by
  refine ⟨Real.exp 40000, ?_⟩
  intro Pa X hx hX hXb
  -- ### the parameters: `log x ≥ 40000`, `log x < 4 log N`, so `log N ≥ 10000`
  have hxpos : (0 : ℝ) < (Pa.x : ℝ) := lt_of_lt_of_le (Real.exp_pos 40000) hx
  have hs_ge : 40000 ≤ Real.log (Pa.x : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 40000) hx
    rwa [Real.log_exp] at h
  have hspos : 0 < Real.log (Pa.x : ℝ) := by linarith
  have hs1 : 1 ≤ Real.log (Pa.x : ℝ) := by linarith
  set t : ℝ := Real.log Pa.N with ht
  have ht_gt : (1 / 4) * Real.log (Pa.x : ℝ) < t := by
    have hlog_lt : Real.log ((Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η)) < Real.log Pa.N :=
      Real.log_lt_log (Real.rpow_pos_of_pos hxpos _) Pa.hNlo
    rw [Real.log_rpow hxpos] at hlog_lt
    have hlt : (1 / 4) * Real.log (Pa.x : ℝ) < ((1 : ℝ) / 4 + Pa.η) * Real.log (Pa.x : ℝ) := by
      nlinarith [Pa.hη, hspos]
    rw [ht]
    linarith
  have ht_ge : 10000 ≤ t := by linarith
  have ht4 : 4 ≤ t := by linarith
  have h8192 : 8192 ≤ t := by linarith
  have htpos : 0 < t := by linarith
  have hsle : Real.log (Pa.x : ℝ) ≤ 4 * t := by linarith
  have hNpos : 0 < Pa.N := by linarith [Pa.hN1]
  have hlog2 : Real.log 2 ≤ t := by
    have h1 : Real.log 2 ≤ 1 := le_of_lt (lt_trans Real.log_two_lt_d9 (by norm_num))
    linarith
  have hN2 : 2 ≤ Pa.N := by
    have hlog2' : Real.log 2 ≤ Real.log Pa.N := by rw [ht] at hlog2; exact hlog2
    exact (Real.log_le_log_iff (by norm_num : (0 : ℝ) < 2) hNpos).mp hlog2'
  have hA'0 : 0 ≤ Pa.A' := by
    have h2 : (0 : ℝ) < (2 : ℝ) ^ (20 : ℕ) := by norm_num
    linarith [Pa.hA', Pa.hA]
  -- ### `θ⁻¹ = (log x)^{A'}`, and the two `⌈·⌉` bounds
  have hθinv : Pa.θ⁻¹ = (Real.log (Pa.x : ℝ)) ^ Pa.A' := by
    rw [Pa.hθ, Real.rpow_neg hspos.le Pa.A', inv_inv]
  have hθinv_nn : 0 ≤ Pa.θ⁻¹ := by rw [hθinv]; positivity
  have hθinv1 : 1 ≤ Pa.θ⁻¹ := by
    rw [hθinv]
    exact Real.one_le_rpow hs1 hA'0
  have hcθ : (Nat.ceil Pa.θ⁻¹ : ℝ) ≤ 2 * Pa.θ⁻¹ := by
    have h := Nat.ceil_lt_add_one hθinv_nn
    linarith
  have hlog3 : 1 ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
    linarith [Real.exp_one_lt_three]
  have hlogN2ge1 : 1 ≤ Real.log (Pa.N + 2) := by
    have h3 : (3 : ℝ) ≤ Pa.N + 2 := by linarith [Pa.hN1]
    exact le_trans hlog3 (Real.log_le_log (by norm_num : (0 : ℝ) < 3) h3)
  have hclog : (Nat.ceil (Real.log (Pa.N + 2)) : ℝ) ≤ 2 * Real.log (Pa.N + 2) := by
    have h := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ Real.log (Pa.N + 2))
    linarith
  have hclog6 : (Nat.ceil (Real.log (Pa.N + 2)) : ℝ) ^ 6 ≤ (4 * t) ^ 6 := by
    have h2 : Real.log (Pa.N + 2) ≤ 2 * t := by
      have h := log_add_two_le_two_log hN2
      rw [ht]
      exact h
    have h3 : 2 * Real.log (Pa.N + 2) ≤ 4 * t := by linarith
    calc (Nat.ceil (Real.log (Pa.N + 2)) : ℝ) ^ 6 ≤ (2 * Real.log (Pa.N + 2)) ^ 6 :=
          pow_le_pow_left₀ (by positivity) hclog 6
      _ ≤ (4 * t) ^ 6 := pow_le_pow_left₀ (by positivity) h3 6
  -- ### `modeLen` as a real number
  have hmode : ((modeLen Pa X : ℕ) : ℝ)
      = (Nat.ceil Pa.θ⁻¹ : ℝ) * (X : ℝ) * (Nat.ceil (Real.log (Pa.N + 2)) : ℝ) ^ 6 := by
    rw [modeLen]
    push_cast
    ring
  -- ### the lower bound
  have hlow : Pa.θ⁻¹ * (X : ℝ) * (Real.log (Pa.N + 2)) ^ 6 ≤ (modeLen Pa X : ℝ) := by
    have h := ceil_mul_ceil_pow_le Pa.θ⁻¹ (Real.log (Pa.N + 2)) X 6 hθinv_nn (by linarith)
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow] at h
    rwa [hmode]
  -- ### the upper bound
  have hA_first : (Nat.ceil Pa.θ⁻¹ : ℝ) * (X : ℝ)
        * (Nat.ceil (Real.log (Pa.N + 2)) : ℝ) ^ 6
      ≤ (2 * Pa.θ⁻¹) * (X : ℝ) * (4 * t) ^ 6 := by
    have hX0 : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
    have hC0 : (0 : ℝ) ≤ (Nat.ceil (Real.log (Pa.N + 2)) : ℝ) ^ 6 := by positivity
    have h2θ : (0 : ℝ) ≤ 2 * Pa.θ⁻¹ := by linarith
    calc (Nat.ceil Pa.θ⁻¹ : ℝ) * (X : ℝ) * (Nat.ceil (Real.log (Pa.N + 2)) : ℝ) ^ 6
        ≤ (2 * Pa.θ⁻¹) * (X : ℝ) * (Nat.ceil (Real.log (Pa.N + 2)) : ℝ) ^ 6 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcθ hX0) hC0
      _ ≤ (2 * Pa.θ⁻¹) * (X : ℝ) * (4 * t) ^ 6 :=
          mul_le_mul_of_nonneg_left hclog6 (mul_nonneg h2θ hX0)
  have hkey : (2 * Pa.θ⁻¹) * (X : ℝ) * (4 * t) ^ 6
      = 8192 * (Real.log (Pa.x : ℝ)) ^ Pa.A' * (X : ℝ) * t ^ 6 := by
    have h4t6 : (4 * t) ^ 6 = 4096 * t ^ 6 := by ring
    rw [h4t6, hθinv]
    ring
  have hstep : 8192 * (Real.log (Pa.x : ℝ)) ^ Pa.A' * (X : ℝ) * t ^ 6
      ≤ 8192 * (Real.log (Pa.x : ℝ)) ^ Pa.A' * t ^ (Work.FITop4.nuU + 6) := by
    have h6 : t ^ 6 = t ^ (6 : ℝ) := (Real.rpow_natCast t 6).symm
    rw [h6]
    have hcomb : t ^ Work.FITop4.nuU * t ^ (6 : ℝ) = t ^ (Work.FITop4.nuU + 6) :=
      (Real.rpow_add htpos Work.FITop4.nuU (6 : ℝ)).symm
    have hX6 : (X : ℝ) * t ^ (6 : ℝ) ≤ t ^ Work.FITop4.nuU * t ^ (6 : ℝ) :=
      mul_le_mul_of_nonneg_right hXb (Real.rpow_nonneg htpos.le 6)
    calc 8192 * (Real.log (Pa.x : ℝ)) ^ Pa.A' * (X : ℝ) * t ^ (6 : ℝ)
        = (8192 * (Real.log (Pa.x : ℝ)) ^ Pa.A') * ((X : ℝ) * t ^ (6 : ℝ)) := by ring
      _ ≤ (8192 * (Real.log (Pa.x : ℝ)) ^ Pa.A') * (t ^ Work.FITop4.nuU * t ^ (6 : ℝ)) :=
          mul_le_mul_of_nonneg_left hX6 (by positivity)
      _ = (8192 * (Real.log (Pa.x : ℝ)) ^ Pa.A') * t ^ (Work.FITop4.nuU + 6) := by rw [hcomb]
      _ = 8192 * (Real.log (Pa.x : ℝ)) ^ Pa.A' * t ^ (Work.FITop4.nuU + 6) := by ring
  have hcore := rpow_polylog_core (C := 8192) (s := Real.log (Pa.x : ℝ)) (t := t)
    (β := Pa.A') (ν := Work.FITop4.nuU) (by norm_num) h8192 hs1 ht4 hsle hA'0 nuU_nonneg
  have hupp : (modeLen Pa X : ℝ) ≤ t ^ (2 * Pa.A' + Work.FITop4.nuU + 7) := by
    rw [hmode]
    calc (Nat.ceil Pa.θ⁻¹ : ℝ) * (X : ℝ) * (Nat.ceil (Real.log (Pa.N + 2)) : ℝ) ^ 6
        ≤ (2 * Pa.θ⁻¹) * (X : ℝ) * (4 * t) ^ 6 := hA_first
      _ = 8192 * (Real.log (Pa.x : ℝ)) ^ Pa.A' * (X : ℝ) * t ^ 6 := hkey
      _ ≤ 8192 * (Real.log (Pa.x : ℝ)) ^ Pa.A' * t ^ (Work.FITop4.nuU + 6) := hstep
      _ ≤ t ^ (2 * Pa.A' + Work.FITop4.nuU + 7) := hcore
  exact ⟨hlow, hupp⟩

end

end Work.FIArea7
