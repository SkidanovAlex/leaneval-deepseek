/-
# `Submission.Work.FIArea7.modeLen_log_le`

The polylogarithmic cap on the §17 mode length,

  `modeLen Pa X = ⌈θ⁻¹⌉ · X · ⌈log(N+2)⌉⁶`  (`Submission/Work/FIArea7/Bridge17Defs.lean`),

in the *only* regime in which the bridge consumes it: `x ≥ exp 40000`, `X ≤ (log N)^{nuU}`,
`Pa.τ = tauOf Pa.x Asave` and, crucially, `1 < θ²τX`.

The last hypothesis is what bounds `θ⁻¹`: `θ²τX > 1` gives `θ⁻¹ < (τX)^{1/2}`, and since
`τ = tauOf Pa.x Asave = (log x)^{201048576}` while `log x < 4 log N`, every factor becomes a
power of `L = log N`:

  `modeLen ≤ 2θ⁻¹ · X · (4L)⁶ ≤ 8192 · τ^{1/2} · X^{3/2} · L⁶
          ≤ 8192 · (log x)^{100524288} · L^{3ν/2} · L⁶
          ≤ L^{201048576 + 3ν/2 + 7}`,

and `201048576 + 3·nuU/2 + 7 = 4719922997.5 < 5·10⁹`.  The two real-arithmetic inputs are the
standalone lemma `modeLen_rpow_arith` (`Submission/Work/FIArea7/modeLen_rpow_arith.lean`) and the
`⌈·⌉`-bound `modeLen_struct_le` below.

NOTES.md §61 and AREA7_ROUTE_LEAD.md record the route.
-/
import Mathlib
import Submission.Work.FIArea7.Bridge17Defs
import Submission.Work.FIArea7.modeLen_bounds
import Submission.Work.FIArea7.modeLen_rpow_arith

set_option autoImplicit false

namespace Work.FIArea7

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- **The structural bound for the mode length.**  `⌈θ⁻¹⌉ ≤ 2θ⁻¹` and, with `log(N+2) ≥ 1` and
`log(N+2) ≤ 2 log N`, also `⌈log(N+2)⌉⁶ ≤ (4 log N)⁶`.  Hence
`modeLen Pa X ≤ 8192 · θ⁻¹ · X · (log N)⁶`. -/
theorem modeLen_struct_le (Pa : Work.FITop.Params) (X : ℕ)
    (hθinv1 : 1 ≤ Pa.θ⁻¹) (hlogN2ge1 : 1 ≤ Real.log (Pa.N + 2))
    (hlogN2le : Real.log (Pa.N + 2) ≤ 2 * Real.log Pa.N) :
    (Work.FIArea7.modeLen Pa X : ℝ) ≤ 8192 * Pa.θ⁻¹ * (X : ℝ) * (Real.log Pa.N) ^ 6 := by
  have hcθ : (Nat.ceil Pa.θ⁻¹ : ℝ) ≤ 2 * Pa.θ⁻¹ := by
    have h := Nat.ceil_lt_add_one (le_trans zero_le_one hθinv1)
    linarith
  have hlogN2nn : 0 ≤ Real.log (Pa.N + 2) := le_trans zero_le_one hlogN2ge1
  have hclog : (Nat.ceil (Real.log (Pa.N + 2)) : ℝ) ≤ 2 * Real.log (Pa.N + 2) := by
    have h := Nat.ceil_lt_add_one hlogN2nn
    linarith
  have hlogN2le' : 2 * Real.log (Pa.N + 2) ≤ 4 * Real.log Pa.N := by linarith
  have hclog6 : (Nat.ceil (Real.log (Pa.N + 2)) : ℝ) ^ 6 ≤ (4 * Real.log Pa.N) ^ 6 :=
    le_trans (pow_le_pow_left₀ (by positivity) hclog 6)
      (pow_le_pow_left₀ (by linarith) hlogN2le' 6)
  have hmode : ((Work.FIArea7.modeLen Pa X : ℕ) : ℝ)
      = (Nat.ceil Pa.θ⁻¹ : ℝ) * (X : ℝ) * (Nat.ceil (Real.log (Pa.N + 2)) : ℝ) ^ 6 := by
    rw [Work.FIArea7.modeLen]; push_cast; ring
  rw [hmode]
  calc (Nat.ceil Pa.θ⁻¹ : ℝ) * (X : ℝ) * (Nat.ceil (Real.log (Pa.N + 2)) : ℝ) ^ 6
      ≤ (2 * Pa.θ⁻¹) * (X : ℝ) * (4 * Real.log Pa.N) ^ 6 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hcθ (Nat.cast_nonneg X)) hclog6
          (by positivity) (by positivity)
    _ = 8192 * Pa.θ⁻¹ * (X : ℝ) * (Real.log Pa.N) ^ 6 := by ring

theorem modeLen_log_le : ∃ x0 : ℝ, ∀ (Pa : Work.FITop.Params) (X : ℕ),
    x0 ≤ (Pa.x : ℝ) → 1 ≤ X → (X : ℝ) ≤ (Real.log Pa.N) ^ Work.FITop4.nuU →
    Pa.τ = Work.FITop4.tauOf Pa.x Work.FITop4.Asave → 1 < Pa.θ ^ 2 * Pa.τ * X →
    (Work.FIArea7.modeLen Pa X : ℝ) ≤ (Real.log Pa.N) ^ (5 * 10 ^ 9 : ℝ) := by
  refine ⟨Real.exp 40000, ?_⟩
  intro Pa X hx hX hXb hτ hθτ
  have hxpos : (0 : ℝ) < (Pa.x : ℝ) := lt_of_lt_of_le (Real.exp_pos 40000) hx
  have hx1 : (1 : ℝ) ≤ (Pa.x : ℝ) := by
    have h1 : (1 : ℝ) ≤ Real.exp 40000 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by norm_num)
    linarith
  set s : ℝ := Real.log (Pa.x : ℝ) with hs
  set L : ℝ := Real.log Pa.N with hLd
  have hs_ge : 40000 ≤ s := by
    have h := Real.log_le_log (Real.exp_pos 40000) hx
    rw [Real.log_exp] at h
    rwa [hs]
  have hs1 : 1 ≤ s := by linarith
  have hspos : 0 < s := by linarith
  have hL_gt : (1/4) * s < L := by
    have hlog_lt : Real.log ((Pa.x : ℝ) ^ ((1:ℝ)/4 + Pa.η)) < Real.log Pa.N :=
      Real.log_lt_log (Real.rpow_pos_of_pos hxpos _) Pa.hNlo
    rw [Real.log_rpow hxpos] at hlog_lt
    have hlt : (1/4) * s < ((1:ℝ)/4 + Pa.η) * s := by nlinarith [Pa.hη, hspos]
    rw [← hs] at hlog_lt
    rw [hLd]
    linarith
  have hL_ge : 8192 ≤ L := by linarith
  have hL4 : 4 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hsle : s ≤ 4 * L := by linarith
  -- N >= 2
  have hexp10000 : Real.exp 10000 ≤ (Pa.x : ℝ) ^ ((1:ℝ)/4 + Pa.η) := by
    have h1 : (Pa.x : ℝ) ^ ((1:ℝ)/4) ≤ (Pa.x : ℝ) ^ ((1:ℝ)/4 + Pa.η) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [Pa.hη])
    have h2 : (Real.exp 40000 : ℝ) ^ ((1:ℝ)/4) ≤ (Pa.x : ℝ) ^ ((1:ℝ)/4) :=
      Real.rpow_le_rpow (Real.exp_pos 40000).le hx (by norm_num)
    have h3 : (Real.exp 40000 : ℝ) ^ ((1:ℝ)/4) = Real.exp 10000 := by
      rw [← Real.exp_mul]; norm_num
    linarith [h1, h2, h3]
  have hN2 : 2 ≤ Pa.N := by
    have h4 : (Real.exp 1 : ℝ) ≤ Real.exp 10000 := Real.exp_le_exp.mpr (by norm_num)
    have h5 : (2:ℝ) < Real.exp 1 := Real.exp_one_gt_two
    linarith [Pa.hNlo, hexp10000, h4, h5]
  have hlog3 : 1 ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 3)]
    linarith [Real.exp_one_lt_three]
  have hlogN2ge1 : 1 ≤ Real.log (Pa.N + 2) :=
    le_trans hlog3 (Real.log_le_log (by norm_num : (0:ℝ) < 3) (by linarith [Pa.hN1]))
  have hlogN2le : Real.log (Pa.N + 2) ≤ 2 * L := by
    have h := log_add_two_le_two_log hN2
    rw [hLd]
    exact h
  -- A' positivity, theta inverse
  have hA'pos : 0 < Pa.A' := by
    have h2 : (0:ℝ) < (2:ℝ)^(20:ℕ) := by norm_num
    linarith [Pa.hA, Pa.hA']
  have hθinv_eq : Pa.θ⁻¹ = s ^ Pa.A' := by
    have hθeq : Pa.θ = s ^ (-Pa.A') := by rw [hs]; exact Pa.hθ
    rw [hθeq, Real.rpow_neg hspos.le, inv_inv]
  have hθinv1 : 1 ≤ Pa.θ⁻¹ := by
    rw [hθinv_eq]
    exact Real.one_le_rpow hs1 hA'pos.le
  -- theta^{-1} <= sqrt(tau X)
  have hθ2pos : (0:ℝ) < Pa.θ ^ 2 := pow_pos Pa.hθ0 2
  have hprod : (0:ℝ) < Pa.θ ^ 2 * (Pa.τ * (X:ℝ)) := by nlinarith [hθτ]
  have hτXpos : (0:ℝ) < Pa.τ * (X:ℝ) := pos_of_mul_pos_right hprod hθ2pos.le
  have hτnn : (0:ℝ) ≤ Pa.τ := (pos_of_mul_pos_left hτXpos (Nat.cast_nonneg X)).le
  have hθinv_le : Pa.θ⁻¹ ≤ (Pa.τ * (X:ℝ)) ^ (1/2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, Real.le_sqrt (by positivity : (0:ℝ) ≤ Pa.θ⁻¹) hτXpos.le]
    rw [inv_pow, inv_le_iff_one_le_mul₀ hθ2pos]
    nlinarith [hθτ]
  -- tau value
  have hτs : Pa.τ = s ^ (201048576 : ℝ) := by
    have h1 : Work.FITop4.tauOf Pa.x Work.FITop4.Asave = (Real.log (Pa.x:ℝ)) ^ (201048576:ℝ) := by
      unfold Work.FITop4.tauOf Work.FITop4.Asave
      norm_num
    rw [hτ, h1, ← hs]
  -- step: theta^{-1} X <= s^c L^{nuU*3/2}
  have hτ12 : Pa.τ ^ (1/2:ℝ) = s ^ (100524288:ℝ) := by
    rw [hτs, ← Real.rpow_mul hspos.le (201048576:ℝ) (1/2)]
    norm_num
  have hX32 : (X:ℝ)^((3:ℝ)/2) ≤ L ^ (Work.FITop4.nuU * (3/2)) := by
    have h1 : (X:ℝ)^((3:ℝ)/2) ≤ ((Real.log Pa.N) ^ Work.FITop4.nuU) ^ ((3:ℝ)/2) :=
      Real.rpow_le_rpow (Nat.cast_nonneg X) hXb (by norm_num)
    have h2 : ((Real.log Pa.N) ^ Work.FITop4.nuU) ^ ((3:ℝ)/2) = L ^ (Work.FITop4.nuU * (3/2)) := by
      rw [← hLd, Real.rpow_mul (by positivity : (0:ℝ) ≤ Real.log Pa.N)]
    linarith [h1, h2]
  have hXpos : (0:ℝ) < (X:ℝ) := by exact_mod_cast hX
  have hθX : Pa.θ⁻¹ * (X:ℝ) ≤ Pa.τ ^ (1/2:ℝ) * (X:ℝ)^((3:ℝ)/2) := by
    have h1 : Pa.θ⁻¹ * (X:ℝ) ≤ (Pa.τ * (X:ℝ))^(1/2:ℝ) * (X:ℝ) :=
      mul_le_mul_of_nonneg_right hθinv_le (Nat.cast_nonneg X)
    have h2 : (Pa.τ * (X:ℝ))^(1/2:ℝ) * (X:ℝ) = Pa.τ^(1/2:ℝ) * (X:ℝ)^((3:ℝ)/2) := by
      rw [Real.mul_rpow hτnn (Nat.cast_nonneg X)]
      have hX32' : (X:ℝ)^(1/2:ℝ) * (X:ℝ) = (X:ℝ)^((3:ℝ)/2) := by
        calc (X:ℝ)^(1/2:ℝ) * (X:ℝ) = (X:ℝ)^(1/2:ℝ) * (X:ℝ)^(1:ℝ) := by rw [Real.rpow_one]
          _ = (X:ℝ)^((1:ℝ)/2 + 1) := (Real.rpow_add hXpos (1/2) 1).symm
          _ = (X:ℝ)^((3:ℝ)/2) := by congr 1; norm_num
      rw [mul_assoc, hX32']
    linarith [h1, h2]
  have hstep1 : Pa.θ⁻¹ * (X:ℝ) ≤ s ^ (100524288:ℝ) * L ^ (Work.FITop4.nuU * (3/2)) := by
    calc Pa.θ⁻¹ * (X:ℝ) ≤ Pa.τ ^ (1/2:ℝ) * (X:ℝ)^((3:ℝ)/2) := hθX
      _ = s ^ (100524288:ℝ) * (X:ℝ)^((3:ℝ)/2) := by rw [hτ12]
      _ ≤ s ^ (100524288:ℝ) * L ^ (Work.FITop4.nuU * (3/2)) :=
          mul_le_mul_of_nonneg_left hX32 (Real.rpow_nonneg hspos.le _)
  -- modeLen structural bound
  have hmode : (Work.FIArea7.modeLen Pa X : ℝ) ≤ 8192 * Pa.θ⁻¹ * (X:ℝ) * L ^ 6 := by
    rw [hLd]
    exact modeLen_struct_le Pa X hθinv1 hlogN2ge1 hlogN2le
  have hmain : (Work.FIArea7.modeLen Pa X : ℝ)
      ≤ 8192 * (s ^ (100524288:ℝ) * L ^ (Work.FITop4.nuU * (3/2))) * L ^ 6 := by
    calc (Work.FIArea7.modeLen Pa X : ℝ) ≤ 8192 * Pa.θ⁻¹ * (X:ℝ) * L ^ 6 := hmode
      _ = 8192 * (Pa.θ⁻¹ * (X:ℝ)) * L ^ 6 := by ring
      _ ≤ 8192 * (s ^ (100524288:ℝ) * L ^ (Work.FITop4.nuU * (3/2))) * L ^ 6 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep1 (by norm_num))
            (pow_nonneg hLpos.le 6)
  have hL6 : L ^ (6:ℝ) = L ^ (6:ℕ) := Real.rpow_ofNat L 6
  exact le_trans hmain (hL6 ▸ modeLen_rpow_arith hs1 hL4 hL_ge hsle)

end

end Work.FIArea7
