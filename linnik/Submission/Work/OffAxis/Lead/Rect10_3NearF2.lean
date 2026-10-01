import Mathlib
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.OffAxis.Rect10_3EndgameClean
import Submission.Work.ZeroFreeTables.OffAxis.HB10_3Engine
import Submission.Work.ZeroFreeTables.OffAxis.TF72Calc
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Work.OffAxis.HB10_3EngineNear
import Submission.Work.OffAxis.tf72FcOneNum

open DirichletCharacter Complex
open scoped Classical BigOperators Interval

namespace Work.OffAxis.Lead

open Work.ZeroFreeTables

/-! ## The moment step of the `F`-method endgame (HB §10, pp. 60–61)

From (10.7) with a slack `s` — `F(-6/7) - F(-λ₁) ≤ 2(F 0 - F(6/7-λ₁)) + s` — and the two
moments of Lemma 7.2's test function at `λ = 6/7`, `∫₀^{7/3} t f = 8/15` and
`∫₀^{7/3} t e^{(6/7)t} f = 56/45`, one gets
`d·((56/45)e^{-7d/3} - 16/15) ≤ s` for `d = 6/7 - λ₁`.  Since that function of `d` is
`≥ d/13` for `d ≤ 1/30` and `≥ 1/15000` on `[1/30, 57/875]`, while the numerical falsity of
(10.7) on `λ₁ ≤ 792/1000` (margin `83/9000`, `tf72f_refute_quant`) forces `d ≤ 57/875`, a small
slack forces `d ≤ 13s`, i.e. `λ₁ ≥ 6/7 - 13s`. -/

/-- `∫₀^{x₀} t f(t)dt = 8/15` (HB's `|F'(0)| = 16/(35λ)` at `λ = 6/7`). -/
theorem int_mul_f (T : TestFn) (hx₀ : T.x₀ = 7/3) (hf : T.f = tf72f (6/7)) :
    (∫ t in (0:ℝ)..T.x₀, t * T.f t) = 8/15 := by
  have h := (Work.ZeroFreeTables.OffAxis.TF72Calc (6/7) (by norm_num)).1
  rw [show (2:ℝ)/(6/7) = 7/3 by norm_num] at h
  rw [hx₀, hf, h]
  norm_num

/-- `∫₀^{x₀} t e^{(6/7)t} f(t)dt = 56/45` (HB's `∫ x e^{λx}f = 16/(15λ)` at `λ = 6/7`). -/
theorem int_mul_exp_f (T : TestFn) (hx₀ : T.x₀ = 7/3) (hf : T.f = tf72f (6/7)) :
    (∫ t in (0:ℝ)..T.x₀, t * Real.exp ((6/7)*t) * T.f t) = 56/45 := by
  have h := (Work.ZeroFreeTables.OffAxis.TF72Calc (6/7) (by norm_num)).2.1
  rw [show (2:ℝ)/(6/7) = 7/3 by norm_num] at h
  rw [hx₀, hf, h]
  norm_num

/-- The comparison function `φ(d) = d((56/45)e^{-7d/3} - 16/15)` of the moment step. -/
noncomputable def phiF (d : ℝ) : ℝ := d * (Real.exp (-(7*d/3)) * (56/45) - 16/15)

/-- Alternating-series lower bound: `e^{-u} ≥ 1 - u + u²/2 - u³/6 - u⁴·(5/96)` for `0 ≤ u ≤ 1`. -/
theorem exp_neg_lower {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.exp (-u) ≥ 1 - u + u^2/2 - u^3/6 - u^4 * (5/96) := by
  have hu1' : |(-u : ℝ)| ≤ 1 := by rw [abs_neg, abs_of_nonneg hu0]; exact hu1
  have hb := Real.exp_bound (x := -u) hu1' (n := 4) (by norm_num)
  have hsum : (∑ m ∈ Finset.range 4, (-u)^m / (m.factorial : ℝ))
      = 1 - u + u^2/2 - u^3/6 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
    ring
  rw [hsum] at hb
  have h1 : |(-u : ℝ)| = u := by rw [abs_neg, abs_of_nonneg hu0]
  rw [h1] at hb
  have hpow : (↑(Nat.succ 4) / (↑(Nat.factorial 4) * ↑(4:ℕ)) : ℝ) = 5/96 := by
    norm_num
  rw [hpow] at hb
  linarith [(abs_le.mp hb).1]

/-- `φ(d) ≥ 1/15000` on `[1/30, 57/875]`. -/
theorem phiF_ge_const {d : ℝ} (hd1 : 1/30 ≤ d) (hd2 : d ≤ 57/875) : (1/15000 : ℝ) ≤ phiF d := by
  have hd0 : (0:ℝ) < d := by linarith
  have hu0 : 0 ≤ 7*d/3 := by linarith
  have hu1 : 7*d/3 ≤ 1 := by linarith
  have hexp := exp_neg_lower hu0 hu1
  -- the cubic lower bound is maximal at `u = 399/2625`
  have hcub : (1 : ℝ) - 7*d/3 + (7*d/3)^2/2 - (7*d/3)^3/6 ≥
      1 - 399/2625 + (399/2625)^2/2 - (399/2625)^3/6 := by
    have hfac : (1 - 7*d/3 + (7*d/3)^2/2 - (7*d/3)^3/6)
        - (1 - 399/2625 + (399/2625)^2/2 - (399/2625)^3/6)
        = (399/2625 - 7*d/3) * (1 - (7*d/3 + 399/2625)/2 + ((7*d/3)^2 + (7*d/3)*(399/2625) + (399/2625)^2)/6) := by
      ring
    have hpos : 0 ≤ 399/2625 - 7*d/3 := by linarith
    have hbr : 0 ≤ 1 - (7*d/3 + 399/2625)/2 + ((7*d/3)^2 + (7*d/3)*(399/2625) + (399/2625)^2)/6 := by
      have h1 : 7*d/3 + 399/2625 ≤ 2 := by linarith
      have h2 : 0 ≤ ((7*d/3)^2 + (7*d/3)*(399/2625) + (399/2625)^2)/6 := by positivity
      linarith
    nlinarith [hfac, hpos, hbr]
  have hpow4 : (7*d/3)^4 ≤ (399/2625)^4 := by
    have h : 0 ≤ 7*d/3 := hu0
    exact pow_le_pow_left₀ h (by linarith) 4
  have hexp2 : Real.exp (-(7*d/3)) ≥ 8/10 := by
    have h1 : (1 : ℝ) - 7*d/3 + (7*d/3)^2/2 - (7*d/3)^3/6
        - (7*d/3)^4 * (5/96) ≥ 8/10 := by
      have h5 : (7*d/3)^4 * (5/96) ≤ (399/2625)^4 * (5/96) :=
        mul_le_mul_of_nonneg_right hpow4 (by norm_num)
      nlinarith [hcub, h5]
    linarith
  have hkey : Real.exp (-(7*d/3)) * (56/45) - 16/15 ≥ 1/500 := by
    nlinarith [hexp2]
  unfold phiF
  nlinarith [hkey, hd1, hd0]

/-- `φ(d) ≥ d/13` for `0 ≤ d ≤ 1/30`. -/
theorem phiF_ge_div13 {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 1/30) : d/13 ≤ phiF d := by
  have hexp : Real.exp (-(7*d/3)) ≥ 1 - 7*d/3 := by
    have := Real.add_one_le_exp (-(7*d/3)); linarith
  have hbr : Real.exp (-(7*d/3)) * (56/45) - 16/15 ≥ 8/45 - (392/135)*d := by
    have h : (1 - 7*d/3) * (56/45) - 16/15 = 8/45 - (392/135)*d := by ring
    nlinarith [hexp]
  have hq : d * (8/45 - (392/135)*d) ≥ d/13 := by nlinarith [hd0, hd]
  unfold phiF
  nlinarith [hbr, hd0]

/-- **The moment step of the `F`-method endgame.**  From (10.7) with slack `s ≤ 1/20000` and
`s ≤ ε/40` one concludes `λ₁ ≤ 792/1000` or `λ₁ ≥ 6/7 - ε/2`. -/
theorem hmom_step (T : TestFn) (hx₀ : T.x₀ = 7/3) (hf : T.f = tf72f (6/7)) {ε s l : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1/20000) (hs2 : s ≤ ε/40)
    (hl0 : 0 ≤ l) (hl67 : l < 6/7)
    (h107 : T.F (-(6/7)) - T.F (-l) ≤ 2 * (T.F 0 - T.F (6/7 - l)) + s) :
    l ≤ 792/1000 ∨ 6/7 - ε/2 ≤ l := by
  have hint : ∀ c : ℝ, IntervalIntegrable
      (fun t : ℝ => Real.exp (-(c*t)) * T.f t) MeasureTheory.volume (0:ℝ) T.x₀ := by
    intro c
    refine ContinuousOn.intervalIntegrable_of_Icc (le_of_lt T.x₀_pos) ?_
    exact ((Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)).continuousOn).mul
      (T.f_cont.mono (fun t ht => ht.1))
  have hint2 : ∀ c : ℝ, IntervalIntegrable
      (fun t : ℝ => Real.exp (c*t) * T.f t) MeasureTheory.volume (0:ℝ) T.x₀ := by
    intro c
    refine ContinuousOn.intervalIntegrable_of_Icc (le_of_lt T.x₀_pos) ?_
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
      (T.f_cont.mono (fun t ht => ht.1))
  have hintF : IntervalIntegrable (fun t : ℝ => T.f t) MeasureTheory.volume (0:ℝ) T.x₀ :=
    ContinuousOn.intervalIntegrable_of_Icc (le_of_lt T.x₀_pos)
      (T.f_cont.mono (fun t ht => ht.1))
  by_cases hcase : l ≤ 792/1000
  · exact Or.inl hcase
  · right
    push_neg at hcase
    set d : ℝ := 6/7 - l with hd
    have hd0 : 0 < d := by rw [hd]; linarith
    have hdle : d ≤ 57/875 := by rw [hd]; norm_num at hcase ⊢; linarith
    have hld : l = 6/7 - d := by rw [hd]; ring
    -- ## (A)  `2(F 0 - F d) ≤ 16 d/15`
    have hA : 2 * (T.F 0 - T.F d) ≤ 16 * d / 15 := by
      have h0 : T.F 0 = ∫ t in (0:ℝ)..T.x₀, T.f t := by
        rw [TestFn_F_eq_integral T 0]
        exact intervalIntegral.integral_congr (fun t _ => by simp)
      have hdF : T.F d = ∫ t in (0:ℝ)..T.x₀, Real.exp (-(d*t)) * T.f t :=
        TestFn_F_eq_integral T d
      have hsub : T.F 0 - T.F d
          = ∫ t in (0:ℝ)..T.x₀, (1 - Real.exp (-(d*t))) * T.f t := by
        rw [h0, hdF, ← intervalIntegral.integral_sub hintF (hint d)]
        exact intervalIntegral.integral_congr (fun t _ => by ring)
      rw [hsub]
      have hleft : IntervalIntegrable
          (fun t : ℝ => (1 - Real.exp (-(d*t))) * T.f t) MeasureTheory.volume (0:ℝ) T.x₀ := by
        refine ContinuousOn.intervalIntegrable_of_Icc (le_of_lt T.x₀_pos) ?_
        exact ((continuous_const.sub
          (Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg))).continuousOn).mul
          (T.f_cont.mono (fun t ht => ht.1))
      have hright : IntervalIntegrable
          (fun t : ℝ => d * (t * T.f t)) MeasureTheory.volume (0:ℝ) T.x₀ := by
        refine ContinuousOn.intervalIntegrable_of_Icc (le_of_lt T.x₀_pos) ?_
        exact continuousOn_const.mul (continuousOn_id.mul
          (T.f_cont.mono (fun t ht => ht.1)))
      have hmono : (∫ t in (0:ℝ)..T.x₀, (1 - Real.exp (-(d*t))) * T.f t)
          ≤ ∫ t in (0:ℝ)..T.x₀, d * (t * T.f t) := by
        refine intervalIntegral.integral_mono_on (le_of_lt T.x₀_pos) hleft hright ?_
        intro t ht
        have ht0 : 0 ≤ t := ht.1
        have hexp : Real.exp (-(d*t)) ≥ 1 - d*t := by
          have := Real.add_one_le_exp (-(d*t)); linarith
        have hle : 1 - Real.exp (-(d*t)) ≤ d*t := by linarith
        have hfnn : 0 ≤ T.f t := T.f_nonneg t
        nlinarith [hle, hfnn, ht0, hd0]
      have hconst : (∫ t in (0:ℝ)..T.x₀, d * (t * T.f t)) = d * (8/15) := by
        rw [intervalIntegral.integral_const_mul, int_mul_f T hx₀ hf]
      linarith [hmono, hconst]
    -- ## (B)  `d e^{-7d/3} (56/45) ≤ F(-6/7) - F(-l)`
    have hB : d * Real.exp (-(7*d/3)) * (56/45) ≤ T.F (-(6/7)) - T.F (-l) := by
      have h67 : T.F (-(6/7)) = ∫ t in (0:ℝ)..T.x₀, Real.exp ((6/7)*t) * T.f t := by
        rw [TestFn_F_eq_integral T (-(6/7))]
        exact intervalIntegral.integral_congr (fun t _ => by
          congr 1
          ring)
      have hlF : T.F (-l) = ∫ t in (0:ℝ)..T.x₀, Real.exp (l*t) * T.f t := by
        rw [TestFn_F_eq_integral T (-l)]
        exact intervalIntegral.integral_congr (fun t _ => by
          congr 1
          ring)
      have hsub : T.F (-(6/7)) - T.F (-l)
          = ∫ t in (0:ℝ)..T.x₀, (Real.exp ((6/7)*t) - Real.exp (l*t)) * T.f t := by
        rw [h67, hlF, ← intervalIntegral.integral_sub (hint2 (6/7)) (hint2 l)]
        exact intervalIntegral.integral_congr (fun t _ => by ring)
      rw [hsub]
      have hleft : IntervalIntegrable
          (fun t : ℝ => d * Real.exp (-(7*d/3)) * (t * (Real.exp ((6/7)*t) * T.f t)))
          MeasureTheory.volume (0:ℝ) T.x₀ := by
        refine ContinuousOn.intervalIntegrable_of_Icc (le_of_lt T.x₀_pos) ?_
        exact continuousOn_const.mul (continuousOn_id.mul
          (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
            (T.f_cont.mono (fun t ht => ht.1))))
      have hright : IntervalIntegrable
          (fun t : ℝ => (Real.exp ((6/7)*t) - Real.exp (l*t)) * T.f t)
          MeasureTheory.volume (0:ℝ) T.x₀ := by
        refine ContinuousOn.intervalIntegrable_of_Icc (le_of_lt T.x₀_pos) ?_
        exact ((((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).sub
          ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn)).mul
            (T.f_cont.mono (fun t ht => ht.1)))
      have hmono : (∫ t in (0:ℝ)..T.x₀,
            d * Real.exp (-(7*d/3)) * (t * (Real.exp ((6/7)*t) * T.f t)))
          ≤ ∫ t in (0:ℝ)..T.x₀, (Real.exp ((6/7)*t) - Real.exp (l*t)) * T.f t := by
        refine intervalIntegral.integral_mono_on (le_of_lt T.x₀_pos) hleft hright ?_
        intro t ht
        have ht0 : 0 ≤ t := ht.1
        have htx : t ≤ 7/3 := by rw [← hx₀]; exact ht.2
        have hfnn : 0 ≤ T.f t := T.f_nonneg t
        have he : (0:ℝ) < Real.exp ((6/7)*t) := Real.exp_pos _
        have h1 : Real.exp (l*t) = Real.exp ((6/7)*t) * Real.exp (-(d*t)) := by
          rw [← Real.exp_add]
          congr 1
          rw [hld]
          ring
        have h2 : d*t*Real.exp (-(d*t)) ≤ 1 - Real.exp (-(d*t)) := by
          have h := Real.add_one_le_exp (d*t)
          have hone : Real.exp (d*t) * Real.exp (-(d*t)) = 1 := by
            rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
          have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos (-(d*t))).le
          rw [hone] at hmul
          nlinarith [hmul]
        have h3 : Real.exp (-(7*d/3)) ≤ Real.exp (-(d*t)) := by
          apply Real.exp_le_exp.mpr
          nlinarith [htx, hd0]
        have hdt : 0 ≤ d*t := mul_nonneg hd0.le ht0
        have step1 : Real.exp ((6/7)*t) * (d*t*Real.exp (-(7*d/3))) * T.f t
            ≤ Real.exp ((6/7)*t) * (d*t*Real.exp (-(d*t))) * T.f t := by
          have h3' : d*t*Real.exp (-(7*d/3)) ≤ d*t*Real.exp (-(d*t)) :=
            mul_le_mul_of_nonneg_left h3 hdt
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3' he.le) hfnn
        have step2 : Real.exp ((6/7)*t) * (d*t*Real.exp (-(d*t))) * T.f t
            ≤ Real.exp ((6/7)*t) * (1 - Real.exp (-(d*t))) * T.f t :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 he.le) hfnn
        calc d * Real.exp (-(7*d/3)) * (t * (Real.exp ((6/7)*t) * T.f t))
            = Real.exp ((6/7)*t) * (d*t*Real.exp (-(7*d/3))) * T.f t := by ring
          _ ≤ Real.exp ((6/7)*t) * (d*t*Real.exp (-(d*t))) * T.f t := step1
          _ ≤ Real.exp ((6/7)*t) * (1 - Real.exp (-(d*t))) * T.f t := step2
          _ = (Real.exp ((6/7)*t) - Real.exp (l*t)) * T.f t := by rw [h1]; ring
      have hconst : (∫ t in (0:ℝ)..T.x₀,
            d * Real.exp (-(7*d/3)) * (t * (Real.exp ((6/7)*t) * T.f t)))
          = d * Real.exp (-(7*d/3)) * (56/45) := by
        rw [show (fun t : ℝ => d * Real.exp (-(7*d/3)) * (t * (Real.exp ((6/7)*t) * T.f t)))
              = (fun t : ℝ => (d * Real.exp (-(7*d/3))) * (t * Real.exp ((6/7)*t) * T.f t))
            from by funext t; ring]
        rw [intervalIntegral.integral_const_mul, int_mul_exp_f T hx₀ hf]
      linarith [hmono, hconst]
    -- ## (C)  the comparison function at `d` is at most the slack
    have hC : phiF d ≤ s := by
      unfold phiF
      linarith [h107, hA, hB]
    by_cases hd1 : 1/30 ≤ d
    · exfalso
      have hge := phiF_ge_const hd1 hdle
      linarith [hge, hC, hs1]
    · push_neg at hd1
      have hge := phiF_ge_div13 hd0.le hd1.le
      have hds : d ≤ 13 * s := by linarith [hge, hC]
      have h13 : 13 * s ≤ ε/2 := by linarith [hs2]
      rw [hld]
      linarith [hds, h13]

/-! ## `λ ≥ 0` at a zero -/

/-- `λ(ρ) ≥ 0` for a zero of a non-principal character (the zero lies in the critical strip). -/
theorem lamOf_nonneg_of_zeroMult {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (hzm : Work.LinnikContract.zeroMult χ ρ ≠ 0) : 0 ≤ Work.LinnikContract.lamOf q ρ := by
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast NeZero.one_le)
  rw [Work.LinnikContract.lamOf]
  refine mul_nonneg ?_ hlog
  have := Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ hzm
  linarith

/-! ## The numerics of (10.8)/(10.9) for the test function `tf72T (6/7)` -/

/-- **The transfer of the scale-free numerics to `tf72T (6/7)`.**  The hypothesis is the two
conjuncts of `OffAxis/tf72FcOneNum` in the self-similar normalisation `λ = 1`; the scaling
identity `tf72Fc_scale` turns them into the two numeric hypotheses of the engine for
`T = tf72T (6/7)`: the point `-a + iμ` of `tf72Fc (6/7)` is the point
`-(a·7/6) + i(μ·7/6)` of `tf72Fc 1`, and `(tf72T (6/7)).f 0 / 6 = 16/105 ≥ 1/10`, so the
constants `1/100`, `1/10` more than suffice. -/
theorem num_transfer
    (hnum : (∀ a μ : ℝ, 0 ≤ a → a ≤ 17/16 → |μ| ≤ 5 →
        (tf72Fc 1 (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re
          - 2 * (tf72Fc 1 ((μ : ℂ) * Complex.I)).re ≤ 1/100)
      ∧ (∀ a μ : ℝ, 0 ≤ a → a ≤ 17/16 → 4 ≤ |μ| →
        (tf72Fc 1 (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re ≤ 1/10)) :
    (∀ a μ : ℝ, 0 ≤ a → a ≤ 6/7 → |μ| ≤ 4 →
        ((tf72T (6/7) (by norm_num)).Fc (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re
          - 2 * ((tf72T (6/7) (by norm_num)).Fc ((μ : ℂ) * Complex.I)).re
            ≤ (tf72T (6/7) (by norm_num)).f 0 / 6)
    ∧ (∀ a μ : ℝ, 0 ≤ a → a ≤ 6/7 → 4 ≤ |μ| →
        ((tf72T (6/7) (by norm_num)).Fc (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re
          ≤ (tf72T (6/7) (by norm_num)).f 0 / 6) := by
  have h67 : (0:ℝ) < 6/7 := by norm_num
  have hlam : (((6:ℝ)/7 : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    norm_num
  have hf0 : (tf72T (6/7) h67).f 0 = 32/35 := by
    change tf72f (6/7) 0 = 32/35
    rw [tf72f_at_zero (6/7) (by norm_num)]
    norm_num
  have hpoint : ∀ a μ : ℝ,
      (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I) / (((6:ℝ)/7 : ℝ) : ℂ)
        = (((-(a * (7/6)) : ℝ)) : ℂ) + ((μ * (7/6) : ℝ) : ℂ) * Complex.I := by
    intro a μ
    field_simp
    push_cast
    ring
  have hpoint2 : ∀ μ : ℝ, ((μ : ℂ) * Complex.I) / (((6:ℝ)/7 : ℝ) : ℂ)
      = (((μ * (7/6) : ℝ)) : ℂ) * Complex.I := by
    intro μ
    field_simp
    push_cast
    ring
  constructor
  · intro a μ ha0 ha hmu
    have h1 : a * (7/6) ≤ 17/16 := by linarith
    have h2 : 0 ≤ a * (7/6) := by linarith
    have h3 : |μ * (7/6)| ≤ 5 := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 7/6)]
      nlinarith [abs_nonneg μ]
    have h4 := hnum.1 (a * (7/6)) (μ * (7/6)) h2 h1 h3
    have e1 : tf72Fc (6/7) (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)
        = tf72Fc 1 ((((-(a * (7/6)) : ℝ)) : ℂ) + ((μ * (7/6) : ℝ) : ℂ) * Complex.I) := by
      rw [tf72Fc_scale (6/7) h67, hpoint]
    have e2 : tf72Fc (6/7) ((μ : ℂ) * Complex.I)
        = tf72Fc 1 ((((μ * (7/6) : ℝ)) : ℂ) * Complex.I) := by
      rw [tf72Fc_scale (6/7) h67, hpoint2]
    have hb : ((tf72T (6/7) h67).Fc (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re
        - 2 * ((tf72T (6/7) h67).Fc ((μ : ℂ) * Complex.I)).re
        = (tf72Fc 1 ((((-(a * (7/6)) : ℝ)) : ℂ) + ((μ * (7/6) : ℝ) : ℂ) * Complex.I)).re
          - 2 * (tf72Fc 1 ((((μ * (7/6) : ℝ)) : ℂ) * Complex.I)).re := by
      change (tf72Fc (6/7) (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re
        - 2 * (tf72Fc (6/7) ((μ : ℂ) * Complex.I)).re = _
      rw [e1, e2]
    have h56 : (1:ℝ)/100 ≤ 32/35/6 := by norm_num
    rw [hb, hf0]
    linarith
  · intro a μ ha0 ha hmu
    have h1 : a * (7/6) ≤ 17/16 := by linarith
    have h2 : 0 ≤ a * (7/6) := by linarith
    have h3 : 4 ≤ |μ * (7/6)| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 7/6)]
      nlinarith [abs_nonneg μ]
    have h4 := hnum.2 (a * (7/6)) (μ * (7/6)) h2 h1 h3
    have e1 : tf72Fc (6/7) (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)
        = tf72Fc 1 ((((-(a * (7/6)) : ℝ)) : ℂ) + ((μ * (7/6) : ℝ) : ℂ) * Complex.I) := by
      rw [tf72Fc_scale (6/7) h67, hpoint]
    have hb : ((tf72T (6/7) h67).Fc (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re
        = (tf72Fc 1 ((((-(a * (7/6)) : ℝ)) : ℂ) + ((μ * (7/6) : ℝ) : ℂ) * Complex.I)).re := by
      change (tf72Fc (6/7) (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re = _
      rw [e1]
    have h56 : (1:ℝ)/10 ≤ 32/35/6 := by norm_num
    rw [hb, hf0]
    linarith

/-- **The near-configuration endgame.**  From HB's (10.6) for the test function of Lemma 7.2 at
`λ = 6/7` (`tf72T (6/7)`), the `λ`-ordering `λ₁ ≤ λ₂ ≤ λ₃ ≤ 6/7 - ε` and the slack
`ε' = min (ε/10⁶) 10⁻⁶` (whose `s = 8ε'f(0)` satisfies all the smallness conditions), one gets
`6/7 - ε ≤ λ₃`.  The numerical inputs are `tf72f_refute_quant` (the falsity of (10.7) up to
`792/1000`, margin `83/9000`) and the moment step `hmom_step`. -/
theorem nearF2_of_h106 {ε : ℝ} (hε : 0 < ε) {L : ℝ} (hL : 1 ≤ L) {q : ℕ} [NeZero q]
    {χ₁ χ₂ χ₃ : DirichletCharacter ℂ q} {ρ₁ ρ₂ ρ₃ : ℂ}
    (hR : Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁)
    (hZ2 : Work.ZeroFreeTables.IsZAt L χ₂ ρ₂) (hZ3 : Work.ZeroFreeTables.IsZAt L χ₃ ρ₃)
    (hlam23 : Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q ρ₃)
    (hlam3 : Work.LinnikContract.lamOf q ρ₃ ≤ 6/7 - ε)
    (h106 : (tf72T (6/7) (by norm_num)).F (-(Work.LinnikContract.lamOf q ρ₁))
        - (tf72T (6/7) (by norm_num)).F 0
        - (tf72T (6/7) (by norm_num)).F
            (Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₁)
        - (tf72T (6/7) (by norm_num)).F
            (Work.LinnikContract.lamOf q ρ₃ - Work.LinnikContract.lamOf q ρ₁)
        + (tf72T (6/7) (by norm_num)).f 0 * (7/6 + 8 * min (ε/1000000) (1/1000000)) ≥ 0) :
    6/7 - ε ≤ Work.LinnikContract.lamOf q ρ₃ := by
  have h67 : (0:ℝ) < 6/7 := by norm_num
  have hx₀ : (tf72T (6/7) h67).x₀ = 7/3 := by
    show (2:ℝ)/(6/7) = 7/3
    norm_num
  have hfT : (tf72T (6/7) h67).f = tf72f (6/7) := rfl
  have hF0 : (tf72T (6/7) h67).F 0 = 8/9 := by
    change (tf72Fc (6/7) ((0:ℝ):ℂ)).re = 8/9
    rw [show ((0:ℝ):ℂ) = 0 from by norm_num]
    exact tf72Fc_zero_re (6/7) h67
  have hF6 : (tf72T (6/7) h67).F (-(6/7)) = 8/5 := by
    change (tf72Fc (6/7) ((-(6/7):ℝ):ℂ)).re = 8/5
    exact tf72Fc_neglam_re (6/7) h67
  have hf0 : (tf72T (6/7) h67).f 0 = 32/35 := by
    change tf72f (6/7) 0 = 32/35
    rw [tf72f_at_zero (6/7) (by norm_num)]
    norm_num
  have hL75 : (tf72T (6/7) h67).f 0 * (7/6) = 3 * (tf72T (6/7) h67).F 0
      - (tf72T (6/7) h67).F (-(6/7)) := by
    rw [hf0, hF0, hF6]
    norm_num
  set ε' : ℝ := min (ε/1000000) (1/1000000) with hε'def
  have hε'pos : 0 < ε' := by
    rw [hε'def]
    exact lt_min (by linarith) (by norm_num)
  have hε'ε : ε' ≤ ε/1000000 := by
    rw [hε'def]; exact min_le_left _ _
  have hε'1 : ε' ≤ 1/1000000 := by
    rw [hε'def]; exact min_le_right _ _
  have hs0 : 0 ≤ 8 * ε' * (tf72T (6/7) h67).f 0 :=
    mul_nonneg (mul_nonneg (by norm_num) hε'pos.le) (le_of_lt (tf72T (6/7) h67).f0_pos)
  have hs1 : 8 * ε' * (tf72T (6/7) h67).f 0 ≤ 1/20000 := by
    rw [hf0]
    nlinarith [hε'1]
  have hs2 : 8 * ε' * (tf72T (6/7) h67).f 0 ≤ ε/40 := by
    rw [hf0]
    nlinarith [hε'ε, hε]
  have hs83 : 8 * ε' * (tf72T (6/7) h67).f 0 < 83/9000 := by
    rw [hf0]
    nlinarith [hε'1]
  have hse : 8 * ε' * (tf72T (6/7) h67).f 0 ≤ ε/10000 := by
    rw [hf0]
    nlinarith [hε'ε, hε]
  have hL10 : L ≤ 10 * L := by linarith
  have hl1nn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ :=
    lamOf_nonneg_of_zeroMult hR.1.2.1
  have hl12 : Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q ρ₂ :=
    hR.2 χ₂ ρ₂ ⟨hZ2.1, hZ2.2.1, le_trans hZ2.2.2 hL10⟩
  have hl13 : Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q ρ₃ :=
    le_trans hl12 hlam23
  have hl36 : Work.LinnikContract.lamOf q ρ₃ ≤ 6/7 := by linarith
  have hmom : ∀ l : ℝ, 0 ≤ l → l < 6/7 →
      (tf72T (6/7) h67).F (-(6/7)) - (tf72T (6/7) h67).F (-l)
        ≤ 2 * ((tf72T (6/7) h67).F 0 - (tf72T (6/7) h67).F (6/7 - l))
          + 8 * ε' * (tf72T (6/7) h67).f 0 →
      l ≤ 792/1000 ∨ 6/7 - ε/2 ≤ l :=
    fun l hl0 hl67 h107 =>
      hmom_step (tf72T (6/7) h67) hx₀ hfT hs0 hs1 hs2 hl0 hl67 h107
  have href : ∀ l : ℝ, 0 ≤ l → l ≤ 792/1000 →
      (tf72T (6/7) h67).F (-(6/7)) - (tf72T (6/7) h67).F (-l)
        ≥ 2 * ((tf72T (6/7) h67).F 0 - (tf72T (6/7) h67).F (6/7 - l)) + 83/9000 :=
    Work.OffAxis.tf72f_refute_quant_clean (tf72T (6/7) h67) hx₀ hfT hF0 hF6
  exact Work.OffAxis.rect10_3_endgame_clean (tf72T (6/7) h67) ε' ε
    (8 * ε' * (tf72T (6/7) h67).f 0)
    (Work.LinnikContract.lamOf q ρ₁) (Work.LinnikContract.lamOf q ρ₂)
    (Work.LinnikContract.lamOf q ρ₃) hε hx₀ hfT hF0 hF6 hL75 hs0 hse le_rfl hs83 hmom href
    h106 hl1nn hl13 hlam23 hl36

/-! ## The target statement

The proof combines
* the `F`-method engine at rectangle height `L`, `OffAxis/HB10_3EngineNear` (HB §10 Lemmas 10.1
  and 10.2: `F(-λ₁) - F(0) - F(λ₂-λ₁) - F(λ₃-λ₁) + f(0)(7/6 + 8ε') ≥ 0`), instantiated at the
  Lemma 7.2 test function `tf72T (6/7)`;
* its two numeric hypotheses (HB (10.8)/(10.9)), obtained from the scale-free bounds
  `OffAxis/tf72FcOneNum` via the scaling identity `tf72Fc_scale`;
* the moment step `hmom_step` (this file) and the numerical falsity of (10.7) on `λ₁ ≤ 792/1000`
  (`OffAxis/Rect10_3H_F2`, `tf72f_refute_quant` with its margin `83/9000`);
* the endgame `OffAxis/Rect10_3H_F2`, `rect10_3_endgame`.

The hypothesis `χ₁χ₂χ₃ = 1 ∨ …` is not needed: the engine covers every configuration of the
three conjugate pairs as soon as `Im ρ₁ ≠ 0` (HB Lemma 10.2's hypothesis is "`χ₁` complex or
`ρ₁` complex"). -/
theorem Rect10_3NearF2 : ∀ ε : ℝ, 0 < ε → ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q) (ρ₁ ρ₂ ρ₃ : ℂ),
      Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ → ρ₁.im ≠ 0 →
      Work.ZeroFreeTables.IsZAt L χ₂ ρ₂ → Work.ZeroFreeTables.IsZAt L χ₃ ρ₃ →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₃ ≠ χ₁ → χ₃ ≠ χ₁⁻¹ → χ₃ ≠ χ₂ → χ₃ ≠ χ₂⁻¹ →
      Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q ρ₃ →
      Work.LinnikContract.lamOf q ρ₃ ≤ 6/7 - ε →
      (χ₁ * χ₂ * χ₃ = 1 ∨ χ₁ * χ₂ = χ₃ ∨ χ₁ * χ₃ = χ₂ ∨ χ₂ * χ₃ = χ₁) →
      6/7 - ε ≤ Work.LinnikContract.lamOf q ρ₃ := by
  intro ε hε L hL
  by_cases hbig : ((6:ℝ)/7 ≤ ε)
  · -- any non-principal zero has `λ ≥ 0`
    refine ⟨0, ?_⟩
    intro q _hq _inst χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ _hR _him _hZ2 hZ3 _ _ _ _ _ _ _ _ _
    have hl3 : 0 ≤ Work.LinnikContract.lamOf q ρ₃ := lamOf_nonneg_of_zeroMult hZ3.2.1
    linarith
  push_neg at hbig
  -- HB Lemma 7.2's test function at `λ = 6/7` and the slack `ε'` of the endgame
  set T : Work.ZeroFreeTables.TestFn := tf72T (6/7) (by norm_num) with hTdef
  obtain ⟨q₀, hq₀⟩ := Work.OffAxis.HB10_3EngineNear T (min (ε/1000000) (1/1000000))
    (lt_min (by linarith) (by norm_num)) L hL
  have hnum := num_transfer tf72FcOneNum
  refine ⟨q₀, fun q hq _inst χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hR him hZ2 hZ3 h21 h2i h31 h3i h32 h3ii
    hlam23 hlam3 _hprod => ?_⟩
  have h106 := hq₀ q hq χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hR him hZ2 hZ3 h21 h2i h31 h3i h32 h3ii
    hlam23 (by linarith : Work.LinnikContract.lamOf q ρ₃ ≤ 6/7) hnum.1 hnum.2
  exact nearF2_of_h106 hε hL hR hZ2 hZ3 hlam23 hlam3 h106


end Work.OffAxis.Lead
