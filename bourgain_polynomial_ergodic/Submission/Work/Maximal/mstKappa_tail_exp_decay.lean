import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs

namespace Work.Maximal

open Real

/-- `mstKappa P s` dominates `20 * deg P * (s+1)^{1/10}`. -/
lemma mstKappa_ge_rpow_mul (P : Polynomial ℤ) (s : ℕ) :
    20 * (P.natDegree : ℝ) * (((s : ℝ) + 1) ^ (1 / 10 : ℝ))
      ≤ (Work.BourgainPlan.Maximal.mstKappa P s : ℝ) := by
  have hx0 : (0 : ℝ) ≤ ((s : ℝ) + 1) ^ (1 / 10 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hfloor : ((s : ℝ) + 1) ^ (1 / 10 : ℝ)
      ≤ (((⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ : ℕ) : ℝ) + 1) :=
    le_of_lt (Nat.lt_floor_add_one _)
  have hdnn : (0 : ℝ) ≤ (P.natDegree : ℝ) := Nat.cast_nonneg _
  rw [Work.BourgainPlan.Maximal.mstKappa]
  push_cast
  nlinarith [hfloor, hx0, hdnn]

/-- `exp y ≥ y^2/4` for `y ≥ 0`. -/
lemma sq_div_four_le_exp {y : ℝ} (hy : 0 ≤ y) : y ^ 2 / 4 ≤ Real.exp y := by
  have h1 : 1 + y / 2 ≤ Real.exp (y / 2) := by linarith [Real.add_one_le_exp (y / 2)]
  have h2 : (0 : ℝ) ≤ 1 + y / 2 := by linarith
  have h3 : (1 + y / 2) ^ 2 ≤ (Real.exp (y / 2)) ^ 2 := pow_le_pow_left₀ h2 h1 2
  have h4 : (Real.exp (y / 2)) ^ 2 = Real.exp y := by
    rw [sq, ← Real.exp_add]; ring_nf
  have h5 : y ^ 2 / 4 ≤ (1 + y / 2) ^ 2 := by nlinarith [hy, sq_nonneg y]
  rw [h4] at h3
  linarith

/-- **The doubly exponential tail beats the polynomial and sub-exponential factors.**
For `P ∈ ℤ[X]` of degree `≥ 2`, `δ > 0`, `l ≥ 1`, `θ ∈ (0,1)` and `M > 0`, for all large `s`

  `M (s+1)^{-δ l} · exp((1-θ)(s+1)^{1/10}) · 2^{-θ 2^{κ_s}/(2 deg P)} ≤ 1`,

with `κ_s = mstKappa P s = 20·deg P·(⌊(s+1)^{1/10}⌋ + 1)`.

Route.  Write `x = (s+1)^{1/10}`, `d = deg P`.  For `x ≥ 1` the first factor is `≤ 1`, so it suffices
to show `M · exp((1-θ)x) · 2^{-A} ≤ 1` where `A = θ 2^{κ_s}/(2d)`.  Taking the exponential form
(`M = exp(log M)`, `2^{-A} = exp(-A log 2)`) this is `log M + (1-θ)x ≤ A log 2`.  Since
`κ_s ≥ 20 d x` we have `2^{κ_s} ≥ exp(20 d x log 2)`, and `exp t ≥ t²/4` turns this into the purely
polynomial comparison `log M + (1-θ)x ≤ 50 θ d (log 2)³ x²`, which holds once `x` exceeds an explicit
threshold `X₀`. -/
theorem mstKappa_tail_exp_decay (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    {δ : ℝ} (hδ : 0 < δ) (l : ℕ) (hl : 1 ≤ l) {θ M : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hM : 0 < M) :
    ∃ S : ℕ, ∀ s : ℕ, S ≤ s →
      M * ((s : ℝ) + 1) ^ (-(δ * l))
        * Real.exp ((1 - θ) * ((s : ℝ) + 1) ^ (1 / 10 : ℝ))
        * (2 : ℝ) ^ (-(θ * ((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
            / (2 * (P.natDegree : ℝ)))) ≤ 1 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hdR : 0 < (P.natDegree : ℝ) := by
    have : 0 < P.natDegree := by omega
    exact_mod_cast this
  have h1mθ : 0 < 1 - θ := by linarith
  set B : ℝ := (1 - θ) + max (Real.log M) 0 with hB_def
  have hBpos : 0 < B := by
    rw [hB_def]
    have := le_max_right (Real.log M) 0
    linarith
  set Cq : ℝ := 50 * θ * (P.natDegree : ℝ) * (Real.log 2) ^ 3 with hCq_def
  have hCqpos : 0 < Cq := by
    rw [hCq_def]
    have h3 : (0 : ℝ) < (Real.log 2) ^ 3 := pow_pos hlog2 3
    positivity
  set X0 : ℝ := max 1 (2 * B / Cq) with hX0_def
  have hX0ge1 : 1 ≤ X0 := le_max_left _ _
  have hX0geC : 2 * B / Cq ≤ X0 := le_max_right _ _
  have hX0pos : 0 < X0 := lt_of_lt_of_le zero_lt_one hX0ge1
  refine ⟨⌈X0 ^ 10⌉₊, fun s hs => ?_⟩
  set x : ℝ := ((s : ℝ) + 1) ^ (1 / 10 : ℝ) with hx_def
  set A : ℝ := θ * ((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
      / (2 * (P.natDegree : ℝ)) with hA_def
  set y : ℝ := 20 * (P.natDegree : ℝ) * x * Real.log 2 with hy_def
  have hsX0 : X0 ^ 10 ≤ (s : ℝ) := by
    have h1 : X0 ^ 10 ≤ ((⌈X0 ^ 10⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((⌈X0 ^ 10⌉₊ : ℕ) : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    linarith
  have hx1 : 1 ≤ x := by
    rw [hx_def]
    calc (1 : ℝ) = (1 : ℝ) ^ (1 / 10 : ℝ) := (Real.one_rpow _).symm
      _ ≤ ((s : ℝ) + 1) ^ (1 / 10 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) s]) (by norm_num)
  have hxX0 : X0 ≤ x := by
    rw [hx_def]
    have hb : X0 ^ 10 ≤ (s : ℝ) + 1 := by linarith
    have hkey : (X0 ^ 10) ^ (1 / 10 : ℝ) = X0 := by
      rw [← Real.rpow_natCast X0 10]
      rw [← Real.rpow_mul (le_of_lt hX0pos)]
      rw [show ((10 : ℕ) : ℝ) * (1 / 10) = 1 by norm_num, Real.rpow_one]
    calc X0 = (X0 ^ 10) ^ (1 / 10 : ℝ) := hkey.symm
      _ ≤ ((s : ℝ) + 1) ^ (1 / 10 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hb (by norm_num)
  -- the arithmetic core
  have hxnn : 0 ≤ x := le_trans zero_le_one hx1
  have hy : 0 ≤ y := by rw [hy_def]; positivity
  have hcore : Real.log M + (1 - θ) * x ≤ Cq * x ^ 2 := by
    have hmaxnn : 0 ≤ max (Real.log M) 0 := le_max_right _ _
    have hlogMx : Real.log M ≤ max (Real.log M) 0 * x := by
      rcases le_or_gt (Real.log M) 0 with h | h
      · nlinarith [hmaxnn, hx1]
      · have hmax : max (Real.log M) 0 = Real.log M := max_eq_left (le_of_lt h)
        rw [hmax]; nlinarith [h, hx1]
    have hstep : Real.log M + (1 - θ) * x ≤ B * x := by
      rw [hB_def]; nlinarith [hlogMx]
    have hCx : B * x ≤ Cq * x ^ 2 := by
      have hxC : 2 * B ≤ Cq * x := by
        have h := le_trans hX0geC hxX0
        rw [div_le_iff₀ hCqpos] at h
        linarith [h]
      nlinarith [hxC, hBpos, hCqpos, hx1]
    linarith [hstep, hCx]
  have hmid : Cq * x ^ 2
      ≤ θ * Real.log 2 / (2 * (P.natDegree : ℝ)) * Real.exp y := by
    have hexp : y ^ 2 / 4 ≤ Real.exp y := sq_div_four_le_exp hy
    have hcoef : 0 ≤ θ * Real.log 2 / (2 * (P.natDegree : ℝ)) :=
      div_nonneg (mul_nonneg (le_of_lt hθ0) (le_of_lt hlog2)) (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hexp hcoef
    have halg : Cq * x ^ 2
        = θ * Real.log 2 / (2 * (P.natDegree : ℝ)) * (y ^ 2 / 4) := by
      rw [hCq_def, hy_def]
      field_simp
      ring
    rw [halg]
    exact hmul
  have h2powle : Real.exp y ≤ ((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ) := by
    have hκ := mstKappa_ge_rpow_mul P s
    rw [← hx_def] at hκ
    have hcast : ((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
        = (2 : ℝ) ^ ((Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ) := by
      push_cast
      rw [Real.rpow_natCast]
    rw [hcast]
    have h1 : (2 : ℝ) ^ (20 * (P.natDegree : ℝ) * x)
        ≤ (2 : ℝ) ^ ((Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hκ
    have h2 : (2 : ℝ) ^ (20 * (P.natDegree : ℝ) * x) = Real.exp y := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), hy_def]
      congr 1; ring
    rw [← h2]
    exact h1
  have htop : θ * Real.log 2 / (2 * (P.natDegree : ℝ)) * Real.exp y
      ≤ A * Real.log 2 := by
    rw [hA_def]
    have hcoef : 0 ≤ θ * Real.log 2 / (2 * (P.natDegree : ℝ)) :=
      div_nonneg (mul_nonneg (le_of_lt hθ0) (le_of_lt hlog2)) (by positivity)
    have hmul := mul_le_mul_of_nonneg_left h2powle hcoef
    calc θ * Real.log 2 / (2 * (P.natDegree : ℝ)) * Real.exp y
        ≤ θ * Real.log 2 / (2 * (P.natDegree : ℝ))
            * ((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ) := hmul
      _ = θ * ((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
            / (2 * (P.natDegree : ℝ)) * Real.log 2 := by ring
  have hchain : Real.log M + (1 - θ) * x ≤ A * Real.log 2 := by
    linarith [hcore, hmid, htop]
  -- the sub-exponential factor `(s+1)^{-δl}` is `≤ 1`
  have hlR : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  have hδl : 0 < δ * l := mul_pos hδ hlR
  have hs1 : (1 : ℝ) ≤ (s : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) s]
  have hbase : (1 : ℝ) ≤ ((s : ℝ) + 1) ^ (δ * l) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (δ * l) := (Real.one_rpow _).symm
      _ ≤ ((s : ℝ) + 1) ^ (δ * l) :=
          Real.rpow_le_rpow (by norm_num) hs1 (le_of_lt hδl)
  have hrpow_le : ((s : ℝ) + 1) ^ (-(δ * l)) ≤ 1 := by
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (s : ℝ) + 1) (δ * l)]
    exact inv_le_one_of_one_le₀ hbase
  have h2A : (2 : ℝ) ^ (-A) = Real.exp (-(A * Real.log 2)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1; ring
  have hstep1 : M * ((s : ℝ) + 1) ^ (-(δ * l)) * Real.exp ((1 - θ) * x) * (2 : ℝ) ^ (-A)
      ≤ M * Real.exp ((1 - θ) * x) * (2 : ℝ) ^ (-A) := by
    have h1 : M * ((s : ℝ) + 1) ^ (-(δ * l)) ≤ M * 1 :=
      mul_le_mul_of_nonneg_left hrpow_le (le_of_lt hM)
    have h2 : M * ((s : ℝ) + 1) ^ (-(δ * l)) * Real.exp ((1 - θ) * x)
        ≤ M * 1 * Real.exp ((1 - θ) * x) :=
      mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
    have h3 : M * ((s : ℝ) + 1) ^ (-(δ * l)) * Real.exp ((1 - θ) * x) * (2 : ℝ) ^ (-A)
        ≤ M * 1 * Real.exp ((1 - θ) * x) * (2 : ℝ) ^ (-A) :=
      mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (by norm_num) _)
    simpa using h3
  have hstep2 : M * Real.exp ((1 - θ) * x) * (2 : ℝ) ^ (-A)
      = Real.exp (Real.log M + ((1 - θ) * x - A * Real.log 2)) := by
    calc M * Real.exp ((1 - θ) * x) * (2 : ℝ) ^ (-A)
        = Real.exp (Real.log M) * Real.exp ((1 - θ) * x)
            * Real.exp (-(A * Real.log 2)) := by
          rw [Real.exp_log hM, ← h2A]
      _ = Real.exp (Real.log M + ((1 - θ) * x) + (-(A * Real.log 2))) := by
          rw [← Real.exp_add, ← Real.exp_add]
      _ = Real.exp (Real.log M + ((1 - θ) * x - A * Real.log 2)) := by
          congr 1; ring
  refine le_trans (le_trans hstep1 (le_of_eq hstep2)) ?_
  exact Real.exp_le_one_iff.mpr (by linarith [hchain])

end Work.Maximal
