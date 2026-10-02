/-
# The budget inequality `(R + 4) J^3 ≤ (1/2) L^4 √D`

With `L = ncpL D = log (D + 2)`, `J = ncpJlev D` and `R = ncpRR D = 11 (T + log (2J) + 10)`,
`T = L^4/5000 + 2`, this file proves

`(R + 4) · J^3 ≤ (1/2) · L^4 · √D`   whenever `L ≥ 44`.

This is the arithmetic that pays for the "large colour class" cutoff level `J` out of the
`√D · L^4` budget available in the sparse colouring argument: at `D ≥ e^{44} - 2`, the
polynomial growth `J^3 · R ≈ L^{16}` of the cutoff is dominated by the exponential `√D ≈ e^{L/2}`.

## The chain

Write `X = L^4 ≥ 44^4 = 3748096`.

* `⌈·⌉₊ < · + 1` gives `J ≤ X/2500 + 2L + 123`; since `L^3 ≥ 85000` (`44^3 = 85184`) and
  `X ≥ 3748096` one has `2L ≤ X/42500` and `123 ≤ X/30000`, whence
  `J ≤ X/2500 + X/42500 + X/30000 ≤ 8X/17500`.
* `R + 4 = 11X/5000 + 11 log (2J) + 136`.  Here `log (2J) ≤ log X = 4 log L ≤ 4(L-1) ≤ 4L`
  and `4L ≤ X/21250`, while `136 ≤ X/25000`; the coefficients satisfy
  `11/21250 + 1/25000 ≤ 3/5000`, so `R + 4 ≤ 11X/5000 + 3X/5000 = 7X/2500`.
* Hence `(R+4) J^3 ≤ (7X/2500)(8X/17500)^3 = 3584 X^4/(2500 · 17500^3)`.
* On the other side `√D ≥ e^{L/2}/2` (because `e^L = D + 2 ≤ 4D` for `D ≥ 43`) and
  `e^{L/2} ≥ e^22 (L/2)^12 / 22^12` (the function `u ↦ u^12/e^u` is decreasing on `[22,∞)`:
  write `u = 22(1+t)` with `t = (u-22)/22 ≥ 0`; then `(1+t)^12 ≤ e^{12t} ≤ e^{u-22}`).
  So `(1/2) L^4 √D ≥ X^4 e^22/(2^14 22^12)`.
* The two sides meet in the numerical inequality
  `3584/(2500 · 17500^3) ≤ e^22/(2^14 · 22^12)`, which holds because `e^22 ≥ (6/5)^110` and
  `(6/5)^110 · 2500 · 17500^3 ≥ 3584 · 2^14 · 22^12 · ...` (exact integer arithmetic).
-/
import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ncpTailDefs

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Deep.Sparse

/-- For `u ≥ 22`, `u^12 · e^22 ≤ 22^12 · e^u`: the function `u ↦ u^12/e^u` is decreasing on
`[22, ∞)`.  Proof: write `u = 22 (1 + t)` with `t = (u - 22)/22 ≥ 0`; then
`(1 + t)^12 ≤ e^{12t}` (from `1 + t ≤ e^t`) and `12 t ≤ u - 22`. -/
private lemma pow12_mul_exp22_le (u : ℝ) (hu : (22 : ℝ) ≤ u) :
    u ^ 12 * Real.exp 22 ≤ (22 : ℝ) ^ 12 * Real.exp u := by
  set t : ℝ := (u - 22) / 22 with ht
  have ht0 : (0 : ℝ) ≤ t := by
    rw [ht]
    exact div_nonneg (by linarith) (by norm_num)
  have hle : 1 + t ≤ Real.exp t := by
    have h := Real.add_one_le_exp t
    linarith
  have hp : (1 + t) ^ 12 ≤ (Real.exp t) ^ 12 := pow_le_pow_left₀ (by linarith) hle 12
  have he : (Real.exp t) ^ 12 = Real.exp (12 * t) := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h12t : 12 * t ≤ u - 22 := by
    have h : (12 : ℝ) * t = 12 * (u - 22) / 22 := by rw [ht]; ring
    rw [h, div_le_iff₀ (by norm_num : (0 : ℝ) < 22)]
    nlinarith
  have hmono : Real.exp (12 * t) ≤ Real.exp (u - 22) := Real.exp_le_exp.mpr h12t
  have hstep : (1 + t) ^ 12 ≤ Real.exp (u - 22) :=
    le_trans hp (le_trans (le_of_eq he) hmono)
  have hEq : u = 22 * (1 + t) := by rw [ht]; ring
  calc u ^ 12 * Real.exp 22
      = ((22 : ℝ) ^ 12 * (1 + t) ^ 12) * Real.exp 22 := by rw [hEq, mul_pow]
    _ ≤ ((22 : ℝ) ^ 12 * Real.exp (u - 22)) * Real.exp 22 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hstep (by positivity)) (Real.exp_pos 22).le
    _ = (22 : ℝ) ^ 12 * Real.exp u := by
        rw [mul_assoc, ← Real.exp_add, show u - 22 + 22 = u from by ring]

/-- `(6/5)^110 ≤ e^22` (and `(6/5)^110 ≈ 5.13·10^8`). -/
private lemma exp22_lower_bound : ((6 : ℝ) / 5) ^ 110 ≤ Real.exp 22 := by
  have h1 : (1 : ℝ) + 1 / 5 ≤ Real.exp (1 / 5) := by
    have h := Real.add_one_le_exp (1 / 5)
    linarith
  have h2 : ((6 : ℝ) / 5) ^ 110 ≤ (Real.exp (1 / 5)) ^ 110 := by
    have hbase : (1 : ℝ) + 1 / 5 = 6 / 5 := by norm_num
    rw [← hbase]
    exact pow_le_pow_left₀ (by norm_num) h1 110
  have h3 : (Real.exp ((1 : ℝ) / 5)) ^ 110 = Real.exp 22 := by
    rw [← Real.exp_nat_mul]
    norm_num
  calc ((6 : ℝ) / 5) ^ 110 ≤ (Real.exp (1 / 5)) ^ 110 := h2
    _ = Real.exp 22 := h3

/-- The numerical meeting point: `3584/(2500 · 17500^3) ≤ e^22/(2^14 · 22^12)`. -/
private lemma budget_const :
    (3584 : ℝ) / (2500 * 17500 ^ 3) ≤ Real.exp 22 / (2 ^ 14 * 22 ^ 12) := by
  have hd : (0 : ℝ) < (2 : ℝ) ^ 14 * 22 ^ 12 := by norm_num
  have hbase : (3584 : ℝ) / (2500 * 17500 ^ 3) ≤ ((6 : ℝ) / 5) ^ 110 / (2 ^ 14 * 22 ^ 12) := by
    have hd1 : (0 : ℝ) < 2500 * 17500 ^ 3 := by norm_num
    have hd2 : (0 : ℝ) < (2 : ℝ) ^ 14 * 22 ^ 12 := by norm_num
    rw [div_le_div_iff₀ hd1 hd2, div_pow, div_mul_eq_mul_div,
      le_div_iff₀ (by positivity : (0 : ℝ) < (5 : ℝ) ^ 110)]
    norm_num
  refine le_trans hbase ?_
  rw [div_le_div_iff₀ hd hd]
  exact mul_le_mul_of_nonneg_right exp22_lower_bound hd.le

theorem ncp_budget_arith (D : ℕ) (hL : 44 ≤ ncpL D) :
    (ncpRR D + 4) * ((ncpJlev D : ℕ) : ℝ) ^ 3
      ≤ (1 / 2 : ℝ) * (ncpL D) ^ 4 * Real.sqrt (D : ℝ) := by
  set L : ℝ := ncpL D with hLdef
  set J : ℕ := ncpJlev D with hJdef
  have h44 : (44 : ℝ) ≤ L := by simpa only [hLdef] using hL
  have hLpos : (0 : ℝ) < L := by linarith
  have hXpos : (0 : ℝ) < L ^ 4 := by positivity
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  -- the exponential identity `e^L = D + 2`
  have hexpL : Real.exp L = (D : ℝ) + 2 := by
    have h : Real.exp (ncpL D) = (D : ℝ) + 2 := by
      simp only [ncpL]
      exact Real.exp_log (by positivity)
    simpa only [hLdef] using h
  have hDge43 : (43 : ℝ) ≤ (D : ℝ) := by
    have h45 : (45 : ℝ) ≤ Real.exp 44 := by
      have h := Real.add_one_le_exp 44
      norm_num at h
      linarith
    have hmono : Real.exp 44 ≤ Real.exp L := Real.exp_le_exp.mpr h44
    have h45L : (45 : ℝ) ≤ Real.exp L := le_trans h45 hmono
    rw [hexpL] at h45L
    linarith
  -- power lower bounds coming from `L ≥ 44`
  have hX44 : (44 : ℝ) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) h44 4
  have hXbig : (3748096 : ℝ) ≤ L ^ 4 := by norm_num at hX44; linarith
  have hLcub44 : (44 : ℝ) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) h44 3
  have hL3big : (85000 : ℝ) ≤ L ^ 3 := by norm_num at hLcub44; linarith
  have hX85000 : 85000 * L ≤ L ^ 4 := by
    have h := mul_le_mul_of_nonneg_right hL3big hLpos.le
    calc 85000 * L ≤ L ^ 3 * L := h
      _ = L ^ 4 := by ring
  -- bound for `J`
  have hJceil1 : ((⌈L ^ 4 / 5000⌉₊ : ℕ) : ℝ) < L ^ 4 / 5000 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hJceil2 : ((⌈L⌉₊ : ℕ) : ℝ) < L + 1 := Nat.ceil_lt_add_one hLpos.le
  have hJexpand : (J : ℝ)
      = 19 + 2 * (((⌈L ^ 4 / 5000⌉₊ : ℕ) : ℝ) + ((⌈L⌉₊ : ℕ) : ℝ) + 50) := by
    rw [hJdef, ncpJlev]
    simp only [← hLdef]
    push_cast
    ring
  have hJle : (J : ℝ) ≤ L ^ 4 / 2500 + 2 * L + 123 := by
    rw [hJexpand]
    linarith [hJceil1, hJceil2]
  have h2L : 2 * L ≤ L ^ 4 / 42500 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 42500)]
    nlinarith [hX85000]
  have h123 : (123 : ℝ) ≤ L ^ 4 / 30000 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 30000)]
    nlinarith [hXbig]
  have hcoefJ : L ^ 4 / 2500 + L ^ 4 / 42500 + L ^ 4 / 30000 ≤ 8 * L ^ 4 / 17500 := by
    have hc : (1 : ℝ) / 2500 + 1 / 42500 + 1 / 30000 ≤ 8 / 17500 := by norm_num
    have hmul := mul_le_mul_of_nonneg_left hc hXpos.le
    linarith
  have hJbound : (J : ℝ) ≤ 8 * L ^ 4 / 17500 := by linarith [hJle, h2L, h123, hcoefJ]
  -- bound for `R`
  have hRexp : ncpRR D + 4 = 11 * (L ^ 4 / 5000) + 11 * Real.log (2 * (J : ℝ)) + 136 := by
    rw [ncpRR, ncpT]
    simp only [← hLdef, ← hJdef]
    ring
  have hJ1 : 1 ≤ J := by rw [hJdef, ncpJlev]; omega
  have hlog2Jpos : (0 : ℝ) < 2 * (J : ℝ) := by
    have h : (1 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ1
    linarith
  have h2JX : 2 * (J : ℝ) ≤ L ^ 4 := by
    have h16 : (16 : ℝ) * L ^ 4 / 17500 ≤ L ^ 4 := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 17500)]
      nlinarith [hXpos]
    have heq : 2 * (8 * L ^ 4 / 17500) = 16 * L ^ 4 / 17500 := by ring
    linarith [hJbound]
  have h4L : 4 * L ≤ L ^ 4 / 21250 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 21250)]
    nlinarith [hX85000]
  have hlog2J : Real.log (2 * (J : ℝ)) ≤ L ^ 4 / 21250 := by
    calc Real.log (2 * (J : ℝ)) ≤ Real.log (L ^ 4) := Real.log_le_log hlog2Jpos h2JX
      _ = 4 * Real.log L := by rw [Real.log_pow]; norm_num
      _ ≤ 4 * (L - 1) := by
          have h := Real.log_le_sub_one_of_pos hLpos
          linarith
      _ ≤ 4 * L := by linarith
      _ ≤ L ^ 4 / 21250 := h4L
  have h136 : (136 : ℝ) ≤ L ^ 4 / 25000 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 25000)]
    nlinarith [hXbig]
  have hRbound : ncpRR D + 4 ≤ 7 * L ^ 4 / 2500 := by
    have hcoefR : (11 : ℝ) / 21250 + 1 / 25000 ≤ 3 / 5000 := by norm_num
    have hA : 11 * Real.log (2 * (J : ℝ)) ≤ 11 * (L ^ 4 / 21250) :=
      mul_le_mul_of_nonneg_left hlog2J (by norm_num)
    have hB := mul_le_mul_of_nonneg_left hcoefR hXpos.le
    rw [hRexp]
    linarith
  -- the right-hand side
  have hRHS : (L ^ 4) ^ 4 * Real.exp 22 / (2 ^ 14 * 22 ^ 12)
      ≤ (1 / 2 : ℝ) * L ^ 4 * Real.sqrt (D : ℝ) := by
    have hhalf22 : (22 : ℝ) ≤ L / 2 := by linarith
    have hkey := pow12_mul_exp22_le (L / 2) hhalf22
    have hkey' : Real.exp 22 * (L / 2) ^ 12 ≤ (22 : ℝ) ^ 12 * Real.exp (L / 2) := by
      calc Real.exp 22 * (L / 2) ^ 12 = (L / 2) ^ 12 * Real.exp 22 := by ring
        _ ≤ (22 : ℝ) ^ 12 * Real.exp (L / 2) := hkey
    have hexp2 : Real.exp 22 * L ^ 12 / (2 ^ 12 * 22 ^ 12) ≤ Real.exp (L / 2) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ 12 * 22 ^ 12)]
      calc Real.exp 22 * L ^ 12 = (Real.exp 22 * (L / 2) ^ 12) * 2 ^ 12 := by
            rw [div_pow]; ring
        _ ≤ ((22 : ℝ) ^ 12 * Real.exp (L / 2)) * 2 ^ 12 :=
            mul_le_mul_of_nonneg_right hkey' (by positivity)
        _ = Real.exp (L / 2) * ((2 : ℝ) ^ 12 * 22 ^ 12) := by ring
    have hsq : (Real.exp (L / 2)) ^ 2 = Real.exp L := by
      rw [pow_two, ← Real.exp_add, show L / 2 + L / 2 = L from by ring]
    have hsqrt : Real.exp (L / 2) / 2 ≤ Real.sqrt (D : ℝ) := by
      rw [Real.le_sqrt (by positivity) hD0]
      rw [div_pow, hsq, show ((2 : ℝ)) ^ 2 = 4 from by norm_num,
        div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
      nlinarith [hexpL, hDge43]
    have hchain : Real.exp 22 * L ^ 12 / (2 ^ 12 * 22 ^ 12) / 2 ≤ Real.sqrt (D : ℝ) := by
      have h2 : Real.exp 22 * L ^ 12 / (2 ^ 12 * 22 ^ 12) / 2
          = Real.exp 22 * L ^ 12 / (2 ^ 12 * 22 ^ 12) * (1 / 2) := by ring
      rw [h2]
      have := mul_le_mul_of_nonneg_left hexp2 (by norm_num : (0 : ℝ) ≤ (1 / 2))
      linarith
    calc (L ^ 4) ^ 4 * Real.exp 22 / (2 ^ 14 * 22 ^ 12)
        = (1 / 2 : ℝ) * L ^ 4
            * (Real.exp 22 * L ^ 12 / (2 ^ 12 * 22 ^ 12) / 2) := by ring
      _ ≤ (1 / 2 : ℝ) * L ^ 4 * Real.sqrt (D : ℝ) :=
          mul_le_mul_of_nonneg_left hchain (by positivity)
  -- the left-hand side
  have hLHS : (ncpRR D + 4) * (J : ℝ) ^ 3 ≤ 3584 * (L ^ 4) ^ 4 / (2500 * 17500 ^ 3) := by
    have hJpow : (J : ℝ) ^ 3 ≤ (8 * L ^ 4 / 17500) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hJbound 3
    have h1 : (ncpRR D + 4) * (J : ℝ) ^ 3
        ≤ (7 * L ^ 4 / 2500) * (8 * L ^ 4 / 17500) ^ 3 :=
      mul_le_mul hRbound hJpow (by positivity) (by positivity)
    have h2 : (7 * L ^ 4 / 2500) * (8 * L ^ 4 / 17500) ^ 3
        = 3584 * (L ^ 4) ^ 4 / (2500 * 17500 ^ 3) := by ring
    linarith
  calc (ncpRR D + 4) * (J : ℝ) ^ 3
      ≤ 3584 * (L ^ 4) ^ 4 / (2500 * 17500 ^ 3) := hLHS
    _ = (3584 / (2500 * 17500 ^ 3)) * (L ^ 4) ^ 4 := by ring
    _ ≤ (Real.exp 22 / (2 ^ 14 * 22 ^ 12)) * (L ^ 4) ^ 4 :=
        mul_le_mul_of_nonneg_right budget_const (by positivity)
    _ = (L ^ 4) ^ 4 * Real.exp 22 / (2 ^ 14 * 22 ^ 12) := by ring
    _ ≤ (1 / 2 : ℝ) * L ^ 4 * Real.sqrt (D : ℝ) := hRHS

end Work.Deep.Sparse
