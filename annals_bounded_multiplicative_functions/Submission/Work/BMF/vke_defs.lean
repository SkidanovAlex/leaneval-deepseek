import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Quantities for the Vinogradov–Korobov exponential-sum bound `Work.BMF.vk_exp_sum`

Given `2 ≤ N ≤ t` and `λ = log t / log N ≥ 1`, the reduction of the block sum
`Σ_{N<n≤R} (n+u)^{-it}` runs the `k`-th-derivative (Weyl) reduction with

* `k = 2⌈2λ⌉ + 2` (even, subject to `4λ+2 ≤ k ≤ 4λ+4`),
* `r = ⌈4k log k⌉ + 1`, `s = (k-1) r` (so that the Vinogradov mean-value exponent
  `2s - (k-1)k/2 + η` loses only `η = ((k-1)²/2)(1 - 1/(k-1))^r`),
* `μ = (t/2π)(k-1)!/N^k`, the size of the `k`-th derivative of the phase
  `x ↦ -(t log (x+u))/(2π)`, and `H = μ^{-1/k}`, the Weyl shift.

The saving produced by the reduction is `δ_avail = (λ/k - (1-λ/k)η)/(2s)`, the saving required by
the target is `δ_req = c (log N/log t)²/log(λ+2)`, and `δ_avail ≥ 2 δ_req` is the exponent
comparison.
-/

namespace Work.BMF

open scoped BigOperators

noncomputable section

/-- `λ = log t / log N`. -/
noncomputable def vkLam (N t : ℝ) : ℝ := Real.log t / Real.log N

/-- `k = 2⌈2λ⌉ + 2`. -/
noncomputable def vkK (N t : ℝ) : ℕ := 2 * ⌈2 * vkLam N t⌉₊ + 2

/-- `r = ⌈4k log k⌉ + 1`. -/
noncomputable def vkR (N t : ℝ) : ℕ :=
  ⌈(4 : ℝ) * ((vkK N t : ℕ) : ℝ) * Real.log ((vkK N t : ℕ) : ℝ)⌉₊ + 1

/-- `s = (k-1) r`. -/
noncomputable def vkS (N t : ℝ) : ℕ := (vkK N t - 1) * vkR N t

/-- `η = ((k-1)²/2)(1 - 1/(k-1))^r`. -/
noncomputable def vkEta (N t : ℝ) : ℝ :=
  (((vkK N t - 1 : ℕ) : ℝ)^2 / 2) * (1 - 1/(((vkK N t - 1 : ℕ)) : ℝ))^(vkR N t)

/-- `μ = (t/2π)(k-1)!/(N-1)^k`.  The shift `N - 1` (rather than `N`) is what makes the two-sided
derivative bounds of `Work.BMF.vke_deriv` usable on the whole interval `(0, M+1)`: the left
endpoint of the block is `⌊N⌋ ≥ N - 1`, so the `k`-th derivative of the phase is at most `μ` there,
and the reduction runs with `A = 8^k`, `lam = μ/8^k`. -/
noncomputable def vkMu (N t : ℝ) : ℝ :=
  (t / (2 * Real.pi)) * (((Nat.factorial (vkK N t - 1) : ℕ)) : ℝ) / (N - 1) ^ (vkK N t)

/-- `H = μ^{-1/k}`. -/
noncomputable def vkH (N t : ℝ) : ℝ := (vkMu N t) ^ (-(1/((vkK N t : ℕ) : ℝ)))

/-- The logarithmic error accumulated by the reduction: the exponent of the multiplicative factor
`exp (C₀k³) · (14 k² · 56 K 4^k (k-1)!)^(1/(2s)) · exp (C₁ (k-1) r (1 + log((k-1)r))/2)` that
multiplies `N^{1-δ_avail}` in the main estimate. -/
noncomputable def vkLogErr (C0 C1 K N t : ℝ) : ℝ :=
  C0 * ((vkK N t : ℕ) : ℝ)^3
    + C1 * ((((vkK N t - 1 : ℕ) : ℝ) * ((vkR N t : ℕ) : ℝ)) *
        (1 + Real.log ((((vkK N t - 1 : ℕ) : ℝ) * ((vkR N t : ℕ) : ℝ))))) / 2
    + Real.log (14 * ((vkK N t : ℕ) : ℝ)^2)
    + Real.log (56 * K * (4 : ℝ) ^ ((vkK N t : ℕ)) * (((Nat.factorial (vkK N t - 1) : ℕ)) : ℝ))
        / (2 * ((vkS N t : ℕ) : ℝ))

/-- `δ_req = c (log N/log t)²/log(λ+2)`. -/
noncomputable def vkDelta (c N t : ℝ) : ℝ :=
  c * (Real.log N / Real.log t)^2 / Real.log (vkLam N t + 2)

/-- `δ_avail = (λ/k - (1-λ/k)η)/(2s)`. -/
noncomputable def vkDeltaA (N t : ℝ) : ℝ :=
  (vkLam N t / ((vkK N t : ℕ) : ℝ) - (1 - vkLam N t / ((vkK N t : ℕ) : ℝ)) * vkEta N t) /
    (2 * ((vkS N t : ℕ) : ℝ))

/-- The logarithmic phase of the block sum, as a function of the shift `x`:
`blkPh L t u x = -(t log (L + x + u))/(2π)`.  With `n = L + i` the summand `(n+u)^{-it}` of the
target equals `e(blkPh L t u i)`. -/
noncomputable def blkPh (L : ℕ) (t u : ℝ) : ℝ → ℝ :=
  fun x => -(t * Real.log ((L : ℝ) + x + u)) / (2 * Real.pi)

lemma blkPh_arg_pos (L : ℕ) {u x : ℝ} (hu : 0 < u) (hx : 0 ≤ x) :
    0 < (L : ℝ) + x + u := by
  have hL : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  linarith

/-- The summand `(n+u)^{-it}` with `n = L + i` is `e(blkPh L t u i)`. -/
lemma cpow_eq_blkPh (L n : ℕ) (t u : ℝ) (hu : 0 < u) (hL : L ≤ n) (hn : 1 ≤ n) :
    ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))
      = Complex.exp ((↑(2 * Real.pi * blkPh L t u ((n - L : ℕ) : ℝ)) : ℂ) * Complex.I) := by
  have hnpos : (0 : ℝ) < (n : ℝ) + u := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have harg : (L : ℝ) + ((n - L : ℕ) : ℝ) + u = (n : ℝ) + u := by
    rw [Nat.cast_sub hL]; ring
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (ne_of_gt hnpos)),
      ← Complex.ofReal_log (le_of_lt hnpos)]
  rw [blkPh, harg]
  congr 1
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  field_simp

/-- Reindexing a block sum over `(L, L']` by the shift `i = n - L ∈ [1, L' - L]`. -/
lemma sum_Ioc_eq_sum_Icc_sub (L L' : ℕ) (f : ℕ → ℂ) :
    ∑ n ∈ Finset.Ioc L L', f n = ∑ i ∈ Finset.Icc 1 (L' - L), f (L + i) := by
  have hIoc : Finset.Ioc L L' = Finset.Ico (L + 1) (L' + 1) := by
    ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
  have hIcc : Finset.Icc 1 (L' - L) = Finset.Ico 1 ((L' - L) + 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIoc, hIcc, Finset.sum_Ico_eq_sum_range f (L + 1) (L' + 1),
    Finset.sum_Ico_eq_sum_range (fun i => f (L + i)) 1 ((L' - L) + 1)]
  have e1 : L' + 1 - (L + 1) = L' - L := by omega
  have e2 : (L' - L) + 1 - 1 = L' - L := by omega
  rw [e1, e2]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  omega

/-- Cross-multiplied form of a quotient comparison (the `div_le_div_iff` of older libraries). -/lemma div_le_div_of_mul_le {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d) (h : a * d ≤ c * b) :
    a / b ≤ c / d := by
  rw [div_le_iff₀ hb, div_mul_eq_mul_div, le_div_iff₀ hd]
  exact h

lemma vkLam_ge_one {N t : ℝ} (hN : 2 ≤ N) (hNt : N ≤ t) : 1 ≤ vkLam N t := by
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  rw [vkLam, one_le_div hlogN]
  exact Real.log_le_log (by linarith) hNt

lemma vkLam_pos {N t : ℝ} (hN : 2 ≤ N) (hNt : N ≤ t) : 0 < vkLam N t :=
  lt_of_lt_of_le one_pos (vkLam_ge_one hN hNt)

/-- `4λ + 2 ≤ k ≤ 4λ + 4`. -/
lemma vkK_bounds {N t : ℝ} (hN : 2 ≤ N) (hNt : N ≤ t) :
    4 * vkLam N t + 2 ≤ ((vkK N t : ℕ) : ℝ) ∧ ((vkK N t : ℕ) : ℝ) ≤ 4 * vkLam N t + 4 := by
  have hlam : 0 < vkLam N t := vkLam_pos hN hNt
  have h1 : 2 * vkLam N t ≤ ((⌈2 * vkLam N t⌉₊ : ℕ) : ℝ) := Nat.le_ceil (2 * vkLam N t)
  have h2 : ((⌈2 * vkLam N t⌉₊ : ℕ) : ℝ) < 2 * vkLam N t + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  constructor
  · rw [vkK]; push_cast; linarith
  · rw [vkK]; push_cast; linarith

lemma vkK_ge_six {N t : ℝ} (hN : 2 ≤ N) (hNt : N ≤ t) : 6 ≤ vkK N t := by
  have hlam : 1 ≤ vkLam N t := vkLam_ge_one hN hNt
  have h1 : (2 : ℕ) ≤ ⌈2 * vkLam N t⌉₊ := by
    have h2 : (2 : ℝ) ≤ ((⌈2 * vkLam N t⌉₊ : ℕ) : ℝ) :=
      le_trans (by linarith) (Nat.le_ceil (2 * vkLam N t))
    exact_mod_cast h2
  rw [vkK]
  omega

/-- `λ/k ≥ 1/8`. -/
lemma vkLam_div_k_ge {N t : ℝ} (hN : 2 ≤ N) (hNt : N ≤ t) :
    (1 : ℝ) / 8 ≤ vkLam N t / ((vkK N t : ℕ) : ℝ) := by
  obtain ⟨h1, h2⟩ := vkK_bounds hN hNt
  have hlam : 1 ≤ vkLam N t := vkLam_ge_one hN hNt
  have hk : (0 : ℝ) < ((vkK N t : ℕ) : ℝ) := by linarith
  rw [le_div_iff₀ hk]
  nlinarith [h1, hlam]

/-- `r ≥ 4 k log k`. -/
lemma vkR_ge {N t : ℝ} :
    (4 : ℝ) * ((vkK N t : ℕ) : ℝ) * Real.log ((vkK N t : ℕ) : ℝ) ≤ (vkR N t : ℝ) := by
  have := Nat.le_ceil ((4 : ℝ) * ((vkK N t : ℕ) : ℝ) * Real.log ((vkK N t : ℕ) : ℝ))
  rw [vkR]; push_cast; linarith

/-- `r ≤ 4 k log k + 2`. -/
lemma vkR_le {N t : ℝ} (hN : 2 ≤ N) (hNt : N ≤ t) :
    (vkR N t : ℝ) ≤ 4 * ((vkK N t : ℕ) : ℝ) * Real.log ((vkK N t : ℕ) : ℝ) + 2 := by
  have hk1 : (1 : ℝ) < ((vkK N t : ℕ) : ℝ) := by
    have := vkK_ge_six hN hNt
    exact_mod_cast (by omega : 1 < vkK N t)
  have hnn : (0 : ℝ) ≤ (4 : ℝ) * ((vkK N t : ℕ) : ℝ) * Real.log ((vkK N t : ℕ) : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (by positivity)) (Real.log_pos hk1).le
  have := Nat.ceil_lt_add_one hnn
  rw [vkR]; push_cast; linarith

/-- `exp (-(4 log k)) = (k^4)⁻¹`. -/
lemma exp_neg_four_log (k : ℕ) (hk : 0 < k) :
    Real.exp (-(4 * Real.log (k : ℝ))) = (((k : ℝ) ^ 4))⁻¹ := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h1 : -(4 * Real.log (k : ℝ)) = (4 : ℕ) * (-(Real.log (k : ℝ))) := by push_cast; ring
  rw [h1, Real.exp_nat_mul, Real.exp_neg, Real.exp_log hk0]
  exact inv_pow (k : ℝ) 4

/-- The numeric core of `η ≤ 1/(2k²)`: `((k-1)²/2)·(k^4)⁻¹ ≤ 1/(2k²)`. -/
lemma eta_numeric (k : ℕ) (hk : 2 ≤ k) :
    (((k - 1 : ℕ) : ℝ)^2 / 2) * (((k : ℝ)^4)⁻¹) ≤ 1 / (2 * (k : ℝ)^2) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by
    have : 0 < k := by omega
    exact_mod_cast this
  have hk1 : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]; push_cast; linarith
  have hsq : (((k - 1 : ℕ) : ℝ))^2 ≤ (k : ℝ)^2 :=
    pow_le_pow_left₀ (by positivity) hk1 2
  rw [inv_eq_one_div, div_mul_eq_mul_div]
  refine div_le_div_of_mul_le (by norm_num) (by positivity) ?_
  have hkey : (((k - 1 : ℕ) : ℝ)^2 * (1 / (k : ℝ)^4)) * (2 * (k : ℝ)^2)
      = 2 * ((((k - 1 : ℕ) : ℝ))^2 / (k : ℝ)^2) := by
    field_simp
  rw [hkey]
  have h2 : ((((k - 1 : ℕ) : ℝ))^2 / (k : ℝ)^2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact hsq
  linarith

/-- `η ≤ 1/(2k²)`. -/
lemma vkEta_le {N t : ℝ} (hN : 2 ≤ N) (hNt : N ≤ t) :
    vkEta N t ≤ 1 / (2 * ((vkK N t : ℕ) : ℝ)^2) := by
  have hk6 : 6 ≤ vkK N t := vkK_ge_six hN hNt
  have hk6r : (6 : ℝ) ≤ ((vkK N t : ℕ) : ℝ) := by exact_mod_cast hk6
  have hm2 : (2 : ℝ) ≤ (((vkK N t - 1 : ℕ)) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ vkK N t)]; push_cast; linarith
  have hmpos : (0 : ℝ) < (((vkK N t - 1 : ℕ)) : ℝ) := by linarith
  have hkpos : (0 : ℝ) < ((vkK N t : ℕ) : ℝ) := by linarith
  have hk1 : ((vkK N t - 1 : ℕ) : ℝ) ≤ ((vkK N t : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ vkK N t)]; push_cast; linarith
  have hlogk : 0 < Real.log ((vkK N t : ℕ) : ℝ) := Real.log_pos (by linarith)
  -- the geometric power is bounded by `k^-4`
  have hstep1 : (1 - 1/(((vkK N t - 1 : ℕ)) : ℝ))^(vkR N t)
      ≤ Real.exp (-((vkR N t : ℝ)/(((vkK N t - 1 : ℕ)) : ℝ))) := by
    have hbase : 0 ≤ 1 - 1/(((vkK N t - 1 : ℕ)) : ℝ) := by
      rw [sub_nonneg, div_le_one hmpos]; linarith
    calc (1 - 1/(((vkK N t - 1 : ℕ)) : ℝ))^(vkR N t)
        ≤ (Real.exp (-(1/(((vkK N t - 1 : ℕ)) : ℝ))))^(vkR N t) :=
          pow_le_pow_left₀ hbase (Real.one_sub_le_exp_neg _) _
      _ = Real.exp (-((vkR N t : ℝ)/(((vkK N t - 1 : ℕ)) : ℝ))) := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp
  have hstep2 : Real.exp (-((vkR N t : ℝ)/(((vkK N t - 1 : ℕ)) : ℝ)))
      ≤ Real.exp (-(4 * Real.log ((vkK N t : ℕ) : ℝ))) := by
    apply Real.exp_le_exp.mpr
    rw [neg_le_neg_iff, le_div_iff₀ hmpos]
    calc 4 * Real.log ((vkK N t : ℕ) : ℝ) * (((vkK N t - 1 : ℕ)) : ℝ)
        ≤ 4 * Real.log ((vkK N t : ℕ) : ℝ) * ((vkK N t : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hk1 (by positivity)
      _ = 4 * ((vkK N t : ℕ) : ℝ) * Real.log ((vkK N t : ℕ) : ℝ) := by ring
      _ ≤ (vkR N t : ℝ) := vkR_ge
  rw [vkEta]
  refine le_trans (mul_le_mul_of_nonneg_left (le_trans hstep1 hstep2) (by positivity)) ?_
  rw [exp_neg_four_log _ (by omega : 0 < vkK N t)]
  exact eta_numeric (vkK N t) (by omega : 2 ≤ vkK N t)

/-- `δ_avail ≥ 1/(18 s)`. -/
lemma vkDeltaA_ge {N t : ℝ} (hN : 2 ≤ N) (hNt : N ≤ t) :
    1 / (18 * ((vkS N t : ℕ) : ℝ)) ≤ vkDeltaA N t := by
  have hlk := vkLam_div_k_ge hN hNt
  have hk6 : 6 ≤ vkK N t := vkK_ge_six hN hNt
  have hk6r : (6 : ℝ) ≤ ((vkK N t : ℕ) : ℝ) := by exact_mod_cast hk6
  have hkpos : (0 : ℝ) < ((vkK N t : ℕ) : ℝ) := by linarith
  have hmpos : (0 : ℝ) < (((vkK N t - 1 : ℕ)) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ vkK N t)]; push_cast; linarith
  have heta72 : vkEta N t ≤ 1/72 := by
    refine le_trans (vkEta_le hN hNt) ?_
    refine div_le_div_of_mul_le (a := 1) (b := 2 * ((vkK N t : ℕ) : ℝ)^2) (c := 1) (d := 72)
      (by positivity) (by norm_num) ?_
    nlinarith [hk6r]
  have heta0 : 0 ≤ vkEta N t := by
    rw [vkEta]
    refine mul_nonneg (by positivity) (pow_nonneg ?_ _)
    rw [sub_nonneg, div_le_one hmpos]
    have h1 : (1 : ℝ) ≤ (((vkK N t - 1 : ℕ)) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ vkK N t)]; push_cast; linarith
    linarith
  have hprod : (1 - vkLam N t / ((vkK N t : ℕ) : ℝ)) * vkEta N t ≤ 1 * (1/72) := by
    refine mul_le_mul ?_ heta72 heta0 (by norm_num)
    have : 0 ≤ vkLam N t / ((vkK N t : ℕ) : ℝ) := by positivity
    linarith
  have hkey : (1 : ℝ)/9 ≤
      vkLam N t / ((vkK N t : ℕ) : ℝ)
        - (1 - vkLam N t / ((vkK N t : ℕ) : ℝ)) * vkEta N t := by
    linarith [hlk, hprod]
  have hs1 : (1 : ℝ) ≤ ((vkS N t : ℕ) : ℝ) := by
    have h1 : 1 ≤ vkK N t - 1 := by omega
    have h2 : 1 ≤ vkR N t := by rw [vkR]; omega
    have h3 : 1 ≤ vkS N t := by
      rw [vkS]
      calc (1 : ℕ) = 1 * 1 := by ring
        _ ≤ (vkK N t - 1) * vkR N t := Nat.mul_le_mul h1 h2
    exact_mod_cast h3
  have hsne : (((vkS N t : ℕ) : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < ((vkS N t : ℕ) : ℝ) := by linarith
    exact ne_of_gt this
  rw [vkDeltaA]
  refine div_le_div_of_mul_le (a := 1) (b := 18 * ((vkS N t : ℕ) : ℝ))
    (c := vkLam N t / ((vkK N t : ℕ) : ℝ)
      - (1 - vkLam N t / ((vkK N t : ℕ) : ℝ)) * vkEta N t)
    (d := 2 * ((vkS N t : ℕ) : ℝ)) (by positivity) (by positivity) ?_
  have hmul : (1/9) * (18 * ((vkS N t : ℕ) : ℝ))
      ≤ (vkLam N t / ((vkK N t : ℕ) : ℝ)
          - (1 - vkLam N t / ((vkK N t : ℕ) : ℝ)) * vkEta N t) * (18 * ((vkS N t : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_right hkey (by positivity)
  have hL : (1 / (18 * ((vkS N t : ℕ) : ℝ))) * (2 * ((vkS N t : ℕ) : ℝ)) = 1/9 := by
    field_simp
    ring
  have hR : (1/9) * (18 * ((vkS N t : ℕ) : ℝ)) = 2 * ((vkS N t : ℕ) : ℝ) := by ring
  linarith [hmul, hL, hR]

end

end Work.BMF
