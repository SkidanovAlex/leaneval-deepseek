import Mathlib

open Filter

namespace Work.ZeroFreeTables.P9

/-!
# Absorption of the P9 error bracket, eventually

The estimate `absorption_eventual` says that, for `q` large, the slowly varying
bracket of error terms occurring in the `P9` engine is bounded by any prescribed
positive number `a * ε / 2`.  Since

* `1 / log q → 0`,
* `1 / (log q)^k → 0` for `k ≥ 1`,
* `(log (log q))^j / (log q)^m → 0` for `m ≥ 1` (the classical sub-polynomial
  growth of iterated logarithms),

the whole bracket tends to `0`, and the claim follows from the definition of
convergence.

The only non-trivial analytic input is the Mathlib fact
`Real.tendsto_pow_log_div_mul_add_atTop`: `(log x)^n / (a * x + b) → 0` as
`x → ∞`; everything else is elementary.
-/

/-- `(log u)^k / u^m → 0` as `u → ∞`, for every `m ≥ 1`. -/
lemma tendsto_log_pow_div_pow (k m : ℕ) (hm : 1 ≤ m) :
    Filter.Tendsto (fun u : ℝ => Real.log u ^ k / u ^ m) Filter.atTop (nhds 0) := by
  -- `(log u)^k / u → 0`
  have h1 : Filter.Tendsto (fun u : ℝ => Real.log u ^ k / u) Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 k one_ne_zero
  rcases eq_or_lt_of_le hm with h | h
  · -- `m = 1`
    subst h
    simpa using h1
  · -- `m ≥ 2`: split off one factor `1 / u` and use `u^(m-1) → ∞`
    have hm1 : m - 1 ≠ 0 := by omega
    have h2 : Filter.Tendsto (fun u : ℝ => (u ^ (m - 1))⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (Filter.tendsto_pow_atTop hm1)
    have h3 : Filter.Tendsto (fun u : ℝ => (Real.log u ^ k / u) * (u ^ (m - 1))⁻¹)
        Filter.atTop (nhds 0) := by
      simpa using h1.mul h2
    refine h3.congr' ?_
    filter_upwards with u
    rw [← div_eq_mul_inv, div_div, ← pow_succ', Nat.sub_add_cancel hm]

/-- The bracket of error terms absorbed in `P9`, as a function of `q`. -/
noncomputable def Brack (aup δ C₀ Ct Cn Cz Cc Cp : ℝ) (q : ℕ) : ℝ :=
  (aup / Real.log q) * C₀
    + (aup ^ 2 / (Real.log q) ^ 2) * ((1 + 4 / δ ^ 2) * (Cn * (Real.log q + 6) + Cz) + Ct)
    + (2 / 3) * (aup ^ 3 / (Real.log q) ^ 3)
        * ((2 / δ) * (1 + 4 / δ ^ 2) * (Cn * (Real.log q + 6) + Cz) + Ct)
    + (Cc / Real.log q) * (aup * Cp * (Real.log (Real.log q)) ^ 2
        + (aup ^ 2 / Real.log q) * Cp * (Real.log (Real.log q)) ^ 3
        + (aup ^ 3 / (Real.log q) ^ 2) * Cp * (Real.log (Real.log q)) ^ 4)
    + 64 * aup / (δ * Real.log q)

/-- The bracket tends to `0` as `q → ∞`. -/
lemma tendsto_Brack (aup δ C₀ Ct Cn Cz Cc Cp : ℝ) (hδ : δ ≠ 0) :
    Filter.Tendsto (fun q : ℕ => Brack aup δ C₀ Ct Cn Cz Cc Cp q) Filter.atTop (nhds 0) := by
  have hlog : Filter.Tendsto (fun q : ℕ => Real.log q) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Filter.Tendsto (fun q : ℕ => (Real.log q)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hlog
  -- the five atoms of the bracket
  have hT1 : Filter.Tendsto (fun q : ℕ =>
      (aup * C₀ + aup ^ 2 * (1 + 4 / δ ^ 2) * Cn + 64 * aup / δ) / Real.log q)
      Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hlog
  have hT2 : Filter.Tendsto (fun q : ℕ =>
      (6 * (aup ^ 2 * (1 + 4 / δ ^ 2) * Cn) + aup ^ 2 * (1 + 4 / δ ^ 2) * Cz + aup ^ 2 * Ct
        + (2 / 3) * aup ^ 3 * (2 / δ) * (1 + 4 / δ ^ 2) * Cn) / (Real.log q) ^ 2)
      Filter.atTop (nhds 0) := by
    have h := (hinv.pow 2).const_mul (6 * (aup ^ 2 * (1 + 4 / δ ^ 2) * Cn)
      + aup ^ 2 * (1 + 4 / δ ^ 2) * Cz + aup ^ 2 * Ct
      + (2 / 3) * aup ^ 3 * (2 / δ) * (1 + 4 / δ ^ 2) * Cn)
    simpa [div_eq_mul_inv, inv_pow] using h
  have hT3 : Filter.Tendsto (fun q : ℕ =>
      ((2 / 3) * aup ^ 3 * (2 / δ) * (1 + 4 / δ ^ 2) * Cz + (2 / 3) * aup ^ 3 * Ct
        + 6 * ((2 / 3) * aup ^ 3 * (2 / δ) * (1 + 4 / δ ^ 2) * Cn)) / (Real.log q) ^ 3)
      Filter.atTop (nhds 0) := by
    have h := (hinv.pow 3).const_mul ((2 / 3) * aup ^ 3 * (2 / δ) * (1 + 4 / δ ^ 2) * Cz
      + (2 / 3) * aup ^ 3 * Ct + 6 * ((2 / 3) * aup ^ 3 * (2 / δ) * (1 + 4 / δ ^ 2) * Cn))
    simpa [div_eq_mul_inv, inv_pow] using h
  have hT4 : Filter.Tendsto (fun q : ℕ =>
      Cc * aup * Cp * (Real.log (Real.log q)) ^ 2 / Real.log q) Filter.atTop (nhds 0) := by
    have h := ((tendsto_log_pow_div_pow 2 1 le_rfl).comp hlog).const_mul (Cc * aup * Cp)
    simpa [mul_div_assoc] using h
  have hT5 : Filter.Tendsto (fun q : ℕ =>
      Cc * aup ^ 2 * Cp * (Real.log (Real.log q)) ^ 3 / (Real.log q) ^ 2)
      Filter.atTop (nhds 0) := by
    have h := ((tendsto_log_pow_div_pow 3 2 (by norm_num)).comp hlog).const_mul (Cc * aup ^ 2 * Cp)
    simpa [mul_div_assoc] using h
  have hT6 : Filter.Tendsto (fun q : ℕ =>
      Cc * aup ^ 3 * Cp * (Real.log (Real.log q)) ^ 4 / (Real.log q) ^ 3)
      Filter.atTop (nhds 0) := by
    have h := ((tendsto_log_pow_div_pow 4 3 (by norm_num)).comp hlog).const_mul (Cc * aup ^ 3 * Cp)
    simpa [mul_div_assoc] using h
  -- the expanded bracket
  have hE : Filter.Tendsto (fun q : ℕ =>
      (aup * C₀ + aup ^ 2 * (1 + 4 / δ ^ 2) * Cn + 64 * aup / δ) / Real.log q
      + (6 * (aup ^ 2 * (1 + 4 / δ ^ 2) * Cn) + aup ^ 2 * (1 + 4 / δ ^ 2) * Cz + aup ^ 2 * Ct
        + (2 / 3) * aup ^ 3 * (2 / δ) * (1 + 4 / δ ^ 2) * Cn) / (Real.log q) ^ 2
      + ((2 / 3) * aup ^ 3 * (2 / δ) * (1 + 4 / δ ^ 2) * Cz + (2 / 3) * aup ^ 3 * Ct
        + 6 * ((2 / 3) * aup ^ 3 * (2 / δ) * (1 + 4 / δ ^ 2) * Cn)) / (Real.log q) ^ 3
      + Cc * aup * Cp * (Real.log (Real.log q)) ^ 2 / Real.log q
      + Cc * aup ^ 2 * Cp * (Real.log (Real.log q)) ^ 3 / (Real.log q) ^ 2
      + Cc * aup ^ 3 * Cp * (Real.log (Real.log q)) ^ 4 / (Real.log q) ^ 3)
      Filter.atTop (nhds 0) := by
    have hh := ((((hT1.add hT2).add hT3).add hT4).add hT5).add hT6
    simpa using hh
  refine hE.congr' ?_
  filter_upwards [eventually_ge_atTop 3] with q hq
  have hL : Real.log q ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < q by omega)))
  unfold Brack
  field_simp
  ring

theorem absorption_eventual (a K ε aup δ C₀ Ct Cn Cz Cc Cp : ℝ)
    (ha : 0 < a) (hK : 0 ≤ K) (hε : 0 < ε) (hδ : 0 < δ) (haup : 0 < aup)
    (hC₀ : 0 ≤ C₀) (hCt : 0 < Ct) (hCn : 0 < Cn) (hCz : 0 < Cz) (hCc : 0 ≤ Cc) (hCp : 0 ≤ Cp) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      2 * (K + 1) ^ 2 * ((aup / Real.log q) * C₀
        + (aup ^ 2 / (Real.log q) ^ 2) * ((1 + 4 / δ ^ 2) * (Cn * (Real.log q + 6) + Cz) + Ct)
        + (2 / 3) * (aup ^ 3 / (Real.log q) ^ 3)
            * ((2 / δ) * (1 + 4 / δ ^ 2) * (Cn * (Real.log q + 6) + Cz) + Ct)
        + (Cc / Real.log q) * (aup * Cp * (Real.log (Real.log q)) ^ 2
            + (aup ^ 2 / Real.log q) * Cp * (Real.log (Real.log q)) ^ 3
            + (aup ^ 3 / (Real.log q) ^ 2) * Cp * (Real.log (Real.log q)) ^ 4)
        + 64 * aup / (δ * Real.log q)) ≤ a * ε / 2 := by
  have hεa : 0 < a * ε / 2 := by positivity
  have hB : Filter.Tendsto (fun q : ℕ => Brack aup δ C₀ Ct Cn Cz Cc Cp q) Filter.atTop (nhds 0) :=
    tendsto_Brack aup δ C₀ Ct Cn Cz Cc Cp (ne_of_gt hδ)
  have htot : Filter.Tendsto
      (fun q : ℕ => 2 * (K + 1) ^ 2 * Brack aup δ C₀ Ct Cn Cz Cc Cp q) Filter.atTop (nhds 0) := by
    simpa using hB.const_mul (2 * (K + 1) ^ 2)
  have hkey : ∀ᶠ q : ℕ in Filter.atTop,
      2 * (K + 1) ^ 2 * Brack aup δ C₀ Ct Cn Cz Cc Cp q < a * ε / 2 :=
    Filter.Tendsto.eventually_lt_const hεa htot
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.mp hkey
  exact ⟨q₀, fun q hq => le_of_lt (hq₀ q hq)⟩

end Work.ZeroFreeTables.P9
