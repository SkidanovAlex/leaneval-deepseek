import Mathlib

/-!
# The off-arc `(1/2)`-splitting estimate

`offArc_numeric` is the elementary "eventually exponential beats polynomial" bookkeeping lemma
used when the minor-arc contribution is split as

`A · 2^σ · (n^{L-1})^{-σ}  +  Cg · 2^{-n c₀}  ≤  (n+1)^{-α}`

for all large `n`: the first summand is a *polynomial* (inverse) power, the second a geometric
decay, and the hypothesis `α + 1 ≤ (L - 1) σ` says exactly that the polynomial summand decays
strictly faster than `(n+1)^{-α}`.  Each of the two summands is shown to be `≤ (1/2)(n+1)^{-α}`
for large `n`, and the results are added.

* the polynomial half is elementary: `n^{-(L-1)σ} ≤ n^{-(α+1)}` because `(L-1)σ ≥ α+1`, and
  `n^{-1} n^{-α} ≤ (1/2)(n+1)^{-α}` as soon as `n ≥ 2A 2^{σ+α}` (using `n + 1 ≤ 2n`);
* the geometric half is the classical `x^α 2^{-cx} → 0`, taken from Mathlib's
  `isLittleO_rpow_exp_pos_mul_atTop`.
-/

namespace Work.BourgainPlan.Maximal

/-- For `n ≥ 1`, `(n+1)^α ≤ 2^α n^α`. -/
private lemma add_one_rpow_le {n α : ℝ} (hn : 1 ≤ n) (hα : 0 ≤ α) :
    (n + 1) ^ α ≤ (2:ℝ) ^ α * n ^ α := by
  have hn0 : 0 ≤ n := by linarith
  have h1 : n + 1 ≤ 2 * n := by linarith
  calc (n + 1) ^ α ≤ (2 * n) ^ α := Real.rpow_le_rpow (by linarith) h1 hα
    _ = (2:ℝ) ^ α * n ^ α := Real.mul_rpow (by norm_num) hn0

/-- For `n ≥ 1` and `α > 0`, `n^{-α} ≤ 2^α (n+1)^{-α}`. -/
private lemma rpow_neg_le_two_rpow_mul {n α : ℝ} (hn : 1 ≤ n) (hα : 0 < α) :
    n ^ (-α) ≤ (2:ℝ) ^ α * (n + 1) ^ (-α) := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hn10 : 0 < n + 1 := by linarith
  have h := add_one_rpow_le hn hα.le
  have hp1 : 0 < (n + 1) ^ α := Real.rpow_pos_of_pos hn10 α
  have h2 : 1 / ((2:ℝ) ^ α * n ^ α) ≤ 1 / ((n + 1) ^ α) := one_div_le_one_div_of_le hp1 h
  rw [one_div, one_div, mul_inv, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) α,
      ← Real.rpow_neg hn0.le α, ← Real.rpow_neg hn10.le α] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ (2:ℝ) ^ α)
  have he : (2:ℝ) ^ α * ((2:ℝ) ^ (-α) * n ^ (-α)) = n ^ (-α) := by
    rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0:ℝ) < 2), add_neg_cancel, Real.rpow_zero,
      one_mul]
  rw [he] at h3
  exact h3

/-- The polynomial half: if `α + 1 ≤ m σ` then `A 2^σ (n^m)^{-σ} ≤ (1/2)(n+1)^{-α}` for all
sufficiently large `n`. -/
private lemma eventually_term1 (A σ α : ℝ) (m : ℕ) (hA : 0 < A) (hα : 0 < α)
    (hLσ : α + 1 ≤ (m:ℝ) * σ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      A * (2:ℝ)^σ * (((n:ℝ)^m)^(-σ)) ≤ (1/2) * ((n:ℝ)+1)^(-α) := by
  refine ⟨max 1 ⌈2 * A * (2:ℝ)^(σ+α)⌉₊, fun n hn => ?_⟩
  have hn1n : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hB : 2 * A * (2:ℝ)^(σ+α) ≤ (n:ℝ) :=
    Nat.ceil_le.mp (le_trans (le_max_right _ _) hn)
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1n
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith
  have e1 : (((n:ℝ)^m)^(-σ)) = (n:ℝ)^(-((m:ℝ)*σ)) := by
    rw [← Real.rpow_natCast (n:ℝ) m, ← Real.rpow_mul (le_of_lt hnpos)]
    congr 1
    ring
  rw [e1]
  have hstep1 : (n:ℝ)^(-((m:ℝ)*σ)) ≤ (n:ℝ)^(-(α+1)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hstep2 : A * (2:ℝ)^σ * (n:ℝ)^(-((m:ℝ)*σ)) ≤ A * (2:ℝ)^σ * (n:ℝ)^(-(α+1)) :=
    mul_le_mul_of_nonneg_left hstep1 (by positivity)
  have hna : (n:ℝ)^(-α) ≤ (2:ℝ)^α * ((n:ℝ)+1)^(-α) := rpow_neg_le_two_rpow_mul hn1 hα
  have hsplit : (n:ℝ)^(-(α+1)) = (n:ℝ)^(-α) * (n:ℝ)⁻¹ := by
    rw [← Real.rpow_neg_one (n:ℝ), ← Real.rpow_add hnpos (-α) (-1 : ℝ)]
    congr 1
    ring
  have hstep3 : A * (2:ℝ)^σ * (n:ℝ)^(-(α+1))
      ≤ (A * (2:ℝ)^σ * (2:ℝ)^α / (n:ℝ)) * ((n:ℝ)+1)^(-α) := by
    rw [hsplit]
    have h2 := mul_le_mul_of_nonneg_right hna (by positivity : (0:ℝ) ≤ (n:ℝ)⁻¹)
    calc A * (2:ℝ)^σ * ((n:ℝ)^(-α) * (n:ℝ)⁻¹)
        ≤ A * (2:ℝ)^σ * (((2:ℝ)^α * ((n:ℝ)+1)^(-α)) * (n:ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (A * (2:ℝ)^σ * (2:ℝ)^α / (n:ℝ)) * ((n:ℝ)+1)^(-α) := by
          rw [div_eq_mul_inv]
          ring
  have hcoef : A * (2:ℝ)^σ * (2:ℝ)^α / (n:ℝ) ≤ 1/2 := by
    rw [div_le_iff₀ hnpos]
    have hB' : 2 * (A * (2:ℝ)^σ * (2:ℝ)^α) ≤ (n:ℝ) := by
      have := hB
      rw [Real.rpow_add (by norm_num : (0:ℝ) < 2) σ α] at this
      nlinarith
    linarith
  have hstep4 : (A * (2:ℝ)^σ * (2:ℝ)^α / (n:ℝ)) * ((n:ℝ)+1)^(-α)
      ≤ (1/2) * ((n:ℝ)+1)^(-α) :=
    mul_le_mul_of_nonneg_right hcoef (by positivity)
  linarith [hstep2, hstep3, hstep4]

/-- The geometric half: `Cg · 2^{-n c} ≤ (1/2)(n+1)^{-α}` for all sufficiently large `n`. -/
private lemma eventually_term2 (Cg c α : ℝ) (hCg : 0 < Cg) (hc : 0 < c) (hα : 0 < α) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Cg * (2:ℝ)^(-(n:ℝ)*c) ≤ (1/2) * ((n:ℝ)+1)^(-α) := by
  have hb : 0 < c * Real.log 2 := mul_pos hc (Real.log_pos one_lt_two)
  have hlittle := (isLittleO_rpow_exp_pos_mul_atTop α hb).comp_tendsto
    (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n:ℝ)) Filter.atTop Filter.atTop)
  rw [Asymptotics.isLittleO_iff] at hlittle
  have hc' : 0 < 1 / (2 * Cg * (2:ℝ)^α) := by positivity
  have hev := hlittle hc'
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1n : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1n
  have h1 := hN n (le_trans (le_max_left _ _) hn)
  simp only [Function.comp_apply] at h1
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)) α),
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h1
  have hexp : Real.exp ((c * Real.log 2) * (n:ℝ)) = (2:ℝ)^((n:ℝ)*c) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  rw [hexp] at h1
  have h2 : ((n:ℝ)+1)^α ≤ (2:ℝ)^α * (n:ℝ)^α := add_one_rpow_le hn1 hα.le
  have hstep1 : Cg * (2:ℝ)^(-((n:ℝ)*c)) * ((n:ℝ)+1)^α
      ≤ Cg * (2:ℝ)^(-((n:ℝ)*c)) * ((2:ℝ)^α * (n:ℝ)^α) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have hstep2 : Cg * (2:ℝ)^(-((n:ℝ)*c)) * ((2:ℝ)^α * (n:ℝ)^α)
      ≤ Cg * (2:ℝ)^(-((n:ℝ)*c)) *
          ((2:ℝ)^α * ((1 / (2 * Cg * (2:ℝ)^α)) * (2:ℝ)^((n:ℝ)*c))) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hfin : Cg * (2:ℝ)^(-((n:ℝ)*c)) *
        ((2:ℝ)^α * ((1 / (2 * Cg * (2:ℝ)^α)) * (2:ℝ)^((n:ℝ)*c))) = 1/2 := by
    have h2a : (2:ℝ)^α ≠ 0 := (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) α).ne'
    have h2nc : (2:ℝ)^((n:ℝ)*c) ≠ 0 :=
      (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _).ne'
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    field_simp
    try ring
  have h3 : Cg * (2:ℝ)^(-((n:ℝ)*c)) * ((n:ℝ)+1)^α ≤ 1/2 := by
    calc Cg * (2:ℝ)^(-((n:ℝ)*c)) * ((n:ℝ)+1)^α
        ≤ Cg * (2:ℝ)^(-((n:ℝ)*c)) * ((2:ℝ)^α * (n:ℝ)^α) := hstep1
      _ ≤ Cg * (2:ℝ)^(-((n:ℝ)*c)) *
            ((2:ℝ)^α * ((1 / (2 * Cg * (2:ℝ)^α)) * (2:ℝ)^((n:ℝ)*c))) := hstep2
      _ = 1/2 := hfin
  have hprod : ((n:ℝ)+1)^α * ((n:ℝ)+1)^(-α) = 1 := by
    rw [← Real.rpow_add (by positivity : (0:ℝ) < (n:ℝ)+1), add_neg_cancel, Real.rpow_zero]
  have h4 := mul_le_mul_of_nonneg_right h3 (by positivity : (0:ℝ) ≤ ((n:ℝ)+1)^(-α))
  rw [mul_assoc, hprod, mul_one] at h4
  simpa only [neg_mul] using h4

/-- **Numeric off-arc estimate.**  For `A, σ, Cg, c₀, α > 0`, `1 ≤ L` and `α + 1 ≤ (L-1) σ`,
there is `N₀` such that for every `n ≥ N₀`,
`A 2^σ ((n^{L-1})^{-σ}) + Cg 2^{-n c₀} ≤ (n+1)^{-α}`. -/
theorem offArc_numeric (A σ Cg c₀ α : ℝ) (L : ℕ)
    (hA : 0 < A) (hσ : 0 < σ) (hCg : 0 < Cg) (hc₀ : 0 < c₀) (hα : 0 < α)
    (hL1 : 1 ≤ L) (hLσ : α + 1 ≤ ((L : ℝ) - 1) * σ) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      A * (2 : ℝ) ^ σ * (((n : ℝ) ^ (L - 1)) ^ (-σ)) + Cg * (2 : ℝ) ^ (-(n : ℝ) * c₀)
        ≤ ((n : ℝ) + 1) ^ (-α) := by
  have _hσpos : (0 : ℝ) < σ := hσ
  have hLσ' : α + 1 ≤ ((L - 1 : ℕ) : ℝ) * σ := by
    rw [Nat.cast_sub hL1]
    simpa using hLσ
  obtain ⟨N₁, h₁⟩ := eventually_term1 A σ α (L-1) hA hα hLσ'
  obtain ⟨N₂, h₂⟩ := eventually_term2 Cg c₀ α hCg hc₀ hα
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have e₁ := h₁ n hn₁
  have e₂ := h₂ n hn₂
  linarith

end Work.BourgainPlan.Maximal
