import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.n8_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

open Work.BMF

/-- Auxiliary analytic fact: for any real constants `A, C` and any `d > 0`, the linear-in-`P`
quantity `d (P / log P) log (P / 2)` eventually dominates `A + C log P`.  (The left factor
`P / log P` is `π₀(P)` in the notation of the paper, and `log (P/2) → ∞`, so the right-hand side
grows like `d P / 2` while the left-hand side only grows like `log P`.)

This isolates the "`exp` beats every power of `log X · X^{(3k+1)/δ}`" comparison needed in
`Work.N8.primes_big`. -/
theorem exists_le_mul_log_div (A C d : ℝ) (hd : 0 < d) :
    ∃ B : ℝ, ∀ P : ℝ, B ≤ P →
      A + C * Real.log P ≤ d * (P / Real.log P) * Real.log (P / 2) := by
  have hc0pos : 0 < d / (4 * (|C| + 1)) := by positivity
  have hlog : ∀ᶠ P : ℝ in Filter.atTop, Real.log P ≤ (d / (4 * (|C| + 1))) * P := by
    have h := Real.isLittleO_log_id_atTop.bound hc0pos
    filter_upwards [h, Filter.eventually_ge_atTop (1 : ℝ)] with P hP hP1
    simp only [id_eq, Real.norm_eq_abs] at hP
    rw [abs_of_nonneg (Real.log_nonneg hP1), abs_of_nonneg (by linarith : (0 : ℝ) ≤ P)] at hP
    exact hP
  obtain ⟨B0, hB0⟩ := Filter.eventually_atTop.1 hlog
  refine ⟨max B0 (max 4 (4 * A / d + 1)), ?_⟩
  intro P hP
  have hPB0 : B0 ≤ P := le_trans (le_max_left _ _) hP
  have hP4 : 4 ≤ P := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hP
  have hPA : 4 * A / d + 1 ≤ P := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hP
  have hPpos : 0 < P := by linarith
  have hlogPpos : 0 < Real.log P := Real.log_pos (by linarith)
  have hP2pos : 0 < P / 2 := by linarith
  have hlogB : Real.log P ≤ (d / (4 * (|C| + 1))) * P := hB0 P hPB0
  have hlogsplit : Real.log P = Real.log 2 + Real.log (P / 2) := by
    have h : P = 2 * (P / 2) := by ring
    calc Real.log P = Real.log (2 * (P / 2)) := congrArg Real.log h
      _ = Real.log 2 + Real.log (P / 2) := Real.log_mul (by norm_num) (ne_of_gt hP2pos)
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog2le : Real.log 2 ≤ Real.log P / 2 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by linarith : (4 : ℝ) ≤ P)
    rw [hlog4] at h
    linarith
  have hhalf : (1 / 2) * Real.log P ≤ Real.log (P / 2) := by linarith
  have hClogP : C * Real.log P ≤ d * P / 4 := by
    have hb : Real.log P ≤ d * P / (4 * (|C| + 1)) := by
      calc Real.log P ≤ (d / (4 * (|C| + 1))) * P := hlogB
        _ = d * P / (4 * (|C| + 1)) := by ring
    have hCnonneg : 0 ≤ |C| := abs_nonneg C
    calc C * Real.log P ≤ |C| * Real.log P :=
            mul_le_mul_of_nonneg_right (le_abs_self C) hlogPpos.le
      _ ≤ |C| * (d * P / (4 * (|C| + 1))) := mul_le_mul_of_nonneg_left hb hCnonneg
      _ = |C| / (|C| + 1) * (d * P / 4) := by field_simp
      _ ≤ 1 * (d * P / 4) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            rw [div_le_one (by linarith : (0 : ℝ) < |C| + 1)]
            linarith [hCnonneg]
      _ = d * P / 4 := by ring
  have hA : A ≤ d * P / 4 := by
    have h1 : 4 * A / d ≤ P := by linarith
    have h2 : (4 * A / d) * (d / 4) ≤ P * (d / 4) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : (4 * A / d) * (d / 4) = A := by field_simp
    have h4 : P * (d / 4) = d * P / 4 := by ring
    linarith [h2, h3, h4]
  have hmain : A + C * Real.log P ≤ d * P / 2 := by linarith
  have hRHS : d * P / 2 ≤ d * (P / Real.log P) * Real.log (P / 2) := by
    have h1 : (P / Real.log P) * ((1 / 2) * Real.log P) = P / 2 := by field_simp
    have h3 : (P / Real.log P) * ((1 / 2) * Real.log P) ≤
        (P / Real.log P) * Real.log (P / 2) :=
      mul_le_mul_of_nonneg_left hhalf (by positivity)
    calc d * P / 2 = d * ((P / Real.log P) * ((1 / 2) * Real.log P)) := by rw [h1]; ring
      _ ≤ d * ((P / Real.log P) * Real.log (P / 2)) := mul_le_mul_of_nonneg_left h3 hd.le
      _ = d * (P / Real.log P) * Real.log (P / 2) := by ring
  linarith [hmain, hRHS]

/-- Auxiliary fact: a product of natural numbers each at least `b ≥ 0` is at least `b ^ #Ps`. -/
theorem prod_ge_card_pow (b : ℝ) (Ps : Finset ℕ) (hb : 0 ≤ b) (hpr : ∀ p ∈ Ps, b ≤ (p : ℝ)) :
    b ^ Ps.card ≤ ∏ p ∈ Ps, (p : ℝ) := by
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun p hp => hb) (fun p hp => hpr p hp)

/-- **The certifying prime products are effectively infinite** (`Work.BMF.PrimesBig`).
Under the scale hypotheses `X^{ε²/2} ≤ P₂ ≤ X^ε` of the main theorem, the product of any set of at
least `δ¹² π₀(P₂)` primes in `[P₂/2, P₂]` dominates every polynomial-size quantity: it exceeds
`(k! X^{2k/δ})(2(k+1)δ⁻¹(X^{(k+1)/δ} + 1))`, for `X ≥ X₀(k, ε, δ)`.

Route: `∏𝒜 ≥ (P₂/2)^{#𝒜} ≥ (P₂/2)^{δ¹² π₀(P₂)}`, and
`log((P₂/2)^{δ¹² π₀(P₂)}) = δ¹² P₂ log(P₂/2)/log P₂ ≥ δ¹² P₂/2` for `P₂ ≥ 4`, so the product is at
least `exp(δ¹² X^{ε²/2}/2)`; compare with the polynomial threshold using
`exp` dominating powers of `log X · X^{(3k+1)/δ}` for large `X` (take `X₀ ≥ 1` and large enough that
`P₂ ≥ 4`, which follows from `P₂ ≥ X^{ε²/2}`). -/
theorem primes_big (k : ℕ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ X₀ : ℝ, ∀ (X P₂ : ℝ), X₀ ≤ X → X ^ (ε ^ 2 / 2) ≤ P₂ → P₂ ≤ X ^ ε →
      Work.BMF.PrimesBig k δ X P₂ := by
  have _ := hδ1
  have hdpos : 0 < δ ^ 12 := by positivity
  obtain ⟨B, hB⟩ := exists_le_mul_log_div
      (Real.log (k.factorial) + Real.log (4 * ((k : ℝ) + 1) * δ⁻¹))
      (((3 * (k : ℝ) + 1) / δ) * (2 / ε ^ 2)) (δ ^ 12) hdpos
  refine ⟨max 1 ((max B 4) ^ (2 / ε ^ 2)), ?_⟩
  intro X P₂ hX hPlow hPhigh
  have hX1 : 1 ≤ X := le_trans (le_max_left _ _) hX
  have hXc : (max B 4) ^ (2 / ε ^ 2) ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hmaxpos : 0 ≤ max B 4 := by positivity
  have hPge : max B 4 ≤ P₂ := by
    have h1 : ((max B 4) ^ (2 / ε ^ 2)) ^ (ε ^ 2 / 2) = max B 4 := by
      rw [← Real.rpow_mul hmaxpos]
      have htwo : 2 / ε ^ 2 * (ε ^ 2 / 2) = 1 := by field_simp
      rw [htwo, Real.rpow_one]
    calc max B 4 = ((max B 4) ^ (2 / ε ^ 2)) ^ (ε ^ 2 / 2) := h1.symm
      _ ≤ X ^ (ε ^ 2 / 2) := Real.rpow_le_rpow (Real.rpow_nonneg hmaxpos (2 / ε ^ 2)) hXc (by positivity)
      _ ≤ P₂ := hPlow
  have hPB : B ≤ P₂ := le_trans (le_max_left _ _) hPge
  have hP4 : 4 ≤ P₂ := le_trans (le_max_right _ _) hPge
  have hkey := hB P₂ hPB
  have hlogX : Real.log X ≤ (2 / ε ^ 2) * Real.log P₂ := by
    have hpos : 0 < X ^ (ε ^ 2 / 2) := Real.rpow_pos_of_pos hXpos _
    have h := Real.log_le_log hpos hPlow
    rw [Real.log_rpow hXpos] at h
    have hmul : (2 / ε ^ 2) * (ε ^ 2 / 2 * Real.log X) ≤ (2 / ε ^ 2) * Real.log P₂ :=
      mul_le_mul_of_nonneg_left h (by positivity)
    have heq : (2 / ε ^ 2) * (ε ^ 2 / 2 * Real.log X) = Real.log X := by field_simp
    linarith [hmul, heq]
  unfold Work.BMF.PrimesBig
  intro Ps hprime hcard
  unfold Work.BMF.Qprod
  unfold Work.BMF.IsPrimeIn at hprime
  have hP2pos : 0 < P₂ / 2 := by linarith
  have hbase : 1 ≤ P₂ / 2 := by linarith
  have hprod : (P₂ / 2) ^ Ps.card ≤ ∏ p ∈ Ps, (p : ℝ) :=
    prod_ge_card_pow (P₂ / 2) Ps (by linarith) (fun p hp => (hprime p hp).2.1)
  have hcard' : δ ^ 12 * (P₂ / Real.log P₂) ≤ (Ps.card : ℝ) := by
    have h := hcard
    unfold Work.BMF.pi0 at h
    exact h
  have hrpow : (P₂ / 2) ^ (δ ^ 12 * (P₂ / Real.log P₂)) ≤ (P₂ / 2) ^ Ps.card := by
    have h := Real.rpow_le_rpow_of_exponent_le hbase hcard'
    rwa [Real.rpow_natCast] at h
  have hthr : ((k.factorial : ℝ) * (X ^ (1 / δ)) ^ (2 * k)) *
        (2 * ((k : ℝ) + 1) * δ⁻¹ * ((X ^ (1 / δ)) ^ (k + 1) + 1))
      ≤ (P₂ / 2) ^ (δ ^ 12 * (P₂ / Real.log P₂)) := by
    have ha1 : 1 ≤ X ^ (1 / δ) := Real.one_le_rpow hX1 (by positivity)
    have hk1 : 1 ≤ (X ^ (1 / δ)) ^ (k + 1) := one_le_pow₀ ha1
    have hfac : ((X ^ (1 / δ)) ^ (k + 1) + 1) ≤ 2 * (X ^ (1 / δ)) ^ (k + 1) := by linarith
    have hBnd : ((k.factorial : ℝ) * (X ^ (1 / δ)) ^ (2 * k)) *
          (2 * ((k : ℝ) + 1) * δ⁻¹ * ((X ^ (1 / δ)) ^ (k + 1) + 1))
        ≤ ((k.factorial : ℝ) * (4 * ((k : ℝ) + 1) * δ⁻¹)) * (X ^ (1 / δ)) ^ (3 * k + 1) := by
      have step : 2 * ((k : ℝ) + 1) * δ⁻¹ * ((X ^ (1 / δ)) ^ (k + 1) + 1)
            ≤ (4 * ((k : ℝ) + 1) * δ⁻¹) * (X ^ (1 / δ)) ^ (k + 1) := by
        have h := mul_le_mul_of_nonneg_left hfac
          (by positivity : (0 : ℝ) ≤ 2 * ((k : ℝ) + 1) * δ⁻¹)
        calc 2 * ((k : ℝ) + 1) * δ⁻¹ * ((X ^ (1 / δ)) ^ (k + 1) + 1)
            ≤ 2 * ((k : ℝ) + 1) * δ⁻¹ * (2 * (X ^ (1 / δ)) ^ (k + 1)) := h
          _ = (4 * ((k : ℝ) + 1) * δ⁻¹) * (X ^ (1 / δ)) ^ (k + 1) := by ring
      have hpow : (X ^ (1 / δ)) ^ (2 * k) * (X ^ (1 / δ)) ^ (k + 1) =
          (X ^ (1 / δ)) ^ (3 * k + 1) := by
        rw [← pow_add]; congr 1; ring
      calc ((k.factorial : ℝ) * (X ^ (1 / δ)) ^ (2 * k)) *
              (2 * ((k : ℝ) + 1) * δ⁻¹ * ((X ^ (1 / δ)) ^ (k + 1) + 1))
          ≤ ((k.factorial : ℝ) * (X ^ (1 / δ)) ^ (2 * k)) *
              ((4 * ((k : ℝ) + 1) * δ⁻¹) * (X ^ (1 / δ)) ^ (k + 1)) :=
            mul_le_mul_of_nonneg_left step (by positivity)
        _ = ((k.factorial : ℝ) * (4 * ((k : ℝ) + 1) * δ⁻¹)) *
              ((X ^ (1 / δ)) ^ (2 * k) * (X ^ (1 / δ)) ^ (k + 1)) := by ring
        _ = ((k.factorial : ℝ) * (4 * ((k : ℝ) + 1) * δ⁻¹)) * (X ^ (1 / δ)) ^ (3 * k + 1) := by
            rw [hpow]
    have hlogBnd :
        Real.log (((k.factorial : ℝ) * (4 * ((k : ℝ) + 1) * δ⁻¹)) * (X ^ (1 / δ)) ^ (3 * k + 1))
        = Real.log (k.factorial) + Real.log (4 * ((k : ℝ) + 1) * δ⁻¹) +
            ((3 * (k : ℝ) + 1) / δ) * Real.log X := by
      rw [Real.log_mul (ne_of_gt (by positivity : (0:ℝ) < (k.factorial : ℝ) * (4 * ((k : ℝ) + 1) * δ⁻¹)))
            (ne_of_gt (by positivity : (0:ℝ) < (X ^ (1 / δ)) ^ (3 * k + 1))),
          Real.log_mul (ne_of_gt (by positivity : (0:ℝ) < (k.factorial : ℝ)))
            (ne_of_gt (by positivity : (0:ℝ) < 4 * ((k : ℝ) + 1) * δ⁻¹)),
          Real.log_pow, Real.log_rpow hXpos]
      push_cast
      ring
    have hlog_le :
        Real.log (((k.factorial : ℝ) * (4 * ((k : ℝ) + 1) * δ⁻¹)) * (X ^ (1 / δ)) ^ (3 * k + 1))
        ≤ δ ^ 12 * (P₂ / Real.log P₂) * Real.log (P₂ / 2) := by
      rw [hlogBnd]
      have h1 : ((3 * (k : ℝ) + 1) / δ) * Real.log X ≤
          ((3 * (k : ℝ) + 1) / δ) * (2 / ε ^ 2) * Real.log P₂ := by
        have hm := mul_le_mul_of_nonneg_left hlogX (by positivity : (0:ℝ) ≤ (3 * (k : ℝ) + 1) / δ)
        calc ((3 * (k : ℝ) + 1) / δ) * Real.log X
            ≤ ((3 * (k : ℝ) + 1) / δ) * ((2 / ε ^ 2) * Real.log P₂) := hm
          _ = ((3 * (k : ℝ) + 1) / δ) * (2 / ε ^ 2) * Real.log P₂ := by ring
      linarith [hkey, h1]
    have hE : ((k.factorial : ℝ) * (4 * ((k : ℝ) + 1) * δ⁻¹)) * (X ^ (1 / δ)) ^ (3 * k + 1)
        ≤ (P₂ / 2) ^ (δ ^ 12 * (P₂ / Real.log P₂)) := by
      rw [Real.rpow_def_of_pos hP2pos]
      rw [← Real.exp_log (by positivity : (0:ℝ) <
        ((k.factorial : ℝ) * (4 * ((k : ℝ) + 1) * δ⁻¹)) * (X ^ (1 / δ)) ^ (3 * k + 1))]
      rw [Real.exp_le_exp]
      have hcomm : Real.log (P₂ / 2) * (δ ^ 12 * (P₂ / Real.log P₂))
          = δ ^ 12 * (P₂ / Real.log P₂) * Real.log (P₂ / 2) := by ring
      rw [hcomm]
      exact hlog_le
    linarith [hBnd, hE]
  exact hthr.trans (hrpow.trans hprod)

end Work.N8
