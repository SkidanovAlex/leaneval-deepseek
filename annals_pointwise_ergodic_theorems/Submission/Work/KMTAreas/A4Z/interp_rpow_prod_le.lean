import Mathlib
import Submission.Work.KMTAreas.A5.logbPowLeConstMulRpow
import Submission.Work.Analysis.IWMultiplier.Defs

namespace Work.KMTAreas.A4Z

/-- Polynomial growth is absorbed by arbitrarily slow exponential growth: for every `P ≥ 0`
and `ε > 0` there is a constant `C ≥ 0` with `n ^ P ≤ C * 2 ^ (ε * n)` for every `n : ℕ`.

Proof: with `k = ⌈P⌉₊` one has `n ^ P ≤ n ^ k` for `n ≥ 1` (and `n ^ P ≤ 1` for `n = 0`),
and the elementary bound `x ^ k / k ! ≤ exp x` at `x = ε log 2 · n` gives
`n ^ k ≤ (k ! / (ε log 2) ^ k) · 2 ^ (ε n)`. -/
private theorem natCast_rpow_le_two_pow {P ε : ℝ} (hP : 0 ≤ P) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, (n : ℝ) ^ P ≤ C * (2 : ℝ) ^ (ε * (n : ℝ)) := by
  set k : ℕ := Nat.ceil P with hkdef
  have hPk : P ≤ (k : ℝ) := by rw [hkdef]; exact Nat.le_ceil P
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hεl : 0 < ε * Real.log 2 := mul_pos hε hlog2
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hbase : (0 : ℝ) < (ε * Real.log 2) ^ k := pow_pos hεl k
  refine ⟨max 1 ((k.factorial : ℝ) / (ε * Real.log 2) ^ k),
    le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro n
  have hC1 : (1 : ℝ) ≤ max 1 ((k.factorial : ℝ) / (ε * Real.log 2) ^ k) := le_max_left _ _
  have hCle : ((k.factorial : ℝ) / (ε * Real.log 2) ^ k)
      ≤ max 1 ((k.factorial : ℝ) / (ε * Real.log 2) ^ k) := le_max_right _ _
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1le : (1 : ℝ)
      ≤ max 1 ((k.factorial : ℝ) / (ε * Real.log 2) ^ k) * (2 : ℝ) ^ (ε * (n : ℝ)) := by
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ)) :=
      Real.one_le_rpow (by norm_num) (mul_nonneg hε.le hnn)
    have hCn : (0 : ℝ) ≤ max 1 ((k.factorial : ℝ) / (ε * Real.log 2) ^ k) :=
      le_trans zero_le_one hC1
    have hh := mul_le_mul hC1 h2 zero_le_one hCn
    simpa using hh
  have step1 : (n : ℝ) ^ P ≤ max 1 ((n : ℝ) ^ k) := by
    rcases lt_or_ge (n : ℝ) 1 with h | h
    · exact le_trans (Real.rpow_le_one hnn (le_of_lt h) hP) (le_max_left _ _)
    · have h' : (n : ℝ) ^ P ≤ (n : ℝ) ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le h hPk
      rw [Real.rpow_natCast] at h'
      exact le_trans h' (le_max_right _ _)
  have step2 : (n : ℝ) ^ k
      ≤ max 1 ((k.factorial : ℝ) / (ε * Real.log 2) ^ k) * (2 : ℝ) ^ (ε * (n : ℝ)) := by
    have hx : (0 : ℝ) ≤ ε * Real.log 2 * (n : ℝ) := by positivity
    have key := Real.pow_div_factorial_le_exp (ε * Real.log 2 * (n : ℝ)) hx k
    have hexp : Real.exp (ε * Real.log 2 * (n : ℝ)) = (2 : ℝ) ^ (ε * (n : ℝ)) := by
      rw [show ε * Real.log 2 * (n : ℝ) = Real.log 2 * (ε * (n : ℝ)) by ring, Real.exp_mul,
        Real.exp_log (by norm_num)]
    rw [hexp, mul_pow] at key
    have hmul := mul_le_mul_of_nonneg_left key (le_of_lt (div_pos hfac hbase))
    have hsimp : ((k.factorial : ℝ) / (ε * Real.log 2) ^ k)
        * (((ε * Real.log 2) ^ k * (n : ℝ) ^ k) / (k.factorial : ℝ)) = (n : ℝ) ^ k := by
      field_simp
    rw [hsimp] at hmul
    exact le_trans hmul (mul_le_mul_of_nonneg_right hCle (Real.rpow_nonneg (by norm_num) _))
  exact le_trans step1 (max_le h1le step2)

theorem interp_rpow_prod_le {c₀ p C0 C1 C3 : ℝ} (hc₀ : 0 < c₀) (hp1 : 1 < p) (hp2 : p < 2) (hC0 : 0 < C0) (hC1 : 0 ≤ C1) (hC3 : 0 < C3) : ∃ K : ℝ, 0 < K ∧ ∀ (Nd : ℝ), 1 ≤ Nd → ∀ l : ℕ, (C0 * ((2 : ℝ) ^ (-(c₀ * (l : ℝ))) * Nd ^ (1 / 2 : ℝ))) ^ (1 - p / 2) * ((1 + C1 * (Work.Analysis.IWMultiplier.angleBracket l : ℝ)) * C3 * Nd ^ (1 / 2 - 1 / p)) ^ (p / 2) ≤ K * (2 : ℝ) ^ (-((c₀ * (1 - p / 2) / 2) * (l : ℝ))) := by
  have hθ0 : 0 < 1 - p / 2 := by linarith
  have hpn : 0 ≤ p / 2 := by linarith
  have hε0 : 0 < c₀ * (1 - p / 2) / 2 := by positivity
  obtain ⟨C, hCnn, hC⟩ :=
    natCast_rpow_le_two_pow (P := p / 2) (ε := c₀ * (1 - p / 2) / 2) hpn hε0
  refine ⟨max 1 (C0 ^ (1 - p / 2) * C3 ^ (p / 2)
      * ((1 + C1) ^ (p / 2) * (C * (2 : ℝ) ^ (c₀ * (1 - p / 2) / 2)))), ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · intro Nd hNd l
    have hNd0 : 0 < Nd := lt_of_lt_of_le zero_lt_one hNd
    have hA1 : (1 : ℝ) ≤ 1 + C1 * (Work.Analysis.IWMultiplier.angleBracket l : ℝ) := by
      have h : (0 : ℝ) ≤ C1 * (Work.Analysis.IWMultiplier.angleBracket l : ℝ) :=
        mul_nonneg hC1 (by positivity)
      linarith
    have hAle : (1 + C1 * (Work.Analysis.IWMultiplier.angleBracket l : ℝ))
        ≤ (1 + C1) * ((l : ℝ) + 1) := by
      have hb : ((Work.Analysis.IWMultiplier.angleBracket l : ℝ)) ≤ (l : ℝ) + 1 := by
        have h : ((Work.Analysis.IWMultiplier.angleBracket l : ℝ)) = max 1 (l : ℝ) := by
          simp [Work.Analysis.IWMultiplier.angleBracket]
        rw [h]
        exact max_le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) l])
      have h1 : 1 + C1 * (Work.Analysis.IWMultiplier.angleBracket l : ℝ)
          ≤ 1 + C1 * ((l : ℝ) + 1) := by
        have := mul_le_mul_of_nonneg_left hb hC1
        linarith
      have h2 : 1 + C1 * ((l : ℝ) + 1) ≤ ((l : ℝ) + 1) + C1 * ((l : ℝ) + 1) := by
        have h : (1 : ℝ) ≤ (l : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) l]
        linarith
      calc 1 + C1 * (Work.Analysis.IWMultiplier.angleBracket l : ℝ)
          ≤ 1 + C1 * ((l : ℝ) + 1) := h1
        _ ≤ ((l : ℝ) + 1) + C1 * ((l : ℝ) + 1) := h2
        _ = (1 + C1) * ((l : ℝ) + 1) := by ring
    have hApow : (1 + C1 * (Work.Analysis.IWMultiplier.angleBracket l : ℝ)) ^ (p / 2)
        ≤ (1 + C1) ^ (p / 2) * (C * (2 : ℝ) ^ (c₀ * (1 - p / 2) / 2))
          * (2 : ℝ) ^ ((c₀ * (1 - p / 2) / 2) * (l : ℝ)) := by
      have hsplit : ((1 + C1) * ((l : ℝ) + 1)) ^ (p / 2)
          = (1 + C1) ^ (p / 2) * ((l : ℝ) + 1) ^ (p / 2) :=
        Real.mul_rpow (by linarith) (by positivity)
      have hstep2 : ((l : ℝ) + 1) ^ (p / 2)
          ≤ C * (2 : ℝ) ^ ((c₀ * (1 - p / 2) / 2) * ((l : ℝ) + 1)) := by
        have h := hC (l + 1)
        push_cast at h
        simpa using h
      have hexpadd : (2 : ℝ) ^ ((c₀ * (1 - p / 2) / 2) * ((l : ℝ) + 1))
          = (2 : ℝ) ^ (c₀ * (1 - p / 2) / 2)
            * (2 : ℝ) ^ ((c₀ * (1 - p / 2) / 2) * (l : ℝ)) := by
        rw [show (c₀ * (1 - p / 2) / 2) * ((l : ℝ) + 1)
              = (c₀ * (1 - p / 2) / 2) + (c₀ * (1 - p / 2) / 2) * (l : ℝ) by ring,
            Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      calc (1 + C1 * (Work.Analysis.IWMultiplier.angleBracket l : ℝ)) ^ (p / 2)
          ≤ ((1 + C1) * ((l : ℝ) + 1)) ^ (p / 2) :=
            Real.rpow_le_rpow (le_trans zero_le_one hA1) hAle hpn
        _ = (1 + C1) ^ (p / 2) * ((l : ℝ) + 1) ^ (p / 2) := hsplit
        _ ≤ (1 + C1) ^ (p / 2)
              * (C * (2 : ℝ) ^ ((c₀ * (1 - p / 2) / 2) * ((l : ℝ) + 1))) :=
              mul_le_mul_of_nonneg_left hstep2 (Real.rpow_nonneg (by linarith) _)
        _ = (1 + C1) ^ (p / 2)
              * (C * ((2 : ℝ) ^ (c₀ * (1 - p / 2) / 2)
                * (2 : ℝ) ^ ((c₀ * (1 - p / 2) / 2) * (l : ℝ)))) := by rw [hexpadd]
        _ = (1 + C1) ^ (p / 2) * (C * (2 : ℝ) ^ (c₀ * (1 - p / 2) / 2))
              * (2 : ℝ) ^ ((c₀ * (1 - p / 2) / 2) * (l : ℝ)) := by ring
    have hF1 : (C0 * ((2 : ℝ) ^ (-(c₀ * (l : ℝ))) * Nd ^ (1 / 2 : ℝ))) ^ (1 - p / 2)
        = C0 ^ (1 - p / 2) * (2 : ℝ) ^ ((-(c₀ * (l : ℝ))) * (1 - p / 2))
          * Nd ^ ((1 / 2 : ℝ) * (1 - p / 2)) := by
      conv_lhs => rw [Real.mul_rpow (x := C0)
                        (y := (2 : ℝ) ^ (-(c₀ * (l : ℝ))) * Nd ^ (1 / 2 : ℝ)) (z := 1 - p / 2)
                        hC0.le (by positivity),
                      Real.mul_rpow (x := (2 : ℝ) ^ (-(c₀ * (l : ℝ)))) (y := Nd ^ (1 / 2 : ℝ))
                        (z := 1 - p / 2) (by positivity) (by positivity),
                      ← Real.rpow_mul (x := 2) (by norm_num : (0 : ℝ) ≤ 2)
                        (-(c₀ * (l : ℝ))) (1 - p / 2),
                      ← Real.rpow_mul (x := Nd) (le_of_lt hNd0) (1 / 2 : ℝ) (1 - p / 2)]
      ring
    have hF2 : ((1 + C1 * (Work.Analysis.IWMultiplier.angleBracket l : ℝ)) * C3
          * Nd ^ (1 / 2 - 1 / p)) ^ (p / 2)
        = (1 + C1 * (Work.Analysis.IWMultiplier.angleBracket l : ℝ)) ^ (p / 2) * C3 ^ (p / 2)
          * Nd ^ ((1 / 2 - 1 / p) * (p / 2)) := by
      conv_lhs => rw [Real.mul_rpow
                        (x := (1 + C1 * (Work.Analysis.IWMultiplier.angleBracket l : ℝ)) * C3)
                        (y := Nd ^ (1 / 2 - 1 / p)) (z := p / 2) (by positivity) (by positivity),
                      Real.mul_rpow (x := (1 + C1 * (Work.Analysis.IWMultiplier.angleBracket l : ℝ)))
                        (y := C3) (z := p / 2) (by positivity) (by positivity),
                      ← Real.rpow_mul (x := Nd) (le_of_lt hNd0) (1 / 2 - 1 / p) (p / 2)]
    have e3 : Nd ^ ((1 / 2 : ℝ) * (1 - p / 2)) * Nd ^ ((1 / 2 - 1 / p) * (p / 2)) = 1 := by
      rw [← Real.rpow_add hNd0]
      have hexp : (1 / 2 : ℝ) * (1 - p / 2) + (1 / 2 - 1 / p) * (p / 2) = 0 := by
        have h1 : (1 / p) * (p / 2) = (1 / 2 : ℝ) := by field_simp
        calc (1 / 2 : ℝ) * (1 - p / 2) + (1 / 2 - 1 / p) * (p / 2)
            = (1 / 2) * (1 - p / 2) + (1 / 2) * (p / 2) - (1 / p) * (p / 2) := by ring
          _ = (1 / 2) * (1 - p / 2) + (1 / 2) * (p / 2) - 1 / 2 := by rw [h1]
          _ = 0 := by ring
      rw [hexp, Real.rpow_zero]
    have hExpand' : (C0 * ((2 : ℝ) ^ (-(c₀ * (l : ℝ))) * Nd ^ (1 / 2 : ℝ))) ^ (1 - p / 2)
        * ((1 + C1 * (Work.Analysis.IWMultiplier.angleBracket l : ℝ)) * C3
            * Nd ^ (1 / 2 - 1 / p)) ^ (p / 2)
        = C0 ^ (1 - p / 2) * C3 ^ (p / 2) * (2 : ℝ) ^ ((-(c₀ * (l : ℝ))) * (1 - p / 2))
          * (1 + C1 * (Work.Analysis.IWMultiplier.angleBracket l : ℝ)) ^ (p / 2)
          * (Nd ^ ((1 / 2 : ℝ) * (1 - p / 2)) * Nd ^ ((1 / 2 - 1 / p) * (p / 2))) := by
      rw [hF1, hF2]
      ring
    have hExpand : (C0 * ((2 : ℝ) ^ (-(c₀ * (l : ℝ))) * Nd ^ (1 / 2 : ℝ))) ^ (1 - p / 2)
        * ((1 + C1 * (Work.Analysis.IWMultiplier.angleBracket l : ℝ)) * C3
            * Nd ^ (1 / 2 - 1 / p)) ^ (p / 2)
        = C0 ^ (1 - p / 2) * C3 ^ (p / 2) * (2 : ℝ) ^ ((-(c₀ * (l : ℝ))) * (1 - p / 2))
          * (1 + C1 * (Work.Analysis.IWMultiplier.angleBracket l : ℝ)) ^ (p / 2) := by
      rw [hExpand', e3, mul_one]
    have hpow : (2 : ℝ) ^ ((-(c₀ * (l : ℝ))) * (1 - p / 2))
        * (2 : ℝ) ^ ((c₀ * (1 - p / 2) / 2) * (l : ℝ))
        = (2 : ℝ) ^ (-((c₀ * (1 - p / 2) / 2) * (l : ℝ))) := by
      rw [← Real.rpow_add (x := 2) (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    have hfinal : (C0 * ((2 : ℝ) ^ (-(c₀ * (l : ℝ))) * Nd ^ (1 / 2 : ℝ))) ^ (1 - p / 2)
        * ((1 + C1 * (Work.Analysis.IWMultiplier.angleBracket l : ℝ)) * C3
            * Nd ^ (1 / 2 - 1 / p)) ^ (p / 2)
        ≤ (C0 ^ (1 - p / 2) * C3 ^ (p / 2)
            * ((1 + C1) ^ (p / 2) * (C * (2 : ℝ) ^ (c₀ * (1 - p / 2) / 2))))
          * (2 : ℝ) ^ (-((c₀ * (1 - p / 2) / 2) * (l : ℝ))) := by
      rw [hExpand]
      calc C0 ^ (1 - p / 2) * C3 ^ (p / 2) * (2 : ℝ) ^ ((-(c₀ * (l : ℝ))) * (1 - p / 2))
            * (1 + C1 * (Work.Analysis.IWMultiplier.angleBracket l : ℝ)) ^ (p / 2)
          ≤ C0 ^ (1 - p / 2) * C3 ^ (p / 2)
              * (2 : ℝ) ^ ((-(c₀ * (l : ℝ))) * (1 - p / 2))
              * ((1 + C1) ^ (p / 2) * (C * (2 : ℝ) ^ (c₀ * (1 - p / 2) / 2))
                * (2 : ℝ) ^ ((c₀ * (1 - p / 2) / 2) * (l : ℝ))) :=
              mul_le_mul_of_nonneg_left hApow (by positivity)
        _ = (C0 ^ (1 - p / 2) * C3 ^ (p / 2)
              * ((1 + C1) ^ (p / 2) * (C * (2 : ℝ) ^ (c₀ * (1 - p / 2) / 2))))
              * ((2 : ℝ) ^ ((-(c₀ * (l : ℝ))) * (1 - p / 2))
                * (2 : ℝ) ^ ((c₀ * (1 - p / 2) / 2) * (l : ℝ))) := by ring
        _ = (C0 ^ (1 - p / 2) * C3 ^ (p / 2)
              * ((1 + C1) ^ (p / 2) * (C * (2 : ℝ) ^ (c₀ * (1 - p / 2) / 2))))
              * (2 : ℝ) ^ (-((c₀ * (1 - p / 2) / 2) * (l : ℝ))) := by rw [hpow]
    have hKle : C0 ^ (1 - p / 2) * C3 ^ (p / 2)
        * ((1 + C1) ^ (p / 2) * (C * (2 : ℝ) ^ (c₀ * (1 - p / 2) / 2)))
        ≤ max 1 (C0 ^ (1 - p / 2) * C3 ^ (p / 2)
            * ((1 + C1) ^ (p / 2) * (C * (2 : ℝ) ^ (c₀ * (1 - p / 2) / 2)))) :=
      le_max_right _ _
    exact le_trans hfinal (mul_le_mul_of_nonneg_right hKle (Real.rpow_nonneg (by norm_num) _))

end Work.KMTAreas.A4Z
