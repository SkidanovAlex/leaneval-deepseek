import Mathlib

/-!
# The arithmetic interpolation estimate for the `(struct iii)` interpolation step

This file proves `Work.KMTAreas.A4.structiiiInterpArith`, the elementary arithmetic
inequality behind the interpolation of the structural estimate.  Concretely, for
`1 < p < 2`, `a > 0`, `0 < c < a * (1 - p / 2)`, `CA, CY > 0`, `d : ℕ`, there is a constant
`K > 0` with

  `(CA · 2^{-a l} · N^{d/2})^{1 - p/2} · (CY · max 1 l · N^{d (1/2 - 1/p)})^{p/2}
      ≤ K · 2^{-c l}`

for every `N ≥ 1` and every `l : ℕ`.

The point of the estimate is that the exponent of `N` **vanishes**:

  `(d/2) (1 - p/2) + d (1/2 - 1/p) (p/2) = d/4 - d/4 = 0`,

so the left-hand side is independent of `N` and equals

  `CA^{1 - p/2} · CY^{p/2} · (max 1 l)^{p/2} · 2^{-a (1 - p/2) l}`;

with `δ := a (1 - p/2) - c > 0` this is at most `CA^{1-p/2} CY^{p/2} K₀ · 2^{-c l}` where `K₀`
bounds the polynomial-times-exponentially-decaying sequence `l ↦ (max 1 l)^{p/2} 2^{-δ l}`.
-/

namespace Work.KMTAreas.A4

/-- Polynomial growth is beaten by any exponential decay: for every exponent `s` and every
`δ > 0` the sequence `l ↦ (max 1 l)^s · 2^{-δ l}` is bounded.  (For `l = 0` the value is `1`.)

The proof: for `l ≥ 1` the expression is `l^s · e^{-δ log 2 · l}`, and the function
`x ↦ x^s · e^{-b x}` tends to `0` at `+∞` for `b > 0`, hence has bounded range on `ℕ`. -/
theorem maxOneRpowMulTwoRpowNegBounded (s δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ l : ℕ, (max 1 (l : ℝ)) ^ s * (2 : ℝ) ^ (-(δ * (l : ℝ))) ≤ K := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hb : (0:ℝ) < δ * Real.log 2 := mul_pos hδ hlog2
  have htend : Filter.Tendsto (fun l : ℕ => ((l:ℝ)) ^ s * Real.exp (-(δ * Real.log 2) * (l:ℝ)))
      Filter.atTop (nhds 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s (δ * Real.log 2) hb).comp
      tendsto_natCast_atTop_atTop
  have hbdd : BddAbove
      (Set.range fun l : ℕ => ((l:ℝ)) ^ s * Real.exp (-(δ * Real.log 2) * (l:ℝ))) :=
    htend.bddAbove_range
  obtain ⟨Kv, hKv⟩ := hbdd
  refine ⟨max 1 Kv, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro l
  rcases Nat.eq_zero_or_pos l with hl | hl
  · subst hl
    simp
  · have hl1 : (1:ℝ) ≤ (l:ℝ) := by exact_mod_cast hl
    have hmax : max 1 (l:ℝ) = (l:ℝ) := max_eq_right hl1
    have h2 : (2:ℝ) ^ (-(δ * (l:ℝ))) = Real.exp (-(δ * Real.log 2) * (l:ℝ)) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
      congr 1
      ring
    rw [hmax, h2]
    exact le_trans (hKv ⟨l, rfl⟩) (le_max_right _ _)

set_option linter.unusedVariables false in
theorem structiiiInterpArith {p a c CA CY : ℝ} {d : ℕ} (hp1 : 1 < p) (hp2 : p < 2) (ha : 0 < a) (hc : 0 < c) (hca : c < a * (1 - p / 2)) (hCA : 0 < CA) (hCY : 0 < CY) : ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ), 1 ≤ N → ∀ l : ℕ, (CA * (2 : ℝ) ^ (-(a * (l : ℝ))) * (((N : ℝ) ^ d) ^ (1 / 2 : ℝ))) ^ (1 - p / 2) * (CY * (max 1 (l : ℝ)) * (N : ℝ) ^ ((d : ℝ) * (1 / 2 - 1 / p))) ^ (p / 2) ≤ K * (2 : ℝ) ^ (-(c * (l : ℝ))) := by
  have hp0 : p ≠ 0 := by linarith
  have hδ : 0 < a * (1 - p / 2) - c := by linarith
  obtain ⟨K0, hK0pos, hK0⟩ := maxOneRpowMulTwoRpowNegBounded (p / 2) (a * (1 - p / 2) - c) hδ
  refine ⟨CA ^ (1 - p / 2) * CY ^ (p / 2) * K0, ?_, ?_⟩
  · positivity
  · intro N hN l
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have hNpos : (0:ℝ) < (N:ℝ) := by linarith
    have hM0 : (0:ℝ) ≤ (max 1 (l:ℝ)) := le_trans zero_le_one (le_max_left _ _)
    -- the exponent of `N` is `0`, so the whole `N`-dependence cancels
    have hNc : ((((N:ℝ) ^ d) ^ (1/2:ℝ)) ^ (1 - p/2))
        * (((N:ℝ) ^ ((d:ℝ) * (1/2 - 1/p))) ^ (p/2)) = 1 := by
      rw [← Real.rpow_natCast (N:ℝ) d]
      rw [← Real.rpow_mul hNpos.le]
      rw [← Real.rpow_mul hNpos.le]
      rw [← Real.rpow_mul hNpos.le]
      rw [← Real.rpow_add hNpos]
      have hzero : (d:ℝ) * (1/2) * (1 - p/2) + (d:ℝ) * (1/2 - 1/p) * (p/2) = 0 := by
        field_simp
        ring
      rw [hzero, Real.rpow_zero]
    -- `(2^{-a l})^{1-p/2} = 2^{-a(1-p/2) l}`
    have h2p : ((2:ℝ) ^ (-(a * (l:ℝ)))) ^ (1 - p/2)
        = (2:ℝ) ^ (-(a * (1 - p/2)) * (l:ℝ)) := by
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      ring
    -- split the exponential into decay at rate `δ` and at rate `c`
    have h2add : (2:ℝ) ^ (-(a * (1 - p/2)) * (l:ℝ))
        = (2:ℝ) ^ (-((a * (1 - p/2) - c) * (l:ℝ))) * (2:ℝ) ^ (-(c * (l:ℝ))) := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      congr 1
      ring
    have hA1 : (0:ℝ) ≤ CA * (2:ℝ) ^ (-(a * (l:ℝ))) := by positivity
    have hA2 : (0:ℝ) ≤ (((N:ℝ) ^ d) ^ (1/2:ℝ)) := by positivity
    have hB1 : (0:ℝ) ≤ CA := le_of_lt hCA
    have hB2 : (0:ℝ) ≤ (2:ℝ) ^ (-(a * (l:ℝ))) := by positivity
    have hC1 : (0:ℝ) ≤ CY * (max 1 (l:ℝ)) := by positivity
    have hC2 : (0:ℝ) ≤ (N:ℝ) ^ ((d:ℝ) * (1/2 - 1/p)) := by positivity
    have hD1 : (0:ℝ) ≤ CY := le_of_lt hCY
    calc
      (CA * (2 : ℝ) ^ (-(a * (l : ℝ))) * (((N : ℝ) ^ d) ^ (1 / 2 : ℝ))) ^ (1 - p / 2)
          * (CY * (max 1 (l : ℝ)) * (N : ℝ) ^ ((d : ℝ) * (1 / 2 - 1 / p))) ^ (p / 2)
        = CA^(1-p/2) * CY^(p/2) * (max 1 (l:ℝ))^(p/2)
            * (((2:ℝ) ^ (-(a * (l:ℝ)))) ^ (1-p/2)
               * ((((N:ℝ) ^ d) ^ (1/2:ℝ)) ^ (1-p/2)
                  * ((N:ℝ) ^ ((d:ℝ) * (1/2 - 1/p))) ^ (p/2))) := by
          rw [Real.mul_rpow hA1 hA2, Real.mul_rpow hB1 hB2,
              Real.mul_rpow hC1 hC2, Real.mul_rpow hD1 hM0]
          ring
        _ = CA^(1-p/2) * CY^(p/2) * (max 1 (l:ℝ))^(p/2)
              * (2:ℝ) ^ (-(a * (1 - p/2)) * (l:ℝ)) := by
          rw [hNc, mul_one, h2p]
        _ = CA^(1-p/2) * CY^(p/2) * (max 1 (l:ℝ))^(p/2)
              * ((2:ℝ) ^ (-((a * (1 - p/2) - c) * (l:ℝ))) * (2:ℝ) ^ (-(c * (l:ℝ)))) := by
          rw [h2add]
        _ = CA^(1-p/2) * CY^(p/2)
              * ((max 1 (l:ℝ))^(p/2) * (2:ℝ) ^ (-((a * (1 - p/2) - c) * (l:ℝ))))
              * (2:ℝ) ^ (-(c * (l:ℝ))) := by ring
        _ ≤ CA^(1-p/2) * CY^(p/2) * K0 * (2:ℝ) ^ (-(c * (l:ℝ))) := by
          have hA : (0:ℝ) ≤ CA^(1-p/2) * CY^(p/2) := by positivity
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hK0 l) hA) (by positivity)
        _ = (CA ^ (1 - p / 2) * CY ^ (p / 2) * K0) * (2 : ℝ) ^ (-(c * (l : ℝ))) := by ring

end Work.KMTAreas.A4
