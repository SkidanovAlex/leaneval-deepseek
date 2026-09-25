import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs

/-!
# The MST threshold `κ_s` beats the exponential weight `2^{s(d-χ)}`

For a polynomial `P : ℤ[X]` of degree `d = P.natDegree ≥ 2` and any real `χ`, the MST threshold
`κ_s = mstKappa P s = 20 d (⌊(s+1)^{1/10}⌋ + 1)` grows like a power `s^{1/10}`, so the exponential

  `2^{2^{κ_s} / (4d)}`

dominates the (possibly very large) weight `2^{s (d - χ)}` for all large `s`.  Concretely:

  `2^{s (d - χ)} ≤ 2^{2^{κ_s} / (4d)}` eventually in `s`.

The proof goes through the elementary bound `log s ≤ 10 (s+1)^{1/10}`, which gives
`(2 : ℝ)^{mstKappa P s} ≥ 2^{2 d log s} = s^{2 d log 2}`; since `2 d log 2 ≥ 2` the right side
beats any fixed multiple of `s`.
-/

namespace Work.Maximal

open Real

/-- For `s ≥ 1`, `log s / 10 ≤ (s+1)^{1/10}`. -/
lemma log_div_ten_le_rpow_ten_add_one (s : ℕ) (hs : 1 ≤ s) :
    Real.log (s : ℝ) / 10 ≤ ((s : ℝ) + 1) ^ (1 / 10 : ℝ) := by
  have hs0 : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
  have hx10pos : (0 : ℝ) < (s : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hs0 _
  have hlog : Real.log (s : ℝ) = 10 * Real.log ((s : ℝ) ^ (1 / 10 : ℝ)) := by
    rw [Real.log_rpow hs0]; ring
  have h1 : Real.log ((s : ℝ) ^ (1 / 10 : ℝ)) ≤ (s : ℝ) ^ (1 / 10 : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hx10pos
  have h2 : (s : ℝ) ^ (1 / 10 : ℝ) ≤ ((s : ℝ) + 1) ^ (1 / 10 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  rw [hlog]
  linarith

/-- **`κ_s` dominates `2 d log s`**: for `s ≥ 1`,
`2 d log s ≤ mstKappa P s`. -/
lemma mstKappa_ge_two_mul_log (P : Polynomial ℤ) (s : ℕ) (hs : 1 ≤ s) :
    2 * (P.natDegree : ℝ) * Real.log (s : ℝ)
      ≤ (Work.BourgainPlan.Maximal.mstKappa P s : ℝ) := by
  have hfloor : ((s : ℝ) + 1) ^ (1 / 10 : ℝ)
      ≤ ((⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ : ℕ) : ℝ) + 1 :=
    le_of_lt (Nat.lt_floor_add_one _)
  have hlog : Real.log (s : ℝ) / 10 ≤ ((s : ℝ) + 1) ^ (1 / 10 : ℝ) :=
    log_div_ten_le_rpow_ten_add_one s hs
  have step : Real.log (s : ℝ) / 10
      ≤ ((⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ : ℕ) : ℝ) + 1 := le_trans hlog hfloor
  have hmain : 20 * (P.natDegree : ℝ) * (Real.log (s : ℝ) / 10)
      ≤ 20 * (P.natDegree : ℝ)
        * (((⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ : ℕ) : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left step (by positivity)
  have heq : 20 * (P.natDegree : ℝ) * (Real.log (s : ℝ) / 10)
      = 2 * (P.natDegree : ℝ) * Real.log (s : ℝ) := by ring
  rw [Work.BourgainPlan.Maximal.mstKappa]
  push_cast
  linarith [hmain, heq]

/-- **Exponential beats linear**: for every real `B` there is `s₀` with
`B · s ≤ (2 : ℝ)^{mstKappa P s}` for all `s ≥ s₀`. -/
lemma two_pow_mstKappa_ge_mul (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (B : ℝ) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
      B * (s : ℝ) ≤ (2 : ℝ) ^ (Work.BourgainPlan.Maximal.mstKappa P s) := by
  refine ⟨max 2 (⌈B⌉₊ + 1), fun s hs => ?_⟩
  have hs2 : 2 ≤ s := le_trans (le_max_left _ _) hs
  have hsB : ⌈B⌉₊ + 1 ≤ s := le_trans (le_max_right _ _) hs
  have hD2 : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have ha : (2 : ℝ) ≤ 2 * (P.natDegree : ℝ) * Real.log 2 := by nlinarith
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast (by omega : 1 ≤ s)
  have hspos : (0 : ℝ) < (s : ℝ) := by linarith
  have hBs : B ≤ (s : ℝ) := by
    have h1 := Nat.le_ceil B
    have h2 : ((⌈B⌉₊ : ℕ) : ℝ) + 1 ≤ (s : ℝ) := by exact_mod_cast hsB
    linarith
  have heq : (2 : ℝ) ^ (2 * (P.natDegree : ℝ) * Real.log (s : ℝ))
      = (s : ℝ) ^ (2 * (P.natDegree : ℝ) * Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_def_of_pos hspos]
    ring_nf
  have hsq : B * (s : ℝ) ≤ (s : ℝ) ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    nlinarith [mul_nonneg (le_of_lt hspos) (sub_nonneg.mpr hBs)]
  have hmono : (s : ℝ) ^ (2 : ℝ) ≤ (s : ℝ) ^ (2 * (P.natDegree : ℝ) * Real.log 2) :=
    Real.rpow_le_rpow_of_exponent_le hs1 ha
  have h1 : B * (s : ℝ) ≤ (2 : ℝ) ^ (2 * (P.natDegree : ℝ) * Real.log (s : ℝ)) := by
    rw [heq]; exact le_trans hsq hmono
  have h2 : (2 : ℝ) ^ (2 * (P.natDegree : ℝ) * Real.log (s : ℝ))
      ≤ (2 : ℝ) ^ (Work.BourgainPlan.Maximal.mstKappa P s) := by
    rw [← Real.rpow_natCast (2 : ℝ) (Work.BourgainPlan.Maximal.mstKappa P s)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mstKappa_ge_two_mul_log P s (by omega))
  exact le_trans h1 h2

theorem mstKappa_chi_le (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (χ : ℝ) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
      (2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ))
        ≤ (2 : ℝ) ^ (((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
            / (4 * (P.natDegree : ℝ))) := by
  by_cases hχ : χ < (P.natDegree : ℝ)
  · have hDpos : 0 < (P.natDegree : ℝ) := by
      exact_mod_cast (by omega : 0 < P.natDegree)
    obtain ⟨s₀, hs₀⟩ := two_pow_mstKappa_ge_mul P hd
      (4 * (P.natDegree : ℝ) * ((P.natDegree : ℝ) - χ))
    refine ⟨s₀, fun s hs => ?_⟩
    have h4D : 0 < 4 * (P.natDegree : ℝ) := by positivity
    have hcast : ((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
        = (2 : ℝ) ^ (Work.BourgainPlan.Maximal.mstKappa P s) := by push_cast; ring
    have hkey : (s : ℝ) * ((P.natDegree : ℝ) - χ)
        ≤ ((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
            / (4 * (P.natDegree : ℝ)) := by
      rw [hcast, le_div_iff₀ h4D]
      nlinarith [hs₀ s hs]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hkey
  · have hχge : (P.natDegree : ℝ) ≤ χ := not_lt.mp hχ
    refine ⟨0, fun s _ => ?_⟩
    have hexple : (s : ℝ) * ((P.natDegree : ℝ) - χ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
    have hrhs : (0 : ℝ) ≤ ((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
        / (4 * (P.natDegree : ℝ)) := by positivity
    calc (2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ))
          ≤ (2 : ℝ) ^ 0 := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexple
      _ ≤ (2 : ℝ) ^ (((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
              / (4 * (P.natDegree : ℝ))) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hrhs

end Work.Maximal
