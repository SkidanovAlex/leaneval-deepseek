import Mathlib

namespace Work.PertCrux

/-- Choice of the shadowing constants.  For a Lipschitz constant `K ≥ 1`, `ε ∈ (0,1]` and a
horizon `m : ℕ` there are `δ₀ ∈ (0,1]` and `η > 0` with `K^j (η + j δ₀) < ε` for every `j ≤ m`.
(Witnesses: `η = ε/(4K^m)`, `δ₀ = min 1 (ε/(4(m+1)K^m))`.) -/
theorem shadow_constants {K ε : ℝ} (hK : 1 ≤ K) (hε : 0 < ε) (hε1 : ε ≤ 1) (m : ℕ) :
    ∃ δ₀ η : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < η ∧
      ∀ j : ℕ, j ≤ m → K ^ j * (η + (j : ℝ) * δ₀) < ε := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  -- the two witnesses
  set δ : ℝ := ε / (4 * ((m : ℝ) + 1) * K ^ m) with hδdef
  set η : ℝ := ε / (4 * K ^ m) with hηdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hηpos : 0 < η := by rw [hηdef]; positivity
  refine ⟨min 1 δ, η, lt_min one_pos hδpos, min_le_left _ _, hηpos, ?_⟩
  -- exact values of the two products
  have hKmη : K ^ m * η = ε / 4 := by rw [hηdef]; field_simp
  have hKmδ : K ^ m * δ = ε / (4 * ((m : ℝ) + 1)) := by rw [hδdef]; field_simp
  intro j hj
  have hjm : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast hj
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hδ0pos : 0 < min 1 δ := lt_min one_pos hδpos
  have hKj : K ^ j ≤ K ^ m := pow_le_pow_right₀ hK hj
  -- monotonicity in `j` of `η + j δ₀`
  have hstep1 : η + (j : ℝ) * min 1 δ ≤ η + (m : ℝ) * δ := by
    have h1 : (j : ℝ) * min 1 δ ≤ (m : ℝ) * min 1 δ :=
      mul_le_mul_of_nonneg_right hjm (le_of_lt hδ0pos)
    have h2 : (m : ℝ) * min 1 δ ≤ (m : ℝ) * δ :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hm0
    linarith
  have hstep2 : K ^ j * (η + (j : ℝ) * min 1 δ) ≤ K ^ m * (η + (m : ℝ) * δ) := by
    have h1 : K ^ j * (η + (j : ℝ) * min 1 δ) ≤ K ^ j * (η + (m : ℝ) * δ) :=
      mul_le_mul_of_nonneg_left hstep1 (le_of_lt (pow_pos hKpos j))
    have h2 : K ^ j * (η + (m : ℝ) * δ) ≤ K ^ m * (η + (m : ℝ) * δ) :=
      mul_le_mul_of_nonneg_right hKj (by positivity)
    linarith
  -- the value at `j = m` is `< ε`
  have htop : K ^ m * (η + (m : ℝ) * δ) < ε := by
    have heq : K ^ m * (η + (m : ℝ) * δ) = ε / 4 + (m : ℝ) * (ε / (4 * ((m : ℝ) + 1))) := by
      rw [mul_add, hKmη]
      congr 1
      rw [← mul_assoc, mul_comm (K ^ m) (m : ℝ), mul_assoc, hKmδ]
    rw [heq]
    have hmm : (m : ℝ) / ((m : ℝ) + 1) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    have hlt : (m : ℝ) * (ε / (4 * ((m : ℝ) + 1))) < ε / 4 := by
      have hthis : (m : ℝ) * (ε / (4 * ((m : ℝ) + 1))) = ((m : ℝ) / ((m : ℝ) + 1)) * (ε / 4) := by
        field_simp
      rw [hthis]
      calc ((m : ℝ) / ((m : ℝ) + 1)) * (ε / 4) < 1 * (ε / 4) :=
            mul_lt_mul_of_pos_right hmm (by positivity)
        _ = ε / 4 := by ring
    linarith
  linarith

end Work.PertCrux
