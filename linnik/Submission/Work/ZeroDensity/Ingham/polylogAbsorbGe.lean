import Mathlib

namespace Work.ZeroDensity.Ingham

/-- **A polylogarithm is bounded by a small power of a linear function.**
For `A > 0`, `η > 0` there is `M > 0` with `(log x)^A ≤ M * x^η` for every `x ≥ 1`.
This follows from `log x ≤ x^(η/A) / (η/A)`, itself a consequence of `log y ≤ y`. -/
lemma rpowLogLe (A η : ℝ) (hA : 0 < A) (hη : 0 < η) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, 1 ≤ x → Real.log x ^ A ≤ M * x ^ η := by
  refine ⟨(A / η) ^ A, Real.rpow_pos_of_pos (div_pos hA hη) A, fun x hx => ?_⟩
  have hxpos : 0 < x := lt_of_lt_of_le one_pos hx
  have hs : 0 < η / A := div_pos hη hA
  have hxs : 0 < x ^ (η / A) := Real.rpow_pos_of_pos hxpos _
  have key : Real.log x ≤ (A / η) * x ^ (η / A) := by
    have hlog : Real.log (x ^ (η / A)) = (η / A) * Real.log x := Real.log_rpow hxpos _
    have h2 : (η / A) * Real.log x ≤ x ^ (η / A) := by
      rw [← hlog]; exact Real.log_le_self hxs.le
    have h3 : Real.log x ≤ x ^ (η / A) / (η / A) := by
      rw [le_div_iff₀ hs]; rw [mul_comm]; exact h2
    calc Real.log x ≤ x ^ (η / A) / (η / A) := h3
      _ = (A / η) * x ^ (η / A) := by rw [div_eq_mul_inv, inv_div]; ring
  have hnl : 0 ≤ Real.log x := Real.log_nonneg hx
  calc Real.log x ^ A ≤ ((A / η) * x ^ (η / A)) ^ A := Real.rpow_le_rpow hnl key hA.le
    _ = (A / η) ^ A * (x ^ (η / A)) ^ A := by
        rw [Real.mul_rpow (le_of_lt (div_pos hA hη)) (Real.rpow_nonneg hxpos.le _)]
    _ = (A / η) ^ A * x ^ η := by
        congr 1
        rw [← Real.rpow_mul hxpos.le]
        congr 1
        field_simp

/-- **Absorbing a polylogarithm into `C T^ε`, with `C ≥ 1`.**  For `K > 0`, `A > 0`, `ε > 0` there is a constant `C ≥ 1` (depending only on `K`, `A`, `ε`) with
`K (log (2 C T))^A ≤ C T^ε` for every `T ≥ 2`.

Hint: for `C` with `log (4C) ≥ A/ε` the ratio `(log (2CT))^A / T^ε` is decreasing on `[2,∞)`, so it suffices to have `K (log (4C))^A ≤ 2^ε C`, which holds for all large `C` since `C` grows linearly and `(log C)^A` only polylogarithmically. -/
theorem polylogAbsorbGe (K A ε : ℝ) (hK : 0 < K) (hA : 0 < A) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ T : ℝ, 2 ≤ T → K * (Real.log (2 * C * T)) ^ A ≤ C * T ^ ε := by
  -- Pick an exponent `η` with `0 < η < 1` and `η < ε`.
  set η : ℝ := min (ε / 2) (1 / 2) with hηdef
  have hηpos : 0 < η := by rw [hηdef]; exact lt_min (by linarith) (by norm_num)
  have hη1 : η < 1 := by rw [hηdef]; have h := min_le_right (ε / 2) (1 / 2); linarith
  have hηε : η < ε := by rw [hηdef]; have h := min_le_left (ε / 2) (1 / 2); linarith
  have h1mη : 0 < 1 - η := by linarith
  -- Bound the polylogarithm: `(log x)^A ≤ M x^η` for `x ≥ 1`.
  obtain ⟨M, hMpos, hM⟩ := rpowLogLe A η hA hηpos
  -- The constant `C` is chosen so that `C^(1-η)` dominates `K M 2^(2η-ε)`.
  refine ⟨(max 1 (K * M * 2 ^ (2 * η - ε))) ^ (1 / (1 - η)), ?_⟩
  set C : ℝ := (max 1 (K * M * 2 ^ (2 * η - ε))) ^ (1 / (1 - η)) with hCdef
  have hC1 : 1 ≤ C := by
    rw [hCdef]
    exact Real.one_le_rpow (le_max_left _ _) (le_of_lt (one_div_pos.mpr h1mη))
  refine ⟨hC1, fun T hT => ?_⟩
  have hTpos : 0 < T := by linarith
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hx1 : 1 ≤ 2 * C * T := by nlinarith [hC1, hT]
  have hbpos : 0 < max 1 (K * M * 2 ^ (2 * η - ε)) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  -- `C^(1-η) ≥ K M 2^(2η-ε)`.
  have hCX : K * M * 2 ^ (2 * η - ε) ≤ C ^ (1 - η) := by
    rw [hCdef]
    rw [← Real.rpow_mul (le_of_lt hbpos)]
    rw [show (1 / (1 - η)) * (1 - η) = 1 by rw [div_mul_cancel₀]; exact h1mη.ne']
    rw [Real.rpow_one]
    exact le_max_right _ _
  have hpow2 : (2 : ℝ) ^ (2 * η - ε) * 2 ^ (ε - η) = 2 ^ η := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1; ring
  have hCC : C ^ (1 - η) * C ^ η = C := by
    rw [← Real.rpow_add hCpos]
    rw [show (1 - η) + η = 1 by ring, Real.rpow_one]
  -- `K M 2^η C^η ≤ C 2^(ε-η)`.
  have hkey1 : K * M * 2 ^ η * C ^ η ≤ C * 2 ^ (ε - η) := by
    have hA1 : (K * M * 2 ^ (2 * η - ε)) * 2 ^ (ε - η) ≤ C ^ (1 - η) * 2 ^ (ε - η) :=
      mul_le_mul_of_nonneg_right hCX
        (le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _))
    have heq1 : (K * M * 2 ^ (2 * η - ε)) * 2 ^ (ε - η) = K * M * 2 ^ η := by
      calc (K * M * 2 ^ (2 * η - ε)) * 2 ^ (ε - η)
          = K * M * (2 ^ (2 * η - ε) * 2 ^ (ε - η)) := by ring
        _ = K * M * 2 ^ η := by rw [hpow2]
    have heq2 : C ^ (1 - η) * 2 ^ (ε - η) * C ^ η = C * 2 ^ (ε - η) := by
      calc C ^ (1 - η) * 2 ^ (ε - η) * C ^ η
          = (C ^ (1 - η) * C ^ η) * 2 ^ (ε - η) := by ring
        _ = C * 2 ^ (ε - η) := by rw [hCC]
    calc K * M * 2 ^ η * C ^ η
        = (K * M * 2 ^ (2 * η - ε)) * 2 ^ (ε - η) * C ^ η := by rw [heq1]
      _ ≤ C ^ (1 - η) * 2 ^ (ε - η) * C ^ η :=
            mul_le_mul_of_nonneg_right hA1 (Real.rpow_nonneg hCpos.le _)
      _ = C * 2 ^ (ε - η) := heq2
  -- `T^η ≤ 2^(η-ε) T^ε` for `T ≥ 2`.
  have hkey2 : T ^ η ≤ 2 ^ (η - ε) * T ^ ε := by
    have hm : η - ε ≤ 0 := by linarith
    have hle : T ^ (η - ε) ≤ (2 : ℝ) ^ (η - ε) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hT hm
    have hsplit : T ^ η = T ^ (η - ε) * T ^ ε := by
      have h1 : T ^ η = T ^ ((η - ε) + ε) := by congr 1; ring
      rw [h1, Real.rpow_add hTpos]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hTpos.le _)
  have hlog : (Real.log (2 * C * T)) ^ A ≤ M * (2 * C * T) ^ η := hM _ hx1
  have hstep2 : K * (Real.log (2 * C * T)) ^ A ≤ K * M * (2 * C * T) ^ η := by
    calc K * (Real.log (2 * C * T)) ^ A ≤ K * (M * (2 * C * T) ^ η) :=
          mul_le_mul_of_nonneg_left hlog hK.le
      _ = K * M * (2 * C * T) ^ η := by ring
  have hpow : (2 * C * T) ^ η = 2 ^ η * C ^ η * T ^ η := by
    rw [Real.mul_rpow (by linarith) hTpos.le, Real.mul_rpow (by norm_num) hCpos.le]
  have hp2 : (2 : ℝ) ^ (ε - η) * 2 ^ (η - ε) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [show (ε - η) + (η - ε) = 0 by ring, Real.rpow_zero]
  calc K * (Real.log (2 * C * T)) ^ A
      ≤ K * M * (2 * C * T) ^ η := hstep2
    _ = K * M * (2 ^ η * C ^ η * T ^ η) := by rw [hpow]
    _ = (K * M * 2 ^ η * C ^ η) * T ^ η := by ring
    _ ≤ (C * 2 ^ (ε - η)) * T ^ η :=
          mul_le_mul_of_nonneg_right hkey1 (Real.rpow_nonneg hTpos.le _)
    _ ≤ (C * 2 ^ (ε - η)) * (2 ^ (η - ε) * T ^ ε) :=
          mul_le_mul_of_nonneg_left hkey2
            (by apply mul_nonneg (le_of_lt hCpos); exact Real.rpow_nonneg (by norm_num) _)
    _ = C * T ^ ε := by
          rw [show (C * 2 ^ (ε - η)) * (2 ^ (η - ε) * T ^ ε)
                = C * (2 ^ (ε - η) * 2 ^ (η - ε)) * T ^ ε by ring, hp2]
          ring

end Work.ZeroDensity.Ingham
