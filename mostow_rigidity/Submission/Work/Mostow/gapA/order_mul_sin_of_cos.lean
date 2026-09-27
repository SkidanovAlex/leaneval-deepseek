import Mathlib

namespace Work.Mostow.gapA
/-- The gap inequality for a rotation of order dividing `n`: with `θ' = arccos (cos θ)` the
rotation angle in `[0, π]`, `2 ≤ n·sin(θ'/2)`. -/
theorem order_mul_sin_of_cos (n : ℕ) (hn : 0 < n) (θ : ℝ)
    (h : ∃ k : ℤ, (n : ℝ) * θ = 2 * Real.pi * k) (hcos : Real.cos θ ≠ 1) :
    2 ≤ (n : ℝ) * Real.sin (Real.arccos (Real.cos θ) / 2) := by
  -- θ' is the rotation angle in `[0, π]` representing the same rotation as `θ`.
  set θ' := Real.arccos (Real.cos θ) with hθ'def
  have hcos_le : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hcos_ge : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
  have hcosθ' : Real.cos θ' = Real.cos θ := Real.cos_arccos hcos_ge hcos_le
  have hθ'pos : 0 < θ' := by
    rw [hθ'def, Real.arccos_pos]
    exact lt_of_le_of_ne hcos_le hcos
  have hθ'le : θ' ≤ Real.pi := by rw [hθ'def]; exact Real.arccos_le_pi _
  obtain ⟨k₀, hk₀⟩ := h
  -- `n θ' ∈ 2πℤ`, because `θ' ≡ ±θ (mod 2π)`.
  obtain ⟨j, hj⟩ : ∃ j : ℤ, (n : ℝ) * θ' = 2 * Real.pi * (j : ℝ) := by
    obtain ⟨k, hk | hk⟩ := (Real.cos_eq_cos_iff).1 hcosθ'
    · refine ⟨k₀ - (n : ℤ) * k, ?_⟩
      push_cast
      have h1 : (n : ℝ) * θ' = (n : ℝ) * θ - 2 * Real.pi * ((n : ℝ) * (k : ℝ)) := by
        rw [hk]; ring
      have h2 : (n : ℝ) * θ - 2 * Real.pi * ((n : ℝ) * (k : ℝ))
          = 2 * Real.pi * ((k₀ : ℝ) - (n : ℝ) * (k : ℝ)) := by
        rw [hk₀]; ring
      exact h1.trans h2
    · refine ⟨(n : ℤ) * k - k₀, ?_⟩
      push_cast
      have h1 : (n : ℝ) * θ' = 2 * Real.pi * ((n : ℝ) * (k : ℝ)) - (n : ℝ) * θ := by
        rw [hk]; ring
      have h2 : 2 * Real.pi * ((n : ℝ) * (k : ℝ)) - (n : ℝ) * θ
          = 2 * Real.pi * ((n : ℝ) * (k : ℝ) - (k₀ : ℝ)) := by
        rw [hk₀]; ring
      exact h1.trans h2
  -- the integer `j` is positive, hence `≥ 1`.
  have hjposR : (0 : ℝ) < (j : ℝ) := by
    have hpos : (0 : ℝ) < (n : ℝ) * θ' := mul_pos (by exact_mod_cast hn) hθ'pos
    rw [hj] at hpos
    nlinarith [Real.pi_pos, hpos]
  have hjpos : 0 < j := by exact_mod_cast hjposR
  have hjge : (1 : ℤ) ≤ j := by omega
  -- Jordan's inequality on `[0, π/2]`: `sin x ≥ 2x/π`.
  have hjordan : 2 / Real.pi * (θ' / 2) ≤ Real.sin (θ' / 2) :=
    Real.mul_le_sin (by linarith) (by linarith [hθ'le])
  have hstep : (n : ℝ) * (2 / Real.pi * (θ' / 2)) ≤ (n : ℝ) * Real.sin (θ' / 2) :=
    mul_le_mul_of_nonneg_left hjordan (Nat.cast_nonneg n)
  have halg : (n : ℝ) * (2 / Real.pi * (θ' / 2)) = 2 * (j : ℝ) := by
    rw [show (n : ℝ) * (2 / Real.pi * (θ' / 2)) = ((n : ℝ) * θ') / Real.pi by ring, hj]
    field_simp
  have hjge1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjge
  calc (2 : ℝ) ≤ 2 * (j : ℝ) := by linarith
    _ = (n : ℝ) * (2 / Real.pi * (θ' / 2)) := halg.symm
    _ ≤ (n : ℝ) * Real.sin (θ' / 2) := hstep

end Work.Mostow.gapA
