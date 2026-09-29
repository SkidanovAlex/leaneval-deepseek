import Mathlib

/-!
# A fundamental matrix solution of a first-order linear ODE system over `ℚ⟦X⟧`

Given `B : Matrix (Fin m) (Fin m) ℚ⟦X⟧`, we construct `Φ : Matrix (Fin m) (Fin m) ℚ⟦X⟧`
with `Φ 0 = 1` (the identity matrix) and `Φ' = B * Φ`.

The construction is the usual "integrating factor" / successive-approximation one, done
coefficient-wise: writing `Φ = ∑_d C_d X^d` and `B = ∑_k B_k X^k`, the equation
`Φ' = B Φ` becomes the recursion

  `C_0 = 1`,  `C_{d+1} = (d+1)⁻¹ · ∑_{k=0}^{d} B_k · C_{d-k} `

which (unlike `exp (∫ B)`, which is only correct when `∫B` commutes with `B`) is
unconditionally valid.  We realize the recursion via well-founded recursion on `ℕ`.
-/

open PowerSeries Matrix

namespace Work.ZeroEst3

/-- The sequence of coefficient matrices `C_d` of the fundamental solution, defined by the
recursion `C_0 = 1`, `C_{d+1} = (d+1)⁻¹ · ∑_{k<d+1} B_k · C_{d-k}`. -/
noncomputable def csolAux (m : ℕ) (B : Matrix (Fin m) (Fin m) (PowerSeries ℚ)) :
    ℕ → Matrix (Fin m) (Fin m) ℚ :=
  WellFounded.fix Nat.lt_wfRel.wf fun d ih =>
    match d with
    | 0 => 1
    | (n+1) => ((n+1 : ℕ) : ℚ)⁻¹ • ∑ k ∈ Finset.range (n+1),
        (B.map (PowerSeries.coeff k)) * ih (n - k)
          (by have h1 : n - k ≤ n := Nat.sub_le _ _
              exact lt_of_le_of_lt h1 (Nat.lt_succ_self n))

theorem csolAux_zero (m : ℕ) (B : Matrix (Fin m) (Fin m) (PowerSeries ℚ)) :
    csolAux m B 0 = 1 := by
  conv_lhs => unfold csolAux; rw [WellFounded.fix_eq]

theorem csolAux_succ (m : ℕ) (B : Matrix (Fin m) (Fin m) (PowerSeries ℚ)) (n : ℕ) :
    csolAux m B (n+1) = ((n+1 : ℕ) : ℚ)⁻¹ • ∑ k ∈ Finset.range (n+1),
        (B.map (PowerSeries.coeff k)) * csolAux m B (n - k) := by
  conv_lhs => unfold csolAux; rw [WellFounded.fix_eq]
  simp only [csolAux]

theorem csolAux_succ_apply (m : ℕ) (B : Matrix (Fin m) (Fin m) (PowerSeries ℚ)) (n : ℕ)
    (i j : Fin m) :
    csolAux m B (n+1) i j =
      ((n+1 : ℕ) : ℚ)⁻¹ * ∑ k ∈ Finset.range (n+1),
        ∑ l : Fin m, (B i l).coeff k * csolAux m B (n-k) l j := by
  rw [csolAux_succ]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply, Matrix.mul_apply, Matrix.map_apply]

theorem fundamentalPhi (m : ℕ) (B : Matrix (Fin m) (Fin m) (PowerSeries ℚ)) :
    ∃ Φ : Matrix (Fin m) (Fin m) (PowerSeries ℚ),
      (∀ i j, (Φ i j).coeff 0 = (1 : Matrix (Fin m) (Fin m) ℚ) i j) ∧
      ∀ i j, PowerSeries.derivative (R := ℚ) (Φ i j) = ∑ k, B i k * Φ k j := by
  refine ⟨fun i j => PowerSeries.mk (fun d => csolAux m B d i j), ?_, ?_⟩
  · intro i j
    rw [PowerSeries.coeff_mk, csolAux_zero]
  · intro i j
    apply PowerSeries.ext
    intro n
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mk]
    let S : ℚ := ∑ k ∈ Finset.range (n+1), ∑ l : Fin m, (B i l).coeff k * (csolAux m B (n-k)) l j
    have hcast : (↑n + 1 : ℚ) = ((n+1 : ℕ) : ℚ) := by push_cast; ring
    have ha : ((n+1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hL : csolAux m B (n+1) i j = (((n+1 : ℕ) : ℚ))⁻¹ * S := by
      rw [csolAux_succ_apply]
    have hR : PowerSeries.coeff n (∑ k : Fin m, B i k * PowerSeries.mk (fun d => csolAux m B d k j)) = S := by
      rw [map_sum]
      simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk]
      rw [Finset.sum_comm]
      exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
        (fun p => ∑ k : Fin m, (B i k).coeff p.1 * (csolAux m B p.2) k j) n
    rw [hL, hR, hcast]
    rw [mul_assoc, mul_comm S, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]

end Work.ZeroEst3
