import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMComp.RedProj.ExpLowerDiophFund
import Submission.Work.TMComp.RedProj.exists_pos_forall_lt

/-!
# Exponential lower bound for `‖exp (2 π i k α) - 1‖` under `DiophBelow α b`

If `DiophBelow α b` holds (the distance of `k α` to the nearest integer decays at most like
`e^{-b k}`) and `η > b`, then `‖exp (2 π i k α) - 1‖` is bounded below by
`C · e^{-η |k|}` for every nonzero integer `k`, for some constant `C > 0`.

The proof splits the nonzero integers into the finitely many with `|k| < N` (where the quantity
is strictly positive, hence has a positive minimum, since `α` is irrational) and the rest
(where `4 · fracDist ≥ 4 e^{-b|k|}` grows at rate `b < η`).
-/

namespace Work.TMComp.RedProj.Part2

open Filter

theorem ExpLowerDioph (α b : ℝ) (hα : Irrational α) (hb : 0 < b)
    (h : Work.TMContract.DiophBelow α b) (η : ℝ) (hη : b < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℤ, k ≠ 0 →
      C * Real.exp (-(η * |(k : ℝ)|)) ≤ ‖Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) - 1‖ := by
  -- `DiophBelow` is an `atTop`-eventually statement on `ℕ`.
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h
  set N : ℕ := max N₀ 1 with hNdef
  -- On the finitely many small indices `1 ≤ m < N` the quantity
  -- `‖exp (2 π i m α) - 1‖ * exp (η m)` is strictly positive, so it has a positive minimum `c`.
  have hpos : ∀ m : ℕ, 1 ≤ m → m < N →
      0 < ‖Complex.exp (2 * Real.pi * (m:ℝ) * α * Complex.I) - 1‖ * Real.exp (η * (m:ℝ)) := by
    intro m hm _
    have h1 : 0 < ‖Complex.exp (2 * Real.pi * ((m:ℤ):ℝ) * α * Complex.I) - 1‖ :=
      Work.TMComp.RedProj.norm_exp_two_pi_pos_of_irrational hα (k := (m:ℤ)) (by omega)
    have h2 : 0 < Real.exp (η * (m:ℝ)) := Real.exp_pos _
    have h3 := mul_pos h1 h2
    simpa using h3
  obtain ⟨c, hcpos, hc⟩ := Work.TMComp.RedProj.exists_pos_forall_lt hpos
  -- The constant `min 2 c` works.
  refine ⟨min 2 c, lt_min two_pos hcpos, ?_⟩
  -- Uniform statement in `m : ℕ`.
  have hkey : ∀ m : ℕ, 1 ≤ m → min 2 c ≤
      ‖Complex.exp (2 * Real.pi * (m:ℝ) * α * Complex.I) - 1‖ * Real.exp (η * (m:ℝ)) := by
    intro m hm
    rcases lt_or_ge m N with hmN | hmN
    · exact le_trans (min_le_right _ _) (hc m hm hmN)
    · -- large index: use `DiophBelow` and `4 * fracDist ≤ ‖exp - 1‖`
      have hN0le : N₀ ≤ m := le_trans (le_max_left _ _) hmN
      have hb1 : Real.exp (-(b * (m:ℝ))) ≤ Work.TMContract.fracDist ((m:ℝ) * α) := hN₀ m hN0le
      have h4 : 4 * Work.TMContract.fracDist ((m:ℝ) * α)
          ≤ ‖Complex.exp (2 * Real.pi * (m:ℝ) * α * Complex.I) - 1‖ := by
        simpa using Work.TMComp.RedProj.four_mul_fracDist_le_norm α (m : ℤ)
      have h4b : 4 * Real.exp (-(b * (m:ℝ)))
          ≤ ‖Complex.exp (2 * Real.pi * (m:ℝ) * α * Complex.I) - 1‖ :=
        le_trans (mul_le_mul_of_nonneg_left hb1 (by norm_num)) h4
      have hprod : Real.exp (-(b * (m:ℝ))) * Real.exp (η * (m:ℝ))
          = Real.exp ((η - b) * (m:ℝ)) := by
        rw [← Real.exp_add]; congr 1; ring
      have hone : (1:ℝ) ≤ Real.exp ((η - b) * (m:ℝ)) :=
        Real.one_le_exp (mul_nonneg (by linarith) (Nat.cast_nonneg m))
      have hexpnn : (0:ℝ) ≤ Real.exp (η * (m:ℝ)) := Real.exp_nonneg _
      have hstep : 4 ≤ ‖Complex.exp (2 * Real.pi * (m:ℝ) * α * Complex.I) - 1‖ * Real.exp (η * (m:ℝ)) := by
        have h1 : 4 * Real.exp (-(b * (m:ℝ))) * Real.exp (η * (m:ℝ))
            ≤ ‖Complex.exp (2 * Real.pi * (m:ℝ) * α * Complex.I) - 1‖ * Real.exp (η * (m:ℝ)) :=
          mul_le_mul_of_nonneg_right h4b hexpnn
        have h2 : 4 ≤ 4 * Real.exp (-(b * (m:ℝ))) * Real.exp (η * (m:ℝ)) := by
          rw [mul_assoc, hprod]
          nlinarith
        linarith
      exact le_trans (le_trans (min_le_left _ _) (by norm_num)) hstep
  intro k hk
  have hm1 : 1 ≤ k.natAbs := Int.natAbs_pos.mpr hk
  have hk1 := hkey k.natAbs hm1
  have habs : (((k.natAbs : ℕ)) : ℝ) = |(k:ℝ)| := by simp
  have hnorm : ‖Complex.exp (2 * Real.pi * (((k.natAbs : ℕ)) : ℝ) * α * Complex.I) - 1‖
      = ‖Complex.exp (2 * Real.pi * (k:ℝ) * α * Complex.I) - 1‖ :=
    (Work.TMComp.RedProj.norm_exp_two_pi_natAbs α k).symm
  have hstep := mul_le_mul_of_nonneg_right hk1 (Real.exp_nonneg (-(η * |(k:ℝ)|)))
  refine le_trans hstep ?_
  rw [hnorm]
  have hone : Real.exp (η * (((k.natAbs : ℕ)) : ℝ)) * Real.exp (-(η * |(k:ℝ)|)) = 1 := by
    rw [← Real.exp_add, habs, show η * |(k:ℝ)| + -(η * |(k:ℝ)|) = 0 by ring, Real.exp_zero]
  rw [mul_assoc, hone, mul_one]

end Work.TMComp.RedProj.Part2
