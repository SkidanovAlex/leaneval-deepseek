import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseBox.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chBimg_arith_aux`

The pure real-arithmetic core of the `chBimg` slot bound: with `t = μa³`, `d = t^{6/323}` and
`ℓ = a·t^{−326/646}` the product `d^{2M}·μ(ℓ³+1)/a` is bounded by
`(a³(max 1 ε₀)^{(12M−166)/323} + (max 1 ε₀)^{(12M+323)/323})/a⁴` for `M ≥ 14`, which is exactly
the amount of `d^{2M}`-smallness needed to beat the `(μa³)^{1/2}` loss in the slot's budget
`A μ = K0·a/(8μ(ℓ³+1))`.

This is a backup of the delegated `Work.BoseBoxFock.PCFU.chBimg_arith` (same statement), proved
here so that `PCFU/chBimg_piece.lean` does not depend on the delegation.
-/

namespace Work.BoseBoxFock.PCFU

/-- Backup proof attempt for the delegated arithmetic lemma. -/
theorem chBimg_arith_aux {a t ε₀ : ℝ} (ha : 0 < a) (ht : 0 < t) (htε : t ≤ ε₀)
    (M : ℕ) (hM : 14 ≤ M) :
    (Work.BoseBox.fsXp t 6) ^ (2 * M) * (t / a ^ 3)
        * ((Work.BoseBox.fsXp t (-(3 / 2 : ℝ)) * (t / a ^ 2) ^ (-(1 / 2 : ℝ))) ^ 3 + 1) / a
      ≤ (a ^ 3 * (max 1 ε₀) ^ (((12 : ℝ) * M - 166) / 323)
          + (max 1 ε₀) ^ (((12 : ℝ) * M + 323) / 323)) / a ^ 4 := by
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  have ha0 : (0 : ℝ) ≤ a := le_of_lt ha
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 14 := ⟨M - 14, by omega⟩
  set A : ℝ := 12 * (↑k + 14) / 323 with hAdef
  -- step 1: the `d`-power
  have hpow : (Work.BoseBox.fsXp t 6) ^ (2 * (k + 14)) = t ^ A := by
    rw [Work.BoseBox.fsXp, ← Real.rpow_natCast, ← Real.rpow_mul ht0, hAdef]
    congr 1
    push_cast
    ring
  -- step 2: the two factors of the cube
  have hK3 : Work.BoseBox.fsXp t (-(3 / 2 : ℝ)) = t ^ (-(3 / 646 : ℝ)) := by
    rw [Work.BoseBox.fsXp]
    congr 1
    norm_num
  have hhalf : (t / a ^ 2) ^ (-(1 / 2 : ℝ)) = a * t ^ (-(1 / 2 : ℝ)) := by
    rw [Real.div_rpow ht0 (by positivity : (0 : ℝ) ≤ a ^ 2)]
    have ha2 : ((a ^ 2 : ℝ)) ^ (-(1 / 2 : ℝ)) = a⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha0,
        show ((2 : ℕ) : ℝ) * (-(1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
    rw [ha2, div_eq_mul_inv, inv_inv]
    ring
  -- step 3: the cube
  have hcube : (Work.BoseBox.fsXp t (-(3 / 2 : ℝ)) * (t / a ^ 2) ^ (-(1 / 2 : ℝ))) ^ 3
      = a ^ 3 * t ^ (-(978 / 646 : ℝ)) := by
    rw [hK3, hhalf, mul_pow, mul_pow]
    rw [show (t ^ (-(3 / 646 : ℝ))) ^ 3 = t ^ (-(9 / 646 : ℝ)) from by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht0]
      norm_num]
    rw [show (t ^ (-(1 / 2 : ℝ))) ^ 3 = t ^ (-(3 / 2 : ℝ)) from by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht0]
      norm_num]
    rw [show t ^ (-(9 / 646 : ℝ)) * (a ^ 3 * t ^ (-(3 / 2 : ℝ)))
        = a ^ 3 * (t ^ (-(9 / 646 : ℝ)) * t ^ (-(3 / 2 : ℝ))) from by ring,
      ← Real.rpow_add ht]
    rw [show (-(9 / 646 : ℝ) + -(3 / 2 : ℝ)) = -(978 / 646 : ℝ) by norm_num]
  -- step 4: the left-hand side
  have hL : (Work.BoseBox.fsXp t 6) ^ (2 * (k + 14)) * (t / a ^ 3)
        * ((Work.BoseBox.fsXp t (-(3 / 2 : ℝ)) * (t / a ^ 2) ^ (-(1 / 2 : ℝ))) ^ 3 + 1) / a
      = (a ^ 3 * t ^ (((12 : ℝ) * (k + 14) - 166) / 323)
          + t ^ (((12 : ℝ) * (k + 14) + 323) / 323)) / a ^ 4 := by
    rw [hpow, hcube]
    -- expand and cancel
    rw [show t ^ A * (t / a ^ 3) * (a ^ 3 * t ^ (-(978 / 646 : ℝ)) + 1) / a
        = t ^ A * t * t ^ (-(978 / 646 : ℝ)) / a
          + t ^ A * t / a ^ 4 from by
      field_simp]
    rw [show t ^ A * t * t ^ (-(978 / 646 : ℝ))
        = t ^ (A + 1 + -(978 / 646 : ℝ)) from by
      rw [← Real.rpow_add_one ht.ne' A, ← Real.rpow_add ht]]
    rw [show t ^ A * t = t ^ (A + 1) from by rw [← Real.rpow_add_one ht.ne' A]]
    rw [show t ^ (A + 1 + -(978 / 646 : ℝ)) / a
          + t ^ (A + 1) / a ^ 4
        = (a ^ 3 * t ^ (A + 1 + -(978 / 646 : ℝ)) + t ^ (A + 1)) / a ^ 4 from by
      field_simp]
    rw [show A + 1 + -(978 / 646 : ℝ) = ((12 : ℝ) * (k + 14) - 166) / 323 from by
      rw [hAdef]; ring,
      show A + 1 = ((12 : ℝ) * (k + 14) + 323) / 323 from by rw [hAdef]; ring]
  rw [hL]
  -- step 5: monotonicity in the base
  have hbase : t ≤ max 1 ε₀ := le_trans htε (le_max_right _ _)
  have he1 : (0 : ℝ) ≤ ((12 : ℝ) * (k + 14) - 166) / 323 := by
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    apply div_nonneg _ (by norm_num)
    nlinarith
  have he2 : (0 : ℝ) ≤ ((12 : ℝ) * (k + 14) + 323) / 323 := by
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    apply div_nonneg _ (by norm_num)
    nlinarith
  have hm1 := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow ht0 hbase he1) (by positivity : (0 : ℝ) ≤ a ^ 3)
  have hm2 := Real.rpow_le_rpow ht0 hbase he2
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  simp only [Nat.cast_add, Nat.cast_ofNat] at hm1 hm2 ⊢
  linarith [hm1, hm2]

end Work.BoseBoxFock.PCFU
