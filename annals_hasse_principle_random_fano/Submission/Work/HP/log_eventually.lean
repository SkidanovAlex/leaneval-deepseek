import Mathlib
import Submission.Work.HP.ArchDefs

/-!
# `Work.HP.log_eventually`

The Archimedean factor is eventually small: for every `φ > 1` and every `ξ > 0`, the quantity
`(16 log(A φ) + 1)^{N_{d,n}}` is eventually dominated by `A^{N_{d,n}} · ξ`.

The point is that `N_{d,n} = NN d n ≥ 1` (there is always at least the monomial `x_0^d`), and the
ratio `(16 log(A φ) + 1)/A` tends to `0` as `A → ∞`, hence so does its `N_{d,n}`-th power.
-/

namespace Work.HP

open Filter
open scoped ENNReal

theorem log_eventually (d n : ℕ) (φ : ℝ) (hφ : 1 < φ) (ξ : ℝ) (hξ : 0 < ξ) :
    ∀ᶠ A : ℝ in atTop, (16 * Real.log (A * φ) + 1) ^ NN d n ≤ A ^ NN d n * ξ := by
  -- `Mon d n` is nonempty (the monomial `x_0^d`), so `NN d n ≠ 0`.
  have hkne : NN d n ≠ 0 := by
    have h : 0 < NN d n := by
      rw [NN, Fintype.card_pos_iff]
      refine ⟨⟨fun i => if i = 0 then (⟨d, Nat.lt_succ_self d⟩ : Fin (d + 1)) else 0, ?_⟩⟩
      have hterm : ∀ i : Fin (n + 1),
          (((if i = 0 then (⟨d, Nat.lt_succ_self d⟩ : Fin (d + 1)) else 0) : Fin (d + 1)) : ℕ)
            = if i = 0 then d else 0 := by
        intro i; by_cases hi : i = 0 <;> simp [hi]
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_ite_eq']
      simp
    omega
  have hφpos : 0 < φ := lt_trans zero_lt_one hφ
  -- The ratio `(16 log(A φ) + 1)/A` tends to `0`.
  have hlog : Tendsto (fun A : ℝ => Real.log A / A) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hinv : Tendsto (fun A : ℝ => A⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have hnum : Tendsto (fun A : ℝ => (16 * Real.log (A * φ) + 1) / A) atTop (nhds 0) := by
    have hmain : Tendsto (fun A : ℝ => 16 * (Real.log A / A) + (16 * Real.log φ + 1) * A⁻¹)
        atTop (nhds 0) := by
      have h := (hlog.const_mul 16).add (hinv.const_mul (16 * Real.log φ + 1))
      simpa using h
    refine hmain.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with A hA
    rw [Real.log_mul (ne_of_gt hA) (ne_of_gt hφpos)]
    field_simp
    ring
  -- Hence its `NN d n`-th power tends to `0`.
  have hpow : Tendsto (fun A : ℝ => ((16 * Real.log (A * φ) + 1) / A) ^ NN d n)
      atTop (nhds 0) := by
    have h := hnum.pow (NN d n)
    rwa [zero_pow hkne] at h
  filter_upwards [hpow.eventually_lt_const hξ, eventually_gt_atTop (0 : ℝ)] with A hlt hApos
  rw [div_pow] at hlt
  rw [div_lt_iff₀ (pow_pos hApos _)] at hlt
  nlinarith [hlt]

end Work.HP
