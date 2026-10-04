import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.ENormSq_seriesFun_le
import Submission.Work.Diff.STE.summable_wt_zpow
import Submission.Work.Diff.STE.flat.CSq_le_of_decay

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `ℓ¹`-summability of the derivative multiplier under a polynomial decay hypothesis

`Work.Diff.STE.fill.tsum_norm_dmulV_le_of_decay`: if the coefficient family `γ : ℤⁿ → ℂ`
decays like `‖γ k‖ ≤ C ⟨k⟩^{-M}` with `M > (n+4)/2`, then for every list `l` of at most two
derivative directions the differentiated family `dmulV l γ` (`dmulV` multiplies the `k`-th
coefficient by `∏_{i ∈ l} 2πi kᵢ`, see `Submission/Work/Diff/STE/ENormSq_seriesFun_le.lean`)
is summable in `ℓ¹`, with a bound uniform in `γ`, `C` and `l` of the form `K C`.

The whole content is the elementary chain

`‖dmulV l γ k‖ ≤ (2π ⟨k⟩)^{|l|} ‖γ k‖ ≤ (2π)^{2} ⟨k⟩^{2} · C ⟨k⟩^{-M}
    = C (2π)^{2} ⟨k⟩^{-(M-2)}`  (since `|l| ≤ 2` and `⟨k⟩ ≥ 1`),

and the weight `⟨k⟩^{-(M-2)}` is summable on `ℤⁿ` precisely because `n < 2(M-2)`, which is the
hypothesis `hM : n + 4 < 2M`.
-/

namespace Work.Diff.STE.fill

open scoped BigOperators

set_option linter.unusedVariables false

/-- **The exponent identity behind the decay estimate.**  For `M ≥ 2` and a positive real `w`,
`w ^ 2 * (w ^ M)⁻¹ = (w ^ (M - 2))⁻¹`: the two extra powers of the weight gained by the
derivative multiplier are exactly traded against the decay order. -/
private lemma sq_mul_inv_pow_eq {w : ℝ} (hw : 0 < w) {M : ℕ} (hM : 2 ≤ M) :
    w ^ 2 * (w ^ M)⁻¹ = (w ^ (M - 2))⁻¹ := by
  rw [show w ^ M = w ^ (M - 2) * w ^ 2 by
    rw [← pow_add]; exact congrArg (fun e => w ^ e) (by omega)]
  rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 (ne_of_gt hw)), one_mul]

theorem tsum_norm_dmulV_le_of_decay {n M : ℕ} (hM : n + 4 < 2 * M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (C : ℝ) (hC : 0 ≤ C) (γ : (Fin n → ℤ) → ℂ),
      (∀ k : Fin n → ℤ, ‖γ k‖ * (Work.Diff.STE.wt k) ^ M ≤ C) →
      ∀ (l : List (Fin n)), l.length ≤ 2 →
        Summable (fun k : Fin n → ℤ => ‖Work.Diff.STE.dmulV l γ k‖) ∧
        (∑' k : Fin n → ℤ, ‖Work.Diff.STE.dmulV l γ k‖) ≤ K * C := by
  -- `hM` gives `M ≥ 3`, hence `n < 2 (M - 2)`, the summability range of the weight `⟨k⟩^{-(M-2)}`
  have hM3 : 3 ≤ M := by omega
  have hcard : n < 2 * (M - 2) := by omega
  have hsumT : Summable (fun k : Fin n → ℤ => ((Work.Diff.STE.wt k) ^ (M - 2))⁻¹) :=
    Work.Diff.STE.flat.summable_wt_inv' (n := n) (s := M - 2) hcard
  refine ⟨(2 * Real.pi) ^ 2 * ∑' k : Fin n → ℤ, ((Work.Diff.STE.wt k) ^ (M - 2))⁻¹,
    mul_nonneg (sq_nonneg _)
      (tsum_nonneg fun k => inv_nonneg.mpr (pow_nonneg (Work.Diff.STE.wt_pos k).le _)), ?_⟩
  intro C _hC γ hγ l hl
  -- the pointwise bound: `(2π⟨k⟩)^{|l|} · (⟨k⟩^{-M} C) ≤ C (2π)² ⟨k⟩^{-(M-2)}`
  have hpt : ∀ k : Fin n → ℤ,
      ‖Work.Diff.STE.dmulV l γ k‖
        ≤ C * (2 * Real.pi) ^ 2 * ((Work.Diff.STE.wt k) ^ (M - 2))⁻¹ := by
    intro k
    have hw : (0 : ℝ) < Work.Diff.STE.wt k := Work.Diff.STE.wt_pos k
    have hwb : (0 : ℝ) ≤ 2 * Real.pi * Work.Diff.STE.wt k :=
      mul_nonneg (by positivity) hw.le
    -- the decay hypothesis, solved for `‖γ k‖`
    have hgam : ‖γ k‖ ≤ C * ((Work.Diff.STE.wt k) ^ M)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hw M)]
      exact hγ k
    -- the base `2π⟨k⟩` is at least `1`, so the exponent `|l|` may be raised to `2`
    have hbase : (1 : ℝ) ≤ 2 * Real.pi * Work.Diff.STE.wt k := by
      nlinarith [Real.pi_gt_three, Work.Diff.STE.wt_one_le k]
    have hpow : (2 * Real.pi * Work.Diff.STE.wt k) ^ l.length
        ≤ (2 * Real.pi * Work.Diff.STE.wt k) ^ 2 := pow_le_pow_right₀ hbase hl
    have hkey : (Work.Diff.STE.wt k) ^ 2 * ((Work.Diff.STE.wt k) ^ M)⁻¹
        = ((Work.Diff.STE.wt k) ^ (M - 2))⁻¹ :=
      sq_mul_inv_pow_eq hw (by omega)
    calc ‖Work.Diff.STE.dmulV l γ k‖
        ≤ (2 * Real.pi * Work.Diff.STE.wt k) ^ l.length * ‖γ k‖ :=
          Work.Diff.STE.norm_dmulV_le l γ k
      _ ≤ (2 * Real.pi * Work.Diff.STE.wt k) ^ 2
            * (C * ((Work.Diff.STE.wt k) ^ M)⁻¹) :=
          mul_le_mul hpow hgam (norm_nonneg _) (pow_nonneg hwb 2)
      _ = C * ((2 * Real.pi) ^ 2
            * ((Work.Diff.STE.wt k) ^ 2 * ((Work.Diff.STE.wt k) ^ M)⁻¹)) := by
          rw [mul_pow]; ring
      _ = C * ((2 * Real.pi) ^ 2 * ((Work.Diff.STE.wt k) ^ (M - 2))⁻¹) := by rw [hkey]
      _ = C * (2 * Real.pi) ^ 2 * ((Work.Diff.STE.wt k) ^ (M - 2))⁻¹ := by ring
  have hmaj : Summable (fun k : Fin n → ℤ =>
      C * (2 * Real.pi) ^ 2 * ((Work.Diff.STE.wt k) ^ (M - 2))⁻¹) :=
    hsumT.mul_left _
  have hsumm : Summable (fun k : Fin n → ℤ => ‖Work.Diff.STE.dmulV l γ k‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hpt hmaj
  refine ⟨hsumm, ?_⟩
  calc ∑' k : Fin n → ℤ, ‖Work.Diff.STE.dmulV l γ k‖
      ≤ ∑' k : Fin n → ℤ, C * (2 * Real.pi) ^ 2 * ((Work.Diff.STE.wt k) ^ (M - 2))⁻¹ :=
        Summable.tsum_le_tsum hpt hsumm hmaj
    _ = (C * (2 * Real.pi) ^ 2) * ∑' k : Fin n → ℤ, ((Work.Diff.STE.wt k) ^ (M - 2))⁻¹ :=
        tsum_mul_left
    _ = ((2 * Real.pi) ^ 2 * ∑' k : Fin n → ℤ, ((Work.Diff.STE.wt k) ^ (M - 2))⁻¹) * C := by
        ring

end Work.Diff.STE.fill
