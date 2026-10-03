import Mathlib
import Submission.Work.KMTAreas.A7.ModelOps

namespace Work.A7.ModelApproxCore_aux

/-- The defining iterated sum of the composed kernel `kernComp K κ κ'` may be evaluated as a
single sum over `ℤ × ℤ`:

`∑' a', ∑' b', K (a - a') (b - b') * κ a' * κ' b' = ∑' z, K (a - z.1) (b - z.2) * κ z.1 * κ' z.2`.

The hypothesis `hK` (joint `ℓ¹`-summability of `K` on `ℤ × ℤ`) together with the `ℓ¹`-summability
of `κ`, `κ'` makes the two-variable family absolutely summable, so Fubini for series
(`Summable.tsum_prod`) applies. -/
theorem kernComp_eq_tsum {K : ℤ → ℤ → ℂ} {κ κ' : ℤ → ℂ}
    (hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖) (hκ : Summable fun j : ℤ => ‖κ j‖)
    (hκ' : Summable fun j : ℤ => ‖κ' j‖) (a b : ℤ) :
    Work.KMTAreas.A7.kernComp K κ κ' a b
      = ∑' z : ℤ × ℤ, K (a - z.1) (b - z.2) * κ z.1 * κ' z.2 := by
  -- `κ` and `κ'` are bounded, with the `ℓ¹`-norms as explicit bounds.
  have hCκnn : 0 ≤ ∑' j : ℤ, ‖κ j‖ := tsum_nonneg fun _ => norm_nonneg _
  have hCκ'nn : 0 ≤ ∑' j : ℤ, ‖κ' j‖ := tsum_nonneg fun _ => norm_nonneg _
  have hκle : ∀ j : ℤ, ‖κ j‖ ≤ ∑' j : ℤ, ‖κ j‖ := fun j => by
    have := hκ.sum_le_tsum ({j} : Finset ℤ) (fun i _ => norm_nonneg _)
    simpa using this
  have hκ'le : ∀ j : ℤ, ‖κ' j‖ ≤ ∑' j : ℤ, ‖κ' j‖ := fun j => by
    have := hκ'.sum_le_tsum ({j} : Finset ℤ) (fun i _ => norm_nonneg _)
    simpa using this
  -- Reindexing `‖K‖` by the translation `z ↦ (a - z.1, b - z.2)` keeps it summable.
  have hbase : Summable fun z : ℤ × ℤ => ‖K (a - z.1) (b - z.2)‖ := by
    have h := (Equiv.summable_iff (Equiv.prodCongr (Equiv.subLeft a) (Equiv.subLeft b))).mpr hK
    simpa [Function.comp_def, Equiv.prodCongr_apply, Equiv.subLeft_apply] using h
  have hg : Summable fun z : ℤ × ℤ =>
      (∑' j : ℤ, ‖κ j‖) * (∑' j : ℤ, ‖κ' j‖) * ‖K (a - z.1) (b - z.2)‖ :=
    hbase.mul_left _
  -- Hence the joint family is absolutely summable.
  have hF : Summable fun z : ℤ × ℤ => K (a - z.1) (b - z.2) * κ z.1 * κ' z.2 :=
    Summable.of_norm_bounded hg (fun z => by
      rw [norm_mul, norm_mul]
      calc ‖K (a - z.1) (b - z.2)‖ * ‖κ z.1‖ * ‖κ' z.2‖
          ≤ ‖K (a - z.1) (b - z.2)‖ * (∑' j : ℤ, ‖κ j‖) * (∑' j : ℤ, ‖κ' j‖) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hκle z.1) (norm_nonneg _))
              (hκ'le z.2) (norm_nonneg _) (mul_nonneg (norm_nonneg _) hCκnn)
        _ = (∑' j : ℤ, ‖κ j‖) * (∑' j : ℤ, ‖κ' j‖) * ‖K (a - z.1) (b - z.2)‖ := by ring)
  -- Fubini for series converts the iterated sum into the sum over `ℤ × ℤ`.
  rw [Work.KMTAreas.A7.kernComp]
  exact hF.tsum_prod.symm

end Work.A7.ModelApproxCore_aux
