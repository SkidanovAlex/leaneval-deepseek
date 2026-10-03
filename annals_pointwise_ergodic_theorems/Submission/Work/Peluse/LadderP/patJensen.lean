import Mathlib
import Submission.Work.Peluse.LadderP.stepPSupp

/-!
# `patPowState ≤ patNormState`

`patPowState` is the average over `h, h' ∈ [M₁]^j` of the **`2^t`-th powers** `boxNormPow t …` of
the box norms of the concatenated ladder state (`t = 2^j - 1 + n'`), whereas `patNormState` is the
same average of the box **norms** themselves.

For a `1`-bounded function supported in `symIcc N` each box-norm power lies in `[0,1]`
(`Work.Peluse.BoxNorm.boxNormPow_le_one`), and for `0 ≤ x ≤ 1` one has `x ≤ x ^ (1/2^t)`
(`Real.self_le_rpow_of_le_one`), i.e. `boxNormPow ≤ boxNorm`; since both states are the same convex
combination of the corresponding terms, the inequality follows term by term.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.LadderP

noncomputable section

open Work.Peluse

/-- For a box-norm power already known to be at most `1`, it is dominated by the box norm
(`boxNorm` is its `2^t`-th root, and `x ^ (1/2^t) ≥ x` on `[0,1]`). -/
private lemma boxNormPow_le_boxNorm_of_le_one {t : ℕ} {Q : Fin t → Finset ℤ} {S : Finset ℤ}
    {f : ℤ → ℂ} (h : Work.Peluse.boxNormPow t Q S f ≤ 1) :
    Work.Peluse.boxNormPow t Q S f ≤ Work.Peluse.boxNorm t Q S f := by
  rw [Work.Peluse.boxNorm]
  refine Real.self_le_rpow_of_le_one (norm_nonneg _) h ?_
  rw [div_le_one (by positivity)]
  exact one_le_pow₀ (by norm_num)

theorem patJensen (j n' M₁ : ℕ) (hM₁ : 1 ≤ M₁) (c : ℤ) (L D N : ℕ) (f : ℤ → ℂ)
    (hbd : ∀ x : ℤ, ‖f x‖ ≤ 1) (hsup : Work.Peluse.SupportIn f N) :
    Work.Peluse.LadderP.patPowState j n' M₁ c L D N f
      ≤ Work.Peluse.LadderP.patNormState j n' M₁ c L D N f := by
  have _ : 1 ≤ M₁ := hM₁
  have hsupp : ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → f x = 0 := by
    intro x hx
    exact hsup x (Nat.lt_of_not_le (fun h => hx (mem_symIcc_iff.mpr h)))
  unfold Work.Peluse.LadderP.patPowState Work.Peluse.LadderP.patNormState
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg M₁)) _)
  refine Finset.sum_le_sum (fun h _ => Finset.sum_le_sum (fun h' _ => ?_))
  exact boxNormPow_le_boxNorm_of_le_one (Work.Peluse.BoxNorm.boxNormPow_le_one hbd hsupp)

end

end Work.Peluse.LadderP
