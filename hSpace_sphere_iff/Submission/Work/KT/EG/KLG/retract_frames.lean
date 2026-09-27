import Mathlib
import Submission.Work.KT.EG.KLG.kappa_bott_defs

/-!
# `Work.KT.EG.KLG.retract_frames`

The frames `upFrame`, `dnFrame` of `Work.KT.EG.KLG.kappa_bott_defs` are *split* by the
retractions `upRet`, `dnRet`: for any idempotents `A`, `B` over `C(X × Ball ℂ, ℂ)` with
`A + B = 1`,

  `upRet A B * upFrame A B = 1`   and   `dnRet A B * dnFrame A B = 1`.

Both products are computed entrywise and turn out to be exactly `A * A + B * B`: the two
"extra" columns of the frames are cancelled by the retractions because

* `(1 + s)⁻¹ · (1 + s) = 1` (`zsinv_mul_one_add_zs`), which kills the upper-disc second column;
* `ζ ζ̄ + s² = 1` (`zc_mul_zcb_eq` and `zsinv * (1 + s) = 1`), which kills the lower-disc one.

Hence `upRet * upFrame = A * A + B * B = A + B = 1` under the hypotheses, and similarly for the
lower disc.
-/

namespace Work.KT.EG.KLG

open _root_.Matrix

noncomputable section

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- The upper-disc contraction: `upRet * upFrame = A * A + B * B`.  The `(n × 2)`-block of the
frame, `v ↦ B v ⊗ (1+s, ζ)`, is sent by the retraction to `B v ⊗ ((1+s)⁻¹, 0)`; summing over the
two columns gives `(1+s)⁻¹(1+s) = 1` on the first and `0 · ζ = 0` on the second. -/
lemma upRet_mul_upFrame {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) C(X × Work.KT.Ball ℂ, ℂ)) :
    upRet X A B * upFrame X A B = A * A + B * B := by
  apply Matrix.ext
  intro i k
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [upRet, upFrame]
  have h1 : (∑ a₁ : Fin n, A i a₁ * A a₁ k) = (A * A) i k := Matrix.mul_apply.symm
  have h2 : (∑ a₂ : Fin n × Fin 2,
      (B i a₂.1 * (if a₂.2 = 0 then Work.KT.Fund.KL.zsinv X else 0)) *
        (B a₂.1 k *
          (if a₂.2 = 0 then 1 + Work.KT.Fund.KL.zs X else Work.KT.Fund.KL.zc X)))
      = (B * B) i k := by
    rw [Fintype.sum_prod_type, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro a _
    rw [Fin.sum_univ_two]
    have h10 : ¬ ((1 : Fin 2) = 0) := by decide
    simp only [h10, if_false, if_true, mul_zero, zero_mul, add_zero]
    linear_combination (B i a * B a k) * (Work.KT.Fund.KL.zsinv_mul_one_add_zs X)
  rw [h1, h2, Matrix.add_apply]

/-- The lower-disc contraction: `dnRet * dnFrame = A * A + B * B`.  Here the retraction sends the
`(n × 2)`-block of the frame, `v ↦ B v ⊗ (ζ̄, 1+s)`, to `B v ⊗ (ζ, s²(1+s)⁻¹)`; summing over the
two columns gives `ζ ζ̄ + s²(1+s)⁻¹(1+s) = ζ ζ̄ + s² = 1`. -/
lemma dnRet_mul_dnFrame {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) C(X × Work.KT.Ball ℂ, ℂ)) :
    dnRet X A B * dnFrame X A B = A * A + B * B := by
  apply Matrix.ext
  intro i k
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [dnRet, dnFrame]
  have h1 : (∑ a₁ : Fin n, A i a₁ * A a₁ k) = (A * A) i k := Matrix.mul_apply.symm
  have h2 : (∑ a₂ : Fin n × Fin 2,
      (B i a₂.1 * (if a₂.2 = 0 then Work.KT.Fund.KL.zc X
        else Work.KT.Fund.KL.zs X * Work.KT.Fund.KL.zs X * Work.KT.Fund.KL.zsinv X)) *
        (B a₂.1 k *
          (if a₂.2 = 0 then Work.KT.Fund.KL.zcb X else 1 + Work.KT.Fund.KL.zs X)))
      = (B * B) i k := by
    rw [Fintype.sum_prod_type, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro a _
    rw [Fin.sum_univ_two]
    have h10 : ¬ ((1 : Fin 2) = 0) := by decide
    simp only [h10, if_false, if_true]
    linear_combination (B i a * B a k) * (Work.KT.Fund.KL.zc_mul_zcb_eq X)
      + (B i a * B a k * (Work.KT.Fund.KL.zs X * Work.KT.Fund.KL.zs X))
        * (Work.KT.Fund.KL.zsinv_mul_one_add_zs X)
  rw [h1, h2, Matrix.add_apply]

theorem retract_frames (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Work.KT.Ball ℂ, ℂ))
    (hA : A * A = A) (hB : B * B = B) (hA1B : A + B = 1) :
    (Work.KT.EG.KLG.upRet X A B * Work.KT.EG.KLG.upFrame X A B = 1) ∧
      (Work.KT.EG.KLG.dnRet X A B * Work.KT.EG.KLG.dnFrame X A B = 1) := by
  constructor
  · rw [upRet_mul_upFrame, hA, hB, hA1B]
  · rw [dnRet_mul_dnFrame, hA, hB, hA1B]

end

end Work.KT.EG.KLG
