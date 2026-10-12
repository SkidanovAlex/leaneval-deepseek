import ChallengeDeps
import Submission.Work.BoseFixR.FarResidBaux.epsFar_le_inv_eight
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

open Work.BoseBox

/-!
# `farRadABound` — the two scalar slack factors of the far leg

The far leg of FS §9 carries two multiplicative slacks: the ε-split parameter
`epsFar v μ ρ = √(𝓜/((ρ+μ)ℓ³))` of `eq:ChoiceEpsilon`, and the regularisation
gap `ε_T = fsXp (μa³) (23/4) = (μa³)^{23/1292}`.  Both are *tiny* at the
admissible diluteness (`FarResidBaux.epsFar_le_inv_eight` and the lemma below),
so their product is bounded below by `9/10`, which is all the far leg needs.

The second factor is the monomial comparison `(μa³)^{23/1292} ≤ (10^{-4000})^{23/1292}
= 10^{-23000/323} ≤ 10^{-2}` at `μa³ ≤ 10^{-4000}`.
-/

/-- **The regularisation gap is below `1/100`** at diluteness `μa³ ≤ 10^{-4000}`:
`fsXp t (23/4) = t^{23/(4·323)} = t^{23/1292} ≤ (10^{-4000})^{23/1292}
= 10^{-23000/323} ≤ 10^{-2}`. -/
lemma fsXp_twentythree_quarters_le {t : ℝ} (ht0 : 0 < t)
    (htle : t ≤ (10 : ℝ) ^ (-(4000 : ℤ))) :
    Work.BoseBox.fsXp t (23 / 4) ≤ 1 / 100 := by
  have hmain : t ^ (((23 : ℝ) / 4) / 323) ≤ 1 / 100 := by
    have h1 : t ^ (((23 : ℝ) / 4) / 323)
        ≤ ((10 : ℝ) ^ (-(4000 : ℤ))) ^ (((23 : ℝ) / 4) / 323) :=
      Real.rpow_le_rpow ht0.le htle (by norm_num)
    have h2 : ((10 : ℝ) ^ (-(4000 : ℤ))) = (1 / 10 : ℝ) ^ (4000 : ℕ) := by
      rw [show (-(4000 : ℤ)) = -((4000 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast,
        ← inv_pow, ← one_div]
    rw [h2] at h1
    have h3 : ((1 / 10 : ℝ) ^ (4000 : ℕ)) ^ (((23 : ℝ) / 4) / 323)
        = (1 / 10 : ℝ) ^ (((4000 : ℕ) : ℝ) * (((23 : ℝ) / 4) / 323)) := by
      rw [← Real.rpow_natCast (1 / 10 : ℝ) 4000,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 10)]
    rw [h3] at h1
    have h4 : (1 / 10 : ℝ) ^ (((4000 : ℕ) : ℝ) * (((23 : ℝ) / 4) / 323))
        ≤ (1 / 10 : ℝ) ^ (((2 : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
    have h5 : (1 / 10 : ℝ) ^ (((2 : ℕ) : ℝ)) = 1 / 100 := by
      rw [Real.rpow_natCast]; norm_num
    linarith
  rwa [Work.BoseBox.fsXp]

/-- `ε_T` of FS's parameter block at the pair `(μ, a v)` is below `1/100` as soon
as `μa³ ≤ 10^{-4000}`. -/
lemma paramsAt_eT_le_inv_hundred {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (hμ : 0 < μ) (hav : 0 < BoseGases.a v)
    (htle : μ * BoseGases.a v ^ 3 ≤ (10 : ℝ) ^ (-(4000 : ℤ))) :
    (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT ≤ 1 / 100 := by
  have ht0 : 0 < μ * BoseGases.a v ^ 3 := mul_pos hμ (pow_pos hav 3)
  have heq : (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
      = Work.BoseBox.fsXp (μ * BoseGases.a v ^ 3) (23 / 4) := by
    simp [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
  rw [heq]
  exact fsXp_twentythree_quarters_le ht0 htle

/-- **The two scalar slacks of the far leg are harmless**: at the admissible box
data the product of `1 - epsFar` and `1 - ε_T` is at least `9/10`.

`epsFar ≤ 10^{-8}` is `FarResidBaux.epsFar_le_inv_eight` and `ε_T ≤ 1/100` is
`paramsAt_eT_le_inv_hundred`, so the product dominates
`(1 - 10^{-8})(1 - 1/100) > 9/10`. -/
theorem farRadABound {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ε₀ μ ρ : ℝ}
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) (hε₀ : ε₀ ≤ 10 ^ (-(4000 : ℤ)))
    (hav : 0 < BoseGases.a v) (hρ : 0 ≤ ρ) (hfar : Work.BoseFixR.FarCond v μ ρ) :
    9 / 10 ≤ (1 - Work.BoseFixR.epsFar v μ ρ)
      * (1 - (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT) := by
  have hE : Work.BoseFixR.epsFar v μ ρ ≤ 1 / 10 ^ 8 :=
    FarResidBaux.epsFar_le_inv_eight hAdm hε₀ hav hρ hfar
  have hT : (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT ≤ 1 / 100 :=
    paramsAt_eT_le_inv_hundred hAdm.1 hav (hAdm.2.1.trans hε₀)
  have hE1 : Work.BoseFixR.epsFar v μ ρ ≤ 1 := by linarith
  calc (9 : ℝ) / 10 ≤ (1 - 1 / 10 ^ 8) * (1 - 1 / 100) := by norm_num
    _ ≤ (1 - Work.BoseFixR.epsFar v μ ρ)
        * (1 - (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT) :=
        mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)

end Work.BoseFixR
