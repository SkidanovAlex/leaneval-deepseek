import Mathlib
import Submission.Work.BMF.kdr_defs
import Submission.Work.BMF.VK2.polySum_pow_expand

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Conjugate-power expansion of the polynomial Weyl sum

`polySum k α X = Σ_{1 ≤ h ≤ X} e(Σ_j α j h^{j+1})`.  Since `phase` is real-valued,
`star (polySum k α X) = Σ_{h} e(-phase h)`, so the product `polySum · star polySum`
expands as a double sum over pairs `(h, h')`, and its `s`-th power as a sum over
`s`-tuples of such pairs.  The exponent of `e` is the pairing of `α` with the difference
of the moment vectors of the two tuples, exactly the quantity used in the Vinogradov
mean-value count.
-/

namespace Work.BMF

open scoped BigOperators
open Finset

/-- Complex conjugation acts on the additive character by `t ↦ -t`. -/
lemma star_eC (t : ℝ) : star (eC t) = eC (-t) := by
  unfold eC
  simp only [RCLike.star_def]
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem polySum_mul_conj_pow_expand (s k X : ℕ) (α : Fin k → ℝ) :
    (Work.BMF.polySum k α (X:ℝ) * starRingEnd ℂ (Work.BMF.polySum k α (X:ℝ)))^s
      = ∑ p : (Fin s → Finset.Icc 1 X) × (Fin s → Finset.Icc 1 X),
          Work.BMF.eC (∑ j : Fin k, α j *
            (((∑ i, (((p.1 i).1 : ℤ) ^ ((j:ℕ)+1))) - (∑ i, (((p.2 i).1 : ℤ) ^ ((j:ℕ)+1)))) : ℝ)) := by
  classical
  have hP : (polySum k α (X:ℝ))^s = ∑ u : Fin s → Finset.Icc 1 X,
      eC (∑ j : Fin k, α j * (VK2.mvMom k u j : ℝ)) := VK2.polySum_pow_expand k s X α
  have hstar : star ((polySum k α (X:ℝ))^s) = ∑ v : Fin s → Finset.Icc 1 X,
      eC (-(∑ j : Fin k, α j * (VK2.mvMom k v j : ℝ))) := by
    rw [hP, star_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [star_eC]
  have key : (polySum k α (X:ℝ) * star (polySum k α (X:ℝ)))^s =
      ∑ p : (Fin s → Finset.Icc 1 X) × (Fin s → Finset.Icc 1 X),
        eC ((∑ j : Fin k, α j * (VK2.mvMom k p.1 j : ℝ))
            - (∑ j : Fin k, α j * (VK2.mvMom k p.2 j : ℝ))) := by
    rw [mul_pow, ← star_pow (polySum k α (X:ℝ)) s, hstar, hP, Fintype.sum_mul_sum]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    rw [← VK2.eC_add']
    congr 1
  calc (polySum k α (X:ℝ) * starRingEnd ℂ (polySum k α (X:ℝ)))^s
      = (polySum k α (X:ℝ) * star (polySum k α (X:ℝ)))^s := by rw [starRingEnd_apply]
    _ = ∑ p : (Fin s → Finset.Icc 1 X) × (Fin s → Finset.Icc 1 X),
          eC ((∑ j : Fin k, α j * (VK2.mvMom k p.1 j : ℝ))
              - (∑ j : Fin k, α j * (VK2.mvMom k p.2 j : ℝ))) := key
    _ = ∑ p : (Fin s → Finset.Icc 1 X) × (Fin s → Finset.Icc 1 X),
          eC (∑ j : Fin k, α j *
            (((∑ i, (((p.1 i).1 : ℤ) ^ ((j:ℕ)+1))) - (∑ i, (((p.2 i).1 : ℤ) ^ ((j:ℕ)+1)))) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro p _
        congr 1
        simp only [VK2.mvMom]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        rw [← mul_sub]

end Work.BMF
