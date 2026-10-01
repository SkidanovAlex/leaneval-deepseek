import Mathlib
import Submission.Work.LinnikAreas.CIDefs
import Submission.Work.LinnikAreas.NormVonMangoldtMulCharDiv

/-!
# `ChiSumSubPrimitive`

The tent-weighted von Mangoldt sum `chiSum χ q X = Σ_{n ≤ X} Λ(n) χ(n)/n · h(log n / log q)`
depends, up to an error controlled by the *non-coprime* von Mangoldt sum `ncsSum q X`, only on
the **primitive** character `χ.primitiveCharacter` inducing `χ`:

`‖chiSum χ q X − chiSum χ.primitiveCharacter q X‖ ≤ ncsSum q X`.

Indeed, for `n` coprime to `q` the values of `χ` and of its primitive character agree
(`DirichletCharacter.primitiveCharacter_apply_of_isCoprime`), while for `n` not coprime to `q`
the character `χ` vanishes (`MulChar.map_nonunit` together with `ZMod.isUnit_iff_coprime`).
Hence the difference of the two sums is (minus) the sum over the `n ≤ X` that are not coprime
to `q`; bounding each term by `Λ(n)/n · h(log n / log q)` using `‖χ⋆(n)‖ ≤ 1`
(`DirichletCharacter.norm_le_one`) and `h ≥ 0` gives the claim.
-/

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped BigOperators Classical

theorem ChiSumSubPrimitive {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    [NeZero χ.conductor] (X : ℕ) :
    ‖Work.LinnikAreas.chiSum χ q X - Work.LinnikAreas.chiSum χ.primitiveCharacter q X‖
      ≤ Work.LinnikAreas.ncsSum q X := by
  classical
  -- the values of `χ` and of its primitive character agree at integers coprime to the level
  have hcop : ∀ n : ℕ, Nat.Coprime n q →
      (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ) = (χ (n : ZMod q) : ℂ) := by
    intro n hn
    have hc : IsCoprime (n : ℤ) (q : ℤ) := by
      rw [Int.isCoprime_iff_nat_coprime]
      simpa using hn
    simpa using χ.primitiveCharacter_apply_of_isCoprime (a := (n : ℤ)) hc
  -- `χ` vanishes at integers that are not coprime to the level
  have hnc : ∀ n : ℕ, ¬ Nat.Coprime n q → (χ (n : ZMod q) : ℂ) = 0 := by
    intro n hn
    exact MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])
  -- the difference of the two sums is (minus) the sum over the non-coprime `n`
  have key : chiSum χ q X - chiSum χ.primitiveCharacter q X
      = - ∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ Nat.Coprime n q),
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ) / (n : ℂ) *
            ((tentW (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ) := by
    rw [chiSum, chiSum, ← Finset.sum_sub_distrib]
    have hpt : ∑ n ∈ Finset.Icc 1 X,
        ((ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) : ℂ) / (n : ℂ) *
            ((tentW (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)
         - (ArithmeticFunction.vonMangoldt n : ℂ) *
            (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ) / (n : ℂ) *
            ((tentW (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ))
        = ∑ n ∈ Finset.Icc 1 X,
          (if Nat.Coprime n q then 0 else
            - ((ArithmeticFunction.vonMangoldt n : ℂ) *
              (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ) / (n : ℂ) *
              ((tentW (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ))) := by
      refine Finset.sum_congr rfl (fun n _ => ?_)
      by_cases h : Nat.Coprime n q
      · rw [hcop n h, if_pos h]; ring
      · rw [hnc n h, if_neg h]; ring
    have hpt2 : ∑ n ∈ Finset.Icc 1 X,
          (if Nat.Coprime n q then 0 else
            - ((ArithmeticFunction.vonMangoldt n : ℂ) *
              (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ) / (n : ℂ) *
              ((tentW (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)))
        = ∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ Nat.Coprime n q),
            - ((ArithmeticFunction.vonMangoldt n : ℂ) *
              (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ) / (n : ℂ) *
              ((tentW (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      by_cases h : Nat.Coprime n q <;> simp [h]
    rw [hpt, hpt2, Finset.sum_neg_distrib]
  -- the tent weight is nonnegative
  have htent : ∀ x : ℝ, 0 ≤ tentW x := fun x =>
    (Commons.NumberTheory.Linnik.tentWeight_bounds (L := 11/2) (K := 3/10)
      (by norm_num) (by norm_num)).1 x
  rw [key, norm_neg]
  calc ‖∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ Nat.Coprime n q),
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ) / (n : ℂ) *
            ((tentW (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)‖
      ≤ ∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ Nat.Coprime n q),
          ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
            (χ.primitiveCharacter (n : ZMod χ.conductor) : ℂ) / (n : ℂ) *
            ((tentW (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ Nat.Coprime n q),
          ArithmeticFunction.vonMangoldt n / (n : ℝ) *
            tentW (Real.log (n : ℝ) / Real.log (q : ℝ)) := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
        exact NormVonMangoldtMulCharDiv χ.primitiveCharacter hn1 (htent _)
    _ = ncsSum q X := by rw [ncsSum]

end Work.LinnikAreas
