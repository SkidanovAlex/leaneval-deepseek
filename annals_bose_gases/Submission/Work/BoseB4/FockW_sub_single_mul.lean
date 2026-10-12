import Mathlib.Algebra.CharP.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finsupp.Order
import Submission.Work.BoseB4.Split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.FockW_sub_single_mul` — lowering one quantum at an excited mode

The Fock weight `fockW n β = √(n! · β!)` of `Work.BoseB4.Split` behaves
multiplicatively under raising the occupation of an excited mode `j` by one:
`fockW n (β + single j 1) = √((β j) + 1) · fockW n β` (`Split_cre_excited`).
The present file proves the *lowering* companion, which is what the excited
annihilation operator needs:

    `(β j) · fockW n (β - single j 1) = √(β j) · fockW n β`.

(As usual the statement is understood with the truncated subtraction of `ℕ`: when
`β j = 0` both sides vanish.)  It is the excited-mode analogue of
`Work.BoseB4.fockW_nsmul_sub_one` (the condensate mode `0`), which reads
`n · fockW (n-1) β = √n · fockW n β`.

## The proof

Both `fockW`'s are square roots of nonnegative numbers, and the whole content is
the single arithmetic identity on multi-index factorials

    `(β j : ℝ) * mfacG (β - single j 1) = mfacG β`   (for `β j ≠ 0`),

which is `β j · (β j - 1)! = (β j)!` at the coordinate `j` and the trivially
unchanged factors `(β l)!` elsewhere (`mul_mfacG_sub_single`).  Applying
`Real.sqrt_mul` to it gives

    `fockW n β = fockW n (β - single j 1) * √(β j)`   (`fockW_sub_single`),

and then `√(β j) · √(β j) = β j` (`Real.mul_self_sqrt`) finishes:

    `(β j) · fockW n (β - single j 1) = √(β j) · (fockW n (β - single j 1) · √(β j))
                                      = √(β j) · fockW n β`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB4

set_option autoImplicit false

/-! ## Auxiliary computations on multi-index factorials -/

/-- The multi-index factorial `mfacG` is nonnegative. -/
private lemma mfacG_nonneg {ι : Type*} (β : ι →₀ ℕ) : 0 ≤ mfacG β := by
  rw [mfacG, Finsupp.prod]
  exact Finset.prod_nonneg fun a _ => by positivity

/-- On a finite index type, `mfacG β = ∏_l (β_l)!`: the factors outside the
support are `0! = 1`. -/
private lemma mfacG_prod_univ {ι : Type*} [Fintype ι] (β : ι →₀ ℕ) :
    mfacG β = ∏ l : ι, ((β l).factorial : ℝ) := by
  rw [mfacG, Finsupp.prod]
  refine Finset.prod_subset (Finset.subset_univ _) ?_
  intro x _ hx
  rw [Finsupp.notMem_support_iff.mp hx]
  simp

/-- **Lowering one quantum at coordinate `j`**: if the `j`-occupation of `β` is
nonzero then `(β j) · (β - single j 1)! = β!`, i.e.
`(β j : ℝ) * mfacG (β - single j 1) = mfacG β`.  At the coordinate `j` this is
`β j · (β j - 1)! = (β j)!`; all other factors are unchanged. -/
private lemma mul_mfacG_sub_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ι →₀ ℕ) (j : ι) (h : β j ≠ 0) :
    (β j : ℝ) * mfacG (β - Finsupp.single j (1:ℕ)) = mfacG β := by
  have hj1 : 1 ≤ β j := Nat.one_le_iff_ne_zero.mpr h
  rw [mfacG_prod_univ, mfacG_prod_univ,
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ j)
      (fun l => (((β - Finsupp.single j (1:ℕ)) l).factorial : ℝ)),
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ j)
      (fun l => ((β l).factorial : ℝ))]
  have hsub : (β - Finsupp.single j (1:ℕ)) j = β j - 1 := by
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
  have hfacj_nat : (β j).factorial = β j * (β j - 1).factorial := by
    conv_lhs => rw [← Nat.sub_add_cancel hj1]
    rw [Nat.factorial_succ, Nat.sub_add_cancel hj1]
  have hfacj : ((β j).factorial : ℝ) = (β j : ℝ) * ((β j - 1).factorial : ℝ) := by
    rw [hfacj_nat]; push_cast; ring
  have hprod : ∏ x ∈ Finset.univ \ {j},
        (((β - Finsupp.single j (1:ℕ)) x).factorial : ℝ)
      = ∏ x ∈ Finset.univ \ {j}, ((β x).factorial : ℝ) := by
    refine Finset.prod_congr rfl ?_
    intro x hx
    have hxj : x ≠ j := fun hh => (Finset.mem_sdiff.mp hx).2 (Finset.mem_singleton.mpr hh)
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_of_ne hxj, tsub_zero]
  rw [hsub, hprod, hfacj]
  ring

/-! ## The Fock weight under lowering -/

/-- **The Fock weight gains the factor `√(β j)` when the `j`-occupation is
lowered by one**: `fockW n β = fockW n (β - single j 1) * √(β j)` for `β j ≠ 0`,
the annihilation counterpart of `fockW_add_single`. -/
private lemma fockW_sub_single {m : ℕ} [NeZero m] (n : ℕ) (β : Excited m →₀ ℕ)
    (j : Excited m) (h : β j ≠ 0) :
    fockW n β = fockW n (β - Finsupp.single j (1:ℕ)) * Real.sqrt (β j) := by
  have hmul := mul_mfacG_sub_single β j h
  rw [fockW, fockW]
  rw [show (n.factorial : ℝ) * mfacG β
        = ((n.factorial : ℝ) * mfacG (β - Finsupp.single j (1:ℕ))) * (β j : ℝ) by
      rw [← hmul]; ring]
  rw [Real.sqrt_mul (mul_nonneg (by positivity) (mfacG_nonneg _))]

/-! ## The target -/

theorem FockW_sub_single_mul {m : ℕ} [NeZero m] (n : ℕ) (β : Excited m →₀ ℕ) (j : Excited m) :
    (β j : ℝ) * fockW n (β - Finsupp.single j 1) = Real.sqrt (β j) * fockW n β := by
  by_cases h : β j = 0
  · rw [h]; simp
  · have hkey := fockW_sub_single n β j h
    have hs : Real.sqrt (β j : ℝ) * Real.sqrt (β j : ℝ) = (β j : ℝ) :=
      Real.mul_self_sqrt (Nat.cast_nonneg _)
    calc (β j : ℝ) * fockW n (β - Finsupp.single j (1:ℕ))
        = (Real.sqrt (β j) * Real.sqrt (β j)) * fockW n (β - Finsupp.single j (1:ℕ)) := by
          rw [hs]
      _ = Real.sqrt (β j) * (fockW n (β - Finsupp.single j (1:ℕ)) * Real.sqrt (β j)) := by
          ring
      _ = Real.sqrt (β j) * fockW n β := by rw [hkey]

end Work.BoseB4
