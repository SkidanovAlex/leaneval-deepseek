/-
Area DSCOH (curric-46) — the normalization comparison: the `y`-component of the homotopy identity.

This file finishes the categorical assembly of `Work.DSCOH.Norm.HomoAssembly`:

* `sum_range_split_at` : splitting a range sum at a threshold;
* `pair_sum` : for a nondecreasing non-injective tuple `y`, the `y`-component of the sum of the two
  differential terms of the homotopy identity is the projection `π_y` onto the `y`-component.

The four `Work.DSCOH.Pair` lemmas provide the cancellation of the individual terms after the sums
are split at the position `frA y` of the first repeat.
-/
import Mathlib
import Submission.Work.DSCOH.Norm.HomoAssembly
import Submission.Work.DSCOH.Pair.Dterm_eq_neg_Hterm_castSucc
import Submission.Work.DSCOH.Pair.Dterm_eq_neg_Hterm_succ
import Submission.Work.DSCOH.Pair.Hterm_mid_cancel
import Submission.Work.DSCOH.Pair.Hterm_self

namespace Work.DSCOH.Norm

open CategoryTheory Limits Opposite TopologicalSpace
open scoped Simplicial BigOperators

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

universe u v w

variable {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
variable {ι : Type w} [LinearOrder ι] [Fintype ι]

section pairing

variable [HasProducts (ModuleCat A)] (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)

/-- Splitting a range sum at a threshold. -/
lemma sum_range_split_at {G : Type*} [AddCommGroup G] (f : ℕ → G) {n a : ℕ} (h : a ≤ n) :
    ∑ i ∈ Finset.range n, f i
      = ∑ i ∈ Finset.range a, f i + ∑ i ∈ Finset.range (n - a), f (a + i) := by
  conv_lhs => rw [show n = a + (n - a) by omega]
  rw [Finset.sum_range_add]

/-- The pairing: for a nondecreasing non-injective `y`, the sum of the `Dterm`s and `Hterm`s at the
`y`-component is `π_y`. -/
lemma pair_sum (k : ℕ) (y : SemiIdx ι (k + 1)) (hy : Monotone y.val) (hh : ¬ StrictMono y.val) :
    (∑ b : Fin (k + 2), Dterm P U k y b) + (∑ c : Fin (k + 3), Hterm P U k y c)
      = Pi.π (fun w : SemiIdx ι (k + 1) => tupleMod P U w.val) y := by
  set fa := (frA y.val hy hh : ℕ) with hfadef
  have hfa : fa ≤ k := by have := (frA y.val hy hh).isLt; omega
  rw [sum_Dterm P U y, sum_Hterm P U y]
  -- the two splits
  have hDsplit : (∑ i ∈ Finset.range (k + 2), DtermN P U k y i)
      = (∑ i ∈ Finset.range fa, DtermN P U k y i)
        + (DtermN P U k y fa + DtermN P U k y (fa + 1))
        + (∑ i ∈ Finset.range (k - fa), DtermN P U k y (fa + 2 + i)) := by
    rw [sum_range_split_at (DtermN P U k y) (by omega : fa ≤ k + 2)]
    rw [sum_range_split_at (fun i => DtermN P U k y (fa + i)) (by omega : 2 ≤ k + 2 - fa)]
    rw [show (k + 2 - fa) - 2 = k - fa by omega]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [Nat.add_zero, zero_add, ← Nat.add_assoc]
    abel
  have hHsplit : (∑ i ∈ Finset.range (k + 3), HtermN P U k y i)
      = (∑ i ∈ Finset.range fa, HtermN P U k y i)
        + (HtermN P U k y fa + HtermN P U k y (fa + 1) + HtermN P U k y (fa + 2))
        + (∑ i ∈ Finset.range (k - fa), HtermN P U k y (fa + 3 + i)) := by
    rw [sum_range_split_at (HtermN P U k y) (by omega : fa ≤ k + 3)]
    rw [sum_range_split_at (fun i => HtermN P U k y (fa + i)) (by omega : 3 ≤ k + 3 - fa)]
    rw [show (k + 3 - fa) - 3 = k - fa by omega]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    simp only [Nat.add_zero, zero_add, ← Nat.add_assoc]
    abel
  -- the four pieces
  have hpair1 : (∑ i ∈ Finset.range fa, DtermN P U k y i)
      + (∑ i ∈ Finset.range fa, HtermN P U k y i) = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have hi' : i < fa := Finset.mem_range.mp hi
    have hib : i < k + 2 := by omega
    have hic : i < k + 3 := by omega
    have hb : (i : ℕ) < (frA y.val hy hh : ℕ) := by rw [hfadef] at hi'; simpa using hi'
    rw [DtermN_eq P U y ⟨i, hib⟩, HtermN_eq P U y ⟨i, hic⟩]
    have hcast : (⟨i, hic⟩ : Fin (k + 3)) = (⟨i, hib⟩ : Fin (k + 2)).castSucc := by
      apply Fin.ext; simp
    rw [hcast]
    rw [Work.DSCOH.Pair.Dterm_eq_neg_Hterm_castSucc P U y hy hh ⟨i, hib⟩ hb]
    abel
  have hmidD : DtermN P U k y fa + DtermN P U k y (fa + 1) = 0 := by
    have h1 : fa < k + 2 := by omega
    have h2 : fa + 1 < k + 2 := by omega
    rw [DtermN_eq P U y ⟨fa, h1⟩, DtermN_eq P U y ⟨fa + 1, h2⟩]
    have hcast : (⟨fa, h1⟩ : Fin (k + 2)) = (frA y.val hy hh).castSucc := by
      apply Fin.ext; simp [hfadef]
    have hsucc : (⟨fa + 1, h2⟩ : Fin (k + 2)) = (frA y.val hy hh).succ := by
      apply Fin.ext; simp [hfadef]
    rw [hcast, hsucc]
    exact Dterm_castSucc_add_succ P U y hy hh
  have hmidH : HtermN P U k y fa + (HtermN P U k y (fa + 1) + HtermN P U k y (fa + 2))
      = Pi.π (fun w : SemiIdx ι (k + 1) => tupleMod P U w.val) y := by
    have h1 : fa < k + 3 := by omega
    have h2 : fa + 1 < k + 3 := by omega
    have h3 : fa + 2 < k + 3 := by omega
    rw [HtermN_eq P U y ⟨fa, h1⟩, HtermN_eq P U y ⟨fa + 1, h2⟩,
      HtermN_eq P U y ⟨fa + 2, h3⟩]
    have hcast : (⟨fa, h1⟩ : Fin (k + 3)) = (frA y.val hy hh).castSucc.castSucc := by
      apply Fin.ext; simp [hfadef]
    have hsucc : (⟨fa + 1, h2⟩ : Fin (k + 3))
        = ((frA y.val hy hh).castSucc : Fin (k + 2)).succ := by
      apply Fin.ext; simp [hfadef]
    have hsucc2 : (⟨fa + 2, h3⟩ : Fin (k + 3))
        = (⟨(frA y.val hy hh : ℕ) + 2,
            by have := (frA y.val hy hh).isLt; omega⟩ : Fin (k + 3)) := by
      apply Fin.ext; simp [hfadef]
    rw [hcast, hsucc, hsucc2, Work.DSCOH.Pair.Hterm_self P U y hy hh,
      Work.DSCOH.Pair.Hterm_mid_cancel P U y hy hh]
    abel
  have hpair2 : (∑ i ∈ Finset.range (k - fa), DtermN P U k y (fa + 2 + i))
      + (∑ i ∈ Finset.range (k - fa), HtermN P U k y (fa + 3 + i)) = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have hi' : i < k - fa := Finset.mem_range.mp hi
    have hib : fa + 2 + i < k + 2 := by omega
    have hic : fa + 3 + i < k + 3 := by omega
    rw [DtermN_eq P U y ⟨fa + 2 + i, hib⟩, HtermN_eq P U y ⟨fa + 3 + i, hic⟩]
    have hb : (frA y.val hy hh : ℕ) + 2 ≤ ((⟨fa + 2 + i, hib⟩ : Fin (k + 2)) : ℕ) := by
      simp only [hfadef, Fin.val_mk]; omega
    have hsucc : ((⟨fa + 2 + i, hib⟩ : Fin (k + 2)).succ : Fin (k + 3)) = ⟨fa + 3 + i, hic⟩ := by
      apply Fin.ext; simp only [Fin.val_succ, Fin.val_mk]; omega
    rw [← hsucc]
    rw [Work.DSCOH.Pair.Dterm_eq_neg_Hterm_succ P U y hy hh ⟨fa + 2 + i, hib⟩ hb]
    abel
  rw [hDsplit, hHsplit,
    show (∑ i ∈ Finset.range fa, DtermN P U k y i)
        + (DtermN P U k y fa + DtermN P U k y (fa + 1))
        + (∑ i ∈ Finset.range (k - fa), DtermN P U k y (fa + 2 + i))
        + ((∑ i ∈ Finset.range fa, HtermN P U k y i)
          + (HtermN P U k y fa + HtermN P U k y (fa + 1) + HtermN P U k y (fa + 2))
          + (∑ i ∈ Finset.range (k - fa), HtermN P U k y (fa + 3 + i)))
      = ((∑ i ∈ Finset.range fa, DtermN P U k y i)
          + (∑ i ∈ Finset.range fa, HtermN P U k y i))
        + (DtermN P U k y fa + DtermN P U k y (fa + 1))
        + (HtermN P U k y fa + (HtermN P U k y (fa + 1) + HtermN P U k y (fa + 2)))
        + ((∑ i ∈ Finset.range (k - fa), DtermN P U k y (fa + 2 + i))
          + (∑ i ∈ Finset.range (k - fa), HtermN P U k y (fa + 3 + i))) from by abel]
  rw [hpair1, hmidD, hmidH, hpair2]
  abel

end pairing

end Work.DSCOH.Norm
