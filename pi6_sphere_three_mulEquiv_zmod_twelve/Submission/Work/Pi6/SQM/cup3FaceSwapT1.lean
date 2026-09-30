import Mathlib
import Submission.Work.Pi6.SQM.Cup3CobSetup
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.SQM

open CategoryTheory

/-!
# The `T1` branch of the `∪₃` pairing involution

`swapT1` pairs a `T1`-index `p = (a,b)` (a term of `u ∪₂ v`) with a `C3`- or `C4`- or `T2`-index
whose faces are *equal* to the faces `t1U n m p`, `t1V n m p` of the `T1`-index.  This file records
that face-preservation, split in the five branches of `swapT1`:

* `h1 : b+3 ≤ m`      — paired with `C3 (a, b, n-2-a) (j = n+1)`;
* `h2 : a+3 ≤ n`      — paired with `C4 (a, m-2, n-3-a) (j = m)`;
* `m = 2`, `n = 2`    — paired with `T2 (0,0)`;
* `m = 2`, `n ≠ 2`    — paired with `C4 (n-3, 0, 0, 0)`;
* otherwise           — paired with `C3 (n-2, m-3, 0, n-1)`.

Each branch is an identity of composites of interval maps, discharged by vertex computation.
-/

private lemma faceU_swapT1 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (p : T1Idx n m) :
    faceU n m hn hm (swapT1 n m hn hm p) = t1U n m hn hm p.1 p.2 := by
  simp only [swapT1]
  split_ifs with h1 h2 h3 h3'
  · simp only [faceU, idxC3, C3a, C3b, C3c, C3j, mkT3]
    unfold c3U t1U
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
    simp only [CategoryTheory.comp_apply, SimplexCategory.coe_δ, cup3U_val, cup2U_val,
      Work.Cohomology.succAbove_val_if', Work.Cohomology.shmap_val]
    split_ifs <;> omega
  · simp only [faceU, idxC4, C4a, C4b, C4c, C4j, mkT4]
    unfold c4U t1U
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
    simp only [CategoryTheory.comp_apply, cup3U_val, cup2U_val,
      Work.Cohomology.shmap_val]
    split_ifs <;> omega
  · simp only [faceU, idxT2, mkT2]
    unfold t2U t1U
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
    simp only [CategoryTheory.comp_apply, cup2U_val, cup2V_val,
      Work.Cohomology.shmap_val]
    split_ifs <;> omega
  · simp only [faceU, idxC4, C4a, C4b, C4c, C4j, mkT4]
    unfold c4U t1U
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
    simp only [CategoryTheory.comp_apply, cup3U_val, cup2U_val,
      Work.Cohomology.shmap_val]
    split_ifs <;> omega
  · simp only [faceU, idxC3, C3a, C3b, C3c, C3j, mkT3]
    unfold c3U t1U
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
    simp only [CategoryTheory.comp_apply, SimplexCategory.coe_δ, cup3U_val, cup2U_val,
      Work.Cohomology.succAbove_val_if', Work.Cohomology.shmap_val]
    split_ifs <;> omega

private lemma faceV_swapT1 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (p : T1Idx n m) :
    faceV n m hn hm (swapT1 n m hn hm p) = t1V n m hn hm p.1 p.2 := by
  simp only [swapT1]
  split_ifs with h1 h2 h3 h3'
  · simp only [faceV, idxC3, C3a, C3b, C3c, C3j, mkT3]
    unfold c3V t1V
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
    simp only [CategoryTheory.comp_apply, cup3V_val, cup2V_val,
      Work.Cohomology.shmap_val]
    split_ifs <;> omega
  · simp only [faceV, idxC4, C4a, C4b, C4c, C4j, mkT4]
    unfold c4V t1V
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
    simp only [CategoryTheory.comp_apply, SimplexCategory.coe_δ, cup3V_val, cup2V_val,
      Work.Cohomology.succAbove_val_if', Work.Cohomology.shmap_val]
    split_ifs <;> omega
  · simp only [faceV, idxT2, mkT2]
    unfold t2V t1V
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
    simp only [CategoryTheory.comp_apply, cup2U_val, cup2V_val,
      Work.Cohomology.shmap_val]
    split_ifs <;> omega
  · simp only [faceV, idxC4, C4a, C4b, C4c, C4j, mkT4]
    unfold c4V t1V
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
    simp only [CategoryTheory.comp_apply, SimplexCategory.coe_δ, cup3V_val, cup2V_val,
      Work.Cohomology.succAbove_val_if', Work.Cohomology.shmap_val]
    split_ifs <;> omega
  · simp only [faceV, idxC3, C3a, C3b, C3c, C3j, mkT3]
    unfold c3V t1V
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
    simp only [CategoryTheory.comp_apply, cup3V_val, cup2V_val,
      Work.Cohomology.shmap_val]
    split_ifs <;> omega

theorem cup3FaceSwapT1 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (p : Work.Pi6.SQM.T1Idx n m) :
    Work.Pi6.SQM.faceU n m hn hm (Work.Pi6.SQM.swapT1 n m hn hm p) = Work.Pi6.SQM.faceU n m hn hm (Sum.inr (Sum.inr (Sum.inr (Sum.inl p)))) ∧
    Work.Pi6.SQM.faceV n m hn hm (Work.Pi6.SQM.swapT1 n m hn hm p) = Work.Pi6.SQM.faceV n m hn hm (Sum.inr (Sum.inr (Sum.inr (Sum.inl p)))) := by
  have hu : faceU n m hn hm (Sum.inr (Sum.inr (Sum.inr (Sum.inl p)))) = t1U n m hn hm p.1 p.2 := rfl
  have hv : faceV n m hn hm (Sum.inr (Sum.inr (Sum.inr (Sum.inl p)))) = t1V n m hn hm p.1 p.2 := rfl
  rw [hu, hv]
  exact ⟨faceU_swapT1 n m hn hm p, faceV_swapT1 n m hn hm p⟩

end Work.Pi6.SQM
