import Mathlib
import Submission.Work.Pi6.SQM.Cup3CobSetup
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQM

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff)

/-- Degenerate case `m = 2`, `A + 3 = n`: the `T1`-face equals the `C4`-face. -/
theorem c4faceT1 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (A : ℕ) (hm2 : m = 2) (hAn : A + 3 = n) :
    (Work.Pi6.SQ.cup2U n m (A+1) 1 (by omega) (by omega) (by omega)
      = cup3U n (m+1) A 1 1 (by omega) (by omega) (by omega) (by omega) ≫ sh4 n m hn hm) ∧
    (Work.Pi6.SQ.cup2V n m (A+1) 1 (by omega) (by omega) (by omega)
      = SimplexCategory.δ (⟨0, by omega⟩ : Fin (m+2)) ≫
        (cup3V n (m+1) A 1 1 (by omega) (by omega) (by omega) (by omega) ≫ sh4 n m hn hm)) := by
  constructor
  · refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    simp only [CategoryTheory.comp_apply, cup2U_val, cup3U_val,
      Work.Cohomology.shmap_val]
    split_ifs <;> omega
  · refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    simp only [CategoryTheory.comp_apply, cup2V_val, cup3V_val, SimplexCategory.coe_δ,
      Work.Cohomology.succAbove_val_if', Work.Cohomology.shmap_val]
    split_ifs <;> omega

/-- Degenerate case `m = 2`, `A + 4 ≤ n`: the `T4 (A+1)`-face equals the `C4`-face. -/
theorem c4faceT4a (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (A : ℕ) (hm2 : m = 2) (hA4 : A + 4 ≤ n) :
    (cup3U n (m+1) (A+1) 1 1 (by omega) (by omega) (by omega) (by omega) ≫ sh4 n m hn hm
      = cup3U n (m+1) A 1 1 (by omega) (by omega) (by omega) (by omega) ≫ sh4 n m hn hm) ∧
    (SimplexCategory.δ (⟨3, by omega⟩ : Fin (m+2)) ≫
        (cup3V n (m+1) (A+1) 1 1 (by omega) (by omega) (by omega) (by omega) ≫ sh4 n m hn hm)
      = SimplexCategory.δ (⟨0, by omega⟩ : Fin (m+2)) ≫
        (cup3V n (m+1) A 1 1 (by omega) (by omega) (by omega) (by omega) ≫ sh4 n m hn hm)) := by
  constructor
  · refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    simp only [CategoryTheory.comp_apply, cup3U_val, Work.Cohomology.shmap_val]
    split_ifs <;> omega
  · refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    simp only [CategoryTheory.comp_apply, cup3V_val, SimplexCategory.coe_δ,
      Work.Cohomology.succAbove_val_if', Work.Cohomology.shmap_val]
    split_ifs <;> omega

/-- Degenerate case `m = 2`, `n ≥ 3`: the `T2 (0,0)`-face equals the `C4`-face. -/
theorem c4faceT2b (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (hm2 : m = 2) (hn3 : 3 ≤ n) :
    (Work.Pi6.SQ.cup2V m n 0 1 (by omega) (by omega) (by omega) ≫ shT2 n m hn hm
      = cup3U n (m+1) 0 1 1 (by omega) (by omega) (by omega) (by omega) ≫ sh4 n m hn hm) ∧
    (Work.Pi6.SQ.cup2U m n 0 1 (by omega) (by omega) (by omega) ≫ shT2 n m hn hm
      = SimplexCategory.δ (⟨3, by omega⟩ : Fin (m+2)) ≫
        (cup3V n (m+1) 0 1 1 (by omega) (by omega) (by omega) (by omega) ≫ sh4 n m hn hm)) := by
  constructor
  · refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    simp only [CategoryTheory.comp_apply, cup2V_val, cup3U_val,
      Work.Cohomology.shmap_val]
    split_ifs <;> omega
  · refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    simp only [CategoryTheory.comp_apply, cup2U_val, cup3V_val, SimplexCategory.coe_δ,
      Work.Cohomology.succAbove_val_if', Work.Cohomology.shmap_val]
    split_ifs <;> omega

/-- Degenerate case `m = 2`, `A ≥ 1`, `A + 3 ≤ n`: the `T4 (A-1)`-face equals the `C4`-face. -/
theorem c4faceT4b (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (A : ℕ) (hm2 : m = 2)
    (hA1 : 1 ≤ A) (hA3 : A + 3 ≤ n) :
    (cup3U n (m+1) (A-1) 1 1 (by omega) (by omega) (by omega) (by omega) ≫ sh4 n m hn hm
      = cup3U n (m+1) A 1 1 (by omega) (by omega) (by omega) (by omega) ≫ sh4 n m hn hm) ∧
    (SimplexCategory.δ (⟨0, by omega⟩ : Fin (m+2)) ≫
        (cup3V n (m+1) (A-1) 1 1 (by omega) (by omega) (by omega) (by omega) ≫ sh4 n m hn hm)
      = SimplexCategory.δ (⟨3, by omega⟩ : Fin (m+2)) ≫
        (cup3V n (m+1) A 1 1 (by omega) (by omega) (by omega) (by omega) ≫ sh4 n m hn hm)) := by
  constructor
  · refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    simp only [CategoryTheory.comp_apply, cup3U_val, Work.Cohomology.shmap_val]
    split_ifs <;> omega
  · refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    simp only [CategoryTheory.comp_apply, cup3V_val, SimplexCategory.coe_δ,
      Work.Cohomology.succAbove_val_if', Work.Cohomology.shmap_val]
    split_ifs <;> omega

end

end Work.Pi6.SQM
