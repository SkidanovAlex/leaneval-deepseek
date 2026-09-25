import Mathlib
import Submission.Work.LT.good_base_defs
import Submission.Work.LT.gb_ext_defs
import Submission.Work.LT.gb_matExt_rowwise
import Submission.Work.LT.gb_matExt_agree
import Submission.Work.LT.gb_matExt_row_span
import Submission.Work.LT.gb_matExt_col_span
import Submission.Work.LT.gb_matRank_matExt_le

namespace Work.LT

/-- Kalachev--Panteleev Lemma 9. Given `x ∈ CA ⊞ CB` and subsets `A`, `B` of rows/columns, there is `x' ∈ CA ⊞ CB` agreeing with `x` on `A × B`, of rank at most that of `x`, every row of which is a linear combination of the rows of `x'` indexed by `A`, and every column of which is a linear combination of the columns of `x'` indexed by `B`. -/
theorem gb_extension {D : ℕ} (CA CB : Submodule (ZMod 2) (Fin D → ZMod 2))
    (x : Fin D × Fin D → ZMod 2) (hx : x ∈ GB.prodSum CA CB) (A B : Finset (Fin D)) :
    ∃ x' ∈ GB.prodSum CA CB,
      (∀ i ∈ A, ∀ j ∈ B, x' (i, j) = x (i, j)) ∧
      GB.matRank x' ≤ GB.matRank x ∧
      (∀ i : Fin D, GB.row x' i ∈
        Submodule.span (ZMod 2) (Set.range (fun i' : {i : Fin D // i ∈ A} => GB.row x' ↑i'))) ∧
      (∀ j : Fin D, GB.col x' j ∈
        Submodule.span (ZMod 2) (Set.range (fun j' : {j : Fin D // j ∈ B} => GB.col x' ↑j'))) := by
  classical
  -- the two `A`-, resp. `B`-extension operators, Kalachev--Panteleev's `g_1`, `g_2`
  let T₁ : GB.ExtOp CA A := Classical.choice (GB.extOp_nonempty CA A)
  let T₂ : GB.ExtOp CB B := Classical.choice (GB.extOp_nonempty CB B)
  -- `x' = (g₁ ⊗ g₂) x(A,B)`
  refine ⟨GB.matExt A B (GB.opVec T₁) (GB.opVec T₂) x, ?_, ?_, ?_, ?_, ?_⟩
  · -- `x'` is still in `CA ⊞ CB`
    obtain ⟨a, ha, b, hb, rfl⟩ := (GB.mem_prodSum x).mp hx
    rw [GB.matExt_add]
    refine (GB.mem_prodSum _).mpr
      ⟨GB.matExt A B (GB.opVec T₁) (GB.opVec T₂) a, ?_,
       GB.matExt A B (GB.opVec T₁) (GB.opVec T₂) b, ?_, rfl⟩
    · rw [GB.mem_colCode]
      exact GB.matExt_colwise A B T₁ (GB.opVec T₂) a ((GB.mem_colCode (CA := CA) a).mp ha)
    · rw [GB.mem_rowCode]
      exact gb_matExt_rowwise A B T₂ (GB.opVec T₁) b ((GB.mem_rowCode (CB := CB) b).mp hb)
  · -- `x' = x` on `A × B`
    exact fun i hi j hj => gb_matExt_agree A B T₁ T₂ x hi hj
  · -- rank does not increase
    exact gb_matRank_matExt_le A B T₁ (GB.opVec T₂) x
  · -- rows of `x'` are spanned by the rows indexed by `A`
    exact gb_matExt_row_span A B T₁ T₂ x
  · -- columns of `x'` are spanned by the columns indexed by `B`
    exact gb_matExt_col_span A B T₁ T₂ x

end Work.LT
