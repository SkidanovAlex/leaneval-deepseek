import Mathlib
import Submission.Work.Pi6.SQM.Cup3CobSetup
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The `T2`-branch of the `∪₃`-coboundary involution preserves the two faces

`Work.Pi6.SQM.swapT2` is the restriction to the `T2`-index family (`v ∪₂ u`) of the
fixed-point-free involution `cup3Swap` of `Idx3` that cancels the terms of the two sides of
`δ(u ∪₃ v) = u∪₂v + v∪₂u + (δu)∪₃v + u∪₃(δv)`.  The pairing is *not* the identity on the
index set, but the two faces attached to an index are unchanged:

  `faceU (swapT2 p) = faceU (idxT2 p)`  and  `faceV (swapT2 p) = faceV (idxT2 p)`

(the `T2` analogue of `cup3FaceSwapL/C3/C4/T1`).  This is what lets the `T2`-terms be
matched pairwise with the terms of the other four families.

With `p = (a,b) : Fin (m-1) × Fin (n-1)` the branches of `swapT2` are

* `1 ≤ a`              → `C3 (0, a-1, b, 0)`; both faces are the identities `C1u`/`C1v`
                          of `Cup3Identities`;
* `a = 0`, `1 ≤ b`     → `C4 (0, 0, b-1, 1)`; both faces are `C3`;
* `a = b = 0`, `m = 2` → `T1 (0,0)` if `n = 2`, else `C4 (0,0,0,3)`; in these two degenerate
                          cases the interval maps appearing on both sides are the identity
                          map (up to the degree transports `shmap`), so the identities hold;
* `a = b = 0`, `m ≠ 2` → `C3 (0,0,0,2)`, which is `C2`.

Each identity is verified vertexwise: after `ConcreteCategory.hom_ext` and `Fin.ext` both
sides are described by the value lemmas `cup3U_val`, `cup3V_val`, `cup2U_val`, `cup2V_val`,
`shmap_val` and `succAbove_val_if'`, and the resulting chain of `if`s is closed by
`split_ifs <;> omega`.
-/

set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQM

noncomputable section

theorem cup3FaceSwapT2 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (p : Work.Pi6.SQM.T2Idx n m) :
    Work.Pi6.SQM.faceU n m hn hm (Work.Pi6.SQM.swapT2 n m hn hm p) = Work.Pi6.SQM.faceU n m hn hm (Sum.inr (Sum.inr (Sum.inr (Sum.inr p)))) ∧
    Work.Pi6.SQM.faceV n m hn hm (Work.Pi6.SQM.swapT2 n m hn hm p) = Work.Pi6.SQM.faceV n m hn hm (Sum.inr (Sum.inr (Sum.inr (Sum.inr p)))) := by
  obtain ⟨a, b⟩ := p
  have ha : (a : ℕ) < m - 1 := a.isLt
  have hb : (b : ℕ) < n - 1 := b.isLt
  by_cases h1 : 1 ≤ (a : ℕ)
  · -- `1 ≤ a`: the image is `C3 (0, a-1, b, 0)`, and `C1u`/`C1v` give the two faces.
    have hs : swapT2 n m hn hm (a, b) =
        idxC3 (mkT3 n m 0 ((a:ℕ) - 1) (b:ℕ) 0 (by omega) (by omega) (by omega) (by omega) (by omega)) := by
      simp only [swapT2]; rw [dite_eq_left h1]
    refine ⟨?_, ?_⟩
    · rw [hs]
      simp only [idxC3, faceU, c3U, t2U, C3a, C3b, C3c, C3j, mkT3]
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
      simp only [CategoryTheory.comp_apply, SimplexCategory.coe_δ, cup3U_val, cup2V_val,
        Work.Cohomology.succAbove_val_if', Work.Cohomology.shmap_val]
      split_ifs <;> omega
    · rw [hs]
      simp only [idxC3, faceV, c3V, t2V, C3a, C3b, C3c, mkT3]
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
      simp only [CategoryTheory.comp_apply, cup3V_val, cup2U_val, Work.Cohomology.shmap_val]
      split_ifs <;> omega
  · by_cases h2 : 1 ≤ (b : ℕ)
    · -- `a = 0`, `1 ≤ b`: the image is `C4 (0, 0, b-1, 1)`, and `C3` gives the two faces.
      have hs : swapT2 n m hn hm (a, b) =
          idxC4 (mkT4 n m 0 0 ((b:ℕ) - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega)) := by
        simp only [swapT2]; rw [dite_eq_right h1, dite_eq_left h2]
      refine ⟨?_, ?_⟩
      · rw [hs]
        simp only [idxC4, faceU, c4U, t2U, C4a, C4b, C4c, mkT4]
        refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
        simp only [CategoryTheory.comp_apply, cup3U_val, cup2V_val, Work.Cohomology.shmap_val]
        split_ifs <;> omega
      · rw [hs]
        simp only [idxC4, faceV, c4V, t2V, C4a, C4b, C4c, C4j, mkT4]
        refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
        simp only [CategoryTheory.comp_apply, SimplexCategory.coe_δ, cup3V_val, cup2U_val,
          Work.Cohomology.succAbove_val_if', Work.Cohomology.shmap_val]
        split_ifs <;> omega
    · by_cases h3 : m = 2
      · by_cases h3' : n = 2
        · -- `a = b = 0`, `m = n = 2`: the image is `T1 (0,0)`; both sides are the identity.
          have hs : swapT2 n m hn hm (a, b) = idxT1 (mkT1 n m 0 0 (by omega) (by omega)) := by
            simp only [swapT2]; rw [dite_eq_right h1, dite_eq_right h2, dite_eq_left h3, dite_eq_left h3']
          refine ⟨?_, ?_⟩
          · rw [hs]
            simp only [idxT1, faceU, t1U, t2U, mkT1]
            refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
            simp only [CategoryTheory.comp_apply, cup2U_val, cup2V_val, Work.Cohomology.shmap_val]
            split_ifs <;> omega
          · rw [hs]
            simp only [idxT1, faceV, t1V, t2V, mkT1]
            refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
            simp only [CategoryTheory.comp_apply, cup2U_val, cup2V_val, Work.Cohomology.shmap_val]
            split_ifs <;> omega
        · -- `a = b = 0`, `m = 2 < n`: the image is `C4 (0,0,0,3)`; both sides are the identity.
          have hs : swapT2 n m hn hm (a, b) =
              idxC4 (mkT4 n m 0 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega)) := by
            simp only [swapT2]; rw [dite_eq_right h1, dite_eq_right h2, dite_eq_left h3, dite_eq_right h3']
          refine ⟨?_, ?_⟩
          · rw [hs]
            simp only [idxC4, faceU, c4U, t2U, C4a, C4b, C4c, mkT4]
            refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
            simp only [CategoryTheory.comp_apply, cup3U_val, cup2V_val, Work.Cohomology.shmap_val]
            split_ifs <;> omega
          · rw [hs]
            simp only [idxC4, faceV, c4V, t2V, C4a, C4b, C4c, C4j, mkT4]
            refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
            simp only [CategoryTheory.comp_apply, SimplexCategory.coe_δ, cup3V_val, cup2U_val,
              Work.Cohomology.succAbove_val_if', Work.Cohomology.shmap_val]
            split_ifs <;> omega
      · -- `a = b = 0`, `m ≥ 3`: the image is `C3 (0,0,0,2)`, which is `C2`.
        have hs : swapT2 n m hn hm (a, b) =
            idxC3 (mkT3 n m 0 0 0 2 (by omega) (by omega) (by omega) (by omega) (by omega)) := by
          simp only [swapT2]; rw [dite_eq_right h1, dite_eq_right h2, dite_eq_right h3]
        refine ⟨?_, ?_⟩
        · rw [hs]
          simp only [idxC3, faceU, c3U, t2U, C3a, C3b, C3c, C3j, mkT3]
          refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
          simp only [CategoryTheory.comp_apply, SimplexCategory.coe_δ, cup3U_val, cup2V_val,
            Work.Cohomology.succAbove_val_if', Work.Cohomology.shmap_val]
          split_ifs <;> omega
        · rw [hs]
          simp only [idxC3, faceV, c3V, t2V, C3a, C3b, C3c, mkT3]
          refine ConcreteCategory.hom_ext _ _ (fun i => ?_); apply Fin.ext
          simp only [CategoryTheory.comp_apply, cup3V_val, cup2U_val, Work.Cohomology.shmap_val]
          split_ifs <;> omega

end

end Work.Pi6.SQM
