/-
  WilG1/Choice/selSet_mem — the `Ω`-membership of the selection set `selSet K R`.

  `selSet K R` is the union of the four disjuncts of `ChoiceDefs.selSet`, intersected with
  the parameter condition `{z | Fin.init z ∈ R}`; the memberships of the four disjuncts are
  proved in `PiecesACD` and `PiecesB`.  We show

    `selSet K R ∈ S.Ω (aK + aR + 8p + 200) (200(p+2)(bK+bR) + 2000(p+2)) (p+1)`

  whenever `K ∈ S.Ω aK (bK D) (p+1)` and `R ∈ S.Ω aR (bR D) p`.
-/
import Mathlib
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.ChoiceDefs
import Submission.Work.WilG1.Choice.PieceDefs
import Submission.Work.WilG1.Choice.PiecesACD
import Submission.Work.WilG1.Choice.PiecesB

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical
open scoped BigOperators

namespace Work.WilG1.Choice

open WilkiesDesign WilkiesConjecture

/-! ## 7. The assembly -/

theorem selSet_mem {S : WilkiesDesign.SOMin} {p : ℕ} {aK aR D : ℕ} {bK bR : Polynomial ℕ}
    {K : Set (Fin (p + 1) → ℝ)} {R : Set (Fin p → ℝ)}
    (hK : K ∈ S.Ω aK (bK.eval D) (p + 1)) (hR : R ∈ S.Ω aR (bR.eval D) p) :
    Work.WilG1.selSet K R ∈ S.Ω (aK + aR + 8 * p + 200)
      ((Polynomial.C (200 * (p + 2)) * (bK + bR) + Polynomial.C (2000 * (p + 2))).eval D)
      (p + 1) := by
  -- the four disjuncts, all at the uniform format `aK + aR + 6p + 110`
  have hA : selA K ∈ S.Ω (aK + aR + 6 * p + 110) (bK.eval D + bR.eval D + 1) (p + 1) :=
    selA_mem (S := S) hK hR
  have hB : selB K ∈ S.Ω (aK + aR + 6 * p + 110)
      (16 * (bK.eval D + bR.eval D) + 33) (p + 1) :=
    selB_mem (S := S) hK hR
  have hC : selC K ∈ S.Ω (aK + aR + 6 * p + 110)
      (4 * (bK.eval D + bR.eval D) + 18) (p + 1) :=
    selC_mem (S := S) hK hR
  have hD : selD K ∈ S.Ω (aK + aR + 6 * p + 110)
      (4 * (bK.eval D + bR.eval D) + 18) (p + 1) :=
    selD_mem (S := S) hK hR
  -- the parameter condition
  have hSR : {z : Fin (p + 1) → ℝ | Fin.init z ∈ R} ∈
      S.Ω (aK + aR + 6 * p + 110) (bK.eval D + bR.eval D) (p + 1) :=
    Omega.mono (S.prod_right hR) (by omega) (by omega)
  -- the union, with clean degrees
  have hu1 : (selA K ∪ selB K) ∈ S.Ω (aK + aR + 6 * p + 110)
      (17 * (bK.eval D + bR.eval D) + 34) (p + 1) :=
    Omega.mono (union2_mem (S := S) hA hB) (by simp only [max_self]; omega) (by omega)
  have hu2 : ((selA K ∪ selB K) ∪ selC K) ∈ S.Ω (aK + aR + 6 * p + 110)
      (21 * (bK.eval D + bR.eval D) + 52) (p + 1) :=
    Omega.mono (union2_mem (S := S) hu1 hC) (by simp only [max_self]; omega) (by omega)
  have hu3 : ((selA K ∪ selB K) ∪ selC K ∪ selD K) ∈ S.Ω (aK + aR + 6 * p + 110)
      (25 * (bK.eval D + bR.eval D) + 70) (p + 1) :=
    Omega.mono (union2_mem (S := S) hu2 hD) (by simp only [max_self]; omega) (by omega)
  have hi : ({z : Fin (p + 1) → ℝ | Fin.init z ∈ R} ∩
      (selA K ∪ selB K ∪ selC K ∪ selD K)) ∈
      S.Ω (aK + aR + 6 * p + 111) (26 * (bK.eval D + bR.eval D) + 70) (p + 1) :=
    Omega.mono (inter2_mem (S := S) hSR hu3) (by simp only [max_self]; omega) (by omega)
  -- identify `selSet K R` with the constructed set
  have hset : Work.WilG1.selSet K R = {z : Fin (p + 1) → ℝ | Fin.init z ∈ R} ∩
      (selA K ∪ selB K ∪ selC K ∪ selD K) := by
    ext z
    simp only [Work.WilG1.selSet, selA, selB, selC, selD, Set.mem_ofPred_eq,
      Set.mem_inter_iff, Set.mem_union, or_assoc, and_assoc, Work.WilG1.inFib,
      Work.WilG1.isAll, Work.WilG1.isCentre, Work.WilG1.unbAbove, Work.WilG1.unbBelow]
    try tauto
  rw [hset]
  refine Omega.mono hi (by omega) ?_
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  have h1 : 26 * (bK.eval D + bR.eval D) ≤
      200 * (p + 2) * (bK.eval D + bR.eval D) := by
    apply Nat.mul_le_mul_right
    omega
  have h2 : 70 ≤ 2000 * (p + 2) := by omega
  linarith [h1, h2]

end Work.WilG1.Choice
