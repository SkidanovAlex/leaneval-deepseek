/-
  `Work.WilE7.Endgame.pairRankSemiPf` — the rank slice
  `{w ∈ W.X.set | pairBaseRank W w = r}` of a *pair* stratum `W` (a stratum in the pair space
  `ℝ^{pPair n m}`) is semi-Pfaffian, of format `≤ F` and of degree bounded by a polynomial
  (depending only on `F`) in `W.deg`.

  This is the pair-space analogue of `Work.CoreStep.rankSlice_projRank`; the latter is stated for
  an absolute stratum `S : Stratum 0 (n+m)` with the base projection `basePrLin n m`.  Here the
  ambient split is `0 + pPair n m` and the projection is the linear map `pairBaseLin n m`, whose
  matrix we call `pairBaseMat`.

  The substance is the *generic* statement `rankSliceMat` below: for any stratum `S : Stratum 0 N`
  and any matrix `P : Matrix (Fin n) (Fin (0+N)) ℝ`, the set
  `{z ∈ S.X.set | finrank ((ker (jac S z)).map P.mulVecLin) = r}` is semi-Pfaffian, with format
  `≤ S.X.fmt ≤ F` and degree `≤ poly_F(S.deg)`.  The construction is the one of
  `Submission/Work/CoreStep/RankSliceDefs.lean` (`RankSlice.rankSemiPf`): the rank of a linear map
  on the tangent space is a Boolean combination of minors of the matrices `jac S z` and
  `[jac S z ; P]`, by the matrix identity
  `rank [jac ; P] = rank (jac) + finrank ((ker jac).map P.mulVecLin)`
  (`Work.CoreStep.finrankMapEqRankStack`), and the disjunction "some minor is nonzero" is realised
  by a sum of squares.  `pairBaseRank` is by definition
  `finrank ((ker (jac W w)).map (pairBaseLin n m))`, so the pair statement is an instantiation of
  `rankSliceMat` at `P = pairBaseMat n m`.
-/
import Mathlib
import Submission.Work.WilE7.CoreStep.CoreLTSuccNodes
import Submission.Work.WilE7.CoreStep.GermDefs
import Submission.Work.CoreStep.RankSliceDefs
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.CoreStep.rankSlice_projRank

set_option autoImplicit false
noncomputable section

namespace Work.WilE7.Endgame

open WilkiesDesign WilkiesDesign.E
open Work.CoreStep.RankSlice
open Work.CoreStep (finrankMapEqRankStack rank_le_iff_sqSum_zero le_rank_iff_sqSum_pos
  jacEval_mulVecLin_eq_jac)

/-! ## 1. The generic rank slice for a matrix-given linear map

Everything the proof of `rankSlice_projRank` uses about the projection is the rank expression
`(ker (jac S z)).map P.mulVecLin` and the format bound `0 + N ≤ F`.  The statement below therefore
holds verbatim for an arbitrary matrix `P`. -/

theorem rankSliceMat (F : ℕ) :
    ∃ (A : ℕ) (B : Polynomial ℕ),
      ∀ (N n r : ℕ) (S : Stratum 0 N) (P : Matrix (Fin n) (Fin (0 + N)) ℝ),
        S.X.fmt ≤ F →
        ∃ Y : SemiPf (0 + N),
          Y.set = {z : Fin (0 + N) → ℝ | z ∈ S.X.set ∧
            Module.finrank ℝ ((LinearMap.ker (Work.WilE7.MainDesign.jac S z)).map
              P.mulVecLin) = r} ∧
          Y.fmt ≤ A ∧ Y.deg ≤ B.eval S.deg := by
  refine ⟨F, Polynomial.C ((F + 1) * (8 * F + 5)) * (Polynomial.X + 1) ^ 2,
    fun N n r S P hS => ?_⟩
  have hNr : 0 + N ≤ F := by
    have h := hS
    simp only [SemiPf.fmt] at h
    omega
  refine ⟨rankSemiPf S.X S.h P F r, ?_, ?_, ?_⟩
  · ext z
    rw [mem_rankSemiPf_set_iff]
    constructor
    · rintro ⟨hzX, s, hsF, h1, h2, h3, h4⟩
      refine ⟨hzX, ?_⟩
      have hJle : (jacEval S.X.c S.h z).rank ≤ s :=
        (rank_le_iff_sqSum_zero S.X.c (jacP S.X.c S.h) z s).mpr h1
      have hJge : s ≤ (jacEval S.X.c S.h z).rank :=
        (le_rank_iff_sqSum_pos S.X.c (jacP S.X.c S.h) z s).mpr h3
      have hJ : (jacEval S.X.c S.h z).rank = s := le_antisymm hJle hJge
      have hSle : (stackEval S.X.c S.h P z).rank ≤ s + r :=
        (rank_le_iff_sqSum_zero S.X.c (stackP S.X.c S.h P) z (s + r)).mpr h2
      have hSge : s + r ≤ (stackEval S.X.c S.h P z).rank :=
        (le_rank_iff_sqSum_pos S.X.c (stackP S.X.c S.h P) z (s + r)).mpr h4
      have hSt : (stackEval S.X.c S.h P z).rank = s + r := le_antisymm hSle hSge
      have hid := finrankMapEqRankStack (jacEval S.X.c S.h z) P
      rw [← stackEval_eq, hJ, hSt] at hid
      rw [jacEval_mulVecLin_eq_jac S z] at hid
      omega
    · rintro ⟨hzX, hfin⟩
      have hid := finrankMapEqRankStack (jacEval S.X.c S.h z) P
      rw [← stackEval_eq] at hid
      rw [jacEval_mulVecLin_eq_jac S z, hfin] at hid
      have hSt : (stackEval S.X.c S.h P z).rank = (jacEval S.X.c S.h z).rank + r := by omega
      have hJ1 : (jacEval S.X.c S.h z).rank ≤ (jacEval S.X.c S.h z).rank := le_rfl
      have hStle : (stackEval S.X.c S.h P z).rank ≤ (jacEval S.X.c S.h z).rank + r :=
        le_of_eq hSt
      have hStge : (jacEval S.X.c S.h z).rank + r ≤ (stackEval S.X.c S.h P z).rank :=
        le_of_eq hSt.symm
      refine ⟨hzX, (jacEval S.X.c S.h z).rank, ?_, ?_, ?_, ?_, ?_⟩
      · exact (Matrix.rank_le_width _).trans hNr
      · exact (rank_le_iff_sqSum_zero S.X.c (jacP S.X.c S.h) z
          (jacEval S.X.c S.h z).rank).mp hJ1
      · exact (rank_le_iff_sqSum_zero S.X.c (stackP S.X.c S.h P) z
          ((jacEval S.X.c S.h z).rank + r)).mp hStle
      · exact (le_rank_iff_sqSum_pos S.X.c (jacP S.X.c S.h) z
          (jacEval S.X.c S.h z).rank).mp hJ1
      · exact (le_rank_iff_sqSum_pos S.X.c (stackP S.X.c S.h P) z
          ((jacEval S.X.c S.h z).rank + r)).mp hStge
  · rw [rankSemiPf_fmt]
    exact hS
  · have hX : ∀ B ∈ S.X.basics, B.deg ≤ S.deg := by
      intro B hB
      have h1 : B.deg ≤ S.X.deg := List.le_sum_of_mem (List.mem_map_of_mem hB)
      have h2 : S.X.deg ≤ S.deg := by
        rw [Stratum.deg]
        exact Nat.le_add_right _ _
      omega
    have hjac : ∀ i l, (jacP S.X.c S.h i l).totalDegree ≤ S.deg := by
      intro i l
      refine (Work.WilE2.totalDegree_eaD_le S.X.c l (S.h i)).trans ?_
      have h1 : atomDeg (S.h i) ≤ S.deg := by
        have h2 : atomDeg (S.h i) ≤ ∑ a, atomDeg (S.h a) :=
          Finset.single_le_sum (f := fun a => atomDeg (S.h a)) (fun a _ => Nat.zero_le _)
            (Finset.mem_univ i)
        have h3 : S.X.deg + ∑ a, atomDeg (S.h a) = S.deg := rfl
        omega
      simp only [atomDeg] at h1
      omega
    have hstack : ∀ i l, (stackP S.X.c S.h P i l).totalDegree ≤ S.deg := by
      intro i l
      rcases i with a | j
      · exact hjac a l
      · change (MvPolynomial.C (P j l)).totalDegree ≤ S.deg
        rw [MvPolynomial.totalDegree_C]
        exact Nat.zero_le _
    have hdeg := rankSemiPf_deg_le (X := S.X) S.h P F r S.deg hX hjac hstack hNr
    have harith : S.deg + 4 * (2 * (F * S.deg) + 1) ≤ (8 * F + 5) * (S.deg + 1) := by
      nlinarith
    have hbase : S.X.deg ≤ S.deg := by
      rw [Stratum.deg]
      exact Nat.le_add_right _ _
    have hfinal : S.X.deg + 1 ≤ S.deg + 1 := by omega
    have hfin2 : (S.X.deg + 1) * (F + 1) * (S.deg + 4 * (2 * (F * S.deg) + 1))
        ≤ (Polynomial.C ((F + 1) * (8 * F + 5)) * (Polynomial.X + 1) ^ 2).eval S.deg := by
      have h1 : (S.X.deg + 1) * (F + 1) * (S.deg + 4 * (2 * (F * S.deg) + 1))
          ≤ (S.deg + 1) * (F + 1) * ((8 * F + 5) * (S.deg + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul hfinal le_rfl) harith
      have h2 : (S.deg + 1) * (F + 1) * ((8 * F + 5) * (S.deg + 1))
          = (Polynomial.C ((F + 1) * (8 * F + 5)) * (Polynomial.X + 1) ^ 2).eval S.deg := by
        rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
          Polynomial.eval_one, Polynomial.eval_C]
        ring
      exact h1.trans (le_of_eq h2)
    have hdeg' : (rankSemiPf S.X S.h P F r).deg
        ≤ (S.X.deg + 1) * (F + 1) * (S.deg + 4 * (2 * (F * S.deg) + 1)) := by
      have hh := hdeg
      simpa only [SemiPf.deg] using hh
    exact hdeg'.trans hfin2

/-! ## 2. The matrix of `pairBaseLin` -/

/-- The matrix of the pair base projection `pairBaseLin n m` (in the standard bases). -/
def pairBaseMat (n m : ℕ) :
    Matrix (Fin n) (Fin (0 + Work.WilE7.CoreStep.pPair n m)) ℝ :=
  LinearMap.toMatrix' (Work.WilE7.CoreLTSuccPlan.pairBaseLin n m)

theorem pairBaseMat_mulVecLin (n m : ℕ) :
    (pairBaseMat n m).mulVecLin = Work.WilE7.CoreLTSuccPlan.pairBaseLin n m := by
  have h : Matrix.mulVecLin (pairBaseMat n m) = Matrix.toLin' (pairBaseMat n m) := by
    apply LinearMap.ext
    intro v
    rw [Matrix.mulVecLin_apply, Matrix.toLin'_apply]
  rw [h, pairBaseMat]
  exact Matrix.toLin'_toMatrix' _

/-! ## 3. The pair rank slice -/

theorem pairRankSemiPf (F : ℕ) :
    ∃ (A : ℕ) (B : Polynomial ℕ),
      ∀ (n m r : ℕ) (W : WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m)),
        W.X.fmt ≤ F →
        ∃ Y : WilkiesDesign.E.SemiPf (0 + Work.WilE7.CoreStep.pPair n m),
          Y.set = {w : Fin (0 + Work.WilE7.CoreStep.pPair n m) → ℝ |
            w ∈ W.X.set ∧ Work.WilE7.CoreLTSuccPlan.pairBaseRank W w = r} ∧
          Y.fmt ≤ A ∧ Y.deg ≤ B.eval W.deg := by
  obtain ⟨A, B, hAB⟩ := rankSliceMat F
  refine ⟨A, B, fun n m r W hW => ?_⟩
  obtain ⟨Y, hYset, hYfmt, hYdeg⟩ :=
    hAB (Work.WilE7.CoreStep.pPair n m) n r W (pairBaseMat n m) hW
  refine ⟨Y, ?_, hYfmt, hYdeg⟩
  ext w
  rw [hYset]
  simp only [Set.mem_ofPred_eq]
  rw [pairBaseMat_mulVecLin]
  show (w ∈ W.X.set ∧ Module.finrank ℝ ((LinearMap.ker (Work.WilE7.MainDesign.jac W w)).map
      (Work.WilE7.CoreLTSuccPlan.pairBaseLin n m)) = r) ↔
    (w ∈ W.X.set ∧ Work.WilE7.CoreLTSuccPlan.pairBaseRank W w = r)
  exact Iff.rfl

end Work.WilE7.Endgame
