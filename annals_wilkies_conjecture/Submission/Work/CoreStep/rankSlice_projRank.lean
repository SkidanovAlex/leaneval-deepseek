/-
  `Work.CoreStep.rankSlice_projRank` — the rank slice
  `{z ∈ S.X.set | finrank ((ker (jac S z)).map (basePrLin n m)) = r}`
  of an absolute stratum `S` is semi-Pfaffian of format `≤ F` (the format of `S.X`) and of degree
  bounded by a polynomial (depending only on `F`) in `S.deg`.

  The construction is in `Submission/Work/CoreStep/RankSliceDefs.lean`
  (`Work.CoreStep.RankSlice.rankSemiPf`): the rank of a linear map on the tangent space is a
  Boolean combination of minors of the matrices `jac S z` and `[jac S z ; basePrLin]`, and the
  disjunction "some minor is nonzero" is realised by a sum of squares.

  The three linear-algebra inputs are
  `Work.CoreStep.rankLeIffMinorsGen`, `Work.CoreStep.leRankIffMinorsGen` (rank vs. minors) and
  `Work.CoreStep.finrankMapEqRankStack` (`rank [A₁;A₂] = rank A₁ + dim (A₂ (ker A₁))`).
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.FiberCutDefs
import Submission.Work.CoreStep.RankSliceDefs
import Submission.Work.CoreStep.rankLeIffMinorsGen
import Submission.Work.CoreStep.leRankIffMinorsGen
import Submission.Work.CoreStep.finrankMapEqRankStack

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.CoreStep

open WilkiesDesign WilkiesDesign.E

/-! ## The matrix of the base projection -/

/-- The matrix of the base projection `basePrLin n m`. -/
def baseMat (n m : ℕ) : Matrix (Fin n) (Fin (0 + (n + m))) ℝ :=
  LinearMap.toMatrix' (Work.WilE7.MainDesign.basePrLin n m)

theorem baseMat_mulVecLin (n m : ℕ) :
    (baseMat n m).mulVecLin = Work.WilE7.MainDesign.basePrLin n m := by
  have h : Matrix.mulVecLin (baseMat n m) = Matrix.toLin' (baseMat n m) := by
    apply LinearMap.ext
    intro v
    rw [Matrix.mulVecLin_apply, Matrix.toLin'_apply]
  rw [h, baseMat]
  exact Matrix.toLin'_toMatrix' _

/-- The symbolic Jacobian matrix evaluated at `z` is the matrix of `jac`. -/
theorem jacEval_mulVecLin_eq_jac {N : ℕ} (S : Stratum 0 N) (z : Fin (0 + N) → ℝ) :
    (RankSlice.jacEval S.X.c S.h z).mulVecLin = Work.WilE7.MainDesign.jac S z := rfl

/-! ## Rank forms of the `sqSum` conditions -/

/-- `rank ≤ k` is the vanishing of the sum of squares of the `(k+1)`-minors. -/
theorem rank_le_iff_sqSum_zero {ι : Type*} [Fintype ι] {N r : ℕ}
    (c : EAChain N r) (M : Matrix ι (Fin N) (EAPoly N r)) (z : Fin N → ℝ) (k : ℕ) :
    (M.map (RankSlice.evalHom c z)).rank ≤ k ↔ eaEval c (RankSlice.sqSum M (k + 1)) z = 0 :=
  (rankLeIffMinorsGen (k := k) (A := M.map (RankSlice.evalHom c z))).trans
    (RankSlice.eaEval_sqSum_eq_zero_iff c M z).symm

/-- `k ≤ rank` is the strict positivity of the sum of squares of the `k`-minors. -/
theorem le_rank_iff_sqSum_pos {ι : Type*} [Fintype ι] {N r : ℕ}
    (c : EAChain N r) (M : Matrix ι (Fin N) (EAPoly N r)) (z : Fin N → ℝ) (k : ℕ) :
    k ≤ (M.map (RankSlice.evalHom c z)).rank ↔ 0 < eaEval c (RankSlice.sqSum M k) z :=
  (leRankIffMinorsGen (k := k) (A := M.map (RankSlice.evalHom c z))).trans
    (RankSlice.eaEval_sqSum_pos_iff c M z).symm

/-! ## The main theorem -/

theorem rankSlice_projRank (F : ℕ) :
    ∃ (A : ℕ) (B : Polynomial ℕ),
      ∀ (n m r : ℕ) (S : WilkiesDesign.E.Stratum 0 (n + m)), S.X.fmt ≤ F →
        ∃ Y : WilkiesDesign.E.SemiPf (0 + (n + m)),
          Y.set = {z | z ∈ S.X.set ∧
            Module.finrank ℝ ((LinearMap.ker (Work.WilE7.MainDesign.jac S z)).map
              (Work.WilE7.MainDesign.basePrLin n m)) = r} ∧
          Y.fmt ≤ A ∧ Y.deg ≤ B.eval S.deg := by
  refine ⟨F, Polynomial.C ((F + 1) * (8 * F + 5)) * (Polynomial.X + 1) ^ 2, fun n m r S hS => ?_⟩
  have hNr : 0 + (n + m) ≤ F := by
    have h := hS
    simp only [SemiPf.fmt] at h
    omega
  refine ⟨RankSlice.rankSemiPf S.X S.h (baseMat n m) F r, ?_, ?_, ?_⟩
  · ext z
    rw [RankSlice.mem_rankSemiPf_set_iff]
    constructor
    · rintro ⟨hzX, s, hsF, h1, h2, h3, h4⟩
      refine ⟨hzX, ?_⟩
      have hJle : (RankSlice.jacEval S.X.c S.h z).rank ≤ s :=
        (rank_le_iff_sqSum_zero S.X.c (RankSlice.jacP S.X.c S.h) z s).mpr h1
      have hJge : s ≤ (RankSlice.jacEval S.X.c S.h z).rank :=
        (le_rank_iff_sqSum_pos S.X.c (RankSlice.jacP S.X.c S.h) z s).mpr h3
      have hJ : (RankSlice.jacEval S.X.c S.h z).rank = s := le_antisymm hJle hJge
      have hSle : (RankSlice.stackEval S.X.c S.h (baseMat n m) z).rank ≤ s + r :=
        (rank_le_iff_sqSum_zero S.X.c (RankSlice.stackP S.X.c S.h (baseMat n m)) z (s + r)).mpr h2
      have hSge : s + r ≤ (RankSlice.stackEval S.X.c S.h (baseMat n m) z).rank :=
        (le_rank_iff_sqSum_pos S.X.c (RankSlice.stackP S.X.c S.h (baseMat n m)) z (s + r)).mpr h4
      have hSt : (RankSlice.stackEval S.X.c S.h (baseMat n m) z).rank = s + r :=
        le_antisymm hSle hSge
      have hid := finrankMapEqRankStack (RankSlice.jacEval S.X.c S.h z) (baseMat n m)
      rw [← RankSlice.stackEval_eq, hJ, hSt] at hid
      rw [jacEval_mulVecLin_eq_jac S z, baseMat_mulVecLin n m] at hid
      omega
    · rintro ⟨hzX, hfin⟩
      have hid := finrankMapEqRankStack (RankSlice.jacEval S.X.c S.h z) (baseMat n m)
      rw [← RankSlice.stackEval_eq] at hid
      rw [jacEval_mulVecLin_eq_jac S z, baseMat_mulVecLin n m, hfin] at hid
      have hSt : (RankSlice.stackEval S.X.c S.h (baseMat n m) z).rank =
          (RankSlice.jacEval S.X.c S.h z).rank + r := by omega
      have hJ1 : (RankSlice.jacEval S.X.c S.h z).rank ≤ (RankSlice.jacEval S.X.c S.h z).rank :=
        le_rfl
      have hStle : (RankSlice.stackEval S.X.c S.h (baseMat n m) z).rank ≤
          (RankSlice.jacEval S.X.c S.h z).rank + r := le_of_eq hSt
      have hStge : (RankSlice.jacEval S.X.c S.h z).rank + r ≤
          (RankSlice.stackEval S.X.c S.h (baseMat n m) z).rank := le_of_eq hSt.symm
      refine ⟨hzX, (RankSlice.jacEval S.X.c S.h z).rank, ?_, ?_, ?_, ?_, ?_⟩
      · exact (Matrix.rank_le_width _).trans hNr
      · exact (rank_le_iff_sqSum_zero S.X.c (RankSlice.jacP S.X.c S.h) z
          (RankSlice.jacEval S.X.c S.h z).rank).mp hJ1
      · exact (rank_le_iff_sqSum_zero S.X.c (RankSlice.stackP S.X.c S.h (baseMat n m)) z
          ((RankSlice.jacEval S.X.c S.h z).rank + r)).mp hStle
      · exact (le_rank_iff_sqSum_pos S.X.c (RankSlice.jacP S.X.c S.h) z
          (RankSlice.jacEval S.X.c S.h z).rank).mp hJ1
      · exact (le_rank_iff_sqSum_pos S.X.c (RankSlice.stackP S.X.c S.h (baseMat n m)) z
          ((RankSlice.jacEval S.X.c S.h z).rank + r)).mp hStge
  · rw [RankSlice.rankSemiPf_fmt]
    exact hS
  · have hX : ∀ B ∈ S.X.basics, B.deg ≤ S.deg := by
      intro B hB
      have h1 : B.deg ≤ S.X.deg := List.le_sum_of_mem (List.mem_map_of_mem hB)
      have h2 : S.X.deg ≤ S.deg := by
        rw [Stratum.deg]
        exact Nat.le_add_right _ _
      omega
    have hjac : ∀ i l, (RankSlice.jacP S.X.c S.h i l).totalDegree ≤ S.deg := by
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
    have hstack : ∀ i l, (RankSlice.stackP S.X.c S.h (baseMat n m) i l).totalDegree ≤ S.deg := by
      intro i l
      rcases i with a | j
      · exact hjac a l
      · change (MvPolynomial.C (baseMat n m j l)).totalDegree ≤ S.deg
        rw [MvPolynomial.totalDegree_C]
        exact Nat.zero_le _
    have hdeg := RankSlice.rankSemiPf_deg_le (X := S.X) S.h (baseMat n m) F r S.deg
      hX hjac hstack hNr
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
    have hdeg' : (RankSlice.rankSemiPf S.X S.h (baseMat n m) F r).deg
        ≤ (S.X.deg + 1) * (F + 1) * (S.deg + 4 * (2 * (F * S.deg) + 1)) := by
      have hh := hdeg
      simpa only [SemiPf.deg] using hh
    exact hdeg'.trans hfin2

end Work.CoreStep
