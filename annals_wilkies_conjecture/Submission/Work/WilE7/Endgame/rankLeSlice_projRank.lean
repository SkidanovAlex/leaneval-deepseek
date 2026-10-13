/-
  `Work.WilE7.Endgame.rankLeSlice_projRank` — the rank-`≤ r` slice
  `{z ∈ S.X.set | projRank S z ≤ r}` of an absolute `Good` stratum `S` is semi-Pfaffian over the
  *same* chain as `S.X`, with format `≤ F` and degree bounded by a polynomial (depending only on
  the format bound `F`) in `S.deg`.

  The point of the construction is that on `S.X.set` the `Good` hypothesis pins the rank of the
  Jacobian to `S.j` (`Work.WilE7.DimAPI.jacRankGood`), so the two-sided rank conditions of
  `Work.CoreStep.RankSlice.rankSemiPf` are not needed: with the level `s` fixed at `K = S.j`, the
  single conjunction

  `rank (jacP) ≤ S.j ∧ S.j ≤ rank (jacP) ∧ rank (stackP) ≤ S.j + r`

  is equivalent to `projRank S z ≤ r`, because of the matrix identity
  `rank [jac ; basePrLin] = rank jac + finrank ((ker jac).map basePrLin)`.

  Each of the three rank conditions is a single sum of squares of minors (`sqSum`), so each
  `Basic` of `S.X` contributes exactly one `Basic` of the slice, over the same chain.

  Main inputs:
  * `Work.CoreStep.rank_le_iff_sqSum_zero`, `Work.CoreStep.le_rank_iff_sqSum_pos`
    (`rank ≤ k` / `k ≤ rank` vs. `sqSum`) and the degree bounds for `sqSum`;
  * `Work.CoreStep.finrankMapEqRankStack` (rank of a vertical stack), together with
    `Work.CoreStep.jacEval_mulVecLin_eq_jac` and `Work.CoreStep.baseMat_mulVecLin`
    (the evaluated symbolic Jacobian is `MainDesign.jac`, the constant matrix `baseMat n m` is
    the linear base projection `basePrLin n m`);
  * `Work.WilE7.DimAPI.jacRankGood` (full row rank of the Jacobian of a `Good` stratum).
-/
import Mathlib
import Submission.Work.CoreStep.rankSlice_projRank
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.DimAPI.rankLocus_nullDimLE

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.Endgame

open WilkiesDesign WilkiesDesign.E
open Work.CoreStep.RankSlice

/-! ## 1. The construction: one `Basic` per `Basic` of `X`, at a fixed Jacobian rank `K` -/

/-- One `Basic` of the rank-`≤` slice at fixed Jacobian rank `K`: the equations say
`rank (jacP) ≤ K` and `rank (stackP) ≤ K + rt`, the inequality `rank (jacP) ≥ K`. -/
def rankLeBasic {N j n r : ℕ} (c : EAChain N r) (h : Fin j → EAPoly N r)
    (P : Matrix (Fin n) (Fin N) ℝ) (K rt : ℕ) (B : Basic N r) : Basic N r :=
  { eqs := B.eqs ++ [sqSum (jacP c h) (K + 1), sqSum (stackP c h P) (K + rt + 1)],
    pos := B.pos ++ [sqSum (jacP c h) K] }

/-- The list of basics of the rank-`≤` slice: one per (`canonicalised`) basic of `X`. -/
def rankLeBasics {N j n r : ℕ} (c : EAChain N r) (h : Fin j → EAPoly N r)
    (P : Matrix (Fin n) (Fin N) ℝ) (K rt : ℕ) (l : List (Basic N r)) : List (Basic N r) :=
  (keepBasics l).map (rankLeBasic c h P K rt)

/-- The rank-`≤` slice, as a `SemiPf` set over the chain of `X`. -/
def rankLeSemiPf {N j n : ℕ} (X : SemiPf N) (h : Fin j → EAPoly N X.r)
    (P : Matrix (Fin n) (Fin N) ℝ) (K rt : ℕ) : SemiPf N :=
  ⟨X.r, X.c, rankLeBasics X.c h P K rt X.basics⟩

@[simp] theorem rankLeSemiPf_r {N j n : ℕ} (X : SemiPf N) (h : Fin j → EAPoly N X.r)
    (P : Matrix (Fin n) (Fin N) ℝ) (K rt : ℕ) : (rankLeSemiPf X h P K rt).r = X.r := rfl

@[simp] theorem rankLeSemiPf_c {N j n : ℕ} (X : SemiPf N) (h : Fin j → EAPoly N X.r)
    (P : Matrix (Fin n) (Fin N) ℝ) (K rt : ℕ) : (rankLeSemiPf X h P K rt).c = X.c := rfl

@[simp] theorem rankLeSemiPf_basics {N j n : ℕ} (X : SemiPf N) (h : Fin j → EAPoly N X.r)
    (P : Matrix (Fin n) (Fin N) ℝ) (K rt : ℕ) :
    (rankLeSemiPf X h P K rt).basics = rankLeBasics X.c h P K rt X.basics := rfl

theorem rankLeSemiPf_fmt {N j n : ℕ} (X : SemiPf N) (h : Fin j → EAPoly N X.r)
    (P : Matrix (Fin n) (Fin N) ℝ) (K rt : ℕ) : (rankLeSemiPf X h P K rt).fmt = X.fmt := rfl

/-! ## 2. Membership and degree -/

theorem rankLeBasic_holds {N j n r : ℕ} (c : EAChain N r) (h : Fin j → EAPoly N r)
    (P : Matrix (Fin n) (Fin N) ℝ) (K rt : ℕ) (B : Basic N r) (z : Fin N → ℝ) :
    (rankLeBasic c h P K rt B).holds c z ↔
      (B.holds c z ∧ eaEval c (sqSum (jacP c h) (K + 1)) z = 0 ∧
        eaEval c (sqSum (stackP c h P) (K + rt + 1)) z = 0 ∧
        0 < eaEval c (sqSum (jacP c h) K) z) := by
  have h1 : (rankLeBasic c h P K rt B).eqs
      = B.eqs ++ [sqSum (jacP c h) (K + 1), sqSum (stackP c h P) (K + rt + 1)] := rfl
  have h2 : (rankLeBasic c h P K rt B).pos = B.pos ++ [sqSum (jacP c h) K] := rfl
  simp only [Basic.holds, h1, h2]
  constructor
  · intro hh
    exact ⟨⟨fun f hf => hh.1 f (List.mem_append.mpr (Or.inl hf)),
        fun g hg => hh.2 g (List.mem_append.mpr (Or.inl hg))⟩,
      hh.1 _ (by simp), hh.1 _ (by simp), hh.2 _ (by simp)⟩
  · rintro ⟨⟨heqs, hpos⟩, h3, h4, h5⟩
    refine ⟨fun f hf => ?_, fun g hg => ?_⟩
    · rcases List.mem_append.mp hf with hf | hf
      · exact heqs f hf
      · rcases List.mem_cons.mp hf with hf | hf
        · rw [hf]; exact h3
        · rw [List.mem_singleton.mp hf]; exact h4
    · rcases List.mem_append.mp hg with hg | hg
      · exact hpos g hg
      · rw [List.mem_singleton.mp hg]; exact h5

theorem rankLeBasic_deg {N j n r : ℕ} (c : EAChain N r) (h : Fin j → EAPoly N r)
    (P : Matrix (Fin n) (Fin N) ℝ) (K rt : ℕ) (B : Basic N r) :
    (rankLeBasic c h P K rt B).deg = B.deg + atomDeg (sqSum (jacP c h) (K + 1)) +
      atomDeg (sqSum (stackP c h P) (K + rt + 1)) + atomDeg (sqSum (jacP c h) K) := by
  simp only [Basic.deg, rankLeBasic, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  ring

/-- Membership in the rank-`≤` slice: `z` lies in `X.set` and satisfies the three rank
conditions at level `K`. -/
theorem mem_rankLeSemiPf_set_iff {N j n : ℕ} (X : SemiPf N) (h : Fin j → EAPoly N X.r)
    (P : Matrix (Fin n) (Fin N) ℝ) (K rt : ℕ) (z : Fin N → ℝ) :
    z ∈ (rankLeSemiPf X h P K rt).set ↔
      z ∈ X.set ∧ eaEval X.c (sqSum (jacP X.c h) (K + 1)) z = 0 ∧
        eaEval X.c (sqSum (stackP X.c h P) (K + rt + 1)) z = 0 ∧
        0 < eaEval X.c (sqSum (jacP X.c h) K) z := by
  show (z ∈ cubeC N ∧ ∃ β ∈ rankLeBasics X.c h P K rt X.basics, β.holds X.c z) ↔
      z ∈ X.set ∧ eaEval X.c (sqSum (jacP X.c h) (K + 1)) z = 0 ∧
        eaEval X.c (sqSum (stackP X.c h P) (K + rt + 1)) z = 0 ∧
        0 < eaEval X.c (sqSum (jacP X.c h) K) z
  constructor
  · rintro ⟨hc, β, hβ, hβh⟩
    obtain ⟨B, hB, heq⟩ := List.mem_map.mp hβ
    rw [← heq] at hβh
    have hBl : B ∈ X.basics := mem_keepBasics.mp hB
    obtain ⟨hbb, h1, h2, h3⟩ := (rankLeBasic_holds X.c h P K rt B z).mp hβh
    exact ⟨⟨hc, B, hBl, hbb⟩, h1, h2, h3⟩
  · rintro ⟨⟨hc, B, hB, hBh⟩, h1, h2, h3⟩
    refine ⟨hc, rankLeBasic X.c h P K rt B, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨B, mem_keepBasics.mpr hB, rfl⟩
    · exact (rankLeBasic_holds X.c h P K rt B z).mpr ⟨hBh, h1, h2, h3⟩

/-- The degree bound for the rank-`≤` slice. -/
theorem rankLeSemiPf_deg_le {N j n : ℕ} (X : SemiPf N) (h : Fin j → EAPoly N X.r)
    (P : Matrix (Fin n) (Fin N) ℝ) (K rt D F : ℕ)
    (hX : ∀ B ∈ X.basics, B.deg ≤ D)
    (hjac : ∀ i l, (jacP X.c h i l).totalDegree ≤ D)
    (hstack : ∀ i l, (stackP X.c h P i l).totalDegree ≤ D)
    (hN : N ≤ F) :
    (rankLeSemiPf X h P K rt).deg ≤
      ((X.basics.map Basic.deg).sum + 1) * (D + 3 * (2 * (F * D) + 1)) := by
  have hmem : ∀ B ∈ rankLeBasics X.c h P K rt X.basics,
      B.deg ≤ D + 3 * (2 * (F * D) + 1) := by
    intro Bc hBc
    obtain ⟨B', hB', heq⟩ := List.mem_map.mp hBc
    have hB'X : B' ∈ X.basics := mem_keepBasics.mp hB'
    rw [← heq, rankLeBasic_deg]
    have h1 := hX B' hB'X
    have h2 := atomDeg_sqSum_le_of_le (jacP X.c h) hjac hN (k := K + 1)
    have h3 := atomDeg_sqSum_le_of_le (stackP X.c h P) hstack hN (k := K + rt + 1)
    have h4 := atomDeg_sqSum_le_of_le (jacP X.c h) hjac hN (k := K)
    omega
  have hmem2 : ∀ x ∈ (rankLeBasics X.c h P K rt X.basics).map Basic.deg,
      x ≤ D + 3 * (2 * (F * D) + 1) := by
    intro x hx
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hx
    exact hmem B hB
  have h1 : (rankLeSemiPf X h P K rt).deg ≤
      (rankLeBasics X.c h P K rt X.basics).length • (D + 3 * (2 * (F * D) + 1)) := by
    rw [SemiPf.deg, rankLeSemiPf_basics]
    have h := List.sum_le_length_nsmul
      (List.map Basic.deg (rankLeBasics X.c h P K rt X.basics))
      (D + 3 * (2 * (F * D) + 1)) hmem2
    rwa [List.length_map] at h
  have h2 : (rankLeBasics X.c h P K rt X.basics).length = (keepBasics X.basics).length := by
    rw [rankLeBasics, List.length_map]
  have h3 : (keepBasics X.basics).length ≤ (X.basics.map Basic.deg).sum + 1 :=
    length_keepBasics_le _
  rw [h2, nsmul_eq_mul] at h1
  calc (rankLeSemiPf X h P K rt).deg
      ≤ (keepBasics X.basics).length * (D + 3 * (2 * (F * D) + 1)) := h1
    _ ≤ ((X.basics.map Basic.deg).sum + 1) * (D + 3 * (2 * (F * D) + 1)) :=
        Nat.mul_le_mul_right _ h3

/-! ## 3. The two rank identities for an absolute stratum -/

/-- On a `Good` absolute stratum the evaluated Jacobian has rank `S.j`. -/
theorem jacEval_rank_eq {N : ℕ} (S : Stratum 0 N) (hS : S.Good) {z : Fin (0 + N) → ℝ}
    (hz : z ∈ S.X.set) :
    (jacEval S.X.c S.h z).rank = S.j := by
  rw [Matrix.rank, Work.CoreStep.jacEval_mulVecLin_eq_jac S z]
  exact Work.WilE7.DimAPI.jacRankGood S hS hz

/-- The rank of the evaluated stacked matrix `[jac ; baseMat]` is the rank of the Jacobian plus
the projection rank. -/
theorem stackEval_rank_eq {n m : ℕ} (S : Stratum 0 (n + m)) (z : Fin (0 + (n + m)) → ℝ) :
    (stackEval S.X.c S.h (Work.CoreStep.baseMat n m) z).rank =
      (jacEval S.X.c S.h z).rank + Work.WilE7.MainDesign.projRank S z := by
  have h := Work.CoreStep.finrankMapEqRankStack (jacEval S.X.c S.h z) (Work.CoreStep.baseMat n m)
  rw [← stackEval_eq] at h
  rw [Work.CoreStep.jacEval_mulVecLin_eq_jac S z, Work.CoreStep.baseMat_mulVecLin n m] at h
  show (stackEval S.X.c S.h (Work.CoreStep.baseMat n m) z).rank =
    (jacEval S.X.c S.h z).rank +
      Module.finrank ℝ ((LinearMap.ker (Work.WilE7.MainDesign.jac S z)).map
        (Work.WilE7.MainDesign.basePrLin n m))
  omega

/-! ## 4. The main theorem -/

theorem rankLeSlice_projRank (F : ℕ) :
    ∃ (A : ℕ) (B : Polynomial ℕ),
      ∀ (n m r : ℕ) (S : WilkiesDesign.E.Stratum 0 (n + m)), S.Good → S.X.fmt ≤ F →
        ∃ Y : WilkiesDesign.E.SemiPf (0 + (n + m)),
          Y.set = {z | z ∈ S.X.set ∧ Work.WilE7.MainDesign.projRank S z ≤ r} ∧
          Y.fmt ≤ A ∧ Y.deg ≤ B.eval S.deg := by
  refine ⟨F, Polynomial.C (8 * F + 5) * (Polynomial.X + 1) ^ 2, fun n m r S hS hfmt => ?_⟩
  have hNr : 0 + (n + m) ≤ F := by
    have h := hfmt
    simp only [SemiPf.fmt] at h
    omega
  refine ⟨rankLeSemiPf S.X S.h (Work.CoreStep.baseMat n m) S.j r, ?_, ?_, ?_⟩
  · ext z
    rw [mem_rankLeSemiPf_set_iff]
    constructor
    · rintro ⟨hzX, h1, h2, h3⟩
      refine ⟨hzX, ?_⟩
      have hJle : (jacEval S.X.c S.h z).rank ≤ S.j :=
        (Work.CoreStep.rank_le_iff_sqSum_zero S.X.c (jacP S.X.c S.h) z S.j).mpr h1
      have hJge : S.j ≤ (jacEval S.X.c S.h z).rank :=
        (Work.CoreStep.le_rank_iff_sqSum_pos S.X.c (jacP S.X.c S.h) z S.j).mpr h3
      have hJ : (jacEval S.X.c S.h z).rank = S.j := le_antisymm hJle hJge
      have hSle : (stackEval S.X.c S.h (Work.CoreStep.baseMat n m) z).rank ≤ S.j + r :=
        (Work.CoreStep.rank_le_iff_sqSum_zero S.X.c
          (stackP S.X.c S.h (Work.CoreStep.baseMat n m)) z (S.j + r)).mpr h2
      rw [stackEval_rank_eq S z, hJ] at hSle
      omega
    · rintro ⟨hzX, hle⟩
      have hJ : (jacEval S.X.c S.h z).rank = S.j := jacEval_rank_eq S hS hzX
      have hst : (stackEval S.X.c S.h (Work.CoreStep.baseMat n m) z).rank =
          S.j + Work.WilE7.MainDesign.projRank S z := by
        rw [stackEval_rank_eq S z, hJ]
      refine ⟨hzX, ?_, ?_, ?_⟩
      · exact (Work.CoreStep.rank_le_iff_sqSum_zero S.X.c (jacP S.X.c S.h) z S.j).mp
          (le_of_eq hJ)
      · exact (Work.CoreStep.rank_le_iff_sqSum_zero S.X.c
          (stackP S.X.c S.h (Work.CoreStep.baseMat n m)) z (S.j + r)).mp
          (by
            show (stackEval S.X.c S.h (Work.CoreStep.baseMat n m) z).rank ≤ S.j + r
            rw [hst]; omega)
      · exact (Work.CoreStep.le_rank_iff_sqSum_pos S.X.c (jacP S.X.c S.h) z S.j).mp
          (le_of_eq hJ.symm)
  · rw [rankLeSemiPf_fmt]
    exact hfmt
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
    have hstack : ∀ i l,
        (stackP S.X.c S.h (Work.CoreStep.baseMat n m) i l).totalDegree ≤ S.deg := by
      intro i l
      rcases i with a | j
      · exact hjac a l
      · change (MvPolynomial.C (Work.CoreStep.baseMat n m j l)).totalDegree ≤ S.deg
        rw [MvPolynomial.totalDegree_C]
        exact Nat.zero_le _
    have hdeg := rankLeSemiPf_deg_le (X := S.X) S.h (Work.CoreStep.baseMat n m) S.j r
      S.deg F hX hjac hstack hNr
    have harith : S.deg + 3 * (2 * (F * S.deg) + 1) ≤ (8 * F + 5) * (S.deg + 1) := by
      nlinarith
    have hfinal : ((S.X.basics.map Basic.deg).sum + 1) *
        (S.deg + 3 * (2 * (F * S.deg) + 1)) ≤
        (Polynomial.C (8 * F + 5) * (Polynomial.X + 1) ^ 2).eval S.deg := by
      have h1 : (S.X.basics.map Basic.deg).sum + 1 ≤ S.deg + 1 := by
        have h0 : (S.X.basics.map Basic.deg).sum = S.X.deg := rfl
        have h2 : S.X.deg ≤ S.deg := by
          rw [Stratum.deg]
          exact Nat.le_add_right _ _
        omega
      have h3 : ((S.X.basics.map Basic.deg).sum + 1) *
          (S.deg + 3 * (2 * (F * S.deg) + 1)) ≤
          (S.deg + 1) * ((8 * F + 5) * (S.deg + 1)) :=
        Nat.mul_le_mul h1 harith
      have h4 : (S.deg + 1) * ((8 * F + 5) * (S.deg + 1))
          = (Polynomial.C (8 * F + 5) * (Polynomial.X + 1) ^ 2).eval S.deg := by
        rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
          Polynomial.eval_one, Polynomial.eval_C]
        ring
      exact h3.trans (le_of_eq h4)
    exact hdeg.trans hfinal

end Work.WilE7.Endgame
