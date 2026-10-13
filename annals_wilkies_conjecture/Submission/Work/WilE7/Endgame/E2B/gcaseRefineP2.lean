import Mathlib
import Submission.Work.WilE7.Endgame.E2B.Pkg
import Submission.Work.WilE7.Endgame.E2B.GSheets
import Submission.Work.WilE7.Endgame.E2B.gcasePlumb
import Submission.Work.WilE7.Endgame.E2B.gcaseSheetsData
import Submission.Work.WilE7.Endgame.E2B.gcaseTrichotomyData
import Submission.Work.WilE7.Endgame.E2B.gcaseHBound
import Submission.Work.WilE7.Endgame.E2B.gcaseProducer
import Submission.Work.WilE7.Endgame.E2B.gcaseMidCompat
import Submission.Work.WilE7.Endgame.E2B.gcaseVertRow
import Submission.Work.WilE7.Endgame.Bv2.refAux
import Submission.Work.WilE7.Endgame.Bv2.Aux2
import Submission.Work.WilE7.Endgame.Bv2.refTriv
import Submission.Work.WilE7.Endgame.E2_swapStratum_projFirst
import Submission.Work.WilE7.cells
import Submission.Work.WilE7.init_set
import Submission.Work.WilE7.DimAPI.cylDecomp_fiber
import Submission.Work.WilE7.CoreStep.Basic

namespace Work.WilE7.Endgame.E2B

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreLTSuccPlan
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt vertCoord)
open Work.CoreStep (frontierSet pairSubBaseFst pairFrontierBaseFst pairBase)

/-- The `G`-branch of the per-base-cell refinement of `Work.WilE7.Endgame.cellRefine_of_nodesB`.
Third statement of this lemma: the two earlier files `E2B/gcaseRefine.lean` and
`E2B/gcaseRefineProved.lean` are the records of the abandoned attempts, the second of which
correctly diagnosed that `E2Pkg` was missing the correspondence between its piece lists `Pie` and
`PieceList` and the piece facts; these are now fields of `E2Pkg` (`hPieceLlen`, `hPieceLget`,
`hPieceLmem`, `specPL`), and the three consequence lemmas `E2B.projRank_vert_of_hImm`,
`E2B.pieceL_vert_of_pkg`, `E2B.pieceL_low_of_pkg` are being proved in the same directory.

Module `Submission/Work/WilE7/Endgame/E2B/gcaseRefineRoute.lean` contains the full route (the common
frame, the padding, the sheet provision `P.hSheet`, the level data `CoreStep.gcase_sheets`, the
producer `P.hGcell`, the three cases on the dimension of the pieces, and the axiom hygiene): read it
first.  The ambient namespace must be `Work.WilE7.Endgame.E2B`, and the statement/name must not be
changed: `Submission/Work/WilE7/Endgame/cellRefine_of_nodesB.lean` calls this lemma. -/
theorem gcaseRefineP2 {n K F : ℕ} (c : E2Const n K F) {Fq : ℕ} {Qq : Polynomial ℕ}
    (c2 : E2Const2 c Fq Qq) {D k l m m' : ℕ} {X : Fin k → WilkiesDesign.E.SemiPf ((n + 1) + m)}
    {Y : Fin l → WilkiesDesign.E.SemiPf (n + m')} (P : E2Pkg c c2 D k l m m' X Y)
    (B : Finset (Set (Fin (n + 1) → ℝ))) (hB : CompatHyp c c2 P B)
    (b : Set (Fin n → ℝ)) (hb : b ∈ B.image (fun κ => Fin.init '' κ))
    (hG : GHyp c c2 P b) :
    RefineConcl c c2 P B b := by
  classical
  unfold RefineConcl
  obtain ⟨hcell, hbne, hbsubC⟩ := bCellData' hB hb
  have hpre : IsPreconnected b := Work.WilE7.isPreconnected_of_isCell hcell
  -- ## the degenerate case `k = 0`: keep the cells of `B` over `b`
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    exact ⟨B.filter (fun κ => Fin.init '' κ = b),
      Or.inl (fun κ hκ => (Finset.mem_filter.mp hκ).1),
      Work.WilE7.DimAPI.cylDecomp_fiber (cubeC (n + 1)) B hB.1 b hb,
      (fun κ hκ => (Finset.mem_filter.mp hκ).2),
      (fun i => i.elim0)⟩
  -- ## no piece at all: the compatibility clause is vacuous
  by_cases hPie : P.Pie = []
  · refine ⟨B.filter (fun κ => Fin.init '' κ = b),
      Or.inl (fun κ hκ => (Finset.mem_filter.mp hκ).1),
      Work.WilE7.DimAPI.cylDecomp_fiber (cubeC (n + 1)) B hB.1 b hb,
      (fun κ hκ => (Finset.mem_filter.mp hκ).2), ?_⟩
    intro i κ _
    have hz : projFirst (n + 1) m '' (X i).set = (∅ : Set (Fin (n + 1) → ℝ)) := by
      rw [P.specPieces.2.2.2.1 i, hPie, List.filter_nil]
      simp
    rw [hz]
    exact Or.inr (Set.disjoint_empty κ)
  -- ## the main case: `Pie ≠ []`
  have hmAp : m ≤ c.Ap := by
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil P.Pie hPie
    have h := (P.specPieces.2.2.1 p hp).2.1
    simp only [WilkiesDesign.E.SemiPf.fmt] at h
    omega
  have hmAc : m ≤ c.Ac := by rw [c.hAc]; omega
  -- ## the active family, its sheets and the level data
  obtain ⟨G, -⟩ := gcaseSheetsData c c2 P B hB b hb hG
  obtain ⟨hbnd, hcls, hdich⟩ := gcaseTrichotomyData c c2 P B hB hb hG G
  -- ## the base presentation, padded into the common frame `(n, Fq + m + 1)`
  obtain ⟨κ₀, hκ₀B, hκ₀b⟩ := Finset.mem_image.mp hb
  obtain ⟨⟨P₀, hP₀set, hP₀fmt, hP₀deg⟩, hSubPfκ₀⟩ := hB.2.2.2 κ₀ hκ₀B
  have hP₀r : P₀.X.r ≤ Fq := by
    have h := hP₀fmt; simp only [WilkiesDesign.E.SemiPf.fmt] at h; omega
  have hP₀m : P₀.m ≤ Fq := by
    have h := hP₀fmt; simp only [WilkiesDesign.E.SemiPf.fmt] at h; omega
  have hP₀m' : (Work.WilE7.StarPiece.init P₀).m = P₀.m + 1 := rfl
  have hP₀r' : (Work.WilE7.StarPiece.init P₀).X.r = P₀.X.r := rfl
  have hpadm : (Work.WilE7.StarPiece.init P₀).m ≤ Fq + m + 1 := by omega
  set Z : WilkiesDesign.E.SemiPf (n + (Fq + m + 1)) :=
    Work.WilE7.SemiPf.pad (Nat.add_le_add_left hpadm n) (Work.WilE7.StarPiece.init P₀).X with hZ
  set u : Fin (n + (Fq + m + 1)) → ℝ :=
    Work.WilE7.padZ (n + (Fq + m + 1)) (Work.WilE7.StarPiece.init P₀).p with hu
  have hZ₀set : (Work.WilE7.StarPiece.init P₀).set = b := by
    rw [Work.WilE7.init_set, hP₀set, hκ₀b]
  have hp_mem : (Work.WilE7.StarPiece.init P₀).p ∈ (Work.WilE7.StarPiece.init P₀).X.set := by
    by_contra hcon
    have hEmpty : (Work.WilE7.StarPiece.init P₀).set = ∅ := by
      show projFirst n (Work.WilE7.StarPiece.init P₀).m ''
        connectedComponentIn (Work.WilE7.StarPiece.init P₀).X.set
          (Work.WilE7.StarPiece.init P₀).p = ∅
      rw [connectedComponentIn_eq_empty hcon]
      simp
    rw [hEmpty] at hZ₀set
    exact hbne.ne_empty hZ₀set.symm
  have hu_mem : u ∈ Z.set := by
    rw [hu, hZ, Work.WilE7.SemiPf.pad_set]
    exact ⟨Work.WilE7.padZ_mem_cubeC hp_mem.1,
      by rw [Work.WilE7.takeZ_padZ]; exact hp_mem⟩
  have hC : b = projFirst n (Fq + m + 1) '' connectedComponentIn Z.set u := by
    rw [hu, hZ, (Work.WilE7.pad_component_proj
      (n := n) (m := (Work.WilE7.StarPiece.init P₀).m) (M := Fq + m + 1)
      hpadm (Work.WilE7.StarPiece.init P₀).X (Work.WilE7.StarPiece.init P₀).p).2]
    show b = (Work.WilE7.StarPiece.init P₀).set
    exact hZ₀set.symm
  have hZF : Z.fmt ≤ c2.Fbig := by
    have h1 : Z.fmt = (n + (Fq + m + 1)) + P₀.X.r := by
      rw [hZ, Bv2.semipf_pad_fmt_eq, hP₀r']
    have h2 : n + 1 + P₀.m + P₀.X.r ≤ Fq := by
      have h := hP₀fmt
      simp only [WilkiesDesign.E.SemiPf.fmt] at h
      omega
    have h5 : (n + (Fq + m + 1)) + P₀.X.r ≤ 2 * Fq + c.Ac := by omega
    have h6 : 2 * Fq + c.Ac ≤ 2 * c.Ac + (F + F + pPair n F + 5) + 4 * Fq + 4 := by omega
    have h7 : c2.Fbig = 2 * c.Ac + (F + F + pPair n F + 5) + 4 * Fq + 4 := by
      rw [c2.hBig, c.hM2]
    rw [h1, h7]
    exact le_trans h5 h6
  have hZD : Z.deg ≤ gcaseDeg c Fq Qq D := by
    have h1 : Z.deg ≤ (Work.WilE7.StarPiece.init P₀).X.deg := by
      rw [hZ]
      exact Work.WilE7.semipf_deg_pad_le _ _
    have h2 : (Work.WilE7.StarPiece.init P₀).X.deg = P₀.X.deg :=
      Work.WilE7.sp_reindex_deg _ _
    have h3 : P₀.X.deg ≤ Qq.eval D := hP₀deg
    have h4 : Qq.eval D ≤ gcaseDeg c Fq Qq D := by
      simp only [gcaseDeg]
      have h4a : (1 : ℕ) ≤ 1 + 2 * Fq := by omega
      calc Qq.eval D ≤ c.Dq.eval D + Qq.eval D := Nat.le_add_left _ _
        _ ≤ (1 + 2 * Fq) * (c.Dq.eval D + Qq.eval D) := by
            exact le_mul_of_one_le_left' h4a
        _ ≤ 2 * (1 + 2 * Fq) * (c.Dq.eval D + Qq.eval D) := by
            have h2' := Nat.le_mul_of_pos_left ((1 + 2 * Fq) * (c.Dq.eval D + Qq.eval D))
              (by omega : 0 < 2)
            simpa only [Nat.mul_assoc] using h2'
        _ ≤ 2 * Fq + 2 * (1 + 2 * Fq) * (c.Dq.eval D + Qq.eval D) + 2 := by omega
    exact le_trans (le_trans h1 (le_of_eq h2)) (le_trans h3 h4)
  -- ## the producer
  obtain ⟨Kc, TT, hTTcont, hTTmono, hTTbnd, hTcov, hTTwit, hKcbd, hinit, hcyl, hcard, hpres⟩ :=
    gcaseProducer c c2 P G hbnd hcls hdich Fq le_rfl Z u hu_mem hC
      (by rw [← hκ₀b]; exact Work.WilE7.CoreStep.SubPf_init hSubPfκ₀) hcell hZF hZD
  -- ## the conclusion
  refine ⟨Work.WilE7.cfs b TT, Or.inr ⟨hpres, ?_⟩, ?_, hinit, ?_⟩
  · -- the cardinality bound
    have hsum : (∑ t, G.kc t) ≤ G.r * c.Ps.eval (c.Dq.eval D) := by
      calc (∑ t, G.kc t) ≤ ∑ _t : Fin G.r, c.Ps.eval (c.Dq.eval D) :=
            Finset.sum_le_sum (fun t _ => G.hcle t)
        _ = G.r * c.Ps.eval (c.Dq.eval D) := by
            simp [Finset.sum_const, smul_eq_mul]
    have hr : G.r ≤ MvPolynomial.eval ![D, k] c.Np *
        (c.Pr.eval (c.Pp.eval D) + c.Pf.eval (c.Pp.eval D) + 2) :=
      le_trans G.hlenc P.specCandLen
    have hNg := c.hNg D k l
    have hmain : 2 * (∑ t, G.kc t) + 3 ≤
        3 + 2 * (MvPolynomial.eval ![D, k] c.Np *
          (c.Pr.eval (c.Pp.eval D) + c.Pf.eval (c.Pp.eval D) + 2) * c.Ps.eval (c.Dq.eval D)) := by
      have h1 : (∑ t, G.kc t) ≤ MvPolynomial.eval ![D, k] c.Np *
          (c.Pr.eval (c.Pp.eval D) + c.Pf.eval (c.Pp.eval D) + 2) * c.Ps.eval (c.Dq.eval D) :=
        le_trans hsum (Nat.mul_le_mul_right _ hr)
      omega
    rw [hNg]
    exact le_trans hcard hmain
  · -- the cell decomposition of the cylinder over `b`
    rw [← Bv2.cyl_eq_cubeC hbsubC]
    exact hcyl
  · -- compatibility with the outer pieces, piece by piece
    intro i κ hκ
    refine Bv2.compat_of_iUnion_list_map (l := P.Pie.filter (fun p => p.1 = i))
      (f := fun p => projFirst (n + 1) m '' absSet (p.2)) (P.specPieces.2.2.2.1 i) ?_
    intro p hp
    obtain ⟨hpPie, -⟩ := List.mem_filter.mp hp
    obtain ⟨q, hq⟩ := List.mem_iff_get.mp hpPie
    set T : Stratum 0 (n + (m + 1)) := E2.swapStratum (P.Pie.get q).2 with hT
    have hTmem : T ∈ P.PieceList := by
      obtain ⟨q', hq'⟩ := P.hPieceLget (P.Pie.get q) (List.get_mem P.Pie q)
      have hsw : E2.swapStratum (P.Pie.get q).2 ∈ P.PieceList := by
        rw [← hq']
        exact List.get_mem P.PieceList q'
      rwa [hT]
    have hTset : projTopSet T = projFirst (n + 1) m '' absSet (P.Pie.get q).2 :=
      E2.swapStratum_projTop (P.Pie.get q).2
    rw [← hq, ← hTset]
    have hact := pieceDichotomy hB hb T hTmem
    rcases hact with hact | hdis
    · -- an active piece: its dimension is `K` or `K + 1`
      obtain ⟨hKle, hKle'⟩ := activePiece_dim hbne hB hb hG hTmem hact
      rcases lt_or_ge (n + (m + 1) - T.j) K with hlt | hge
      · exact absurd hlt (not_lt.mpr hKle)
      · rcases eq_or_lt_of_le hge with heq | hgt
        · -- dimension `K`: the level cells lie inside the rank strata of `T`
          exact gcaseMidCompat c c2 P hG (candDichotomy hB hb) G T hTmem heq.symm
            Kc TT hTTmono hTTbnd hTcov hinit κ hκ
        · -- dimension `K + 1`: the vertical row
          have hdim : n + (m + 1) - T.j = K + 1 := by omega
          obtain ⟨t₀, ht₀⟩ := activePiece_t₀ hbne hB hb hG G hTmem hact
          exact gcaseVertRow c c2 P hG hpre G T (activePiece_vp hTmem hdim) Kc TT
            hTTmono hTTbnd hTcov hcyl t₀ (G.hkpos t₀) ht₀
            (gcaseHBound c c2 P hG G (candDichotomy hB hb) hbnd T
              (activePiece_vp hTmem hdim)) κ hκ
    · -- an inactive piece: the cells are disjoint from it
      exact Or.inr (cells_disjoint_of_pieceInactive hTTmono hTTbnd hdis κ hκ)

end
end Work.WilE7.Endgame.E2B
