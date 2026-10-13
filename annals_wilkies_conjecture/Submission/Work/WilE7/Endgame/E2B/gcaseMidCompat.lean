import Mathlib
import Submission.Work.WilE7.Endgame.E2B.GSheets
import Submission.Work.WilE7.Endgame.E2_union_compat_sub
import Submission.Work.WilE7.Endgame.E2_cells_compat
import Submission.Work.WilE7.Endgame.E2_rank_strata
import Submission.Work.WilE7.coreLT_succ.RankBounds
import Submission.Work.WilE7.CoreStep.fiber_empty_of_good_of_vertical

namespace Work.WilE7.Endgame.E2B

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign

theorem gcaseMidCompat {n K F : ℕ} (c : E2Const n K F) {Fq : ℕ} {Qq : Polynomial ℕ}
    (c2 : E2Const2 c Fq Qq) {D k l m m' : ℕ} {X : Fin k → WilkiesDesign.E.SemiPf ((n + 1) + m)}
    {Y : Fin l → WilkiesDesign.E.SemiPf (n + m')} (P : E2Pkg c c2 D k l m m' X Y)
    {b : Set (Fin n → ℝ)} (hG : GHyp c c2 P b)
    (hCandDec : ∀ S ∈ P.Cand, b ⊆ WilkiesDesign.E.projFirst n (m + 1) '' Work.WilE7.MainDesign.absSet S ∨
      Disjoint b (WilkiesDesign.E.projFirst n (m + 1) '' Work.WilE7.MainDesign.absSet S))
    (G : GSheets c c2 P b)
    (T : WilkiesDesign.E.Stratum 0 (n + (m + 1))) (hT : T ∈ P.PieceList)
    (hdim : n + (m + 1) - T.j = K)
    (Kc : ℕ) (TT : Fin Kc → (Fin n → ℝ) → ℝ)
    (hTTmono : ∀ x ∈ b, StrictMono fun i : Fin Kc => TT i x)
    (hTTbnd : ∀ x ∈ b, ∀ i : Fin Kc, |TT i x| < 1)
    (hTcov : ∀ t j, (∃ i : Fin Kc, ∀ x ∈ b, TT i x = (G.sc t j x) (Fin.last m)) ∨
      (∀ x ∈ b, (G.sc t j x) (Fin.last m) = 1) ∨
      (∀ x ∈ b, (G.sc t j x) (Fin.last m) = -1))
    (hinit : ∀ κ ∈ Work.WilE7.cfs b TT, Fin.init '' κ = b) :
    ∀ κ ∈ Work.WilE7.cfs b TT,
      κ ⊆ Work.WilE7.CoreStep.projTopSet T ∨ Disjoint κ (Work.WilE7.CoreStep.projTopSet T) := by
  classical
  -- Write `T` as a member `P.PieceList.get q` of the piece list, so that all the per-piece data
  -- (`Ld`, `SloR`, `Sig`, ...) applies to it.
  obtain ⟨p, hp, hpT⟩ := P.hPieceLmem T hT
  obtain ⟨q, hq⟩ := P.hPieceLget p hp
  have hqT : P.PieceList.get q = T := by rw [hq, hpT]
  have hTgood : T.Good := (P.specPL T hT).1
  -- Every fibre point of `T` over `b` is rank-full and lies on the graph of an active candidate.
  have hcovT : ∀ z ∈ absSet T, projFirst n (m + 1) z ∈ b →
      ∃ t : Fin G.r, absSet (G.S t) ⊆ absSet T ∧ z ∈ absSet (G.S t) := by
    intro z hz hzb
    obtain ⟨w, hw, rfl⟩ := hz
    -- Rank-fullness: a rank-deficient point would project into the `Σ`-family, which `b` avoids.
    have hrfull : projRank T w = n + (m + 1) - T.j := by
      by_contra hne
      have hle : projRank T w ≤ n + (m + 1) - T.j :=
        Work.WilE7.coreLT_succ.projRank_le_dim T hTgood hw
      have hlt : projRank T w < K := by omega
      obtain ⟨Z, hZmem, hZeq⟩ := P.hSigSloR q ⟨projRank T w, hlt⟩
      have hmem : absPt w ∈ (P.SloR q ⟨projRank T w, hlt⟩).set := by
        rw [(P.specSloR q ⟨projRank T w, hlt⟩).2.2.1]
        exact ⟨w, by rw [hqT]; exact ⟨hw, rfl⟩, rfl⟩
      have hx : projFirst n (m + 1) (absPt w) ∈
          projFirst n (m + 1) '' (P.SloR q ⟨projRank T w, hlt⟩).set := ⟨absPt w, hmem, rfl⟩
      rw [← hZeq] at hx
      exact Set.disjoint_left.mp (hG.1 Z hZmem) hzb hx
    -- The rank-full locus of `T` is covered by the `Ld`-strata, which are candidates.
    have hmem2 : w ∈ ⋃ S ∈ P.Ld q, S.X.set := by
      rw [← P.specLdcov q, hqT]
      exact ⟨hw, hrfull⟩
    obtain ⟨S, hS, hwS⟩ := Set.mem_iUnion₂.mp hmem2
    have hDS : S.X.set ⊆ T.X.set := by
      have h7 := (P.specLd q).2 S hS
      rw [hqT] at h7
      exact h7.2.2.2.2.2.2.1
    have hScand : S ∈ P.Cand := P.specCandLd q S hS
    have hwSabs : absPt w ∈ absSet S := ⟨w, hwS, rfl⟩
    have hbS : b ⊆ projFirst n (m + 1) '' absSet S := by
      rcases hCandDec S hScand with h | h
      · exact h
      · exact absurd ⟨absPt w, hwSabs, rfl⟩ (Set.disjoint_left.mp h hzb)
    obtain ⟨t, ht⟩ := G.hcomplete S hScand hbS
    refine ⟨t, ?_, ?_⟩
    · rw [ht]; exact Set.image_mono hDS
    · rw [ht]; exact hwSabs
  -- Each sheet graph is one of the levels of `TT` (or the extreme levels `±1`).
  have hgr : ∀ κ ∈ Work.WilE7.cfs b TT, ∀ (t : Fin G.r) (j : Fin (G.kc t)),
      κ ⊆ Work.WilE7.gr b (fun x => (G.sc t j x) (Fin.last m)) ∨
        Disjoint κ (Work.WilE7.gr b (fun x => (G.sc t j x) (Fin.last m))) := by
    intro κ hκ t j
    refine Work.WilE7.Endgame.cell_subset_or_disjoint_gr TT hTTmono hTTbnd
      (fun x => (G.sc t j x) (Fin.last m)) ?_ κ hκ
    rcases hTcov t j with ⟨i, hi⟩ | h1 | hm1
    · exact ⟨Fin.succ (Fin.castSucc i), fun x hx => by
        rw [Work.WilE7.lvl_succ]; exact (hi x hx).symm⟩
    · exact ⟨Fin.last (Kc + 1), fun x hx => by
        rw [Work.WilE7.lvl_last]; exact h1 x hx⟩
    · exact ⟨0, fun x hx => by
        rw [Work.WilE7.lvl_zero]; exact hm1 x hx⟩
  exact Work.WilE7.Endgame.E2_union_compat_sub (fun t => G.S t) (fun t => G.kc t) G.sc
    G.hsub G.hcov hcovT TT hgr hinit

end Work.WilE7.Endgame.E2B
