import Mathlib
import Submission.Work.WilE7.Endgame.E2B.GSheets
import Submission.Work.WilE7.Endgame.Bv2.refBound
import Submission.Work.WilE7.CoreStep.hbound_of_frontier_sheets_C

namespace Work.WilE7.Endgame.E2B

set_option autoImplicit false
noncomputable section
open Classical

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign

/-- The height bound in **set form**: the part of the frontier of `projTopSet T` lying in the
cylinder `cyl C` over the base cell `C` is covered by the graphs of a family of continuous sections
`s e j` that lie in a family of *sets* `W e` covering the frontier of `absSet T` over `C`.

This is `Work.WilE7.CoreStep.hbound_of_frontier_sheets_C` with a set-indexed (rather than
`semiPf`-indexed) covering family: the covering `hcov` is exactly the frontier containment, so only
`hcovS` (which sheet passes through a given point of `W e` over `C`) is used of the family. -/
theorem hbound_of_frontier_sheets_set {n m r : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (C : Set (Fin n → ℝ)) (W : Fin r → Set (Fin (n + (m + 1)) → ℝ))
    (hcov : (closure (absSet T) \ absSet T) ∩ {z | projFirst n (m + 1) z ∈ C} ⊆
      ⋃ e : Fin r, W e)
    (k : Fin r → ℕ) (s : (e : Fin r) → Fin (k e) → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hsub : ∀ (e : Fin r) (j : Fin (k e)), ∀ x ∈ C, Fin.append x (s e j x) ∈ W e)
    (hcovS : ∀ (e : Fin r), ∀ z ∈ W e, projFirst n (m + 1) z ∈ C →
      ∃ j : Fin (k e), s e j (projFirst n (m + 1) z) = projSnd n (m + 1) z) :
    (closure (Work.WilE7.CoreStep.projTopSet T) \ Work.WilE7.CoreStep.projTopSet T) ∩
        Work.WilE7.cyl C ⊆
      ⋃ e : Fin r, ⋃ j : Fin (k e),
        Work.WilE7.gr C (fun x => (s e j x) (Fin.last m)) ∩ Work.WilE7.cyl C := by
  intro y hy
  obtain ⟨hyfront, hycyl⟩ := hy
  obtain ⟨hycl, hynot⟩ := hyfront
  -- Step 1: the frontier of the projection comes from the frontier of the piece.
  have hstep1 : y ∈ Work.WilE7.CoreStep.projTop n m ''
      (closure (absSet T) \ absSet T) :=
    Work.WilE7.CoreStep.closure_diff_projTop_subset n m
      (Work.CoreStep.absSet_subset_cubeC T) ⟨hycl, hynot⟩
  obtain ⟨z, hz, hzy⟩ := hstep1
  have hiny : Fin.init y = projFirst n (m + 1) z := by
    rw [← hzy, Work.WilE7.CoreStep.projTop_init]
  -- The lifted frontier point has its base in `C`, since `y ∈ cyl C`.
  have hzC : projFirst n (m + 1) z ∈ C := by
    rw [← hiny]; exact hycyl.1
  -- Step 2: the frontier of the piece is covered by the sets `W e`.
  obtain ⟨e, he⟩ := Set.mem_iUnion.mp (hcov ⟨hz, hzC⟩)
  -- Step 3: over `C`, the sheet of `W e` at the base of `z` graphs `z`.
  obtain ⟨j, hj⟩ := hcovS e z he hzC
  refine Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨j, ⟨⟨hycyl.1, ?_⟩, hycyl⟩⟩⟩
  show y (Fin.last n) = (s e j (Fin.init y)) (Fin.last m)
  rw [hiny, hj, ← hzy, Work.WilE7.CoreStep.projTop_last]

theorem gcaseHBound {n K F : ℕ} (c : E2Const n K F) {Fq : ℕ} {Qq : Polynomial ℕ}
    (c2 : E2Const2 c Fq Qq) {D k l m m' : ℕ} {X : Fin k → WilkiesDesign.E.SemiPf ((n + 1) + m)}
    {Y : Fin l → WilkiesDesign.E.SemiPf (n + m')} (P : E2Pkg c c2 D k l m m' X Y)
    {b : Set (Fin n → ℝ)} (hG : GHyp c c2 P b) (G : GSheets c c2 P b)
    (hCandDec : ∀ S ∈ P.Cand, b ⊆ WilkiesDesign.E.projFirst n (m + 1) '' Work.WilE7.MainDesign.absSet S ∨
      Disjoint b (WilkiesDesign.E.projFirst n (m + 1) '' Work.WilE7.MainDesign.absSet S))
    (hbnd : ∀ t j x, x ∈ b → |(G.sc t j x) (Fin.last m)| ≤ 1)
    (T : WilkiesDesign.E.Stratum 0 (n + (m + 1))) (hT : T ∈ P.Pv) :
    (closure (Work.WilE7.CoreStep.projTopSet T) \ Work.WilE7.CoreStep.projTopSet T) ∩
        Work.WilE7.cyl b ⊆
      ⋃ t : Fin G.r, ⋃ j : Fin (G.kc t),
        Work.WilE7.gr b (fun x => (G.sc t j x) (Fin.last m)) := by
  classical
  -- `T` sits in the piece list, so the frontier data `specLy` applies to it.
  have hTmem : T ∈ P.PieceList := (P.specPv T hT).1
  obtain ⟨p, hp, hpeq⟩ := P.hPieceLmem T hTmem
  obtain ⟨q, hq⟩ := P.hPieceLget p hp
  have hqT : P.PieceList.get q = T := hq.trans hpeq
  -- The frontier of `T` over `b` is covered by the `Lg`-strata of its piece: the `Ly`-sets are
  -- disjoint from `b` (`GHyp`) and each `Lg`-stratum is an active candidate (`hCandDec`).
  have hcov : (closure (absSet T) \ absSet T) ∩ {z | projFirst n (m + 1) z ∈ b} ⊆
      ⋃ t : Fin G.r, absSet (G.S t) := by
    intro z hz
    obtain ⟨hzfront, hzb⟩ := hz
    have hzcover : z ∈ (⋃ Sg ∈ P.Lg q, absSet Sg) ∪ ⋃ Yc ∈ P.Ly q, Yc.set := by
      have hly := (P.specLy q).2.2
      have hzfront' : z ∈ closure (absSet (P.PieceList.get q)) \ absSet (P.PieceList.get q) := by
        rw [hqT]; exact hzfront
      exact hly hzfront'
    rcases hzcover with hz' | hz'
    · -- a member of `Lg q` over `b` must be one of the active candidates
      obtain ⟨Sg, hz'⟩ := Set.mem_iUnion.mp hz'
      obtain ⟨hSg, hzSg⟩ := Set.mem_iUnion.mp hz'
      have hScand : Sg ∈ P.Cand := P.specCandLg q Sg hSg
      rcases hCandDec Sg hScand with hsub | hdisj
      · obtain ⟨t, ht⟩ := G.hcomplete Sg hScand hsub
        exact Set.mem_iUnion.mpr ⟨t, by rw [ht]; exact hzSg⟩
      · exact absurd ⟨z, hzSg, rfl⟩ (Set.disjoint_left.mp hdisj hzb)
    · -- the `Ly`-sets are disjoint from `b`
      obtain ⟨Yc, hz'⟩ := Set.mem_iUnion.mp hz'
      obtain ⟨hYc, hzYc⟩ := Set.mem_iUnion.mp hz'
      exact absurd ⟨z, hzYc, rfl⟩ (Set.disjoint_left.mp (hG.2.2 q Yc hYc) hzb)
  have hb := hbound_of_frontier_sheets_set T b (fun t => absSet (G.S t)) hcov G.kc G.sc
    (fun t j x hx => G.hsub t j x hx) (fun t z hz hbz => G.hcov t z hz hbz)
  intro y hy
  obtain ⟨e, he⟩ := Set.mem_iUnion.mp (hb hy)
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp he
  exact Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨j, hj.1⟩⟩

end

end Work.WilE7.Endgame.E2B
