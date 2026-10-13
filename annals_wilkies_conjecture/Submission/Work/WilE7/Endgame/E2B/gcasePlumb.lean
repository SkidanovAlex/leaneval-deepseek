/-
  Area E7 / E2B, node `gcaseRefineP2`: **the plumbing of the `G`-branch**.

  The lemmas here are the elementary consequences of the package `E2Pkg` (and of the decomposition
  hypothesis `CompatHyp`) that the assembly of `gcaseRefineP2` consumes: the base cell data, the
  active/inactive dichotomy for the candidates and for the pieces, the dimension bounds of the
  candidates/cut/pieces, and the cases in which the produced cells are *disjoint* from the outer
  pieces.

  Dimensions.  Rank-fullness (`CandSpec`, the rank clause of `PiecesSpec`) together with
  `projRank ≤ n` gives `dim S ≤ n` for the candidates and `dim R ≤ n` for the cut members, while
  `PiecesSpec` bounds the pieces by `K + 1`.  An *active* piece (one whose `π_n`-image captures `b`)
  therefore has `dim T ∈ {K, K+1}`: the smaller dimensions are covered by the `Σ`-family and hence
  excluded by `GHyp`, and the two remaining cases are handled by
  `E2B.gcaseMidCompat` (dimension `K`) and `E2B.gcaseVertCompat` (dimension `K+1`).
-/
import Mathlib
import Submission.Work.WilE7.Endgame.E2B.Pkg
import Submission.Work.WilE7.Endgame.E2B.GSheets
import Submission.Work.WilE7.Endgame.E2B.pieceL_low_of_pkg
import Submission.Work.WilE7.Endgame.Bv2.refAux
import Submission.Work.WilE7.Endgame.Bv2.refTriv
import Submission.Work.WilE7.Endgame.E2_swapStratum_projFirst
import Submission.Work.WilE7.cells

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

variable {n K F : ℕ} {c : E2Const n K F} {Fq : ℕ} {Qq : Polynomial ℕ} {c2 : E2Const2 c Fq Qq}
  {D k l m m' : ℕ} {X : Fin k → SemiPf ((n + 1) + m)} {Y : Fin l → SemiPf (n + m')}
  {P : E2Pkg c c2 D k l m m' X Y}

/-! ## 1. Rank and dimension -/

/-- The `π_n`-rank of an absolute stratum is at most the number of base coordinates. -/
theorem projRank_le_card {n m : ℕ} (S : Stratum 0 (n + m)) (z : Fin (0 + (n + m)) → ℝ) :
    projRank S z ≤ n := by
  have h := Submodule.finrank_le
    (Submodule.map (basePrLin n m) (LinearMap.ker (jac S z)))
  rw [Module.finrank_fin_fun] at h
  exact h

/-- A nonempty set has a nonempty `absSet`, and conversely. -/
theorem absSet_nonempty {N : ℕ} (S : Stratum 0 N) : (absSet S).Nonempty ↔ S.X.set.Nonempty := by
  constructor
  · rintro ⟨x, z, hz, rfl⟩
    exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨absPt z, z, hz, rfl⟩

/-- Every nonempty candidate has dimension at most `n`. -/
theorem candDim_le {S : Stratum 0 (n + (m + 1))} (hS : S ∈ P.Cand)
    {z : Fin (0 + (n + (m + 1))) → ℝ} (hz : z ∈ S.X.set) : n + (m + 1) - S.j ≤ n := by
  obtain ⟨-, -, -, -, hrank⟩ := P.specCand S hS
  calc n + (m + 1) - S.j = projRank S z := (hrank z hz).symm
    _ ≤ n := projRank_le_card S z

/-- Every nonempty cut member has dimension at most `n`. -/
theorem cutDim_le {R : Stratum 0 (n + (m + 1))} (hR : R ∈ P.Cut)
    {z : Fin (0 + (n + (m + 1))) → ℝ} (hz : z ∈ R.X.set) : n + (m + 1) - R.j ≤ n := by
  obtain ⟨-, -, -, hrank, -, -⟩ := P.specPieces.2.2.2.2.2.1 R hR
  calc n + (m + 1) - R.j = projRank R z := (hrank z hz).symm
    _ ≤ n := projRank_le_card R z

/-- Every piece of the `π_{n+1}`-cut has dimension at most `K + 1`. -/
theorem pieceDim_le {T : Stratum 0 (n + (m + 1))} (hT : T ∈ P.PieceList) :
    n + (m + 1) - T.j ≤ K + 1 := by
  obtain ⟨p, hp, hpT⟩ := P.hPieceLmem T hT
  rw [← hpT]
  exact (P.specPieces.2.2.2.2.1 p hp).2.2.2.1

/-! ## 2. The base cell and the dichotomies -/

/-- The cell `b` of the base decomposition of `B` is a nonempty cell of `cubeC n`. -/
theorem bCellData {B : Finset (Set (Fin (n + 1) → ℝ))}
    (hB : IsCylDecompOn (n + 1) (cubeC (n + 1)) B) {b : Set (Fin n → ℝ)}
    (hb : b ∈ B.image (fun κ => Fin.init '' κ)) :
    IsCell n b ∧ b.Nonempty ∧ b ⊆ cubeC n :=
  Bv2.base_cell_data hB hb

/-- The same, from the first conjunct of `CompatHyp`. -/
theorem bCellData' {B : Finset (Set (Fin (n + 1) → ℝ))} (hB : CompatHyp c c2 P B)
    {b : Set (Fin n → ℝ)} (hb : b ∈ B.image (fun κ => Fin.init '' κ)) :
    IsCell n b ∧ b.Nonempty ∧ b ⊆ cubeC n :=
  Bv2.base_cell_data hB.1 hb

/-- **The candidate dichotomy.**  Every candidate is either active (captures `b` in its
`π_n`-image) or its `π_n`-image misses `b`; the alternative is read off the compatibility of `B`
with the `Y`-packing. -/
theorem candDichotomy {B : Finset (Set (Fin (n + 1) → ℝ))} (hB : CompatHyp c c2 P B)
    {b : Set (Fin n → ℝ)} (hb : b ∈ B.image (fun κ => Fin.init '' κ)) :
    ∀ S ∈ P.Cand, b ⊆ projFirst n (m + 1) '' absSet S ∨
      Disjoint b (projFirst n (m + 1) '' absSet S) := by
  obtain ⟨κ₀, hκ₀B, hκ₀b⟩ := Finset.mem_image.mp hb
  intro S hS
  obtain ⟨i, hi⟩ := P.specY.2.1 S hS
  have h := hB.2.2.1 i κ₀ hκ₀B
  rw [hκ₀b, hi] at h
  exact h

/-- **The piece dichotomy.**  Every piece of the `π_{n+1}`-cut is either active or its
`π_n`-image misses `b`. -/
theorem pieceDichotomy {B : Finset (Set (Fin (n + 1) → ℝ))} (hB : CompatHyp c c2 P B)
    {b : Set (Fin n → ℝ)} (hb : b ∈ B.image (fun κ => Fin.init '' κ)) :
    ∀ T ∈ P.PieceList, b ⊆ projFirst n (m + 1) '' absSet T ∨
      Disjoint b (projFirst n (m + 1) '' absSet T) := by
  obtain ⟨κ₀, hκ₀B, hκ₀b⟩ := Finset.mem_image.mp hb
  intro T hT
  obtain ⟨i, hi⟩ := P.specY.2.2.2.2.2.2.2.2 T hT
  have h := hB.2.2.1 i κ₀ hκ₀B
  rw [hκ₀b, hi] at h
  exact h

/-! ## 3. Active cut members and active pieces -/

/-- **An active cut member has dimension exactly `K`.**  Its dimension is `≤ K` by the cut clause;
if it were `< K`, the `Σ`-clause of `PiecesSpec` would cover its `π_n`-image by `P.Sig`, which
`GHyp` forbids. -/
theorem cutActive_dim {b : Set (Fin n → ℝ)} (hbne : b.Nonempty) (hG : GHyp c c2 P b)
    {R : Stratum 0 (n + (m + 1))} (hR : R ∈ P.Cut)
    (hRact : b ⊆ projFirst n (m + 1) '' absSet R) :
    n + (m + 1) - R.j = K := by
  obtain ⟨-, -, -, -, hdimK, -⟩ := P.specPieces.2.2.2.2.2.1 R hR
  have hRcand : R ∈ P.Cand := P.specCandCut R hR
  by_contra hcon
  have hlt : n + (m + 1) - R.j < K := by omega
  have hsub := P.specSig.2.1 R hRcand hlt
  obtain ⟨x, hx⟩ := hbne
  obtain ⟨Z, hZ, hxZ⟩ := Set.mem_iUnion₂.mp (hsub (hRact hx))
  exact (Set.disjoint_left.mp (hG.1 Z hZ)) hx hxZ

/-- **An active piece exhibits an active cut member.** -/
theorem activeCut {b : Set (Fin n → ℝ)} (hbne : b.Nonempty)
    {B : Finset (Set (Fin (n + 1) → ℝ))} (hB : CompatHyp c c2 P B)
    (hb : b ∈ B.image (fun κ => Fin.init '' κ))
    {T : Stratum 0 (n + (m + 1))} (hT : T ∈ P.PieceList)
    (hact : b ⊆ projFirst n (m + 1) '' absSet T) :
    ∃ R ∈ P.Cut, b ⊆ projFirst n (m + 1) '' absSet R := by
  obtain ⟨p, hp, hpT⟩ := P.hPieceLmem T hT
  subst hpT
  have hact' : b ⊆ basePr n m '' absSet (p.2) := by
    rw [E2_swapStratum_projFirst] at hact
    exact hact
  have h1 : basePr n m '' absSet (p.2) ⊆ basePr n m '' (X p.1).set := by
    rw [← Bv2.init_image_projFirst, ← Bv2.init_image_projFirst]
    exact Set.image_mono (P.specPieces.2.2.1 p hp).2.2.2.2.2
  have h2 : basePr n m '' (X p.1).set ⊆
      ⋃ R ∈ P.Cut, projFirst n (m + 1) '' absSet R := by
    rw [← P.specPieces.2.2.2.2.2.2]
    exact Set.subset_iUnion (fun i => basePr n m '' (X i).set) p.1
  obtain ⟨x, hx⟩ := hbne
  obtain ⟨R, hR, hxR⟩ := Set.mem_iUnion₂.mp (h2 (h1 (hact' hx)))
  have hRe : R ∈ P.Cand := P.specCandCut R hR
  rcases candDichotomy hB hb R hRe with hactR | hdis
  · exact ⟨R, hR, hactR⟩
  · exact absurd hxR (Set.disjoint_left.mp hdis hx)

/-- **The dimension of an active piece is `K` or `K + 1`.** -/
theorem activePiece_dim {b : Set (Fin n → ℝ)} (hbne : b.Nonempty)
    {B : Finset (Set (Fin (n + 1) → ℝ))} (hB : CompatHyp c c2 P B)
    (hb : b ∈ B.image (fun κ => Fin.init '' κ)) (hG : GHyp c c2 P b)
    {T : Stratum 0 (n + (m + 1))} (hT : T ∈ P.PieceList)
    (hact : b ⊆ projFirst n (m + 1) '' absSet T) :
    K ≤ n + (m + 1) - T.j ∧ n + (m + 1) - T.j ≤ K + 1 := by
  have hle := pieceDim_le hT
  by_contra hcon
  have hlt : n + (m + 1) - T.j < K := by omega
  have hsub := pieceL_low_of_pkg c c2 P hT hlt
  obtain ⟨x, hx⟩ := hbne
  obtain ⟨Z, hZ, hxZ⟩ := hsub x (hact hx)
  exact (Set.disjoint_left.mp (hG.1 Z hZ)) hx hxZ

/-- An active piece of dimension `K + 1` is a vertical piece. -/
theorem activePiece_vp {T : Stratum 0 (n + (m + 1))} (hT : T ∈ P.PieceList)
    (hdim : n + (m + 1) - T.j = K + 1) : T ∈ P.Pv :=
  P.specPvAll T hT hdim

/-- **An active piece yields a candidate of dimension `K` in the active family.** -/
theorem activePiece_t₀ {b : Set (Fin n → ℝ)} (hbne : b.Nonempty)
    {B : Finset (Set (Fin (n + 1) → ℝ))} (hB : CompatHyp c c2 P B)
    (hb : b ∈ B.image (fun κ => Fin.init '' κ)) (hG : GHyp c c2 P b)
    (G : GSheets c c2 P b)
    {T : Stratum 0 (n + (m + 1))} (hT : T ∈ P.PieceList)
    (hact : b ⊆ projFirst n (m + 1) '' absSet T) :
    ∃ t₀ : Fin G.r, n + (m + 1) - (G.S t₀).j = K := by
  obtain ⟨R, hR, hRact⟩ := activeCut hbne hB hb hT hact
  have hRcand : R ∈ P.Cand := P.specCandCut R hR
  obtain ⟨t₀, ht₀⟩ := G.hcomplete R hRcand hRact
  exact ⟨t₀, by rw [ht₀]; exact cutActive_dim hbne hG hR hRact⟩

/-- **A piece of dimension `< K` is inactive.** -/
theorem pieceInactive_of_low {b : Set (Fin n → ℝ)} (hbne : b.Nonempty) (hG : GHyp c c2 P b)
    {T : Stratum 0 (n + (m + 1))} (hT : T ∈ P.PieceList) (hlt : n + (m + 1) - T.j < K) :
    Disjoint b (projFirst n (m + 1) '' absSet T) := by
  rw [Set.disjoint_left]
  intro x hx hxT
  obtain ⟨Z, hZ, hxZ⟩ := pieceL_low_of_pkg c c2 P hT hlt x hxT
  exact (Set.disjoint_left.mp (hG.1 Z hZ)) hx hxZ

/-- **An inactive piece is disjoint from the produced cells.** -/
theorem cells_disjoint_of_pieceInactive {Kc : ℕ} {TT : Fin Kc → (Fin n → ℝ) → ℝ}
    {b : Set (Fin n → ℝ)} (hmono : ∀ x ∈ b, StrictMono fun i : Fin Kc => TT i x)
    (hbnd : ∀ x ∈ b, ∀ i : Fin Kc, |TT i x| < 1)
    {T : Stratum 0 (n + (m + 1))} (hdis : Disjoint b (projFirst n (m + 1) '' absSet T)) :
    ∀ κ ∈ Work.WilE7.cfs b TT, Disjoint κ (projTopSet T) := by
  intro κ hκ
  have hcyl : κ ⊆ Work.WilE7.cyl b := Work.WilE7.cfs_subset_cyl hmono hbnd κ hκ
  rw [Set.disjoint_left]
  intro y hy hyT
  obtain ⟨z, hz, hzy⟩ := hyT
  have hb' : Fin.init y ∈ b := (hcyl hy).1
  refine Set.disjoint_left.mp hdis hb' ?_
  rw [← hzy, Work.WilE7.CoreStep.projTop_init]
  exact ⟨z, hz, rfl⟩

end
end Work.WilE7.Endgame.E2B
