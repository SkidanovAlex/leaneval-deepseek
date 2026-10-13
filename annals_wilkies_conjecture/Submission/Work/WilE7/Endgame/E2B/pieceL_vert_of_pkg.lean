import Mathlib
import Submission.Work.WilE7.Endgame.E2B.Pkg
import Submission.Work.WilE7.coreLT_succ.RankBounds

namespace Work.WilE7.Endgame.E2B

/-- **The vertical pieces of the package are graphs over their base.**  For `T ∈ P.Pv` (a member
of the `π_{n+1}`-cut of dimension `K+1`, `P.specPv`), the package's piece list `P.PieceList`
(`T ∈ P.PieceList` by `P.specPv`) gives, through the correspondence `P.hPieceLmem` and the
`swapStratum` clause of `P.specPieces` (`PiecesSpec`), that

* `projTopLin ∘ absPtLin` is injective on the tangent space of `T` at every point (the `HImm`
  property, displayed expanded since `Work.WilE7.CoreLTSuccPlan.HImm` lives in a `sorry`-tainted
  file), and
* the `π_n`-rank is exactly `dim T - 1 = K` (`hvert`, as required by
  `Work.WilE7.CoreStep.gcase_vertical_cell` / `GCaseVertical` and by `g2_ptwise`).

The second part follows from the first together with `P.specPL`'s bound `projRank T z ≤ K = dim T - 1`
(`hpos : 1 ≤ n + (m + 1) - T.j` holds because `P.specPv` gives `n + (m + 1) - T.j = K + 1`), by the
linear-algebra lemma `Work.WilE7.Endgame.E2B.projRank_vert_of_hImm`. -/
theorem pieceL_vert_of_pkg {n K F : ℕ} (c : E2Const n K F) {Fq : ℕ} {Qq : Polynomial ℕ}
    (c2 : E2Const2 c Fq Qq) {D k l m m' : ℕ} {X : Fin k → WilkiesDesign.E.SemiPf ((n + 1) + m)}
    {Y : Fin l → WilkiesDesign.E.SemiPf (n + m')} (P : E2Pkg c c2 D k l m m' X Y)
    {T : WilkiesDesign.E.Stratum 0 (n + (m + 1))} (hT : T ∈ P.Pv) :
    (∀ z ∈ T.X.set, Module.finrank ℝ
      ↥(Submodule.map ((Work.WilE7.CoreStep.projTopLin n m).comp
          (Work.WilE7.CoreStep.absPtLin (n + (m + 1))))
        (Work.WilE7.MainDesign.jac T z).ker) = n + (m + 1) - T.j) ∧
    (∀ z ∈ T.X.set, Work.WilE7.MainDesign.projRank T z + 1 = n + (m + 1) - T.j) := by
  -- `P.specPv` puts `T` in the piece list and identifies `dim T = n + (m+1) - T.j` with `K + 1`.
  obtain ⟨hmem, hK⟩ := P.specPv T hT
  -- `P.specPL` supplies the `π_n`-rank bound `projRank T z ≤ K = dim T - 1`.
  have hleK : ∀ z ∈ T.X.set, Work.WilE7.MainDesign.projRank T z ≤ K :=
    (P.specPL T hmem).2.2.2.2
  have hpos : 1 ≤ n + (m + 1) - T.j := by omega
  -- ## Part 1: the `HImm` property, transferred along `swapStratum`.
  have himm : ∀ z ∈ T.X.set, Module.finrank ℝ
      ↥(Submodule.map ((Work.WilE7.CoreStep.projTopLin n m).comp
          (Work.WilE7.CoreStep.absPtLin (n + (m + 1))))
        (Work.WilE7.MainDesign.jac T z).ker) = n + (m + 1) - T.j := by
    -- `T ∈ PieceList` is `E2.swapStratum p.2` for some `p ∈ Pie` (`P.hPieceLmem`), so we may
    -- replace `T` by the piece `p` of the `π_{n+1}`-cut to which the `swapStratum` clause of
    -- `PiecesSpec` applies.
    obtain ⟨p, hp, hpT⟩ := P.hPieceLmem T hmem
    subst hpT
    exact (P.specPieces.2.2.2.2.1 p hp).2.2.2.2.2.1
  refine ⟨himm, ?_⟩
  -- ## Part 2: `projRank T z = dim T - 1`, squeezed between `specPL` and the rank inequality.
  intro z hz
  have hle : Work.WilE7.MainDesign.projRank T z ≤ n + (m + 1) - T.j - 1 := by
    have := hleK z hz
    omega
  have hlow := Work.WilE7.coreLT_succ.le_projRank_of_projTop_rank T (himm z hz)
  omega

end Work.WilE7.Endgame.E2B
