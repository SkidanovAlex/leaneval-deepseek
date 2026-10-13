import Mathlib
import Submission.Work.WilE7.Endgame.E2B.Pkg
import Submission.Work.WilE7.coreLT_succ.RankBounds

namespace Work.WilE7.Endgame.E2B

noncomputable section
open Classical

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign

/-- **A piece of dimension `< K` is covered by the `Σ`-family.**  For `T ∈ P.PieceList` with
`dim T = n + (m + 1) - T.j < K`, the base image `projFirst n (m + 1) '' absSet T` (written out
pointwise) is contained in the union of the `π_n`-images of the `Σ`-family `P.Sig`.

Consequently (with `GHyp`, which makes `b` disjoint from the `π_n`-image of every `Z ∈ P.Sig`) such a
piece is never *active* over a `G`-cell: `b ⊄ projFirst n (m + 1) '' absSet T`.

Proof.  Via `P.hPieceLmem`/`P.hPieceLget`, `T` is some `PieceList.get q`.  For `z ∈ T.X.set`,
`P.specPL` gives `T.Good`, hence `finrank (ker (jac T z)) = dim T` and therefore
`projRank T z ≤ dim T < K`; so `z` lies in the rank slice `{z ∈ T.X.set | projRank T z = r}` for
`r := projRank T z < K`; `P.specSloR` identifies that slice with `(P.SloR q r).set` and
`P.hSigSloR` puts `projFirst n (m + 1) '' (P.SloR q r).set` inside the union over `P.Sig`. -/
theorem pieceL_low_of_pkg {n K F : ℕ} (c : E2Const n K F) {Fq : ℕ} {Qq : Polynomial ℕ}
    (c2 : E2Const2 c Fq Qq) {D k l m m' : ℕ} {X : Fin k → WilkiesDesign.E.SemiPf ((n + 1) + m)}
    {Y : Fin l → WilkiesDesign.E.SemiPf (n + m')} (P : E2Pkg c c2 D k l m m' X Y)
    {T : WilkiesDesign.E.Stratum 0 (n + (m + 1))} (hT : T ∈ P.PieceList)
    (hlt : n + (m + 1) - T.j < K)
    (x : Fin n → ℝ) (hx : x ∈ WilkiesDesign.E.projFirst n (m + 1) ''
      Work.WilE7.MainDesign.absSet T) :
    ∃ Z ∈ P.Sig, x ∈ WilkiesDesign.E.projFirst n (Work.WilE7.CoreStep.pPair n m) '' Z.set := by
  classical
  -- write `x` as the base projection of `absPt z` for some `z ∈ T.X.set`
  obtain ⟨z', hz', rfl⟩ := hx
  obtain ⟨z, hz, rfl⟩ := hz'
  -- `T` is a member of the piece list, hence `PieceList.get q` for some `q`
  obtain ⟨p, hp, hpT⟩ := P.hPieceLmem T hT
  obtain ⟨q, hq⟩ := P.hPieceLget p hp
  have hqT : P.PieceList.get q = T := by rw [hq, hpT]
  -- `projRank T z ≤ dim T < K`
  have hTgood : T.Good := (P.specPL T hT).1
  have hrank_le : MainDesign.projRank T z ≤ n + (m + 1) - T.j :=
    Work.WilE7.coreLT_succ.projRank_le_dim T hTgood hz
  have hrlt : MainDesign.projRank T z < K := lt_of_le_of_lt hrank_le hlt
  -- the rank slice `SloR q ⟨projRank T z, hrlt⟩` contains `absPt z` and is covered by `Sig`
  obtain ⟨Z, hZmem, hZeq⟩ := P.hSigSloR q ⟨MainDesign.projRank T z, hrlt⟩
  refine ⟨Z, hZmem, ?_⟩
  rw [hZeq]
  refine ⟨absPt z, ?_, rfl⟩
  rw [(P.specSloR q ⟨MainDesign.projRank T z, hrlt⟩).2.2.1]
  exact ⟨z, by rw [hqT]; exact ⟨hz, rfl⟩, rfl⟩

end

end Work.WilE7.Endgame.E2B
