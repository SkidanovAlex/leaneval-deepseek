/-
  Area E7 / the `CoreLT_succ` endgame: node **E2B** (`cellRefine_of_nodesB`).

  `CellRefineS n K` from the E7 hypotheses.  The construction is split over the modules of
  `Submission/Work/WilE7/Endgame/E2B`: `e2bConst`/`e2bConst2` choose the constants of the
  bookkeeping, `e2bPkg` produces the data package (the pieces, the candidates, the `Sigma`-family,
  the `X'`- and `Y'`-families and their properties) and the per-base-cell refinement is the two
  lemmas `sigmaRefine` (the `Sigma`-case: keep the cells of `B`) and `gcaseRefineP2` (the
  `G`-case: cut with the level family of the sheets; its route is written up in
  `E2B/gcaseRefineRoute.lean`, while `E2B/gcaseRefine.lean` and `E2B/gcaseRefineProved.lean` are the
  superseded records of the two earlier attempts).
-/
import Mathlib
import Submission.Work.WilE7.Endgame.E2B.Data2
import Submission.Work.WilE7.Endgame.E2B.sigmaRefine
import Submission.Work.WilE7.Endgame.E2B.gcaseRefineP2
import Submission.Work.WilE7.Endgame.E2B.e2bPkg

namespace Work.WilE7.Endgame

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

/-- Root of the whole endgame statement: `CellRefineS n K` from the E7 hypotheses. -/
theorem cellRefine_of_nodesB (hFC : HypFC) (hE2 : HypE2) (hE5 : HypE5) (hE6 : HypE6)
    (h0 : FrontierRestrat) (h1 : SigmaVPairs) (hV : GCaseVertical) (n K : ℕ) :
    CellRefineS n K := by
  classical
  intro F
  let c : E2B.E2Const n K F := E2B.e2bConst hFC hE2 hE5 hE6 h0 h1 n K F
  refine ⟨c.Fp0, c.P, c.Nk, c.Nl, c.Ng, ?_⟩
  intro Fq Qq
  let c2 : E2B.E2Const2 c Fq Qq := E2B.e2bConst2 c Fq Qq
  refine ⟨c2.AB, c2.CB, ?_⟩
  intro D k l m m' X Y hX hY hND
  by_cases hk : k = 0
  · -- the degenerate case `k = 0`
    subst hk
    refine ⟨0, l, m, m', (fun i => i.elim0), Y, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Nat.zero_le _
    · exact c.hNl D 0 l
    · intro i; exact i.elim0
    · intro j
      refine ⟨?_, ?_⟩
      · have hF : F ≤ c.Fp0 := by rw [c.hFp0, c.hFt]; omega
        exact le_trans (hY j).1 hF
      · exact le_trans (hY j).2 (c.hPD D)
    · intro i; exact i.elim0
    · intro j; exact ⟨j, rfl⟩
    · intro B hBdec _hBX' _hBY' _hBp b hb
      refine ⟨B.filter (fun κ => Fin.init '' κ = b), Or.inl ?_, ?_, ?_, ?_⟩
      · intro κ hκ
        exact (Finset.mem_filter.mp hκ).1
      · exact Work.WilE7.DimAPI.cylDecomp_fiber (cubeC (n + 1)) B hBdec b hb
      · intro κ hκ
        exact (Finset.mem_filter.mp hκ).2
      · intro i; exact i.elim0
  · -- the main case `k >= 1`
    have hk1 : 0 < k := Nat.pos_of_ne_zero hk
    obtain ⟨Pk, _⟩ :=
      E2B.e2bPkg hFC hE2 hE5 hE6 h0 h1 n K F Fq Qq c2 D k l m m' X Y hX hY hND hk1
    refine ⟨Pk.Zl.length, Pk.Yl.length, m + pPair n m, c.M2, (fun i => Pk.Zl.get i),
      (fun i => Pk.Yl.get i), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Pk.specZout.1
    · exact Pk.specYout.1
    · intro i; exact ⟨(Pk.specZout.2 i).1, (Pk.specZout.2 i).2.1⟩
    · intro i; exact (Pk.specYout.2.1 i)
    · intro i; exact (Pk.specZout.2 i).2.2
    · intro j
      obtain ⟨j', hj'⟩ := Pk.specYout.2.2 j
      exact ⟨j', hj'⟩
    · intro B hBdec hBX' hBY' hBp b hb
      by_cases hcase : ∃ S ∈ Pk.Sig, b ⊆ projFirst n (pPair n m) '' S.set
      · exact E2B.sigmaRefine c c2 Pk B ⟨hBdec, hBX', hBY', hBp⟩ b hb hcase
      · have key : ∀ (i : Fin Pk.Yl.length) (A : Set (Fin n → ℝ)),
            projFirst n c.M2 '' (Pk.Yl.get i).set = A →
            (∃ S ∈ Pk.Sig, A = projFirst n (pPair n m) '' S.set) →
            Disjoint b A := by
          intro i A hiA hA
          obtain ⟨κ₀, hκ₀B, hκ₀⟩ := Finset.mem_image.mp hb
          have h := hBY' i κ₀ hκ₀B
          rw [hκ₀, hiA] at h
          rcases h with h | h
          · obtain ⟨S, hS, hAS⟩ := hA
            exact absurd ⟨S, hS, by rw [← hAS]; exact h⟩ hcase
          · exact h
        refine E2B.gcaseRefineP2 c c2 Pk B ⟨hBdec, hBX', hBY', hBp⟩ b hb ⟨?_, ?_, ?_⟩
        · intro Z hZ
          obtain ⟨i, hi⟩ := Pk.specY.2.2.1 Z hZ
          exact key i _ hi ⟨Z, hZ, rfl⟩
        · intro q r
          obtain ⟨Z, hZSig, hZeq⟩ := Pk.hSigSloR q r
          obtain ⟨i, hi⟩ := Pk.specY.2.2.2.1 q r
          exact key i _ hi ⟨Z, hZSig, hZeq.symm⟩
        · intro q Yc hYc
          obtain ⟨Z, hZSig, hZeq⟩ := Pk.hSigLy q Yc hYc
          obtain ⟨i, hi⟩ := Pk.specY.2.2.2.2.1 q Yc hYc
          exact key i _ hi ⟨Z, hZSig, hZeq.symm⟩

end

end Work.WilE7.Endgame
