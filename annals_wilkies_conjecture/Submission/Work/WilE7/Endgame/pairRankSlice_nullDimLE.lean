import Mathlib
import Submission.Work.WilE7.CoreStep.SigmaAux
import Submission.Work.WilE7.CoreStep.CoreLTSuccNodes
import Submission.Work.WilE7.DimAPI.rankLocusAux
import Submission.Work.WilE7.DimAPI.rankLocusLocal
import Submission.Work.WilE7.DimAPI.rankLocus_nullDimLE
import Submission.Work.WilE9G.Sard.sardOnLevelSet
import Submission.Work.WilE9G.Sard.glueNull

/-
  `Work.WilE7.Endgame.pairRankSlice_nullDimLE` — the base (`π_n`) projection of the locus where the
  *pair* base rank of a `Good` absolute stratum `W` of the pair space `ℝ^{pPair n m}` is `≤ r` is a
  `NullDimLE r` set.

  This is the pair-space analogue of `Work.WilE7.DimAPI.rankLocus_nullDimLE` (the Sard node C1 of
  the E7 main design), and it is proved the same way: the `(r+1)`-coordinate projection of the
  rank-`≤ r` locus is the image of the locus under the analytic coordinate map
  `coordMapPair n m (r+1) e`, and at every point of the stratum the hypothesis of
  `Work.WilE9G.Sard.sardOnLevelSet` is met because the equation family of a `Good` stratum is a
  submersion (`Work.WilE7.DimAPI.eaFamily_surj_of_good`).  The only difference from the absolute
  `ℝ^{n+m}` case is that the base projection is `pairBase n m` (the first `n` coordinates of the
  pair space), whose linear map is `pairBaseLin n m`; that is the rank appearing in
  `pairBaseRank`, so the linear-algebra input `not_surj_restrict_of_finrank_le` applies verbatim.
-/
namespace Work.WilE7.Endgame

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreStep (pPair)
open Work.CoreStep (pairBase)
open Work.WilE7.CoreLTSuccPlan (pairBaseLin pairBaseRank)

/-- `pairBaseLin` is the linear map underlying the base projection `pairBase`: the index produced
by `pairBaseLin` (a `castAdd` into `Fin (pPair n m)`) has the same value as the one produced by
`pairBase` (a `castLE` along `le_pPair`). -/
theorem pairBaseLin_apply (n m : ℕ) (v : Fin (0 + pPair n m) → ℝ) :
    pairBaseLin n m v = pairBase n m v := by
  funext i
  simp only [pairBaseLin, pairBase, absPt, LinearMap.funLeft]
  congr 1

/-- The coordinate projection of the pair space onto the `r` base coordinates `e i`. -/
def coordMapPair (n m r : ℕ) (e : Fin r ↪ Fin n) :
    (Fin (0 + pPair n m) → ℝ) → (Fin r → ℝ) := fun z i => pairBase n m z (e i)

/-- `coordMapPair` as a continuous linear map (it is a coordinate projection). -/
def coordCLMPair (n m r : ℕ) (e : Fin r ↪ Fin n) :
    (Fin (0 + pPair n m) → ℝ) →L[ℝ] (Fin r → ℝ) :=
  ContinuousLinearMap.pi (fun i : Fin r =>
    (ContinuousLinearMap.proj (Fin.cast (Nat.zero_add (pPair n m)).symm
      (Fin.castLE (Work.CoreStep.le_pPair n m) (e i))) : (Fin (0 + pPair n m) → ℝ) →L[ℝ] ℝ))

theorem coordMapPair_eq_clm (n m r : ℕ) (e : Fin r ↪ Fin n) :
    coordMapPair n m r e = ⇑(coordCLMPair n m r e) := by
  funext z i
  simp only [coordMapPair, coordCLMPair, pairBase, absPt, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.proj_apply]

/-- The coordinate map is analytic everywhere. -/
theorem coordMapPair_analyticAt (n m r : ℕ) (e : Fin r ↪ Fin n)
    (z : Fin (0 + pPair n m) → ℝ) : AnalyticAt ℝ (coordMapPair n m r e) z := by
  rw [coordMapPair_eq_clm]
  exact (coordCLMPair n m r e).analyticAt z

/-- Its derivative, in the form used by `not_surj_restrict_of_finrank_le`. -/
theorem fderiv_coordMapPair_apply (n m r : ℕ) (e : Fin r ↪ Fin n)
    (z v : Fin (0 + pPair n m) → ℝ) :
    fderiv ℝ (coordMapPair n m r e) z v = fun i : Fin r => pairBaseLin n m v (e i) := by
  rw [coordMapPair_eq_clm, ContinuousLinearMap.fderiv]
  funext i
  simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply, coordCLMPair,
    pairBaseLin_apply, pairBase, absPt]

/-- **Local Sard input for the pair rank slice.**  At a point `z₀` of a `Good` absolute stratum
`W` of the pair space, the `(r+1)`-coordinate projection of the base-rank-`≤ r` locus is locally
Lebesgue-null.  Verbatim `Work.WilE7.DimAPI.rankLocusLocal` with `projRank`/`basePrLin` replaced by
`pairBaseRank`/`pairBaseLin`. -/
theorem pairRankLocusLocal {n m : ℕ} (W : Stratum 0 (pPair n m)) (hW : W.Good) (r : ℕ)
    (e : Fin (r + 1) ↪ Fin n) {z₀ : Fin (0 + pPair n m) → ℝ} (hz₀ : z₀ ∈ W.X.set) :
    ∃ V : Set (Fin (0 + pPair n m) → ℝ), V ∈ nhds z₀ ∧ MeasureTheory.volume
      (coordMapPair n m (r + 1) e ''
        ({z ∈ W.X.set | pairBaseRank W z ≤ r} ∩ V)) = 0 := by
  obtain ⟨N, U, hvolN, hU, hcond⟩ :=
    Work.WilE9G.Sard.sardOnLevelSet
      (fun w : Fin (0 + pPair n m) → ℝ => fun a : Fin W.j => eaEval W.X.c (W.h a) w)
      (coordMapPair n m (r + 1) e)
      (fun x => Work.WilE7.DimAPI.eaFamily_analyticAt W.X.c W.h x)
      (fun x => coordMapPair_analyticAt n m (r + 1) e x)
      z₀ (Work.WilE7.DimAPI.eaFamily_surj_of_good W hW hz₀)
  refine ⟨U, hU, ?_⟩
  refine MeasureTheory.measure_mono_null ?_ hvolN
  rintro y ⟨z, ⟨⟨hzS, hpr⟩, hzU⟩, rfl⟩
  refine hcond z hzU ?_ ?_
  · funext a
    rw [(hW z hzS).1 a, (hW z₀ hz₀).1 a]
  · intro hbad
    apply Work.WilE7.DimAPI.not_surj_restrict_of_finrank_le
      (LinearMap.ker (jac W z)) (pairBaseLin n m) (LinearMap.funLeft ℝ ℝ e) hpr
    intro w
    obtain ⟨v, hv1, hv2⟩ := hbad w
    refine ⟨v, ?_, ?_⟩
    · rw [LinearMap.mem_ker, ← Work.WilE7.DimAPI.fderiv_eaFamily_apply_jac W z v]
      exact hv1
    · rw [fderiv_coordMapPair_apply] at hv2
      exact hv2

theorem pairRankSlice_nullDimLE {n m : ℕ} (W : WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m))
    (hW : W.Good) (r : ℕ) :
    Work.WilE7.MainDesign.NullDimLE
      (Work.CoreStep.pairBase n m '' {w : Fin (0 + Work.WilE7.CoreStep.pPair n m) → ℝ |
        w ∈ W.X.set ∧ Work.WilE7.CoreLTSuccPlan.pairBaseRank W w ≤ r}) r := by
  intro e
  have hA : (fun x : Fin n → ℝ => x ∘ e) ''
        (pairBase n m '' {w : Fin (0 + pPair n m) → ℝ |
          w ∈ W.X.set ∧ pairBaseRank W w ≤ r})
      = coordMapPair n m (r + 1) e '' {w : Fin (0 + pPair n m) → ℝ |
          w ∈ W.X.set ∧ pairBaseRank W w ≤ r} := by
    rw [Set.image_image]
    rfl
  rw [hA]
  refine Work.WilE9G.Sard.glueNull (coordMapPair n m (r + 1) e) _ ?_
  rintro z₀ ⟨hz₀, -⟩
  exact pairRankLocusLocal W hW r e hz₀

end Work.WilE7.Endgame
