/-
  `Work.WilE7.Endgame.pairAvoid_fst_dim_inj` — the dimension/injectivity half of the G1 node
  (`attain_dichotomy_of_pairAvoid`).

  Setting: `S`, `T` are absolute `Good` strata in `ℝ^{n+(m+1)}`, `T` has `HImm` (the
  `(n+1)`-projection `projTop` is injective on the tangent space `ker (jac T ·)`), `V` is a
  `Good` stratum in the *pair* space `ℝ^{0+pPair n m}` whose point set lies in the level-pair set
  `{(u,v) ∈ absSet S × absSet T : π_{n+1} u = π_{n+1} v}`, and `z ∈ V.X.set`.

  Conclusion: `dim V ≤ dim S`, and the projection of the tangent space `ker (jac V z)` onto the
  *first* block is injective.

  Proof.  Write `v ∈ ker (jac V z)` as its two blocks `σ = blockFirstCLM n m v` and
  `τ = blockSndCLM n m v`.  The two blocks of any point of `V` lie in `S.X.set`, `T.X.set`
  (`pairBlocks_mem`, from the elimination lemma for `absLevelPairSet`) and their `projTop`'s agree,
  so for every defining equation `h` of `T` (resp. `S`) the composed function
  `w ↦ eaEval · h (blockSnd w)` (resp. `blockFirst`) is constant on `V.X.set`; the master lemma
  `deriv_eq_zero_of_vanish_on_good` (via `Auxiliary.kerLeKerOfVanishLevelSet`) then says its
  derivative at `z` vanishes in the direction `v`.  Hence:

  * `τ ∈ ker (jac T (blockSnd z))` (chain rule + `mem_ker_jac_iff`);
  * the level-agreement function `pairLevFun n m = projTop(blockFirst) − projTop(blockSnd)`
    (a continuous linear map) has vanishing derivative, so `projTopLin (absPtLin τ) = 0` as soon as
    `σ = 0`;
  * `σ = 0` (`hσ`) and `projTopLin (absPtLin τ) = 0` force `τ = 0` by `HImm` together with the
    rank–nullity computation `finrank (ker (jac T w)) = n+(m+1)-T.j`
    (`eq_zero_of_mem_ker_jac_of_projTop_eq_zero`), and then `v = pairPtUp σ τ = 0`.

  For the dimension bound, the first-block projection is injective on `ker (jac V z)` (previous
  paragraph) and maps it into `ker (jac S (blockFirst z))`, so
  `pPair n m − V.j = finrank (ker (jac V z)) ≤ finrank (ker (jac S (blockFirst z))) = n+(m+1) − S.j`
  (`coreLT_succ.finrank_ker_jac`).
-/
import Mathlib
import Submission.Work.WilE7.CoreStep.CoreLTSuccNodes
import Submission.Work.CoreStep.mem_absLevelPairSet_elim
import Submission.Work.CoreStep.CrossDefs
import Submission.Work.WilE7.DimAPI.openMap_of_equalDim
import Submission.Work.WilE7.DimAPI.rankLocusAux
import Submission.Work.WilE7.DimAPI.range_fderiv_good_eq_top
import Submission.Work.WilE7.DimAPI.jac_eq_fderiv
import Submission.Work.WilE7.DimAPI.ProjRankAux
import Submission.Work.WilE7.coreLT_succ.SubStratum
import Submission.Work.WilE7.Auxiliary.kerLeKerOfVanishLevelSet
import Submission.Work.WilE7.Endgame.deriv_eq_zero_of_vanish_on_good
import Submission.Work.WilE7.Endgame.pairBlocks_mem
import Submission.Work.WilE7.Endgame.eq_zero_of_mem_ker_jac_of_projTop_eq_zero

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

namespace Work.WilE7.Endgame

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin)
open Work.WilE7.CoreLTSuccPlan (HImm)

/-! ## Elementary helpers for the pair space -/

theorem absPt_zero (N : ℕ) : MainDesign.absPt (0 : Fin (0 + N) → ℝ) = 0 := by
  funext i; rfl

theorem pairPt_zero (n m : ℕ) :
    (Work.WilE7.CoreStep.pairPt (0 : Fin (0 + (n + (m + 1))) → ℝ)
      (0 : Fin (0 + (n + (m + 1))) → ℝ) : Fin (pPair n m) → ℝ) = 0 := by
  funext j
  show Fin.append (MainDesign.absPt (0 : Fin (0 + (n + (m + 1))) → ℝ))
    (MainDesign.absPt (0 : Fin (0 + (n + (m + 1))) → ℝ)) j = 0
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Fin.append_left]; rfl
  · rw [Fin.append_right]; rfl

theorem pairPtUp_zero (n m : ℕ) :
    (Work.WilE7.CoreStep.pairPtUp (0 : Fin (0 + (n + (m + 1))) → ℝ)
      (0 : Fin (0 + (n + (m + 1))) → ℝ) : Fin (0 + pPair n m) → ℝ) = 0 := by
  funext j
  show Work.WilE7.CoreStep.pairPt (0 : Fin (0 + (n + (m + 1))) → ℝ)
    (0 : Fin (0 + (n + (m + 1))) → ℝ) (Fin.cast (Nat.zero_add (pPair n m)) j) = 0
  rw [pairPt_zero]
  rfl

theorem projTopLin_absPtLin (n m : ℕ) (w : Fin (0 + (n + (m + 1))) → ℝ) :
    projTopLin n m (absPtLin (n + (m + 1)) w) = projTop n m (MainDesign.absPt w) := by
  rw [Work.WilE7.CoreStep.absPtLin_apply, Work.WilE7.CoreStep.projTopLin_apply]

/-- The level-agreement function of the pair space, in the two-block picture:
`(u,v) ↦ projTop u − projTop v`. -/
def pairLevFun (n m : ℕ) : (Fin (0 + pPair n m) → ℝ) → (Fin (n + 1) → ℝ) :=
  fun y => projTopLin n m (absPtLin (n + (m + 1)) (Work.CoreStep.blockFirstCLM n m y))
    - projTopLin n m (absPtLin (n + (m + 1)) (Work.CoreStep.blockSndCLM n m y))

/-- The same function, as a continuous linear map. -/
def pairLevCLM (n m : ℕ) : (Fin (0 + pPair n m) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ((projTopLin n m).toContinuousLinearMap).comp
      (((absPtLin (n + (m + 1))).toContinuousLinearMap).comp (Work.CoreStep.blockFirstCLM n m))
    - ((projTopLin n m).toContinuousLinearMap).comp
      (((absPtLin (n + (m + 1))).toContinuousLinearMap).comp (Work.CoreStep.blockSndCLM n m))

theorem pairLevCLM_apply (n m : ℕ) (y : Fin (0 + pPair n m) → ℝ) :
    pairLevCLM n m y = pairLevFun n m y := rfl

theorem pairLevCLM_apply' (n m : ℕ) (y : Fin (0 + pPair n m) → ℝ) :
    pairLevCLM n m y
      = projTopLin n m (absPtLin (n + (m + 1)) (Work.CoreStep.blockFirstCLM n m y))
        - projTopLin n m (absPtLin (n + (m + 1)) (Work.CoreStep.blockSndCLM n m y)) := rfl

/-- **Post-composition form of the master lemma**: if a function of the form `g ∘ L` (with `L`
continuous linear) is constant along a `Good` stratum near `z`, then its derivative vanishes
along the tangent space of the stratum. -/
theorem deriv_comp_clm_eq_zero {M K N' : ℕ} (W : Stratum 0 M) (hW : W.Good)
    {z : Fin (0 + M) → ℝ} (hz : z ∈ W.X.set)
    (L : (Fin (0 + M) → ℝ) →L[ℝ] (Fin (0 + N') → ℝ))
    (g : (Fin (0 + N') → ℝ) → (Fin K → ℝ)) (hg : DifferentiableAt ℝ g (L z))
    (hvan : ∀ᶠ y in 𝓝 z, y ∈ W.X.set → g (L y) = g (L z))
    {v : Fin (0 + M) → ℝ} (hv : v ∈ LinearMap.ker (jac W z)) :
    fderiv ℝ g (L z) (L v) = 0 := by
  have hcomp : HasFDerivAt (fun y : Fin (0 + M) → ℝ => g (L y))
      ((fderiv ℝ g (L z)).comp L) z := hg.hasFDerivAt.comp z L.hasFDerivAt
  have hf : HasFDerivAt (fun y : Fin (0 + M) → ℝ => g (L y))
      (fderiv ℝ (fun y : Fin (0 + M) → ℝ => g (L y)) z) z :=
    hcomp.congr_fderiv hcomp.fderiv.symm
  have h0 := deriv_eq_zero_of_vanish_on_good W hW hz
    (fun y : Fin (0 + M) → ℝ => g (L y)) hf hvan hv
  rw [hcomp.fderiv] at h0
  simpa using h0

/-! ## The target -/

theorem pairAvoid_fst_dim_inj {n m : ℕ}
    (S T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hS : S.Good) (hT : T.Good) (himm : Work.WilE7.CoreLTSuccPlan.HImm T)
    (V : WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m))
    (hV : V.Good)
    (hVsub : V.X.set ⊆ (Work.WilE7.CoreStep.absLevelPairSet S T).set)
    (z : Fin (0 + Work.WilE7.CoreStep.pPair n m) → ℝ)
    (hz : z ∈ V.X.set) :
    (Work.WilE7.CoreStep.pPair n m - V.j ≤ n + (m + 1) - S.j) ∧
      (∀ v ∈ LinearMap.ker (Work.WilE7.MainDesign.jac V z),
        WilkiesDesign.E.projFirst (n + (m + 1)) (n + (m + 1))
          (Work.WilE7.MainDesign.absPt v) = 0 → v = 0) := by
  have hb : ∀ v ∈ LinearMap.ker (Work.WilE7.MainDesign.jac V z),
      WilkiesDesign.E.projFirst (n + (m + 1)) (n + (m + 1))
        (Work.WilE7.MainDesign.absPt v) = 0 → v = 0 := by
    intro v hv hσ
    have hzT : (Work.CoreStep.blockSndCLM n m) z ∈ T.X.set :=
      (pairBlocks_mem S T V hVsub hz).2.1
    -- 1. the second block of `v` is tangent to `T` at the second block of `z`
    have hτ : (Work.CoreStep.blockSndCLM n m) v
        ∈ LinearMap.ker (jac T ((Work.CoreStep.blockSndCLM n m) z)) := by
      rw [Work.WilE7.DimAPI.mem_ker_jac_iff]
      exact deriv_comp_clm_eq_zero V hV hz (Work.CoreStep.blockSndCLM n m)
        (Work.WilE7.DimAPI.eqMap T)
        ((Work.WilE7.DimAPI.analyticAt_eqMap T
          ((Work.CoreStep.blockSndCLM n m) z)).differentiableAt)
        (by
          filter_upwards with y hy
          have hyT : (Work.CoreStep.blockSndCLM n m) y ∈ T.X.set :=
            (pairBlocks_mem S T V hVsub hy).2.1
          funext a
          rw [Work.WilE7.DimAPI.eqMap_apply, Work.WilE7.DimAPI.eqMap_apply,
            (hT _ hyT).1 a, (hT _ hzT).1 a])
        hv
    -- 2. the first block of `v` vanishes
    have hσ0 : (Work.CoreStep.blockFirstCLM n m) v = 0 := by
      refine Work.WilE7.DimAPI.eq_zero_of_absPt_eq_zero ?_
      rw [Work.CoreStep.absPt_blockFirstCLM]
      exact hσ
    -- 3. the level agreement propagates to the tangent space
    have hlin : HasFDerivAt (pairLevFun n m) (pairLevCLM n m) z :=
      ContinuousLinearMap.hasFDerivAt (pairLevCLM n m)
    have hF : HasFDerivAt (pairLevFun n m) (fderiv ℝ (pairLevFun n m) z) z :=
      hlin.congr_fderiv hlin.fderiv.symm
    have hlevA : ∀ w : Fin (0 + pPair n m) → ℝ,
        pairLevFun n m w
          = projTop n m (MainDesign.absPt ((Work.CoreStep.blockFirstCLM n m) w))
            - projTop n m (MainDesign.absPt ((Work.CoreStep.blockSndCLM n m) w)) := by
      intro w
      rw [← pairLevCLM_apply n m w, pairLevCLM_apply' n m w,
        projTopLin_absPtLin, projTopLin_absPtLin]
    have hvanL : ∀ᶠ y in 𝓝 z, y ∈ V.X.set → pairLevFun n m y = pairLevFun n m z := by
      filter_upwards with y hy
      have hy3 : projTop n m (MainDesign.absPt ((Work.CoreStep.blockFirstCLM n m) y))
          = projTop n m (MainDesign.absPt ((Work.CoreStep.blockSndCLM n m) y)) :=
        (pairBlocks_mem S T V hVsub hy).2.2
      have hz3 : projTop n m (MainDesign.absPt ((Work.CoreStep.blockFirstCLM n m) z))
          = projTop n m (MainDesign.absPt ((Work.CoreStep.blockSndCLM n m) z)) :=
        (pairBlocks_mem S T V hVsub hz).2.2
      simp only [hlevA y, hlevA z, hy3, hz3, sub_self]
    have hlev : projTopLin n m (absPtLin (n + (m + 1))
        ((Work.CoreStep.blockSndCLM n m) v)) = 0 := by
      have h0 := deriv_eq_zero_of_vanish_on_good V hV hz (pairLevFun n m) hF hvanL hv
      rw [hlin.fderiv] at h0
      rw [pairLevCLM_apply'] at h0
      rw [hσ0] at h0
      simp only [map_zero, zero_sub, neg_eq_zero] at h0
      exact h0
    have hτ0 : (Work.CoreStep.blockSndCLM n m) v = 0 :=
      eq_zero_of_mem_ker_jac_of_projTop_eq_zero T hT himm hzT hτ hlev
    have hfinal : v = 0 := by
      have h := Work.CoreStep.pairPtUp_block n m v
      rw [hσ0, hτ0] at h
      rw [← h]
      exact pairPtUp_zero n m
    exact hfinal
  refine ⟨?_, hb⟩
  -- (a): the dimension bound
  have hu₁S : (Work.CoreStep.blockFirstCLM n m) z ∈ S.X.set :=
    (pairBlocks_mem S T V hVsub hz).1
  set K : Submodule ℝ (Fin (0 + pPair n m) → ℝ) := LinearMap.ker (jac V z) with hK
  set Ψ : K →ₗ[ℝ] (Fin (0 + (n + (m + 1))) → ℝ) :=
    ((Work.CoreStep.blockFirstCLM n m).toLinearMap).comp K.subtype with hΨ
  have hΨapp : ∀ w : K, (Ψ w : Fin (0 + (n + (m + 1))) → ℝ)
      = (Work.CoreStep.blockFirstCLM n m) (w : Fin (0 + pPair n m) → ℝ) := by
    intro w; rw [hΨ]; rfl
  have hrange_le :
      LinearMap.range Ψ ≤ LinearMap.ker (jac S ((Work.CoreStep.blockFirstCLM n m) z)) := by
    rintro _ ⟨w, -, rfl⟩
    rw [Work.WilE7.DimAPI.mem_ker_jac_iff]
    exact deriv_comp_clm_eq_zero V hV hz (Work.CoreStep.blockFirstCLM n m)
      (Work.WilE7.DimAPI.eqMap S)
      ((Work.WilE7.DimAPI.analyticAt_eqMap S
        ((Work.CoreStep.blockFirstCLM n m) z)).differentiableAt)
      (by
        filter_upwards with y hy
        have hyS : (Work.CoreStep.blockFirstCLM n m) y ∈ S.X.set :=
          (pairBlocks_mem S T V hVsub hy).1
        funext a
        rw [Work.WilE7.DimAPI.eqMap_apply, Work.WilE7.DimAPI.eqMap_apply,
          (hS _ hyS).1 a, (hS _ hu₁S).1 a])
      w.2
  have hinjΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro w hw
    rw [LinearMap.mem_ker] at hw
    rw [hΨapp w] at hw
    have hσw : projFirst (n + (m + 1)) (n + (m + 1))
        (MainDesign.absPt (w : Fin (0 + pPair n m) → ℝ)) = 0 := by
      rw [← Work.CoreStep.absPt_blockFirstCLM (w : Fin (0 + pPair n m) → ℝ), hw, absPt_zero]
    have hw0 := hb (w : Fin (0 + pPair n m) → ℝ) w.2 hσw
    rw [Submodule.mem_bot]
    exact Subtype.ext hw0
  have hfin1 : Module.finrank ℝ K = pPair n m - V.j :=
    Work.WilE7.coreLT_succ.finrank_ker_jac V hV hz
  have hfin2 : Module.finrank ℝ ↥(LinearMap.ker (jac S ((Work.CoreStep.blockFirstCLM n m) z)))
      = n + (m + 1) - S.j :=
    Work.WilE7.coreLT_succ.finrank_ker_jac S hS hu₁S
  have hrange : Module.finrank ℝ ↥(LinearMap.range Ψ) = Module.finrank ℝ K :=
    LinearMap.finrank_range_of_inj hinjΨ
  have hle := Submodule.finrank_mono hrange_le
  omega

end Work.WilE7.Endgame
