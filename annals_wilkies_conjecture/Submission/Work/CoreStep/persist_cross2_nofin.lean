import Mathlib
import Submission.Work.WilE7.CoreStep.GermDefs
import Submission.Work.WilE7.CoreStep.localGraph_on_branch
import Submission.Work.WilE7.DimAPI.projRank_eq_dim_of_sub_fibreGood
import Submission.Work.CoreStep.CrossDefs
import Submission.Work.WilE7.Nondrop.analyticLevelSetChartRange
import Submission.Work.WilE7.DimAPI.finrank_ker_fderiv_eqMap
import Submission.Work.WilE7.DimAPI.range_fderiv_good_eq_top
import Submission.Work.WilE7.DimAPI.jac_eq_fderiv
import Submission.Work.CoreStep.persist_aux_sheet_unique
import Submission.Work.CoreStep.persist_aux_pairPtUp_mem
import Submission.Work.CoreStep.exists_levelSet_chart
import Submission.Work.CoreStep.mem_absLevelPairSet_elim

namespace Work.CoreStep

open Classical Filter Topology
open scoped Topology
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.CoreStep

theorem persist_cross2_nofin {n m k k' : ℕ}
    (T T' : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hT : T.Good) (hT' : T'.Good)
    (hrank : ∀ z ∈ T.X.set, Work.WilE7.MainDesign.projRank T z = n + (m + 1) - T.j)
    (hrank' : ∀ z ∈ T'.X.set, Work.WilE7.MainDesign.projRank T' z = n + (m + 1) - T'.j)
    (C : Set (Fin n → ℝ))
    (s : Fin k → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (s' : Fin k' → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j : Fin k, ContinuousOn (s j) C)
    (hcont' : ∀ j : Fin k', ContinuousOn (s' j) C)
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hinj' : ∀ x ∈ C, Function.Injective fun j : Fin k' => s' j x)
    (hsub : ∀ (j : Fin k) (x : Fin n → ℝ), x ∈ C →
      Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x (s j x)) ∈ T.X.set)
    (hsub' : ∀ (j : Fin k') (x : Fin n → ℝ), x ∈ C →
      Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x (s' j x)) ∈ T'.X.set)
    (hcov : ∀ z ∈ Work.WilE7.MainDesign.absSet T,
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C →
      ∃ j : Fin k, s j (WilkiesDesign.E.projFirst n (m + 1) z) =
        WilkiesDesign.E.projSnd n (m + 1) z)
    (hcov' : ∀ z ∈ Work.WilE7.MainDesign.absSet T',
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C →
      ∃ j : Fin k', s' j (WilkiesDesign.E.projFirst n (m + 1) z) =
        WilkiesDesign.E.projSnd n (m + 1) z)
    (Wl : List (WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m)))
    (hWlgood : ∀ W ∈ Wl, W.Good)
    (hWlsub : ∀ W ∈ Wl, W.X.set ⊆ (Work.WilE7.CoreStep.absLevelPairSet T T').set)
    (hWlcov : (Work.WilE7.CoreStep.absLevelPairSet T T').set = ⋃ W ∈ Wl, W.X.set)
    (havoid : ∀ (j : Fin k) (j' : Fin k') (x₀ : Fin n → ℝ), x₀ ∈ C →
      (s j x₀) (Fin.last m) = (s' j' x₀) (Fin.last m) →
      (∀ W ∈ Wl, Work.WilE7.CoreStep.pPair n m - W.j < n + (m + 1) - T.j →
        Work.WilE7.CoreStep.pairPtUp
          (Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀)))
          (Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x₀ (s' j' x₀)))
            ∉ W.X.set) ∧
      (∀ W ∈ Wl, Work.WilE7.CoreStep.pPair n m - W.j = n + (m + 1) - T.j →
        Work.WilE7.CoreStep.pairPtUp
          (Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀)))
          (Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x₀ (s' j' x₀)))
            ∉ closure W.X.set \ W.X.set)) :
    ∀ (j : Fin k) (j' : Fin k') (x₀ : Fin n → ℝ), x₀ ∈ C →
      (s j x₀) (Fin.last m) = (s' j' x₀) (Fin.last m) →
      ∃ U ∈ nhds x₀, ∀ x ∈ C ∩ U, (s j x) (Fin.last m) = (s' j' x) (Fin.last m) := by

  intro j j' x₀ hx₀ hlev
  have hpzT : absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀)) ∈ T.X.set := hsub j x₀ hx₀
  have hqzT : absPtUp (n := n) (m := m) (Fin.append x₀ (s' j' x₀)) ∈ T'.X.set :=
    hsub' j' x₀ hx₀
  have hPPmem : pairPtUp (absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀)))
      (absPtUp (n := n) (m := m) (Fin.append x₀ (s' j' x₀)))
      ∈ (absLevelPairSet T T').set :=
    mem_absLevelPairSet_sheets T T' j j' s s' x₀ hpzT hqzT hlev
  -- the stratum of the pair set through the pair point
  obtain ⟨W₀, hW₀mem, hW₀pp⟩ : ∃ W ∈ Wl, pairPtUp (absPtUp (n := n) (m := m)
      (Fin.append x₀ (s j x₀))) (absPtUp (n := n) (m := m) (Fin.append x₀ (s' j' x₀)))
      ∈ W.X.set := by
    have h : pairPtUp (absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀)))
        (absPtUp (n := n) (m := m) (Fin.append x₀ (s' j' x₀)))
        ∈ ⋃ W ∈ Wl, W.X.set := hWlcov ▸ hPPmem
    obtain ⟨W, hW⟩ := Set.mem_iUnion.mp h
    obtain ⟨hWmem, hWx⟩ := Set.mem_iUnion.mp hW
    exact ⟨W, hWmem, hWx⟩
  have hW₀good : W₀.Good := hWlgood W₀ hW₀mem
  have hW₀sub : W₀.X.set ⊆ (absLevelPairSet T T').set := hWlsub W₀ hW₀mem
  have havoid1 := (havoid j j' x₀ hx₀ hlev).1
  have hdimW : n + (m + 1) - T.j ≤ pPair n m - W₀.j :=
    not_lt.mp fun hc => havoid1 W₀ hW₀mem hc hW₀pp
  set Z : Fin (0 + pPair n m) → ℝ :=
    pairPtUp (absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀)))
      (absPtUp (n := n) (m := m) (Fin.append x₀ (s' j' x₀))) with hZ
  obtain ⟨γW, VW, UW, χW, hVWopen, h0VW, hγW0, hγWan, hγWrange, hγWinj, hVWgood,
      hUWopen, hUWZ, hχWan, hχWin⟩ :=
    exists_levelSet_chart W₀ hW₀good Z (by rw [hZ]; exact hW₀pp) Set.univ Filter.univ_mem
  obtain ⟨γT, VT, UT, χT, hVTopen, h0VT, hγT0, hγTan, hγTrange, hγTinj, hVTgood,
      hUTopen, hpzUT, hχTan, hχTin⟩ :=
    exists_levelSet_chart T hT (absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀))) hpzT
      Set.univ Filter.univ_mem
  obtain ⟨γT', VT', UT', χT', hVT'open, h0VT', hγT'0, hγT'an, hγT'range, hγT'inj, hVT'good,
      hUT'open, hqzUT', hχT'an, hχT'in⟩ :=
    exists_levelSet_chart T' hT' (absPtUp (n := n) (m := m) (Fin.append x₀ (s' j' x₀))) hqzT
      Set.univ Filter.univ_mem
  have hVWmem : VW ∈ nhds (0 : (fderiv ℝ (Work.WilE7.DimAPI.eqMap W₀) Z).ker) :=
    hVWopen.mem_nhds h0VW
  have haZ : blockFirstCLM n m Z
      = absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀)) := by
    rw [hZ, blockFirst_pairPtUp]
  have hbZ : blockSndCLM n m Z
      = absPtUp (n := n) (m := m) (Fin.append x₀ (s' j' x₀)) := by
    rw [hZ, blockSnd_pairPtUp]
  set η : (fderiv ℝ (Work.WilE7.DimAPI.eqMap W₀) Z).ker
      → (fderiv ℝ (Work.WilE7.DimAPI.eqMap T) (absPtUp (n := n) (m := m)
          (Fin.append x₀ (s j x₀)))).ker :=
    fun y => χT (blockFirstCLM n m (γW y)) with hη
  set η' : (fderiv ℝ (Work.WilE7.DimAPI.eqMap W₀) Z).ker
      → (fderiv ℝ (Work.WilE7.DimAPI.eqMap T') (absPtUp (n := n) (m := m)
          (Fin.append x₀ (s' j' x₀)))).ker :=
    fun y => χT' (blockSndCLM n m (γW y)) with hη'
  have hχT0 : χT (absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀))) = 0 := by
    have hin := hχTin (absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀))) hpzUT
      (Work.WilE7.DimAPI.eqMap_eq_zero_of_good T hT hpzT)
    exact hγTinj hin.1 h0VT (by rw [hin.2, hγT0])
  have hχT'0 : χT' (absPtUp (n := n) (m := m) (Fin.append x₀ (s' j' x₀))) = 0 := by
    have hin := hχT'in (absPtUp (n := n) (m := m) (Fin.append x₀ (s' j' x₀))) hqzUT'
      (Work.WilE7.DimAPI.eqMap_eq_zero_of_good T' hT' hqzT)
    exact hγT'inj hin.1 h0VT' (by rw [hin.2, hγT'0])
  have hη0 : η 0 = 0 := by
    show χT (blockFirstCLM n m (γW 0)) = 0
    rw [hγW0, haZ, hχT0]
  have hη'0 : η' 0 = 0 := by
    show χT' (blockSndCLM n m (γW 0)) = 0
    rw [hγW0, hbZ, hχT'0]
  have helim : ∀ y ∈ VW, γW y ∈ (absLevelPairSet T T').set :=
    fun y hy => hW₀sub (hVWgood y hy).1
  have hblockT : ∀ y ∈ VW, blockFirstCLM n m (γW y) ∈ T.X.set := by
    intro y hy
    have h := (mem_absLevelPairSet_elim T T' (helim y hy)).1
    rw [blockFirstCLM_apply]
    exact (mem_absSet_iff T _).mp h
  have hblockT' : ∀ y ∈ VW, blockSndCLM n m (γW y) ∈ T'.X.set := by
    intro y hy
    have h := (mem_absLevelPairSet_elim T T' (helim y hy)).2.1
    rw [blockSndCLM_apply]
    exact (mem_absSet_iff T' _).mp h
  have hbaseblock : ∀ y ∈ VW, Work.WilE7.MainDesign.basePrLin n (m + 1)
        (blockFirstCLM n m (γW y))
      = Work.WilE7.MainDesign.basePrLin n (m + 1) (blockSndCLM n m (γW y)) := by
    intro y hy
    have h := (mem_absLevelPairSet_elim T T' (helim y hy)).2.2.1
    have key : ∀ v : Fin (0 + (n + (m + 1))) → ℝ,
        Work.WilE7.MainDesign.basePrLin n (m + 1) v
          = projFirst n (m + 1) (Work.WilE7.MainDesign.absPt v) :=
      fun v => (Work.WilE7.CoreStep.projFirst_absPt_eq_basePrLin v).symm
    rw [blockFirstCLM_apply, blockSndCLM_apply, key, key,
      Work.WilE7.DimAPI.absPt_absPtInv, Work.WilE7.DimAPI.absPt_absPtInv]
    exact h
  have hlevblock : ∀ y ∈ VW, levelOf n m (blockFirstCLM n m (γW y))
      = levelOf n m (blockSndCLM n m (γW y)) := by
    intro y hy
    have h := (mem_absLevelPairSet_elim T T' (helim y hy)).2.2.2.1
    simp only [levelOf]
    rw [blockFirstCLM_apply, blockSndCLM_apply,
      Work.WilE7.DimAPI.absPt_absPtInv, Work.WilE7.DimAPI.absPt_absPtInv]
    exact h
  have heqmapT' : ∀ y ∈ VW, Work.WilE7.DimAPI.eqMap T' (blockSndCLM n m (γW y)) = 0 :=
    fun y hy => Work.WilE7.DimAPI.eqMap_eq_zero_of_good T' hT' (hblockT' y hy)
  have hηan : AnalyticAt ℝ η 0 := by
    have h1 : AnalyticAt ℝ (fun y => blockFirstCLM n m (γW y)) 0 :=
      ((blockFirstCLM n m).analyticAt (γW 0)).comp hγWan
    have h2 : AnalyticAt ℝ χT (blockFirstCLM n m (γW 0)) := by
      rw [hγW0, haZ]; exact hχTan
    exact AnalyticAt.comp (g := χT) (f := fun y => blockFirstCLM n m (γW y)) h2 h1
  have hη'an : AnalyticAt ℝ η' 0 := by
    have h1 : AnalyticAt ℝ (fun y => blockSndCLM n m (γW y)) 0 :=
      ((blockSndCLM n m).analyticAt (γW 0)).comp hγWan
    have h2 : AnalyticAt ℝ χT' (blockSndCLM n m (γW 0)) := by
      rw [hγW0, hbZ]; exact hχT'an
    exact AnalyticAt.comp (g := χT') (f := fun y => blockSndCLM n m (γW y)) h2 h1
  have hnearT : ∀ᶠ y in nhds (0 : (fderiv ℝ (Work.WilE7.DimAPI.eqMap W₀) Z).ker),
      blockFirstCLM n m (γW y) ∈ UT := by
    have hcont : ContinuousAt (fun y => blockFirstCLM n m (γW y)) 0 :=
      (blockFirstCLM n m).continuous.continuousAt.comp (hγWan.continuousAt)
    exact hcont.tendsto.eventually
      (hUTopen.mem_nhds (by rw [hγW0, haZ]; exact hpzUT))
  have hnearT' : ∀ᶠ y in nhds (0 : (fderiv ℝ (Work.WilE7.DimAPI.eqMap W₀) Z).ker),
      blockSndCLM n m (γW y) ∈ UT' := by
    have hcont : ContinuousAt (fun y => blockSndCLM n m (γW y)) 0 :=
      (blockSndCLM n m).continuous.continuousAt.comp (hγWan.continuousAt)
    exact hcont.tendsto.eventually
      (hUT'open.mem_nhds (by rw [hγW0, hbZ]; exact hqzUT'))
  have hda : HasFDerivAt (fun y => blockFirstCLM n m (γW y))
      ((blockFirstCLM n m).comp (fderiv ℝ γW 0)) 0 :=
    (blockFirstCLM n m).hasFDerivAt.comp 0 (hγWan.hasStrictFDerivAt.hasFDerivAt)
  have hdb : HasFDerivAt (fun y => blockSndCLM n m (γW y))
      ((blockSndCLM n m).comp (fderiv ℝ γW 0)) 0 :=
    (blockSndCLM n m).hasFDerivAt.comp 0 (hγWan.hasStrictFDerivAt.hasFDerivAt)
  have hχTan' : AnalyticAt ℝ χT (blockFirstCLM n m (γW 0)) := by
    rw [hγW0, haZ]; exact hχTan
  have hdη : HasFDerivAt η ((fderiv ℝ χT (blockFirstCLM n m (γW 0))).comp
      ((blockFirstCLM n m).comp (fderiv ℝ γW 0))) 0 :=
    HasFDerivAt.comp 0 (g := χT) (g' := fderiv ℝ χT (blockFirstCLM n m (γW 0)))
      (f := fun y => blockFirstCLM n m (γW y)) hχTan'.hasStrictFDerivAt.hasFDerivAt hda
  have hidentT : (fun y => γT (η y)) =ᶠ[nhds (0 : (fderiv ℝ (Work.WilE7.DimAPI.eqMap W₀) Z).ker)]
      (fun y => blockFirstCLM n m (γW y)) := by
    filter_upwards [hnearT, hVWmem] with y hyUT hyVW
    exact (hχTin (blockFirstCLM n m (γW y)) hyUT
      (Work.WilE7.DimAPI.eqMap_eq_zero_of_good T hT (hblockT y hyVW))).2
  have hchainT : (fderiv ℝ γT 0).comp (fderiv ℝ η 0)
      = (blockFirstCLM n m).comp (fderiv ℝ γW 0) := by
    have hγTan0 : HasFDerivAt γT (fderiv ℝ γT 0) (η 0) := by
      rw [hη0]; exact hγTan.hasStrictFDerivAt.hasFDerivAt
    have hdη' : HasFDerivAt η (fderiv ℝ η 0) 0 := hdη.fderiv ▸ hdη
    have h1 : HasFDerivAt (fun y => γT (η y))
        ((fderiv ℝ γT 0).comp (fderiv ℝ η 0)) 0 :=
      HasFDerivAt.comp 0 (g := γT) (g' := fderiv ℝ γT 0) (f := η) hγTan0 hdη'
    have h2 : HasFDerivAt (fun y => blockFirstCLM n m (γW y))
        ((fderiv ℝ γT 0).comp (fderiv ℝ η 0)) 0 :=
      h1.congr_of_eventuallyEq hidentT.symm
    rw [← h2.fderiv, ← hda.fderiv]
  have hbase_deriv : (Work.WilE7.MainDesign.basePrLin n (m + 1)).toContinuousLinearMap.comp
        ((blockFirstCLM n m).comp (fderiv ℝ γW 0))
      = (Work.WilE7.MainDesign.basePrLin n (m + 1)).toContinuousLinearMap.comp
        ((blockSndCLM n m).comp (fderiv ℝ γW 0)) := by
    have h1 : HasFDerivAt (fun y => Work.WilE7.MainDesign.basePrLin n (m + 1)
        (blockFirstCLM n m (γW y)))
        ((Work.WilE7.MainDesign.basePrLin n (m + 1)).toContinuousLinearMap.comp
          ((blockFirstCLM n m).comp (fderiv ℝ γW 0))) 0 :=
      ((Work.WilE7.MainDesign.basePrLin n (m + 1)).toContinuousLinearMap.hasFDerivAt.comp 0 hda)
    have h2 : HasFDerivAt (fun y => Work.WilE7.MainDesign.basePrLin n (m + 1)
        (blockSndCLM n m (γW y)))
        ((Work.WilE7.MainDesign.basePrLin n (m + 1)).toContinuousLinearMap.comp
          ((blockSndCLM n m).comp (fderiv ℝ γW 0))) 0 :=
      ((Work.WilE7.MainDesign.basePrLin n (m + 1)).toContinuousLinearMap.hasFDerivAt.comp 0 hdb)
    have h3 : HasFDerivAt (fun y => Work.WilE7.MainDesign.basePrLin n (m + 1)
        (blockFirstCLM n m (γW y)))
        ((Work.WilE7.MainDesign.basePrLin n (m + 1)).toContinuousLinearMap.comp
          ((blockSndCLM n m).comp (fderiv ℝ γW 0))) 0 :=
      h2.congr_of_eventuallyEq
        (Filter.eventually_of_mem hVWmem (fun y hy => hbaseblock y hy))
    exact h1.unique h3
  have heqmap_deriv : ((fderiv ℝ (Work.WilE7.DimAPI.eqMap T')
      (blockSndCLM n m (γW 0))).comp ((blockSndCLM n m).comp (fderiv ℝ γW 0))) = 0 := by
    have h1 : HasFDerivAt (fun y => Work.WilE7.DimAPI.eqMap T' (blockSndCLM n m (γW y)))
        ((fderiv ℝ (Work.WilE7.DimAPI.eqMap T') (blockSndCLM n m (γW 0))).comp
          ((blockSndCLM n m).comp (fderiv ℝ γW 0))) 0 :=
      HasFDerivAt.comp 0 (g := Work.WilE7.DimAPI.eqMap T')
        (g' := fderiv ℝ (Work.WilE7.DimAPI.eqMap T') (blockSndCLM n m (γW 0)))
        (f := fun y => blockSndCLM n m (γW y))
        ((Work.WilE7.DimAPI.analyticAt_eqMap T' (blockSndCLM n m (γW 0))).hasStrictFDerivAt.hasFDerivAt)
        hdb
    have hev : (fun y : (fderiv ℝ (Work.WilE7.DimAPI.eqMap W₀) Z).ker =>
        Work.WilE7.DimAPI.eqMap T' (blockSndCLM n m (γW y))) =ᶠ[nhds 0]
        (fun _ => (0 : Fin T'.j → ℝ)) :=
      Filter.eventually_of_mem hVWmem (fun y hy => heqmapT' y hy)
    have h2 : HasFDerivAt (fun _ : (fderiv ℝ (Work.WilE7.DimAPI.eqMap W₀) Z).ker =>
        (0 : Fin T'.j → ℝ))
        (0 : (fderiv ℝ (Work.WilE7.DimAPI.eqMap W₀) Z).ker →L[ℝ] Fin T'.j → ℝ) 0 :=
      hasFDerivAt_const _ _
    have h3 := (h1.congr_of_eventuallyEq hev.symm).unique h2
    simpa using h3
  have hχWγW : (fun y => χW (γW y)) =ᶠ[nhds (0 : (fderiv ℝ (Work.WilE7.DimAPI.eqMap W₀) Z).ker)]
      (fun y => y) := by
    have hU : ∀ᶠ y in nhds (0 : (fderiv ℝ (Work.WilE7.DimAPI.eqMap W₀) Z).ker), γW y ∈ UW :=
      hγWan.continuousAt.tendsto.eventually (hUWopen.mem_nhds (by rw [hγW0]; exact hUWZ))
    filter_upwards [hVWmem, hU] with y hyVW hyUW
    obtain ⟨h2, h3⟩ := hχWin (γW y) hyUW
      (Work.WilE7.DimAPI.eqMap_eq_zero_of_good W₀ hW₀good (hVWgood y hyVW).1)
    exact hγWinj h2 hyVW (by rw [h3])
  have hinj_γW : Function.Injective (fderiv ℝ γW 0) :=
    injective_fderiv_of_eventually_leftInverse γW χW hγWan
      (by rw [hγW0]; exact hχWan) hχWγW
  have hker_eta : ∀ v, fderiv ℝ η 0 v = 0 → v = 0 := by
    intro v hv
    have hda_v : blockFirstCLM n m ((fderiv ℝ γW 0) v) = 0 := by
      rw [← ContinuousLinearMap.comp_apply, ← hchainT, ContinuousLinearMap.comp_apply,
        hv, map_zero]
    have hdb_v : ((blockSndCLM n m).comp (fderiv ℝ γW 0)) v = 0 := by
      have hb_base : Work.WilE7.MainDesign.basePrLin n (m + 1)
          (((blockSndCLM n m).comp (fderiv ℝ γW 0)) v) = 0 := by
        have hthis := congrArg (fun (F : (fderiv ℝ (Work.WilE7.DimAPI.eqMap W₀) Z).ker
            →L[ℝ] Fin n → ℝ) => F v) hbase_deriv
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_coe] at hthis
        rw [show (blockFirstCLM n m) ((fderiv ℝ γW 0) v) = 0 from hda_v] at hthis
        rw [map_zero] at hthis
        exact hthis.symm
      have hb_ker : (((blockSndCLM n m).comp (fderiv ℝ γW 0)) v)
          ∈ LinearMap.ker (Work.WilE7.MainDesign.jac T'
              (blockSndCLM n m (γW 0))) := by
        rw [Work.WilE7.DimAPI.jac_eq_fderiv T' (blockSndCLM n m (γW 0)), LinearMap.mem_ker]
        exact congrArg (fun (F : (fderiv ℝ (Work.WilE7.DimAPI.eqMap W₀) Z).ker
            →L[ℝ] Fin T'.j → ℝ) => F v) heqmap_deriv
      have hz0 : blockSndCLM n m (γW 0) ∈ T'.X.set := by
        rw [hγW0, hbZ]; exact hqzT
      have hinj := Work.WilE7.CoreStep.basePrLin_injective_on_ker_jac T' hT'
        (blockSndCLM n m (γW 0)) hz0 (hrank' _ hz0)
      have hzero : ((blockSndCLM n m).comp (fderiv ℝ γW 0)) v = 0 := by
        have heq : (⟨((blockSndCLM n m).comp (fderiv ℝ γW 0)) v, hb_ker⟩ :
              LinearMap.ker (Work.WilE7.MainDesign.jac T' (blockSndCLM n m (γW 0))))
            = ⟨0, by simp⟩ :=
          hinj (by
            show Work.WilE7.MainDesign.basePrLin n (m + 1)
                (((blockSndCLM n m).comp (fderiv ℝ γW 0)) v)
              = Work.WilE7.MainDesign.basePrLin n (m + 1)
                (0 : Fin (0 + (n + (m + 1))) → ℝ)
            rw [map_zero]; exact hb_base)
        exact congrArg Subtype.val heq
      exact hzero
    have hγW_v : fderiv ℝ γW 0 v = 0 := by
      have hb : blockSndCLM n m ((fderiv ℝ γW 0) v) = 0 := by
        rw [← ContinuousLinearMap.comp_apply]; exact hdb_v
      rw [← pairPtUp_block n m ((fderiv ℝ γW 0) v), hda_v, hb,
        ← pairingCLM_absPt (n := n) (m := m) (0 : Fin (pDim n m) → ℝ)]
      exact map_zero _
    exact hinj_γW (by rw [hγW_v, map_zero])
  have hinj_η : Function.Injective ⇑(fderiv ℝ η 0) := by
    intro a b hab
    have h : a - b = 0 := hker_eta (a - b) (by rw [map_sub, hab, sub_self])
    exact sub_eq_zero.mp h

  -- the T'-sheet uniqueness data and the good set of parameters
  obtain ⟨VT'', hVT''mem, UT'', hUT''mem, hsheetT'⟩ :=
    persist_aux_sheet_unique T' C s' hcont' hinj' hcov' j' x₀ hx₀
  set G0 : Set (fderiv ℝ (Work.WilE7.DimAPI.eqMap W₀) Z).ker :=
    (VW ∩ {y | blockFirstCLM n m (γW y) ∈ UT} ∩ {y | blockSndCLM n m (γW y) ∈ UT'})
      ∩ {y | projSnd (n + (m + 1)) (n + (m + 1)) (Work.WilE7.MainDesign.absPt (γW y)) ∈ VT''}
    with hG0def
  have hnearVT'' : ∀ᶠ y in nhds (0 : (fderiv ℝ (Work.WilE7.DimAPI.eqMap W₀) Z).ker),
      projSnd (n + (m + 1)) (n + (m + 1)) (Work.WilE7.MainDesign.absPt (γW y)) ∈ VT'' := by
    have hcont : ContinuousAt (fun y => projSnd (n + (m + 1)) (n + (m + 1))
        (Work.WilE7.MainDesign.absPt (γW y))) 0 :=
      (projSndCLM (n + (m + 1))).continuous.continuousAt.comp
        (((Work.WilE7.DimAPI.absPtCLM (pPair n m)).continuous.continuousAt).comp
          (hγWan.continuousAt))
    have hmem : VT'' ∈ nhds (projSnd (n + (m + 1)) (n + (m + 1))
        (Work.WilE7.MainDesign.absPt (γW 0))) := by
      rw [hγW0, hZ, ← absPt_blockSndCLM (n := n) (m := m), hbZ]
      exact hVT''mem
    exact hcont.tendsto.eventually hmem
  have hG0mem : G0 ∈ nhds (0 : (fderiv ℝ (Work.WilE7.DimAPI.eqMap W₀) Z).ker) := by
    simp only [hG0def]
    exact Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hVWmem hnearT) hnearT') hnearVT''
  have hdim_eq : Module.finrank ℝ
        ↥(fderiv ℝ (Work.WilE7.DimAPI.eqMap W₀) Z).ker
      = Module.finrank ℝ
        ↥(fderiv ℝ (Work.WilE7.DimAPI.eqMap T)
          (absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀)))).ker := by
    have h1 : Module.finrank ℝ ↥(fderiv ℝ (Work.WilE7.DimAPI.eqMap W₀) Z).ker
        = pPair n m - W₀.j :=
      Work.WilE7.DimAPI.finrank_ker_fderiv_eqMap W₀ hW₀good (by rw [hZ]; exact hW₀pp)
    have h2 : Module.finrank ℝ ↥(fderiv ℝ (Work.WilE7.DimAPI.eqMap T)
          (absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀)))).ker
        = n + (m + 1) - T.j := Work.WilE7.DimAPI.finrank_ker_fderiv_eqMap T hT hpzT
    have h3 : Module.finrank ℝ ↥(fderiv ℝ (Work.WilE7.DimAPI.eqMap W₀) Z).ker
        ≤ Module.finrank ℝ ↥(fderiv ℝ (Work.WilE7.DimAPI.eqMap T)
          (absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀)))).ker :=
      LinearMap.finrank_le_finrank_of_injective
        (f := ((fderiv ℝ η 0) : (fderiv ℝ (Work.WilE7.DimAPI.eqMap W₀) Z).ker →ₗ[ℝ]
          (fderiv ℝ (Work.WilE7.DimAPI.eqMap T)
            (absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀)))).ker)) hinj_η
    omega
  have hsurj_η : Function.Surjective (fderiv ℝ η 0) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim_eq
      (f := ((fderiv ℝ η 0) : (fderiv ℝ (Work.WilE7.DimAPI.eqMap W₀) Z).ker →ₗ[ℝ]
        (fderiv ℝ (Work.WilE7.DimAPI.eqMap T)
          (absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀)))).ker))).mp hinj_η
  have hopen : η '' G0 ∈ nhds (0 : (fderiv ℝ (Work.WilE7.DimAPI.eqMap T)
      (absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀)))).ker) := by
    rw [← hη0]
    rw [← hηan.hasStrictFDerivAt.map_nhds_eq_of_surj
      (LinearMap.range_eq_top.mpr hsurj_η)]
    exact Filter.mem_map.mpr (Filter.mem_of_superset hG0mem (fun y hy => ⟨y, hy, rfl⟩))
  have hsheetcont : ContinuousOn (fun x => absPtUp (n := n) (m := m)
      (Fin.append x (s j x))) C := by
    have h1 : ContinuousOn (fun x : Fin n → ℝ => Fin.append x (s j x)) C :=
      (Fin.continuous_append (X := ℝ) n (m + 1)).comp_continuousOn
        (continuous_id.continuousOn.prodMk (hcont j))
    exact (absPtInvCLM (n + (m + 1))).continuous.comp_continuousOn h1
  have hxc1 : ∀ᶠ x in nhdsWithin x₀ C,
      absPtUp (n := n) (m := m) (Fin.append x (s j x)) ∈ UT := by
    have h1 : Filter.Tendsto (fun x => absPtUp (n := n) (m := m) (Fin.append x (s j x)))
        (nhdsWithin x₀ C) (nhds (absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀)))) :=
      hsheetcont.continuousWithinAt hx₀
    exact h1.eventually (hUTopen.mem_nhds hpzUT)
  have hxc2 : ∀ᶠ x in nhdsWithin x₀ C, x ∈ UT'' := nhdsWithin_le_nhds hUT''mem
  have hxc3 : ∀ᶠ x in nhdsWithin x₀ C,
      χT (absPtUp (n := n) (m := m) (Fin.append x (s j x))) ∈ η '' G0 := by
    have h1 : Filter.Tendsto (fun x => absPtUp (n := n) (m := m) (Fin.append x (s j x)))
        (nhdsWithin x₀ C) (nhds (absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀)))) :=
      hsheetcont.continuousWithinAt hx₀
    have htend : Filter.Tendsto (fun x => χT (absPtUp (n := n) (m := m)
        (Fin.append x (s j x)))) (nhdsWithin x₀ C)
        (nhds (χT (absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀))))) :=
      hχTan.continuousAt.tendsto.comp h1
    rw [hχT0] at htend
    exact htend.eventually hopen
  have hmain : ∀ᶠ x in nhdsWithin x₀ C, (s j x) (Fin.last m) = (s' j' x) (Fin.last m) := by
    filter_upwards [self_mem_nhdsWithin, hxc1, hxc2, hxc3] with x hxC hxUT hxU'' hxGG
    obtain ⟨y, hyG, hyeq⟩ := hxGG
    rw [hG0def] at hyG
    obtain ⟨⟨⟨hyVW, hyT⟩, hyT'⟩, hyVT''⟩ := hyG
    have hχTinv : γT (χT (absPtUp (n := n) (m := m) (Fin.append x (s j x))))
        = absPtUp (n := n) (m := m) (Fin.append x (s j x)) :=
      (hχTin _ hxUT (Work.WilE7.DimAPI.eqMap_eq_zero_of_good T hT (hsub j x hxC))).2
    have hγTη : γT (η y) = blockFirstCLM n m (γW y) :=
      (hχTin (blockFirstCLM n m (γW y)) hyT
        (Work.WilE7.DimAPI.eqMap_eq_zero_of_good T hT (hblockT y hyVW))).2
    have hγT'η : γT' (η' y) = blockSndCLM n m (γW y) :=
      (hχT'in (blockSndCLM n m (γW y)) hyT' (heqmapT' y hyVW)).2
    have hT'block : Work.WilE7.MainDesign.absPt (γT' (η' y))
        = projSnd (n + (m + 1)) (n + (m + 1)) (Work.WilE7.MainDesign.absPt (γW y)) := by
      rw [hγT'η, absPt_blockSndCLM]
    have hT'block_mem : Work.WilE7.MainDesign.absPt (γT' (η' y))
        ∈ Work.WilE7.MainDesign.absSet T' := by
      rw [hT'block]
      exact (mem_absLevelPairSet_elim T T' (helim y hyVW)).2.1
    have hbaseT' : projFirst n (m + 1) (Work.WilE7.MainDesign.absPt (γT' (η' y))) = x := by
      have hb := (mem_absLevelPairSet_elim T T' (helim y hyVW)).2.2.1
      rw [hT'block, ← hb, ← absPt_blockFirstCLM (n := n) (m := m),
        ← hγTη, hyeq, hχTinv]
      rw [absPtUp_eq_absPtInv, Work.WilE7.DimAPI.absPt_absPtInv]
      exact funext fun i => Fin.append_left _ _ i
    have hsheetT'id : Work.WilE7.MainDesign.absPt (γT' (η' y))
        = Fin.append x (s' j' x) :=
      hsheetT' x ⟨hxC, hxU''⟩ _ hT'block_mem hbaseT'
        (by rw [hT'block]; exact hyVT'')
    have hbranchId : γT' (η' y) = absPtUp (n := n) (m := m) (Fin.append x (s' j' x)) := by
      refine Work.WilE7.DimAPI.absPt_injective (n + (m + 1)) ?_
      rw [hsheetT'id, absPtUp_eq_absPtInv, Work.WilE7.DimAPI.absPt_absPtInv]
    calc (s j x) (Fin.last m)
        = levelOf n m (absPtUp (n := n) (m := m) (Fin.append x (s j x))) :=
          (levelOf_absPtUp_append x (s j x)).symm
      _ = levelOf n m (γT (χT (absPtUp (n := n) (m := m) (Fin.append x (s j x))))) := by
          rw [hχTinv]
      _ = levelOf n m (γT (η y)) := by rw [← hyeq]
      _ = levelOf n m (blockFirstCLM n m (γW y)) := by rw [hγTη]
      _ = levelOf n m (blockSndCLM n m (γW y)) := hlevblock y hyVW
      _ = levelOf n m (γT' (η' y)) := by rw [hγT'η]
      _ = (s' j' x) (Fin.last m) := by rw [hbranchId, levelOf_absPtUp_append]
  refine ⟨_, eventually_nhdsWithin_iff.mp hmain, fun x hx => hx.2 hx.1⟩


end Work.CoreStep
