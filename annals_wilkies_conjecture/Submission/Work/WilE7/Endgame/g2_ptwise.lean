/-
  G2 (`isOpen_projTopSet_inter_cyl_of_pairAvoid`): the pointwise step.

  Given `z₀ ∈ cyl C ∩ projTopSet T` with a `T`-witness `t₀` over it, we produce a neighbourhood
  `U ∈ nhds z₀` with `U ∩ cyl C ⊆ projTopSet T`.  The whole argument is carried out with
  `x₀ = b t₀` and `v₀ = verT t₀` as parameters (so that at the very end `z₀` is recovered as
  `Fin.snoc (Fin.init z₀) (z₀ (Fin.last n))`).

  Design: NOTES_G2_isOpen_projTopSet.md.  The single use of `hWlow` is at the pair point `w₀`.
-/
import Mathlib
import Submission.Work.WilE7.CoreStep.CoreLTSuccNodes
import Submission.Work.WilE7.Endgame.g2_pair_helpers
import Submission.Work.WilE7.Endgame.g2_ball_coverage
import Submission.Work.WilE7.Endgame.g2_injOn_of_kjac_inj
import Submission.Work.WilE7.Endgame.g2_kjac_persist
import Submission.Work.WilE7.Endgame.g2_vertical_radius
import Submission.Work.WilE7.Endgame.deriv_eq_zero_of_vanish_on_good
import Submission.Work.WilE7.Endgame.g2_defs
import Submission.Work.WilE7.Endgame.g2_av_surj
import Submission.Work.WilE7.Endgame.g2_sheet_mem_nhds
import Submission.Work.WilE7.Endgame.g2_block_nhds
import Submission.Work.WilE7.DimAPI.exists_coordProj_surj_of_le_finrank
import Submission.Work.WilE7.DimAPI.jac_range_eq_top_of_good
import Submission.Work.WilE7.CoreStep.basePrLin_injective_on_ker_jac
import Submission.Work.WilE7.exists_ker_equiv

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

namespace Work.WilE7.Endgame

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreLTSuccPlan
open Work.WilE7.CoreStep

theorem g2_ptwise {n m k : ℕ}
    (T R : Stratum 0 (n + (m + 1))) (hT : T.Good) (hR : R.Good) (himm : HImm T)
    (hvert : ∀ z ∈ T.X.set, projRank T z + 1 = n + (m + 1) - T.j)
    (hrankR : ∀ z ∈ R.X.set, projRank R z = n + (m + 1) - R.j)
    (hdimR : n + (m + 1) - R.j + 1 = n + (m + 1) - T.j)
    (C : Set (Fin n → ℝ)) (hk : 0 < k)
    (r : Fin k → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hrcont : ∀ j, ContinuousOn (r j) C)
    (hrsub : ∀ (j : Fin k) (x : Fin n → ℝ), x ∈ C →
      absPtUp (n := n) (m := m) (Fin.append x (r j x)) ∈ R.X.set)
    (Wl : List (Stratum 0 (pPair n m)))
    (hWgood : ∀ W ∈ Wl, W.Good)
    (hWsub : ∀ W ∈ Wl, W.X.set ⊆ (absPairSet2 R T).set)
    (hWcov : (absPairSet2 R T).set = ⋃ W ∈ Wl, W.X.set)
    (hWlow : ∀ W ∈ Wl, ∀ w ∈ W.X.set, pairBaseRank W w < n + (m + 1) - R.j →
      Work.CoreStep.pairBase n m w ∉ C)
    (x₀ : Fin n → ℝ) (v₀ : ℝ) (t₀ : Fin (0 + (n + (m + 1))) → ℝ)
    (hx₀C : x₀ ∈ C) (ht₀ : t₀ ∈ T.X.set)
    (hb0 : basePrLin n (m + 1) t₀ = x₀) (hv0 : verT t₀ = v₀) :
    ∃ U ∈ nhds (Fin.snoc x₀ v₀), U ∩ Work.WilE7.cyl C ⊆ projTopSet T := by
  classical
  -- ## (0) the `R`-sheet point `u₀` over `x₀` and the pair point `w₀`
  let j₀ : Fin k := ⟨0, hk⟩
  set u₀ : Fin (pDim n m) → ℝ :=
    absPtUp (n := n) (m := m) (Fin.append x₀ (r j₀ x₀)) with hu₀def
  have hu₀R : u₀ ∈ R.X.set := hrsub j₀ x₀ hx₀C
  have hu₀b : basePrLin n (m + 1) u₀ = x₀ := by
    rw [hu₀def, g2_basePrLin_absPtUp, Work.WilE7.projFirst_append]
  set tp : Fin (pDim n m) → ℝ := absPtUp (n := n) (m := m) (absPt t₀) with htpdef
  have htpeq : tp = t₀ := by
    rw [htpdef]
    exact Work.WilE7.DimAPI.absPtInv_absPt (n + (m + 1)) t₀
  have htpT : tp ∈ T.X.set := by rw [htpeq]; exact ht₀
  have htpb : basePrLin n (m + 1) tp = x₀ := by rw [htpeq, hb0]
  set w₀ : Fin (0 + pPair n m) → ℝ := pairPtUp u₀ tp with hw₀def
  have hw₀mem : w₀ ∈ (absPairSet2 R T).set := by
    rw [hw₀def]
    refine g2_mem_absPairSet2_of R T u₀ tp hu₀R htpT ?_
    intro i
    rw [hu₀b, htpb]
  have hw₀base : Work.CoreStep.pairBase n m w₀ = x₀ := by
    rw [g2_pairBase_eq_pairBaseLin, hw₀def, g2_pairBaseLin_block,
      Work.CoreStep.blockFirst_pairPtUp, hu₀b]
  have hbw : Work.CoreStep.blockFirstCLM n m w₀ = u₀ := by
    rw [hw₀def]
    exact Work.CoreStep.blockFirst_pairPtUp u₀ tp
  have hbsw : Work.CoreStep.blockSndCLM n m w₀ = tp := by
    rw [hw₀def]
    exact Work.CoreStep.blockSnd_pairPtUp u₀ tp
  obtain ⟨W, hWmem, hw₀W⟩ := Set.mem_iUnion₂.mp (by rw [← hWcov]; exact hw₀mem)
  have hWg : W.Good := hWgood W hWmem
  have hWsubW : W.X.set ⊆ (absPairSet2 R T).set := hWsub W hWmem
  have hw₀abs : w₀ ∈ (absPairSet2 R T).set := hWsubW hw₀W
  have hWrank : n + (m + 1) - R.j ≤ pairBaseRank W w₀ := by
    by_contra hlt
    rw [not_le] at hlt
    exact hWlow W hWmem w₀ hw₀W hlt (by rw [hw₀base]; exact hx₀C)
  -- ## (1) tangent containment for the pair stratum `W`
  have hdiag : ∀ ξ ∈ LinearMap.ker (jac W w₀),
      basePrLin n (m + 1) (Work.CoreStep.blockFirstCLM n m ξ)
        = basePrLin n (m + 1) (Work.CoreStep.blockSndCLM n m ξ) := by
    intro ξ hξ
    set L1 : (Fin (0 + pPair n m) → ℝ) →L[ℝ] (Fin n → ℝ) :=
      (basePrLin n (m + 1)).toContinuousLinearMap.comp (Work.CoreStep.blockFirstCLM n m)
      with hL1
    set L2 : (Fin (0 + pPair n m) → ℝ) →L[ℝ] (Fin n → ℝ) :=
      (basePrLin n (m + 1)).toContinuousLinearMap.comp (Work.CoreStep.blockSndCLM n m)
      with hL2
    have hfd : HasFDerivAt (fun y : Fin (0 + pPair n m) → ℝ => L1 y - L2 y) (L1 - L2) w₀ :=
      (ContinuousLinearMap.hasFDerivAt L1).sub (ContinuousLinearMap.hasFDerivAt L2)
    have hf : HasFDerivAt (fun y : Fin (0 + pPair n m) → ℝ => L1 y - L2 y)
        (fderiv ℝ (fun y : Fin (0 + pPair n m) → ℝ => L1 y - L2 y) w₀) w₀ := by
      rw [hfd.fderiv]; exact hfd
    have hvan : ∀ᶠ y in nhds w₀, y ∈ W.X.set →
        (fun y : Fin (0 + pPair n m) → ℝ => L1 y - L2 y) y
          = (fun y : Fin (0 + pPair n m) → ℝ => L1 y - L2 y) w₀ := by
      filter_upwards with y hy
      have h1 : L1 y = L2 y := by
        simp only [hL1, hL2, ContinuousLinearMap.comp_apply,
          LinearMap.coe_toContinuousLinearMap']
        exact funext (g2_mem_absPairSet2_elim R T (hWsubW hy)).1
      have h2 : L1 w₀ = L2 w₀ := by
        simp only [hL1, hL2, ContinuousLinearMap.comp_apply,
          LinearMap.coe_toContinuousLinearMap']
        exact funext (g2_mem_absPairSet2_elim R T hw₀abs).1
      rw [h1, h2, sub_self, sub_self]
    have h0 := deriv_eq_zero_of_vanish_on_good W hWg hw₀W
      (f := fun y : Fin (0 + pPair n m) → ℝ => L1 y - L2 y) hf hvan hξ
    have h1 : (L1 - L2) ξ = 0 := by rw [← hfd.fderiv]; exact h0
    have h2 : L1 ξ = L2 ξ := sub_eq_zero.mp h1
    simpa only [hL1, hL2, ContinuousLinearMap.comp_apply,
      LinearMap.coe_toContinuousLinearMap'] using h2
  have hRker : ∀ ξ ∈ LinearMap.ker (jac W w₀),
      Work.CoreStep.blockFirstCLM n m ξ ∈ LinearMap.ker (jac R u₀) := by
    intro ξ hξ
    have h1 : HasFDerivAt (fun y : Fin (0 + pPair n m) → ℝ => Work.CoreStep.blockFirstCLM n m y)
        (Work.CoreStep.blockFirstCLM n m) w₀ :=
      ContinuousLinearMap.hasFDerivAt (Work.CoreStep.blockFirstCLM n m)
    have h2 : HasFDerivAt
        (fun y : Fin (0 + (n + (m + 1))) → ℝ => Work.WilE7.DimAPI.eqMap R y)
        (fderiv ℝ (fun y : Fin (0 + (n + (m + 1))) → ℝ => Work.WilE7.DimAPI.eqMap R y)
          (Work.CoreStep.blockFirstCLM n m w₀)) (Work.CoreStep.blockFirstCLM n m w₀) :=
      (Work.WilE7.DimAPI.analyticAt_eqMap R (Work.CoreStep.blockFirstCLM n m w₀)).hasStrictFDerivAt.hasFDerivAt
    have hcomp := h2.comp w₀ h1
    have hchain : fderiv ℝ (fun y : Fin (0 + pPair n m) → ℝ =>
          Work.WilE7.DimAPI.eqMap R (Work.CoreStep.blockFirstCLM n m y)) w₀
        = (fderiv ℝ (fun y : Fin (0 + (n + (m + 1))) → ℝ => Work.WilE7.DimAPI.eqMap R y)
            ((Work.CoreStep.blockFirstCLM n m) w₀)).comp (Work.CoreStep.blockFirstCLM n m) := by
      have hfun : (fun y : Fin (0 + pPair n m) → ℝ =>
            Work.WilE7.DimAPI.eqMap R (Work.CoreStep.blockFirstCLM n m y))
          = (fun y : Fin (0 + (n + (m + 1))) → ℝ => Work.WilE7.DimAPI.eqMap R y)
              ∘ (Work.CoreStep.blockFirstCLM n m) := rfl
      rw [hfun]
      rw [fderiv_comp w₀ h2.differentiableAt h1.differentiableAt, h1.fderiv]
    have hf : HasFDerivAt (fun y : Fin (0 + pPair n m) → ℝ =>
          Work.WilE7.DimAPI.eqMap R (Work.CoreStep.blockFirstCLM n m y))
        (fderiv ℝ (fun y : Fin (0 + pPair n m) → ℝ =>
          Work.WilE7.DimAPI.eqMap R (Work.CoreStep.blockFirstCLM n m y)) w₀) w₀ := by
      rw [hchain]
      exact hcomp
    have hvan : ∀ᶠ y in nhds w₀, y ∈ W.X.set →
        (fun y : Fin (0 + pPair n m) → ℝ =>
          Work.WilE7.DimAPI.eqMap R (Work.CoreStep.blockFirstCLM n m y)) y
        = (fun y : Fin (0 + pPair n m) → ℝ =>
          Work.WilE7.DimAPI.eqMap R (Work.CoreStep.blockFirstCLM n m y)) w₀ := by
      filter_upwards with y hy
      have hy1 := (g2_mem_absPairSet2_elim R T (hWsubW hy)).2.1
      have hy0 := (g2_mem_absPairSet2_elim R T hw₀abs).2.1
      rw [Work.WilE7.DimAPI.eqMap_eq_zero_of_good R hR hy1,
        Work.WilE7.DimAPI.eqMap_eq_zero_of_good R hR hy0]
    have h0 := deriv_eq_zero_of_vanish_on_good W hWg hw₀W
      (f := fun y : Fin (0 + pPair n m) → ℝ =>
        Work.WilE7.DimAPI.eqMap R (Work.CoreStep.blockFirstCLM n m y)) hf hvan hξ
    rw [hchain] at h0
    have h0' : fderiv ℝ (fun y : Fin (0 + (n + (m + 1))) → ℝ => Work.WilE7.DimAPI.eqMap R y)
        ((Work.CoreStep.blockFirstCLM n m) w₀) ((Work.CoreStep.blockFirstCLM n m) ξ) = 0 := by
      simpa only [ContinuousLinearMap.comp_apply] using h0
    have hjack : (jac R u₀ : (Fin (0 + (n + (m + 1))) → ℝ) →ₗ[ℝ] (Fin R.j → ℝ))
        = (((fderiv ℝ (fun y : Fin (0 + (n + (m + 1))) → ℝ => Work.WilE7.DimAPI.eqMap R y))
            ((Work.CoreStep.blockFirstCLM n m) w₀)) :
          (Fin (0 + (n + (m + 1))) → ℝ) →ₗ[ℝ] (Fin R.j → ℝ)) := by
      rw [hbw]
      exact Work.WilE7.DimAPI.jac_eq_fderiv R u₀
    rw [hjack]
    exact h0'
  have hTker : ∀ ξ ∈ LinearMap.ker (jac W w₀),
      Work.CoreStep.blockSndCLM n m ξ ∈ LinearMap.ker (jac T t₀) := by
    intro ξ hξ
    have h1 : HasFDerivAt (fun y : Fin (0 + pPair n m) → ℝ => Work.CoreStep.blockSndCLM n m y)
        (Work.CoreStep.blockSndCLM n m) w₀ :=
      ContinuousLinearMap.hasFDerivAt (Work.CoreStep.blockSndCLM n m)
    have h2 : HasFDerivAt
        (fun y : Fin (0 + (n + (m + 1))) → ℝ => Work.WilE7.DimAPI.eqMap T y)
        (fderiv ℝ (fun y : Fin (0 + (n + (m + 1))) → ℝ => Work.WilE7.DimAPI.eqMap T y)
          (Work.CoreStep.blockSndCLM n m w₀)) (Work.CoreStep.blockSndCLM n m w₀) :=
      (Work.WilE7.DimAPI.analyticAt_eqMap T (Work.CoreStep.blockSndCLM n m w₀)).hasStrictFDerivAt.hasFDerivAt
    have hcomp := h2.comp w₀ h1
    have hchain : fderiv ℝ (fun y : Fin (0 + pPair n m) → ℝ =>
          Work.WilE7.DimAPI.eqMap T (Work.CoreStep.blockSndCLM n m y)) w₀
        = (fderiv ℝ (fun y : Fin (0 + (n + (m + 1))) → ℝ => Work.WilE7.DimAPI.eqMap T y)
            ((Work.CoreStep.blockSndCLM n m) w₀)).comp (Work.CoreStep.blockSndCLM n m) := by
      have hfun : (fun y : Fin (0 + pPair n m) → ℝ =>
            Work.WilE7.DimAPI.eqMap T (Work.CoreStep.blockSndCLM n m y))
          = (fun y : Fin (0 + (n + (m + 1))) → ℝ => Work.WilE7.DimAPI.eqMap T y)
              ∘ (Work.CoreStep.blockSndCLM n m) := rfl
      rw [hfun]
      rw [fderiv_comp w₀ h2.differentiableAt h1.differentiableAt, h1.fderiv]
    have hf : HasFDerivAt (fun y : Fin (0 + pPair n m) → ℝ =>
          Work.WilE7.DimAPI.eqMap T (Work.CoreStep.blockSndCLM n m y))
        (fderiv ℝ (fun y : Fin (0 + pPair n m) → ℝ =>
          Work.WilE7.DimAPI.eqMap T (Work.CoreStep.blockSndCLM n m y)) w₀) w₀ := by
      rw [hchain]
      exact hcomp
    have hvan : ∀ᶠ y in nhds w₀, y ∈ W.X.set →
        (fun y : Fin (0 + pPair n m) → ℝ =>
          Work.WilE7.DimAPI.eqMap T (Work.CoreStep.blockSndCLM n m y)) y
        = (fun y : Fin (0 + pPair n m) → ℝ =>
          Work.WilE7.DimAPI.eqMap T (Work.CoreStep.blockSndCLM n m y)) w₀ := by
      filter_upwards with y hy
      have hy1 := (g2_mem_absPairSet2_elim R T (hWsubW hy)).2.2
      have hy0 := (g2_mem_absPairSet2_elim R T hw₀abs).2.2
      rw [Work.WilE7.DimAPI.eqMap_eq_zero_of_good T hT hy1,
        Work.WilE7.DimAPI.eqMap_eq_zero_of_good T hT hy0]
    have h0 := deriv_eq_zero_of_vanish_on_good W hWg hw₀W
      (f := fun y : Fin (0 + pPair n m) → ℝ =>
        Work.WilE7.DimAPI.eqMap T (Work.CoreStep.blockSndCLM n m y)) hf hvan hξ
    rw [hchain] at h0
    have h0' : fderiv ℝ (fun y : Fin (0 + (n + (m + 1))) → ℝ => Work.WilE7.DimAPI.eqMap T y)
        ((Work.CoreStep.blockSndCLM n m) w₀) ((Work.CoreStep.blockSndCLM n m) ξ) = 0 := by
      simpa only [ContinuousLinearMap.comp_apply] using h0
    have hjack : (jac T t₀ : (Fin (0 + (n + (m + 1))) → ℝ) →ₗ[ℝ] (Fin T.j → ℝ))
        = (((fderiv ℝ (fun y : Fin (0 + (n + (m + 1))) → ℝ => Work.WilE7.DimAPI.eqMap T y))
            ((Work.CoreStep.blockSndCLM n m) w₀)) :
          (Fin (0 + (n + (m + 1))) → ℝ) →ₗ[ℝ] (Fin T.j → ℝ)) := by
      rw [hbsw, htpeq]
      exact Work.WilE7.DimAPI.jac_eq_fderiv T t₀
    rw [hjack]
    exact h0'
  -- ## (2) the two base images agree
  set UR : Submodule ℝ (Fin n → ℝ) :=
    (LinearMap.ker (jac R u₀)).map (basePrLin n (m + 1)) with hURdef
  set UT : Submodule ℝ (Fin n → ℝ) :=
    (LinearMap.ker (jac T t₀)).map (basePrLin n (m + 1)) with hUTdef
  have hURfin : Module.finrank ℝ UR = n + (m + 1) - R.j := hrankR u₀ hu₀R
  have hUTfin : Module.finrank ℝ UT = n + (m + 1) - R.j := by
    have h := hvert t₀ ht₀
    have h' : projRank T t₀ = n + (m + 1) - T.j - 1 := by omega
    rw [hUTdef]
    exact h'.trans (by omega)
  have hmapW : (LinearMap.ker (jac W w₀)).map (pairBaseLin n m) = UR := by
    refine Submodule.eq_of_le_of_finrank_le ?_ ?_
    · rintro y ⟨ξ, hξ, rfl⟩
      rw [g2_pairBaseLin_block]
      exact Submodule.mem_map.mpr
        ⟨Work.CoreStep.blockFirstCLM n m ξ, hRker ξ hξ, rfl⟩
    · rw [hURfin]
      exact hWrank
  have hURUT : UR = UT := by
    refine Submodule.eq_of_le_of_finrank_le ?_ ?_
    · rintro y hy
      rw [← hmapW] at hy
      obtain ⟨ξ, hξ, rfl⟩ := Submodule.mem_map.mp hy
      rw [g2_pairBaseLin_block, hdiag ξ hξ]
      exact Submodule.mem_map.mpr
        ⟨Work.CoreStep.blockSndCLM n m ξ, hTker ξ hξ, rfl⟩
    · rw [hURfin, hUTfin]
  -- ## (3) a coordinate projection whose `e`-coordinates are injective on `UR`
  set K : ℕ := n + (m + 1) - T.j - 1 with hKdef
  have hKsucc : K + 1 = n + (m + 1) - T.j := by rw [hKdef]; omega
  have hKR : n + (m + 1) - R.j = K := by rw [hKdef]; omega
  have hURfinK : Module.finrank ℝ UR = K := hURfin.trans hKR
  obtain ⟨e, he⟩ := Work.WilE7.DimAPI.exists_coordProj_surj_submodule UR K (le_of_eq hURfinK.symm)
  have heinj : ∀ w ∈ UR, (∀ i, w (e i) = 0) → w = 0 := by
    intro w hw h0
    have hsurjφ : Function.Surjective ((πLin e).comp UR.subtype) := he
    have hk := LinearMap.finrank_range_add_finrank_ker ((πLin e).comp UR.subtype)
    rw [LinearMap.range_eq_top.mpr hsurjφ, Submodule.topEquiv.finrank_eq,
      Module.finrank_fin_fun, hURfinK] at hk
    have hker : Module.finrank ℝ ↥(((πLin e).comp UR.subtype).ker) = 0 := by omega
    have hmem : (⟨w, hw⟩ : ↥UR) ∈ ((πLin e).comp UR.subtype).ker := by
      rw [LinearMap.mem_ker]
      funext i
      show (πLin e) w i = 0
      rw [πLin_apply]
      exact h0 i
    have hbot : ((πLin e).comp UR.subtype).ker = ⊥ := Submodule.finrank_eq_zero.mp hker
    have hinj : Function.Injective ((πLin e).comp UR.subtype) := LinearMap.ker_eq_bot.mp hbot
    have hz : (⟨w, hw⟩ : ↥UR) = 0 := by
      refine hinj ?_
      simpa using hmem
    simpa using congrArg Subtype.val hz
  -- ## (4) the `R`-side: the base point is determined by its `e`-coordinates
  have hinjR : ∀ ξ ∈ LinearMap.ker (jac R u₀),
      AeLin (n := n) (m := m) (K := K) e ξ = 0 → ξ = 0 := by
    intro ξ hξ h0
    have hb : basePrLin n (m + 1) ξ = 0 := by
      refine heinj (basePrLin n (m + 1) ξ)
        (Submodule.mem_map.mpr ⟨ξ, hξ, rfl⟩) (fun i => ?_)
      have h1 := congrFun h0 i
      rwa [AeLin_apply] at h1
    have hinj := Work.WilE7.CoreStep.basePrLin_injective_on_ker_jac R hR u₀ hu₀R
      (hrankR u₀ hu₀R)
    have h1 : (⟨ξ, hξ⟩ : ↥(LinearMap.ker (jac R u₀))) = ⟨0, by simp⟩ := by
      refine hinj ?_
      simpa using hb
    simpa using congrArg Subtype.val h1
  obtain ⟨O_R, hO_R, hO_Rinj⟩ := g2_injOn_of_kjac_inj R hR
    (AeLin (n := n) (m := m) (K := K) e) u₀ hu₀R (by omega) hinjR
  -- ## (5) the `T`-side: the vertical coordinate is free
  have hAeT : (LinearMap.ker (jac T t₀)).map (AeLin (n := n) (m := m) (K := K) e) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    obtain ⟨w, hw⟩ := he y
    have hwUT : (w : Fin n → ℝ) ∈ UT := by
      rw [← hURUT]; exact w.2
    obtain ⟨ξ, hξ, hξw⟩ := Submodule.mem_map.mp hwUT
    refine Submodule.mem_map.mpr ⟨ξ, hξ, ?_⟩
    have hw' : (fun i : Fin K => (w : Fin n → ℝ) (e i)) = y := by
      rw [← πLin_apply e (w : Fin n → ℝ)]
      exact hw
    rw [AeLin_apply, hξw]
    exact hw'
  have hpers := g2_kjac_persist T hT (AeLin (n := n) (m := m) (K := K) e) t₀ ht₀ hAeT
  obtain ⟨O_v, hO_v, ε, hε, hεsub⟩ := g2_vertical_radius T hT himm hvert e t₀ ht₀ hpers
  -- ## (6) the ball coverings for the pair stratum and for `T`
  have hWA : (LinearMap.ker (jac W w₀)).map ((πLin e).comp (pairBaseLin n m)) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    obtain ⟨w, hw⟩ := he y
    have hwUR : (w : Fin n → ℝ) ∈ UR := w.2
    have hwUR' : (w : Fin n → ℝ) ∈ (LinearMap.ker (jac W w₀)).map (pairBaseLin n m) := by
      rw [hmapW]; exact hwUR
    obtain ⟨ξ, hξ, hξw⟩ := Submodule.mem_map.mp hwUR'
    refine Submodule.mem_map.mpr ⟨ξ, hξ, ?_⟩
    have hw' : (fun i : Fin K => (w : Fin n → ℝ) (e i)) = y := by
      rw [← πLin_apply e (w : Fin n → ℝ)]
      exact hw
    rw [LinearMap.comp_apply, πLin_apply, hξw]
    exact hw'
  obtain ⟨U_W, hU_W, hU_Wsub⟩ :=
    g2_block_nhds w₀ O_R O_v
      (show O_R ∈ nhds (Work.CoreStep.blockFirstCLM n m w₀) from by rw [hbw]; exact hO_R)
      (show O_v ∈ nhds (Work.CoreStep.blockSndCLM n m w₀) from by rw [hbsw, htpeq]; exact hO_v)
      (ε := ε / 2) (by linarith)
  obtain ⟨δ_W, hδ_W, hδ_Wball⟩ :=
    g2_ball_coverage W hWg w₀ hw₀W ((πLin e).comp (pairBaseLin n m)) hWA U_W hU_W
  have hAeb : ∀ ξ ∈ LinearMap.ker (jac T t₀),
      (∀ i : Fin K, basePrLin n (m + 1) ξ (e i) = 0) → basePrLin n (m + 1) ξ = 0 := by
    intro ξ hξ h0
    have hmem : basePrLin n (m + 1) ξ ∈ UR := by
      rw [hURUT]
      exact Submodule.mem_map.mpr ⟨ξ, hξ, rfl⟩
    exact heinj _ hmem h0
  have hAvT : (LinearMap.ker (jac T t₀)).map (AvLin (n := n) (m := m) (K := K) e) = ⊤ :=
    g2_av_surj T hT himm K e t₀ ht₀ hKsucc hAeb
  obtain ⟨δ_T, hδ_T, hδ_Tball⟩ :=
    g2_ball_coverage T hT t₀ ht₀ (AvLin (n := n) (m := m) (K := K) e) hAvT O_v hO_v
  obtain ⟨ρ_R, hρ_R, hρ_Rsub⟩ := g2_sheet_mem_nhds C r j₀ (hrcont j₀) x₀ hx₀C O_R hO_R
  -- ## (7) the pointwise conclusion
  set ρx : ℝ := min (min ρ_R (δ_T / 2)) δ_W with hρxdef
  set ρv : ℝ := min (ε / 2) (δ_T / 2) with hρvdef
  have hρx1 : ρx ≤ ρ_R := by
    rw [hρxdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hρx2 : ρx ≤ δ_T / 2 := by
    rw [hρxdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hρx3 : ρx ≤ δ_W := by rw [hρxdef]; exact min_le_right _ _
  have hρv1 : ρv ≤ ε / 2 := by rw [hρvdef]; exact min_le_left _ _
  have hρv2 : ρv ≤ δ_T / 2 := by rw [hρvdef]; exact min_le_right _ _
  refine ⟨Metric.ball (Fin.snoc x₀ v₀) (min ρx ρv), Metric.ball_mem_nhds _ (lt_min ?_ ?_), ?_⟩
  · rw [hρxdef]; exact lt_min (lt_min hρ_R (by linarith)) hδ_W
  · rw [hρvdef]; exact lt_min (by linarith) (by linarith)
  · rintro ζ ⟨hζ, hζcyl⟩
    have hζdist : dist ζ (Fin.snoc x₀ v₀) < min ρx ρv := hζ
    have hxle : dist (Fin.init ζ) x₀ ≤ dist ζ (Fin.snoc x₀ v₀) := by
      simpa using dist_init_le ζ (Fin.snoc x₀ v₀)
    have hvle : dist (ζ (Fin.last n)) v₀ ≤ dist ζ (Fin.snoc x₀ v₀) := by
      simpa using dist_last_le ζ (Fin.snoc x₀ v₀)
    have hkey : ∀ x ∈ C, dist x x₀ < ρx → ∀ v : ℝ, dist v v₀ < ρv →
        Fin.snoc x v ∈ projTopSet T := by
      intro x hxC hxclose v hvclose
      -- the sheet point over `x` lies in `O_R`
      have hsheet_R : absPtUp (n := n) (m := m) (Fin.append x (r j₀ x)) ∈ O_R :=
        hρ_Rsub x hxC (lt_of_lt_of_le hxclose hρx1)
      set ux : Fin (pDim n m) → ℝ :=
        absPtUp (n := n) (m := m) (Fin.append x (r j₀ x)) with huxdef
      have huxR : ux ∈ R.X.set := hrsub j₀ x hxC
      have huxb : basePrLin n (m + 1) ux = x := by
        rw [huxdef, g2_basePrLin_absPtUp, Work.WilE7.projFirst_append]
      have huxO : ux ∈ O_R := hsheet_R
      -- the pair point over `x`
      have hdistx : dist (fun i : Fin K => x (e i)) (fun i : Fin K => x₀ (e i)) < δ_T / 2 :=
        lt_of_le_of_lt (dist_coordProj_le e x x₀)
          (lt_of_lt_of_le hxclose hρx2)
      have hdistxW : dist (fun i : Fin K => x (e i)) (fun i : Fin K => x₀ (e i)) < δ_W :=
        lt_of_le_of_lt (dist_coordProj_le e x x₀) (lt_of_lt_of_le hxclose hρx3)
      have htarget : (fun i : Fin K => x (e i))
          ∈ Metric.ball (((πLin e).comp (pairBaseLin n m)) w₀) δ_W := by
        rw [Metric.mem_ball]
        have h0 : ((πLin e).comp (pairBaseLin n m)) w₀ = fun i => x₀ (e i) := by
          funext i
          rw [LinearMap.comp_apply, πLin_apply]
          have hbase : pairBaseLin n m w₀ = x₀ := by
            rw [← g2_pairBase_eq_pairBaseLin]; exact hw₀base
          exact congrFun hbase (e i)
        rw [h0]
        exact hdistxW
      obtain ⟨wp, hwpWU, hwpval⟩ := hδ_Wball htarget
      obtain ⟨hwpW, hwpU_W⟩ := hwpWU
      obtain ⟨hw1, hw2, hw3⟩ := hU_Wsub wp hwpU_W
      -- the first block is the sheet point, by `R`-side injectivity
      have hwpFst : Work.CoreStep.blockFirstCLM n m wp ∈ R.X.set :=
        (g2_mem_absPairSet2_elim R T (hWsubW hwpW)).2.1
      have heqAe : AeLin (n := n) (m := m) (K := K) e (Work.CoreStep.blockFirstCLM n m wp)
          = AeLin (n := n) (m := m) (K := K) e ux := by
        funext i
        rw [AeLin_apply, AeLin_apply, huxb]
        have h := congrFun hwpval i
        rw [LinearMap.comp_apply, πLin_apply, g2_pairBaseLin_block] at h
        exact h
      have hfirst : Work.CoreStep.blockFirstCLM n m wp = ux :=
        hO_Rinj _ ⟨hwpFst, hw1⟩ _ ⟨huxR, huxO⟩ heqAe
      have hbu : basePrLin n (m + 1) (Work.CoreStep.blockFirstCLM n m wp) = x := by
        rw [hfirst]; exact huxb
      -- the second block is a `T`-point over `x`, near `t₀`
      have hwpSndT : Work.CoreStep.blockSndCLM n m wp ∈ T.X.set :=
        (g2_mem_absPairSet2_elim R T (hWsubW hwpW)).2.2
      have hwpSndb : basePrLin n (m + 1) (Work.CoreStep.blockSndCLM n m wp) = x := by
        have hd := (g2_mem_absPairSet2_elim R T (hWsubW hwpW)).1
        funext i
        rw [← hd i]
        exact congrFun hbu i
      have hwpSndOv : Work.CoreStep.blockSndCLM n m wp ∈ O_v := hw2
      have hwpSndV : |verT (Work.CoreStep.blockSndCLM n m wp) - v₀| < ε / 2 := by
        have h3 := hw3
        rw [show Work.CoreStep.blockSndCLM n m w₀ = t₀ from hbsw.trans htpeq, hv0] at h3
        exact h3
      -- the `T`-ball point with the required coordinates
      have hdistv : dist v v₀ < δ_T / 2 := lt_of_lt_of_le hvclose hρv2
      have hdistvε : dist v v₀ < ε / 2 := lt_of_lt_of_le hvclose hρv1
      have htargetT : Fin.cons v (fun i : Fin K => x (e i))
          ∈ Metric.ball ((AvLin (n := n) (m := m) (K := K) e) t₀) δ_T := by
        rw [Metric.mem_ball]
        have hAt : (AvLin (n := n) (m := m) (K := K) e) t₀
            = Fin.cons v₀ (fun i : Fin K => x₀ (e i)) := by
          rw [AvLin_apply, hv0, hb0]
        rw [hAt]
        refine lt_of_le_of_lt (dist_cons_le_max v v₀ (fun i : Fin K => x (e i))
          (fun i : Fin K => x₀ (e i))) (max_lt ?_ ?_)
        · exact lt_of_lt_of_le hdistv (by linarith)
        · exact lt_of_lt_of_le hdistx (by linarith)
      obtain ⟨t, htTU, htval⟩ := hδ_Tball htargetT
      obtain ⟨htT, htOv⟩ := htTU
      have htV : verT t = v := by
        have h := congrFun htval 0
        rw [AvLin_apply, Fin.cons_zero, Fin.cons_zero] at h
        exact h
      have htE : ∀ i : Fin K, basePrLin n (m + 1) t (e i) = x (e i) := by
        intro i
        have h := congrFun htval i.succ
        rw [AvLin_apply, Fin.cons_succ, Fin.cons_succ] at h
        exact h
      -- the vertical radius lemma
      have hvv : |verT t - verT (Work.CoreStep.blockSndCLM n m wp)| < ε := by
        have hΔ : |v - verT (Work.CoreStep.blockSndCLM n m wp)| < ε := by
          have ht := abs_add_le (v - v₀) (v₀ - verT (Work.CoreStep.blockSndCLM n m wp))
          have he : v - verT (Work.CoreStep.blockSndCLM n m wp)
              = (v - v₀) + (v₀ - verT (Work.CoreStep.blockSndCLM n m wp)) := by ring
          rw [he]
          have h2 : |v₀ - verT (Work.CoreStep.blockSndCLM n m wp)| < ε / 2 := by
            rwa [abs_sub_comm]
          have h1 : |v - v₀| = dist v v₀ := (Real.dist_eq v v₀).symm
          linarith [ht, h1, h2, hdistvε]
        rw [htV]
        exact hΔ
      have hbt : basePrLin n (m + 1) t = x := by
        have heq : ∀ i : Fin K, basePrLin n (m + 1) t (e i)
            = basePrLin n (m + 1) (Work.CoreStep.blockSndCLM n m wp) (e i) := by
          intro i
          rw [htE i, ← congrFun hwpSndb (e i)]
        have h := hεsub (Work.CoreStep.blockSndCLM n m wp) ⟨hwpSndT, hwpSndOv⟩ t
          ⟨htT, htOv⟩ heq hvv
        rw [h]; exact hwpSndb
      refine ⟨absPt t, ⟨t, htT, rfl⟩, ?_⟩
      rw [projTop_absPt_snoc, hbt, htV]
    rw [← snoc_init_self ζ]
    exact hkey (Fin.init ζ) hζcyl.1
      (lt_of_lt_of_le (lt_of_le_of_lt hxle hζdist) (min_le_left _ _)) (ζ (Fin.last n))
      (lt_of_lt_of_le (lt_of_le_of_lt hvle hζdist) (min_le_right _ _))

end Work.WilE7.Endgame
