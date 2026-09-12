import Mathlib
import Submission.Work.Extraction.Constants
import Submission.Work.Extraction.AccountingFix
import Submission.Work.Extraction.StageCount
import Submission.Work.Extraction.LambdaPred
import Submission.Work.Extraction.SupplyBound
import Submission.Work.Extraction.Capacity
import Submission.Work.Dani.Endgame
import Submission.GeometryOfNumbers.FlowLatticeMinima
import Submission.Work.Lattice.FlagInstantiation
import Submission.Work.Lattice.ConePerturbation
import Submission.Work.Lattice.Prop5Assembly
import Submission.Work.Dani.LiftFamily
import Submission.Commons.Analysis.InnerProductSpace.norm_exteriorPower_map_prefix_ge
import Submission.Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod
import Submission.Commons.Analysis.InnerProductSpace.norm_exteriorPower_map_sub_le
import Submission.Commons.Analysis.InnerProductSpace.orthonormalBasis_self_of_finrank
import Submission.Commons.Lattice.SuccessiveMinima.covering_radius
import Submission.Commons.Lattice.SuccessiveMinima.positive
import Submission.Commons.Analysis.Real.sum_prefix_le_mul
import Submission.Commons.LinearAlgebra.ExteriorPower.iMulti_linearIndependent_of_ne_zero
import Submission.Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent
import Submission.GeometryOfNumbers.WedgeBlockZero
import Submission.GeometryOfNumbers.PlaneFinrank

/-!
# The §3 production (de Saxcé, Prop. 5 + Theorem 9)

Module `Submission.Work.Extraction.Production`, namespace `Submission.ProductionAssembly`.
-/

noncomputable section
open Module exteriorPower InnerProductGeometry Real Filter
open scoped BigOperators Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2400000

namespace Submission.ProductionAssembly

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.MaxNorm
open Submission.MaxNormPolygon
open Submission.FlowRateAsymptotic
open Submission.FlowDataMax
open Submission.ImageLattice
open Submission.MaxPhiPolygon
open Submission.MaxPhiFlag
open Submission.MaxPhi
open Submission.MaxRankData
open Submission.AngularRanks
open Submission.ActiveBlock
open Submission.MaxCovol
open Submission.LatticePolygon
open Submission.GraysonLattice
open Submission.AccountingOneSided
open Submission.FlagMemberCriterion
open Submission.CnormDataBdd
open Submission.MaxPhiAccounting
open Submission.JoinSubmodularity
open Submission.FlowLatticeImage
open Submission.Supply
open Submission.SupplyBound
open Submission.Accumulate
open Submission.Capacity
open Submission.StageCount
open Submission.AccountingFix
open Submission.LambdaPred
open Submission.LevelBound
open Submission.FlagInstantiation
open Submission.DaniEndgame
open Submission.Prop5Block
open Submission.Prop5Assembly
open Submission.ConePerturbation
open Submission.ImageLattice
open Submission.PolygonUniformBound
open Submission.Polygon
open Submission.UniformBddBelow
open Submission.Prop42Upper
open Submission.SlopeLambda
open Submission.Production
open Submission.MaxFlagMinima
open Submission.FlowLatticeMinima
open Commons.Lattice.SuccessiveMinima
open Commons.Analysis.InnerProductSpace
open Commons.LinearAlgebra.ExteriorPower
open Submission.LiftFamily
open Submission.WedgeBlockZero
open Submission.WedgeBlocks
open LinearSubspaces

variable {d : ℕ}

/-- `floorSeq` is antitone. -/
lemma floorSeq_antitone (d ℓ : ℕ) : Antitone (floorSeq d ℓ) :=
  antitone_nat_of_succ_le (fun n => floorSeq_succ_le d ℓ n)

/-- `numBlocks` is at most `d`. -/
lemma numBlocks_le (d : ℕ) (c : ℕ → ℝ) : numBlocks d c ≤ d := by
  exact Nat.find_min' _ (blockStart_d_eq_d d c)

/-- The prefix-monotonicity of the `π₊`-mass (L206 in the shape used here). -/
lemma norm_prefix_le {k ℓ : ℕ} (hkl : k ≤ ℓ) (P : RD d →ₗ[ℝ] RD d) (hP : ∀ x, ‖P x‖ ≤ ‖x‖)
    (hidem : ∀ x, P (P x) = P x) (e : Fin ℓ → RD d) (heON : Orthonormal ℝ e) :
    ‖exteriorPower.map ℓ P (exteriorPower.ιMulti ℝ ℓ e)‖ ≤
      ‖exteriorPower.map k P (exteriorPower.ιMulti ℝ k (fun j => e (Fin.castLE hkl j)))‖ := by
  have hcast : (fun j : Fin k => e (Fin.cast (Nat.add_sub_cancel' hkl)
      (Fin.castLE (Nat.le_add_right k (ℓ - k)) j))) =
      (fun j : Fin k => e (Fin.castLE hkl j)) := by
    funext j
    have : Fin.cast (Nat.add_sub_cancel' hkl) (Fin.castLE (Nat.le_add_right k (ℓ - k)) j)
        = Fin.castLE hkl j := Fin.ext rfl
    rw [this]
  have h206 := norm_exteriorPower_map_prefix_ge (E := RD d) P hP hidem
      (k := k) (m := ℓ - k) (u := fun i => e (Fin.cast (Nat.add_sub_cancel' hkl) i))
      (heON.comp (Fin.cast (Nat.add_sub_cancel' hkl)) (Fin.cast_injective _))
  rw [hcast] at h206
  have hlhs : ‖exteriorPower.map (k + (ℓ - k)) P
      (exteriorPower.ιMulti ℝ (k + (ℓ - k)) (fun i => e (Fin.cast (Nat.add_sub_cancel' hkl) i)))‖
      = ‖exteriorPower.map ℓ P (exteriorPower.ιMulti ℝ ℓ e)‖ := by
    rw [exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti]
    exact Accumulate.norm_iMulti_cast (d := d) (k := ℓ) (l := k + (ℓ - k))
      (Nat.add_sub_cancel' hkl).symm (fun i => P (e i))
  rw [hlhs] at h206
  exact h206

/-- The `P`-wedge of a family close to an orthonormal family whose `P`-wedge is large is nonzero. -/
lemma cone_wedge_ne_zero {i : ℕ} (P : RD d →L[ℝ] RD d) (hP1 : ∀ x, ‖P x‖ ≤ ‖x‖)
    (hP2 : ∀ x, P (P x) = P x) {δ c : ℝ} (hδ : 0 ≤ δ) (hc : (1 + δ) ^ i - 1 < c)
    (u : Fin i → RD d) (hu : ∀ k, ‖u k‖ = 1)
    (hbig : c ≤ ‖exteriorPower.map i (P : RD d →ₗ[ℝ] RD d) (exteriorPower.ιMulti ℝ i u)‖)
    (v : Fin i → RD d) (hv : ∀ k, ‖v k - u k‖ ≤ δ) :
    exteriorPower.map i (P : RD d →ₗ[ℝ] RD d) (exteriorPower.ιMulti ℝ i v) ≠ 0 := by
  have hsub := Commons.Analysis.InnerProductSpace.norm_exteriorPower_map_sub_le P hP1 hP2 hδ u v hu hv
  have hpos : 0 < c - ((1 + δ) ^ i - 1) := by linarith
  have hlow : c - ((1 + δ) ^ i - 1) ≤
      ‖exteriorPower.map i (P : RD d →ₗ[ℝ] RD d) (exteriorPower.ιMulti ℝ i v)‖ := by
    linarith [hsub, hbig]
  intro h0
  rw [h0, norm_zero] at hlow
  linarith

/-- **The §3 production.** -/
theorem production {ℓ k : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hk1 : 1 ≤ k) (hkl : k ≤ ℓ)
    (s : RD d ≃ₗᵢ[ℝ] RD d) (T : ℝ) :
    ∃ t : ℝ, T ≤ t ∧ ∃ m : Fin k → RD d, (∀ i, m i ∈ intPoints) ∧ LinearIndependent ℝ m ∧
      Dominates d ℓ k t (cK d ℓ k)
        (exteriorPower.map k (s : RD d →ₗ[ℝ] RD d) (exteriorPower.ιMulti ℝ k m)) ∧
      ‖eFlowK d ℓ k t
        (exteriorPower.map k (s : RD d →ₗ[ℝ] RD d) (exteriorPower.ιMulti ℝ k m))‖
        ≤ C0K d ℓ k (Aconst d) := by
  classical
  have hd0 : 0 < d := lt_of_lt_of_le hℓ0 (le_of_lt hℓd)
  set A : ℝ := Aconst d with hAdef
  have hA0 : 0 ≤ A := le_of_lt (by rw [hAdef]; exact Aconst_pos hd0)
  have hAgt : (d : ℝ) * Real.log 2 / 2 < A := by
    rw [hAdef]; unfold Aconst
    have h1 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have h2 : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd0
    nlinarith
  obtain ⟨t, htT, hdiff, hgood0⟩ := phi_good_time (d := d) hℓ0 hℓd A s (c := 1) one_pos T
  set Λ₀ : Submodule ℤ (RD d) := imageSpan (d := d) (s : RD d ≃ₗ[ℝ] RD d) with hΛ₀
  set Λt : Submodule ℤ (RD d) :=
    imageSpan (d := d) ((s : RD d ≃ₗ[ℝ] RD d).trans (eEquiv (d := d) ℓ t)) with hΛt
  set c : ℕ → ℝ := phiPolygonT (d := d) Λ₀ ℓ A t with hc
  set jb : ℕ → ℕ := blockStart d c with hjb
  set N : ℕ := numBlocks d c with hNdef
  obtain ⟨flagFun, hVle, hVsat, hVdim, hVmono, hVtight, hVcrit⟩ :=
    exists_flag_with_criterion (d := d) hℓ0 hℓd s t A hAgt hdiff
  choose wf uf hwfmem hwfLI hwfAct hwfEff hwfSpan using hVcrit
  have hΛtfin : Module.finrank ℤ Λt = d := by rw [hΛt]; exact finrank_imageSpan (d := d) _
  have hNle : N ≤ d := by rw [hNdef]; exact numBlocks_le d c
  have hNpos : 0 < N := by rw [hNdef]; exact numBlocks_pos c hd0
  have hBdd : ∀ (j : ℕ) (hjd : j ≤ d), BddBelow (maxRankDataSet (d := d) Λt j hjd) := by
    intro j hjd
    by_cases hj1 : 1 ≤ j
    · rw [hΛt]; exact bddBelow_maxRankDataSet_imageSpan (d := d) hℓ0 hℓd hjd hj1 s t
    · have hj0 : j = 0 := by omega
      subst hj0
      exact bddBelow_maxRankDataSet_zero (d := d) Λt (Nat.zero_le d)
  have hV1n : ∀ n, 1 ≤ subDim (flagFun n) := by
    intro n
    have h2 : n.1 ≤ blockStart d c n.1 := blockStart_n_ge d c n.1 (le_trans (le_of_lt n.2.2) hNle)
    rw [hVdim n]
    exact le_trans n.2.1 h2
  have hV0n : ∀ n, flagFun n ≠ ⊥ := by
    intro n hbot
    have h1 : subDim (flagFun n) = 0 := by
      rw [hbot]
      exact (subDim_eq_zero_iff_bot (⊥ : Submodule ℤ (RD d))).mpr rfl
    have h2 := hV1n n
    omega
  have hJn : ∀ n, subDim (flagFun n) - uf n ≤ ℓ := fun n =>
    supplyCount_le (d := d) hℓ0 hℓd t (hV1n n) (hwfLI n) (hwfAct n) (hwfSpan n)
  -- the capacity sequence
  let sCnt : ℕ → ℕ := fun i =>
    if h : 1 ≤ i ∧ i < N then subDim (flagFun ⟨i, h.1, h.2⟩) - uf ⟨i, h.1, h.2⟩ else 0
  have hsCnt0 : sCnt 0 = 0 := by
    simp only [sCnt]
    rw [dif_neg]
    rintro ⟨h1, -⟩
    omega
  have hsCntle : ∀ i, sCnt i ≤ ℓ := by
    intro i
    simp only [sCnt]
    split_ifs with h
    · exact hJn _
    · exact Nat.zero_le _
  set ω : ℕ → ℕ := fun u => max ((Finset.range (u+1)).sup sCnt) (if N ≤ u then ℓ else 0) with hωdef
  have hω0 : ω 0 = 0 := by
    rw [hωdef]
    show max ((Finset.range (0+1)).sup sCnt) (if N ≤ 0 then ℓ else 0) = 0
    have h : ¬ (N ≤ 0) := by omega
    rw [if_neg h, max_eq_left (Nat.zero_le _)]
    simpa using hsCnt0
  have hωmono : Monotone ω := by
    intro a b hab
    rw [hωdef]
    refine max_le_max ?_ ?_
    · exact Finset.sup_mono (Finset.range_subset_range.mpr (Nat.succ_le_succ hab))
    · split_ifs with h1 h2
      · exact le_rfl
      · exact absurd (le_trans h1 hab) h2
      · exact Nat.zero_le _
      · exact le_rfl
  have hωN : ω N = ℓ := by
    rw [hωdef]
    show max ((Finset.range (N+1)).sup sCnt) (if N ≤ N then ℓ else 0) = ℓ
    rw [if_pos le_rfl, max_eq_right (Finset.sup_le (fun i _ => hsCntle i))]
  have hωle : ∀ u, ω u ≤ ℓ := by
    intro u
    rw [hωdef]
    refine max_le (Finset.sup_le (fun i _ => hsCntle i)) ?_
    split_ifs
    · exact le_rfl
    · exact Nat.zero_le _
  have hωge : ∀ u, N ≤ u → ω u = ℓ := by
    intro u hu
    rw [hωdef]
    show max ((Finset.range (u+1)).sup sCnt) (if N ≤ u then ℓ else 0) = ℓ
    rw [if_pos hu, max_eq_right (Finset.sup_le (fun i _ => hsCntle i))]
  have hωsucc : ∀ u, 1 ≤ u → u < N → ω u = max (ω (u-1)) (sCnt u) := by
    intro u hu1 huN
    have hnotu : ¬ (N ≤ u) := by omega
    have hnotu1 : ¬ (N ≤ u - 1) := by omega
    rw [hωdef]
    show max ((Finset.range (u+1)).sup sCnt) (if N ≤ u then ℓ else 0)
      = max (max ((Finset.range ((u-1)+1)).sup sCnt) (if N ≤ (u-1) then ℓ else 0)) (sCnt u)
    have hAu : max ((Finset.range (u+1)).sup sCnt) (if N ≤ u then ℓ else 0)
        = max (sCnt u) ((Finset.range u).sup sCnt) := by
      rw [if_neg hnotu, max_eq_left (Nat.zero_le _), Finset.range_add_one, Finset.sup_insert]
    have hsp : u - 1 + 1 = u := by omega
    have hBu : max ((Finset.range ((u-1)+1)).sup sCnt) (if N ≤ u-1 then ℓ else 0)
        = (Finset.range u).sup sCnt := by
      rw [hsp, if_neg hnotu1, max_eq_left (Nat.zero_le _)]
    rw [hAu, hBu]
    exact (max_comm _ _).symm
  have hωpos : ∀ u, u < N → ω u = (Finset.range (u+1)).sup sCnt := by
    intro u hu
    rw [hωdef]
    show max ((Finset.range (u+1)).sup sCnt) (if N ≤ u then ℓ else 0) = _
    rw [if_neg (by omega), max_eq_left (Nat.zero_le _)]
  -- the member sequence
  set W : ℕ → Submodule ℝ (RD d) := fun u =>
    if h : u < N then (if h1 : 1 ≤ u then realSpan (flagFun ⟨u, h1, h⟩) else ⊥) else ⊤ with hW
  have hW0 : W 0 = ⊥ := by
    rw [hW]
    show (if h : 0 < N then (if h1 : 1 ≤ 0 then realSpan (flagFun ⟨0, h1, h⟩) else ⊥) else ⊤) = ⊥
    rw [dif_pos hNpos, dif_neg (by omega : ¬ (1 ≤ 0))]
  have hWtop : ∀ u, N ≤ u → W u = ⊤ := by
    intro u hu
    rw [hW]
    show (if h : u < N then (if h1 : 1 ≤ u then realSpan (flagFun ⟨u, h1, h⟩) else ⊥) else ⊤) = ⊤
    rw [dif_neg (by omega : ¬ (u < N))]
  have hWmem : ∀ u (h1 : 1 ≤ u) (h2 : u < N), W u = realSpan (flagFun ⟨u, h1, h2⟩) := by
    intro u h1 h2
    rw [hW]
    show (if h : u < N then (if h1' : 1 ≤ u then realSpan (flagFun ⟨u, h1', h⟩) else ⊥) else ⊤)
      = realSpan (flagFun ⟨u, h1, h2⟩)
    rw [dif_pos h2, dif_pos h1]
  have hWmono : ∀ a b, a ≤ b → W a ≤ W b := by
    intro a b hab
    rcases Nat.eq_zero_or_pos a with ha0 | ha0
    · subst ha0
      rw [hW0]; exact bot_le
    have ha1 : 1 ≤ a := ha0
    by_cases haN : a < N
    · rw [hWmem a ha1 haN]
      by_cases hbN : b < N
      · have hb1 : 1 ≤ b := le_trans ha1 hab
        rw [hWmem b hb1 hbN]
        exact Submodule.span_mono (fun x hx =>
          hVmono ⟨a, ha1, haN⟩ ⟨b, hb1, hbN⟩ hab hx)
      · rw [hWtop b (by omega)]
        exact le_top
    · rw [hWtop a (by omega), hWtop b (by omega)]
  have hsupply : ∀ u, 1 ≤ u → ω (u-1) < ω u → ∃ a : Fin (ω u) → RD d, Orthonormal ℝ a ∧
      (∀ i, a i ∈ W u) ∧ cStar d ≤ ‖exteriorPower.map (ω u) (modelProj (d := d) ℓ)
        (exteriorPower.ιMulti ℝ (ω u) a)‖ := by
    intro u hu1 hinc
    rcases lt_or_ge u N with huN | huN
    · have hωu : ω u = sCnt u := by
        have hmax := hωsucc u hu1 huN
        have hle : ω (u - 1) ≤ sCnt u := by
          by_contra hc
          have hc' : sCnt u < ω (u - 1) := lt_of_not_ge hc
          rw [hmax, max_eq_left (le_of_lt hc')] at hinc
          exact absurd hinc (lt_irrefl _)
        rw [hmax, max_eq_right hle]
      have hsCnt_eq : sCnt u = subDim (flagFun ⟨u, hu1, huN⟩) - uf ⟨u, hu1, huN⟩ := by
        simp only [sCnt]; rw [dif_pos ⟨hu1, huN⟩]
      obtain ⟨b, hbON, hbsp, hbmass⟩ :=
        exists_supply (d := d) hℓ0 hℓd t (hV1n ⟨u, hu1, huN⟩) (hwfLI ⟨u, hu1, huN⟩)
          (hwfAct ⟨u, hu1, huN⟩) (hwfSpan ⟨u, hu1, huN⟩)
      have hEq : subDim (flagFun ⟨u, hu1, huN⟩) - uf ⟨u, hu1, huN⟩ = ω u := by
        rw [hωu, hsCnt_eq]
      refine ⟨fun i => b (Fin.cast hEq.symm i), ?_, ?_, ?_⟩
      · exact hbON.comp (Fin.cast hEq.symm) (Fin.cast_injective hEq.symm)
      · intro i
        rw [hWmem u hu1 huN]
        exact hbsp (Submodule.subset_span ⟨Fin.cast hEq.symm i, rfl⟩)
      · have hbeq : blockElem (d := d) (k := subDim (flagFun ⟨u, hu1, huN⟩)
            - uf ⟨u, hu1, huN⟩) (ℓ := ℓ)
            (exteriorPower.ιMulti ℝ (subDim (flagFun ⟨u, hu1, huN⟩) - uf ⟨u, hu1, huN⟩) b) 0
            = exteriorPower.map (subDim (flagFun ⟨u, hu1, huN⟩) - uf ⟨u, hu1, huN⟩)
              (modelProj (d := d) ℓ)
              (exteriorPower.ιMulti ℝ (subDim (flagFun ⟨u, hu1, huN⟩) - uf ⟨u, hu1, huN⟩) b) :=
          WedgeBlockZero.blockElem_zero_eq_map_modelProj ℓ _
        rw [hbeq] at hbmass
        refine le_trans hbmass ?_
        have hre : ‖exteriorPower.map (ω u) (modelProj (d := d) ℓ)
            (exteriorPower.ιMulti ℝ (ω u) (fun i => b (Fin.cast hEq.symm i)))‖ =
            ‖exteriorPower.map (subDim (flagFun ⟨u, hu1, huN⟩) - uf ⟨u, hu1, huN⟩)
              (modelProj (d := d) ℓ)
              (exteriorPower.ιMulti ℝ (subDim (flagFun ⟨u, hu1, huN⟩) - uf ⟨u, hu1, huN⟩) b)‖ := by
          rw [exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti]
          exact Accumulate.norm_iMulti_cast (d := d) (k := subDim (flagFun ⟨u, hu1, huN⟩) - uf ⟨u, hu1, huN⟩)
            (l := ω u) hEq (fun i => modelProj (d := d) ℓ (b i))
        rw [hre]
    · have hωu : ω u = ℓ := hωge u huN
      obtain ⟨b, hbON, hbmem, -⟩ :=
        Commons.Analysis.InnerProductSpace.orthonormalBasis_self_of_finrank (modelX (d := d) ℓ)
          (Submission.PlaneFinrank.finrank_modelX (d := d) ℓ (le_of_lt hℓd))
      refine ⟨fun i => b (Fin.cast hωu i), ?_, ?_, ?_⟩
      · exact hbON.comp (Fin.cast hωu) (Fin.cast_injective hωu)
      · intro i
        rw [hWtop u huN]
        exact Submodule.mem_top
      · have hmass : ‖exteriorPower.map ℓ (modelProj (d := d) ℓ)
            (exteriorPower.ιMulti ℝ ℓ b)‖ = 1 := by
          have h := Prop5Assembly.norm_map_modelProj_iMulti_of_mem hℓ0 b hbON hbmem
          rwa [modelProjCL_coe] at h
        have hre : ‖exteriorPower.map (ω u) (modelProj (d := d) ℓ)
            (exteriorPower.ιMulti ℝ (ω u) (fun i => b (Fin.cast hωu i)))‖ =
            ‖exteriorPower.map ℓ (modelProj (d := d) ℓ) (exteriorPower.ιMulti ℝ ℓ b)‖ := by
          rw [exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti]
          exact Accumulate.norm_iMulti_cast (d := d) (k := ℓ) (l := ω u) hωu.symm
            (fun i => modelProj (d := d) ℓ (b i))
        rw [hre, hmass]
        exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  obtain ⟨e, st, heON, heW, hstmono, hstle, hstprop, hlev⟩ :=
    Accumulate.exists_family_of_capacity (d := d) hℓ0 hℓd hNle ω hω0 hωmono hωN W hWmono hsupply
  -- the extension of the stage function to `ℕ`
  have hℓpos : 0 < ℓ := hℓ0
  have hlast : ℓ - 1 < ℓ := by omega
  have hst1 : ∀ j : Fin ℓ, 1 ≤ st j := by
    intro j
    have h := (hstprop j).2
    have h0 : st j ≠ 0 := by
      rintro hzero
      rw [hzero, hω0] at h
      omega
    omega
  let stN : ℕ → ℕ := fun j => if h : j < ℓ then st ⟨j, h⟩ else st ⟨ℓ - 1, hlast⟩
  have hstN_lt : ∀ j (h : j < ℓ), stN j = st ⟨j, h⟩ := by
    intro j h
    simp only [stN]
    rw [dif_pos h]
  have hstN_ge : ∀ j, ℓ ≤ j → stN j = st ⟨ℓ - 1, hlast⟩ := by
    intro j hj
    simp only [stN]
    rw [dif_neg (by omega)]
  have hstN1 : ∀ j, 1 ≤ stN j := by
    intro j
    rcases lt_or_ge j ℓ with hj | hj
    · rw [hstN_lt j hj]; exact hst1 _
    · rw [hstN_ge j hj]; exact hst1 _
  have hstNle : ∀ j, stN j ≤ N := by
    intro j
    rcases lt_or_ge j ℓ with hj | hj
    · rw [hstN_lt j hj]; exact hstle _
    · rw [hstN_ge j hj]; exact hstle _
  have hstNmono : Monotone stN := by
    intro i j hij
    rcases lt_or_ge i ℓ with hi | hi
    · rcases lt_or_ge j ℓ with hj | hj
      · rw [hstN_lt i hi, hstN_lt j hj]
        exact hstmono hij
      · rw [hstN_lt i hi, hstN_ge j hj]
        exact hstmono (by simp only [Fin.le_iff_val_le_val]; omega)
    · rw [hstN_ge i hi, hstN_ge j (le_trans hi hij)]
  -- the stage and direction of each of the first `k` indices
  let uu : Fin k → ℕ := fun j => st (Fin.castLE hkl j)
  let ek : Fin k → RD d := fun j => e (Fin.castLE hkl j)
  have hekON : Orthonormal ℝ ek := heON.comp (Fin.castLE hkl) (Fin.castLE_injective hkl)
  have hekW : ∀ j, ek j ∈ W (uu j) := fun j => heW (Fin.castLE hkl j)
  have huu1 : ∀ j, 1 ≤ uu j := by
    intro j
    have h := (hstprop (Fin.castLE hkl j)).2
    have h0 : st (Fin.castLE hkl j) ≠ 0 := by
      rintro hzero
      rw [hzero, hω0] at h
      omega
    exact Nat.one_le_iff_ne_zero.mpr h0
  have huu_le : ∀ j, uu j ≤ N := fun j => hstle (Fin.castLE hkl j)
  have hstN_cast : ∀ j : Fin k, stN j.val = uu j := by
    intro j
    have h : j.val < ℓ := lt_of_lt_of_le j.isLt hkl
    rw [hstN_lt j.val h]
    exact congrArg st (Fin.ext rfl)
  -- the levels
  let Mfun : ℕ → ℝ := fun j => DK d ℓ k A *
    successiveMinimum (E := RD d) Λt (jb (stN j))
  let Mj : Fin k → ℝ := fun j => Mfun j.val
  have hMj : ∀ j : Fin k, Mj j = DK d ℓ k A *
      successiveMinimum (E := RD d) Λt (jb (uu j)) := by
    intro j
    simp only [Mj, Mfun]
    rw [hstN_cast j]
  have hjbmono : Monotone jb := fun a b hab => blockStart_mono_le c hab
  have hlam_pos : ∀ q : ℕ, 1 ≤ q → q ≤ N → 0 < successiveMinimum (E := RD d) Λt (jb q) := by
    intro q hq1 hqN
    refine Commons.Lattice.SuccessiveMinima.positive (E := RD d) Λt (jb q) ?_ ?_
    · have h1 : q ≤ jb q := blockStart_n_ge d c q (le_trans hqN hNle)
      exact lt_of_lt_of_le hq1 h1
    · rw [hΛtfin]; exact blockStart_le_d d c q
  have hMpos : ∀ j : Fin k, 0 < Mj j := by
    intro j
    rw [hMj j]
    exact mul_pos (DK_pos d ℓ k A) (hlam_pos (uu j) (huu1 j) (huu_le j))
  have hMfun_mono : Monotone Mfun := by
    intro i j hij
    simp only [Mfun]
    have h1 : jb (stN i) ≤ jb (stN j) := hjbmono (hstNmono hij)
    have h2 : successiveMinimum (E := RD d) Λt (jb (stN i)) ≤
        successiveMinimum (E := RD d) Λt (jb (stN j)) :=
      Submission.SuccessiveMinima.successiveMinimum_mono (E := RD d) Λt h1
        (by rw [hΛtfin]; exact blockStart_le_d d c (stN j))
    exact mul_le_mul_of_nonneg_left h2 (le_of_lt (DK_pos d ℓ k A))
  have hMj_le : ∀ j : Fin k, Mj j ≤ Mfun k := by
    intro j
    exact hMfun_mono (le_of_lt j.isLt)
  have hMj_pos : ∀ j : Fin k, 0 < Mj j := hMpos
  -- consistency with the nominal expression
  have hδpos : 0 < deltaK d ℓ k := deltaK_pos d ℓ k
  have hδ0 : 0 ≤ deltaK d ℓ k := le_of_lt hδpos
  have hDKmul : deltaK d ℓ k * DK d ℓ k A = ((d : ℝ) + 1) * (blkFactorK d A + 1) := by
    rw [DK]
    field_simp [ne_of_gt hδpos]
  have hblk1 : (1 : ℝ) ≤ blkFactorK d A := le_max_left _ _
  -- the per-index lattice points
  have hpt : ∀ j : Fin k, ∃ v : RD d, v ∈ Λt ∧
      ‖v - Mj j • ek j‖ ≤ deltaK d ℓ k * Mj j ∧
      ‖v‖ ≤ (1 + deltaK d ℓ k) * Mj j := by
    intro j
    by_cases hcase : uu j < N
    · have hu1' : 1 ≤ uu j := huu1 j
      set n : {m : ℕ // 1 ≤ m ∧ m < N} := ⟨uu j, hu1', hcase⟩ with hn
      have hVmem : ek j ∈ realSpan (flagFun n) := by
        rw [← hWmem (uu j) hu1' hcase]
        exact hekW j
      have hsub : subDim (flagFun n) = jb (uu j) := hVdim n
      have hlam : 0 < successiveMinimum (E := RD d) Λt (jb (uu j)) :=
        hlam_pos (uu j) hu1' (huu_le j)
      obtain ⟨v, hvmem, hvdiff, hvnorm, -⟩ :=
        Submission.MaxFlagMinima.exists_memberPoint_near_direction Λt (flagFun n) hΛtfin hA0
          (hVle n) (hV0n n) (hVtight n) hBdd hVmem (hekON.norm_eq_one j)
          (M := Mj j) (le_of_lt (hMpos j))
          (ε := successiveMinimum (E := RD d) Λt (jb (uu j))) hlam
      have hkey : (subDim (flagFun n) : ℝ) *
          (Submission.MaxFlagMinima.blockConstMax d A Λt (flagFun n) +
            successiveMinimum (E := RD d) Λt (jb (uu j))) ≤ deltaK d ℓ k * Mj j := by
        have hbc : Submission.MaxFlagMinima.blockConstMax d A Λt (flagFun n) =
            ((2 : ℝ) ^ (2 * d) / unitBallVol (subDim (flagFun n)) *
              Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2) +
                (1 / 2) * Real.log (Nat.choose d (subDim (flagFun n))))) *
              successiveMinimum (E := RD d) Λt (subDim (flagFun n)) := rfl
        have hfac : (2 : ℝ) ^ (2 * d) / unitBallVol (subDim (flagFun n)) *
            Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2) +
              (1 / 2) * Real.log (Nat.choose d (subDim (flagFun n)))) ≤ blkFactorK d A :=
          blockFactor_le_blkFactorK (d := d) (j := subDim (flagFun n)) (A := A)
            (subDim_le_ambient _)
        have hfac' : (2 : ℝ) ^ (2 * d) / unitBallVol (jb (uu j)) *
            Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2) +
              (1 / 2) * Real.log (Nat.choose d (jb (uu j)))) ≤ blkFactorK d A := by
          rw [← hsub]; exact hfac
        have hjj : (jb (uu j) : ℝ) ≤ (d : ℝ) := by
          rw [← hsub]; exact_mod_cast subDim_le_ambient (flagFun n)
        have hε0 : (0 : ℝ) ≤ successiveMinimum (E := RD d) Λt (jb (uu j)) := le_of_lt hlam
        rw [hbc, hsub, hMj j]
        conv_rhs => rw [← mul_assoc, hDKmul]
        rw [show (jb (uu j) : ℝ) *
              ((2 : ℝ) ^ (2 * d) / unitBallVol (jb (uu j)) *
                Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2) +
                  (1 / 2) * Real.log (Nat.choose d (jb (uu j)))) *
                successiveMinimum (E := RD d) Λt (jb (uu j)) +
                successiveMinimum (E := RD d) Λt (jb (uu j))) =
              ((jb (uu j) : ℝ) * successiveMinimum (E := RD d) Λt (jb (uu j))) *
                ((2 : ℝ) ^ (2 * d) / unitBallVol (jb (uu j)) *
                  Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2) +
                    (1 / 2) * Real.log (Nat.choose d (jb (uu j)))) + 1) from by ring]
        calc ((jb (uu j) : ℝ) * successiveMinimum (E := RD d) Λt (jb (uu j))) *
              ((2 : ℝ) ^ (2 * d) / unitBallVol (jb (uu j)) *
                Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2) +
                  (1 / 2) * Real.log (Nat.choose d (jb (uu j)))) + 1)
            ≤ ((jb (uu j) : ℝ) * successiveMinimum (E := RD d) Λt (jb (uu j))) *
                (blkFactorK d A + 1) :=
              mul_le_mul_of_nonneg_left (by linarith [hfac'])
                (mul_nonneg (Nat.cast_nonneg _) hε0)
          _ ≤ ((d : ℝ) * successiveMinimum (E := RD d) Λt (jb (uu j))) *
                (blkFactorK d A + 1) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hjj hε0)
                (by linarith [hblk1])
          _ = (d : ℝ) * (blkFactorK d A + 1) *
                successiveMinimum (E := RD d) Λt (jb (uu j)) := by ring
          _ ≤ ((d : ℝ) + 1) * (blkFactorK d A + 1) *
                successiveMinimum (E := RD d) Λt (jb (uu j)) := by nlinarith [hε0, hblk1]
      refine ⟨v, (hVle n) hvmem, le_trans hvdiff hkey, ?_⟩
      calc ‖v‖ ≤ Mj j + (subDim (flagFun n) : ℝ) *
            (Submission.MaxFlagMinima.blockConstMax d A Λt (flagFun n) +
              successiveMinimum (E := RD d) Λt (jb (uu j))) := hvnorm
        _ ≤ Mj j + deltaK d ℓ k * Mj j := by linarith [hkey]
        _ = (1 + deltaK d ℓ k) * Mj j := by ring
    · have huuN : uu j = N := le_antisymm (huu_le j) (Nat.le_of_not_lt hcase)
      have hjbN : jb (uu j) = d := by
        rw [huuN, hjb, hNdef]
        exact blockStart_numBlocks d c
      have hlam : 0 < successiveMinimum (E := RD d) Λt d :=
        Commons.Lattice.SuccessiveMinima.positive (E := RD d) Λt d hd0 (by rw [hΛtfin])
      obtain ⟨v, hv1, hv2, -⟩ :=
        Commons.Lattice.SuccessiveMinima.exists_latticePoint_near_direction (E := RD d) Λt d
          hΛtfin (ek j) hlam (M := Mj j) (le_of_lt (hMpos j)) (hekON.norm_eq_one j)
      have hkey : (d : ℝ) * (successiveMinimum (E := RD d) Λt d +
            successiveMinimum (E := RD d) Λt d) ≤ deltaK d ℓ k * Mj j := by
        have hε0 : (0 : ℝ) ≤ successiveMinimum (E := RD d) Λt d := le_of_lt hlam
        rw [hMj j, hjbN]
        conv_rhs => rw [← mul_assoc, hDKmul]
        have h2d : (2 : ℝ) * (d : ℝ) ≤ ((d : ℝ) + 1) * (blkFactorK d A + 1) := by
          nlinarith [hblk1]
        nlinarith [hε0, h2d]
      refine ⟨(v : RD d), v.2, le_trans hv1 hkey, ?_⟩
      calc ‖(v : RD d)‖ ≤ Mj j + (d : ℝ) *
            (successiveMinimum (E := RD d) Λt d + successiveMinimum (E := RD d) Λt d) := hv2
        _ ≤ Mj j + deltaK d ℓ k * Mj j := by linarith [hkey]
        _ = (1 + deltaK d ℓ k) * Mj j := by ring
  choose p hp using hpt
  -- the accounting
  have hst_N : ∀ j, j < ℓ → ω (stN j - 1) ≤ j ∧ j < ω (stN j) := by
    intro j hj
    rw [hstN_lt j hj]
    exact hstprop ⟨j, hj⟩
  have hjb0' : jb 0 = 0 := rfl
  have hr0' : phiLevelDeriv (d := d) Λ₀ ℓ A t jb 0 = 0 := by
    simp only [phiLevelDeriv, hjb0', Finset.range_zero, Finset.sum_empty]
  have hacc : (∑ u ∈ Finset.range N, ((ω (u+1) : ℝ) - (ω u : ℝ)) *
      phiSlope (d := d) Λ₀ ℓ A t (jb u)) ≤ (ℓ : ℝ) * ((d : ℝ) - (ℓ : ℝ)) / (d : ℝ) := by
    refine AccountingFix.accounting_at (d := d) hℓ0 hℓd A s hdiff hgood0 (fun u => (ω u : ℝ)) ?_ ?_ ?_
    · rw [hω0]; norm_num
    · rw [hωN]
    · intro u hu
      rcases Nat.eq_zero_or_pos u with h0 | hpos
      · subst h0
        rw [effPos_zero (d := d) (ℓ := ℓ) (jb := fun m => (jb m : ℝ))
          (r := phiLevelDeriv (d := d) Λ₀ ℓ A t jb) (by show ((jb 0 : ℕ) : ℝ) = 0; rw [hjb0']; norm_num)
          (by simpa using hr0'), hω0]
        norm_num
      · rcases eq_or_lt_of_le hu with hEq | hLt
        · subst hEq
          have hjbNd : jb N = d := by rw [hjb, hNdef]; exact blockStart_numBlocks d c
          have hrNd : phiLevelDeriv (d := d) Λ₀ ℓ A t jb N = 0 :=
            phiLevelDeriv_top_eq_zero (d := d) hℓ0 hℓd A s hdiff
          rw [effPos_top (d := d) (ℓ := ℓ) (R := N) (jb := fun m => (jb m : ℝ))
            (r := phiLevelDeriv (d := d) Λ₀ ℓ A t jb) hℓ0 hℓd
            (by show ((jb N : ℕ) : ℝ) = (d : ℝ); rw [hjbNd]) (by simpa using hrNd), hωN]
        · have hmem : sCnt u = subDim (flagFun ⟨u, hpos, hLt⟩) - uf ⟨u, hpos, hLt⟩ := by
            simp only [sCnt]; rw [dif_pos ⟨hpos, hLt⟩]
          have hle1 : (sCnt u : ℝ) ≤ (ω u : ℝ) := by
            have h : sCnt u ≤ ω u := by
              rw [hωpos u hLt]
              exact Finset.le_sup (f := sCnt) (Finset.mem_range.mpr (Nat.lt_succ_self u))
            exact_mod_cast h
          calc effPos d ℓ (fun m => (jb m : ℝ)) (phiLevelDeriv (d := d) Λ₀ ℓ A t jb) u
              ≤ (subDim (flagFun ⟨u, hpos, hLt⟩) : ℝ) - (uf ⟨u, hpos, hLt⟩ : ℝ) := hwfEff ⟨u, hpos, hLt⟩
            _ = (sCnt u : ℝ) := by
              rw [hmem]
              exact (Nat.cast_sub (hwfAct ⟨u, hpos, hLt⟩).1.1).symm
            _ ≤ (ω u : ℝ) := hle1
  -- the charge
  have hMfun_pos : ∀ j, 0 < Mfun j := by
    intro j
    simp only [Mfun]
    exact mul_pos (DK_pos d ℓ k A) (hlam_pos (stN j) (hstN1 j) (hstNle j))
  have ha_mono : Monotone (fun j => Real.log (Mfun j)) := fun i j hij =>
    Real.log_le_log (hMfun_pos i) (hMfun_mono hij)
  have hpre : (∑ j ∈ Finset.range k, Real.log (Mfun j)) ≤
      ((k : ℝ) / (ℓ : ℝ)) * (∑ j ∈ Finset.range ℓ, Real.log (Mfun j)) :=
    Commons.Analysis.Real.sum_prefix_le_mul ha_mono hkl
  have hsplit : (∑ j ∈ Finset.range ℓ, Real.log (Mfun j)) =
      (ℓ : ℝ) * Real.log (DK d ℓ k A) + ∑ j ∈ Finset.range ℓ,
        Real.log (successiveMinimum (E := RD d) Λt (jb (stN j))) := by
    have h1 : ∀ j ∈ Finset.range ℓ, Real.log (Mfun j) =
        Real.log (DK d ℓ k A) +
          Real.log (successiveMinimum (E := RD d) Λt (jb (stN j))) := by
      intro j _
      simp only [Mfun]
      exact Real.log_mul (ne_of_gt (DK_pos d ℓ k A))
        (ne_of_gt (hlam_pos (stN j) (hstN1 j) (hstNle j)))
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  have hstage : (∑ j ∈ Finset.range ℓ,
        Real.log (successiveMinimum (E := RD d) Λt (jb (stN j)))) =
      ∑ u ∈ Finset.range N, ((ω (u+1) : ℝ) - (ω u : ℝ)) *
        Real.log (successiveMinimum (E := RD d) Λt (jb (u+1))) :=
    StageCount.sum_comp_stage_eq (ω := ω) (st := stN) hω0 hωmono hωN
      (fun j _ => hstNle j) hst_N
      (fun q => Real.log (successiveMinimum (E := RD d) Λt (jb q)))
  have hstep : ∀ u ∈ Finset.range N,
      ((ω (u+1) : ℝ) - (ω u : ℝ)) * Real.log (successiveMinimum (E := RD d) Λt (jb (u+1)))
      ≤ ((ω (u+1) : ℝ) - (ω u : ℝ)) * phiSlope (d := d) Λ₀ ℓ A t (jb u) +
        ((ω (u+1) : ℝ) - (ω u : ℝ)) * lamConst d A := by
    intro u hu
    have huN : u < N := Finset.mem_range.mp hu
    have hw : 0 ≤ (ω (u+1) : ℝ) - (ω u : ℝ) := by
      have h := hωmono (Nat.le_succ u)
      have : (ω u : ℝ) ≤ (ω (u+1) : ℝ) := by exact_mod_cast h
      linarith
    have hj1 : 1 ≤ jb (u+1) := by
      have h1 : u + 1 ≤ jb (u+1) := blockStart_n_ge d c (u+1) (by omega)
      omega
    have hjd : jb (u+1) ≤ d := blockStart_le_d d c (u+1)
    have hpred := LambdaPred.log_successiveMinimum_le_phiSlope_pred (d := d) hℓ0 hℓd s t A hA0 hj1 hjd hBdd
    have hblt : jb u < d := by
      rw [hjb, hNdef] at *
      exact blockStart_lt_numBlocks d c huN
    have hjbs : jb u < jb (u+1) := by
      have := blockStart_strict d c hblt
      simpa [hjb] using this
    have hjbs' : blockStart d c u < blockStart d c (u+1) := hjbs
    have hblk : phiSlope (d := d) Λ₀ ℓ A t (jb (u+1) - 1) = phiSlope (d := d) Λ₀ ℓ A t (jb u) := by
      have h1 : blockStart d c u ≤ jb (u+1) - 1 := by
        have h : blockStart d c u ≤ blockStart d c (u+1) - 1 := by omega
        exact h
      have h2 : jb (u+1) - 1 < blockStart d c (u+1) := by
        have h : blockStart d c (u+1) - 1 < blockStart d c (u+1) := by
          have := blockStart_n_ge d c (u+1) (by omega)
          omega
        exact h
      have := dslope_eq_on_block c d u (i := jb (u+1) - 1) h1 h2
      simpa only [phiSlope, hc] using this
    have h1 : Real.log (successiveMinimum (E := RD d) Λt (jb (u+1))) ≤
        phiSlope (d := d) Λ₀ ℓ A t (jb u) + lamConst d A := by
      have h := hpred
      rw [hblk] at h
      have hl : lamConst d A = Kconst d + 2 * A * (d : ℝ) ^ 2 + 2 * dataCeil d := rfl
      rw [hl]
      exact h
    calc ((ω (u+1) : ℝ) - (ω u : ℝ)) * Real.log (successiveMinimum (E := RD d) Λt (jb (u+1)))
        ≤ ((ω (u+1) : ℝ) - (ω u : ℝ)) *
            (phiSlope (d := d) Λ₀ ℓ A t (jb u) + lamConst d A) :=
          mul_le_mul_of_nonneg_left h1 hw
      _ = ((ω (u+1) : ℝ) - (ω u : ℝ)) * phiSlope (d := d) Λ₀ ℓ A t (jb u) +
            ((ω (u+1) : ℝ) - (ω u : ℝ)) * lamConst d A := by ring
  have hwtel : (∑ u ∈ Finset.range N, ((ω (u+1) : ℝ) - (ω u : ℝ))) = (ℓ : ℝ) := by
    simpa [hω0, hωN] using Finset.sum_range_sub (fun u => (ω u : ℝ)) N
  have hcharge : (∑ j ∈ Finset.range k, Real.log (Mfun j)) ≤
      (k : ℝ) * (Real.log (DK d ℓ k A) + ((d : ℝ) - (ℓ : ℝ)) / (d : ℝ) + lamConst d A) := by
    have h2 : (∑ j ∈ Finset.range ℓ, Real.log (Mfun j)) ≤
        (ℓ : ℝ) * (Real.log (DK d ℓ k A) + ((d : ℝ) - (ℓ : ℝ)) / (d : ℝ) + lamConst d A) := by
      rw [hsplit, hstage]
      have hA := Finset.sum_le_sum hstep
      rw [Finset.sum_add_distrib] at hA
      have hB : (∑ u ∈ Finset.range N, ((ω (u+1) : ℝ) - (ω u : ℝ)) * lamConst d A)
          = lamConst d A * (ℓ : ℝ) := by
        rw [← Finset.sum_mul, hwtel, mul_comm]
      rw [hB] at hA
      have hsum : (∑ u ∈ Finset.range N, ((ω (u+1) : ℝ) - (ω u : ℝ)) *
            phiSlope (d := d) Λ₀ ℓ A t (jb u))
          ≤ (ℓ : ℝ) * ((d : ℝ) - (ℓ : ℝ)) / (d : ℝ) := hacc
      have hℓ0' : (0 : ℝ) < (ℓ : ℝ) := Nat.cast_pos.mpr hℓ0
      have h3 : (ℓ : ℝ) * Real.log (DK d ℓ k A) +
            (∑ u ∈ Finset.range N, ((ω (u+1) : ℝ) - (ω u : ℝ)) *
              phiSlope (d := d) Λ₀ ℓ A t (jb u)) + lamConst d A * (ℓ : ℝ) ≤
          (ℓ : ℝ) * (Real.log (DK d ℓ k A) + ((d : ℝ) - (ℓ : ℝ)) / (d : ℝ) + lamConst d A) := by
        have hmc : lamConst d A * (ℓ : ℝ) = (ℓ : ℝ) * lamConst d A := mul_comm _ _
        rw [hmc]
        have hexp : (ℓ : ℝ) * (Real.log (DK d ℓ k A) + ((d : ℝ) - (ℓ : ℝ)) / (d : ℝ) + lamConst d A)
            = (ℓ : ℝ) * Real.log (DK d ℓ k A) +
              (ℓ : ℝ) * ((d : ℝ) - (ℓ : ℝ)) / (d : ℝ) + (ℓ : ℝ) * lamConst d A := by ring
        rw [hexp]
        linarith [hsum]
      linarith [hA, h3]
    have hkℓ : (0 : ℝ) < (ℓ : ℝ) := Nat.cast_pos.mpr hℓ0
    calc (∑ j ∈ Finset.range k, Real.log (Mfun j))
        ≤ ((k : ℝ) / (ℓ : ℝ)) * (∑ j ∈ Finset.range ℓ, Real.log (Mfun j)) := hpre
      _ ≤ ((k : ℝ) / (ℓ : ℝ)) *
            ((ℓ : ℝ) * (Real.log (DK d ℓ k A) + ((d : ℝ) - (ℓ : ℝ)) / (d : ℝ) + lamConst d A)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (k : ℝ) * (Real.log (DK d ℓ k A) + ((d : ℝ) - (ℓ : ℝ)) / (d : ℝ) + lamConst d A) := by
          field_simp
  have hwedge : ‖exteriorPower.ιMulti ℝ k p‖ ≤ C0K d ℓ k (Aconst d) := by
    have h1 : ‖exteriorPower.ιMulti ℝ k p‖ ≤ ∏ j : Fin k, ‖p j‖ :=
      Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod _
    have h2 : ∏ j : Fin k, ‖p j‖ ≤ ∏ j : Fin k, (1 + deltaK d ℓ k) * Mj j := by
      refine Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => ?_)
      calc ‖p j‖ ≤ (1 + deltaK d ℓ k) * Mj j := (hp j).2.2
        _ = (1 + deltaK d ℓ k) * Mj j := rfl
    have h3 : ∏ j : Fin k, (1 + deltaK d ℓ k) * Mj j
        = (1 + deltaK d ℓ k) ^ k * ∏ j : Fin k, Mj j := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h4 : ∏ j : Fin k, Mj j = Real.exp (∑ j : Fin k, Real.log (Mj j)) := by
      rw [Real.exp_sum]
      exact Finset.prod_congr rfl (fun j _ => (Real.exp_log (hMpos j)).symm)
    have h5 : (∑ j : Fin k, Real.log (Mj j)) ≤
        (k : ℝ) * (Real.log (DK d ℓ k A) + ((d : ℝ) - (ℓ : ℝ)) / (d : ℝ) + lamConst d A) := by
      have hEq : (∑ j : Fin k, Real.log (Mj j)) = ∑ j ∈ Finset.range k, Real.log (Mfun j) :=
        Fin.sum_univ_eq_sum_range (fun j => Real.log (Mfun j)) k
      rw [hEq]; exact hcharge
    have h6 : Real.exp (∑ j : Fin k, Real.log (Mj j)) ≤
        Real.exp ((k : ℝ) * (Real.log (DK d ℓ k A) + ℓ * ((d : ℝ) - (ℓ : ℝ)) / (d : ℝ) +
          lamConst d A)) := by
      refine Real.exp_le_exp.mpr ?_
      have hdl : ((d : ℝ) - (ℓ : ℝ)) / (d : ℝ) ≤ (ℓ : ℝ) * ((d : ℝ) - (ℓ : ℝ)) / (d : ℝ) := by
        have hℓ1 : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ0
        have hx : (0 : ℝ) ≤ (d : ℝ) - (ℓ : ℝ) := by
          have h2 : (ℓ : ℝ) ≤ (d : ℝ) := by exact_mod_cast le_of_lt hℓd
          linarith
        have hxx : ((d : ℝ) - (ℓ : ℝ)) ≤ (ℓ : ℝ) * ((d : ℝ) - (ℓ : ℝ)) := by
          nlinarith [hℓ1, hx]
        exact div_le_div_of_nonneg_right hxx (Nat.cast_nonneg d)
      nlinarith [h5, hdl, (show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k)]
    have hfin : (1 + deltaK d ℓ k) ^ k *
        Real.exp ((k : ℝ) * (Real.log (DK d ℓ k A) + ℓ * ((d : ℝ) - (ℓ : ℝ)) / (d : ℝ) +
          lamConst d A)) = C0K d ℓ k (Aconst d) := rfl
    calc ‖exteriorPower.ιMulti ℝ k p‖ ≤ ∏ j : Fin k, ‖p j‖ := h1
      _ ≤ ∏ j : Fin k, (1 + deltaK d ℓ k) * Mj j := h2
      _ = (1 + deltaK d ℓ k) ^ k * ∏ j : Fin k, Mj j := h3
      _ = (1 + deltaK d ℓ k) ^ k * Real.exp (∑ j : Fin k, Real.log (Mj j)) := by rw [h4]
      _ ≤ (1 + deltaK d ℓ k) ^ k *
            Real.exp ((k : ℝ) * (Real.log (DK d ℓ k A) + ℓ * ((d : ℝ) - (ℓ : ℝ)) / (d : ℝ) +
              lamConst d A)) :=
          mul_le_mul_of_nonneg_left h6 (by positivity)
      _ = C0K d ℓ k (Aconst d) := hfin
  -- the `π₊`-dominance
  have hbig : floorSeq d ℓ d ≤ ‖exteriorPower.map k (modelProj (d := d) ℓ)
      (exteriorPower.ιMulti ℝ k ek)‖ := by
    have h1 : floorSeq d ℓ d ≤ floorSeq d ℓ N := floorSeq_antitone d ℓ hNle
    have h2 := norm_prefix_le (d := d) hkl (modelProj (d := d) ℓ) (Prop5Block.norm_modelProj_le ℓ)
      (Prop5Block.modelProj_idem ℓ) e heON
    exact le_trans h1 (le_trans hlev h2)
  have hdom : cK d ℓ k * ‖exteriorPower.ιMulti ℝ k p‖ ≤
      ‖exteriorPower.map k (modelProj (d := d) ℓ) (exteriorPower.ιMulti ℝ k p)‖ := by
    have h := ConePerturbation.cone_perturbation_scaled (E := RD d) (Prop5Block.modelProjCL d ℓ)
      (fun x => Prop5Block.norm_modelProj_le ℓ x) (fun x => Prop5Block.modelProj_idem ℓ x)
      (δ := deltaK d ℓ k) (c := floorSeq d ℓ d) hδ0 (one_add_deltaK_pow_sub_one_lt d ℓ k hk1)
      ek (fun i => hekON.norm_eq_one i) ?_ (ρ := Mj) hMpos p (fun i => (hp i).2.1)
    · rwa [Prop5Block.modelProjCL_coe] at h
    · rw [Prop5Block.modelProjCL_coe]; exact hbig
  -- nonzero of the wedge
  let w : Fin k → RD d := fun j => (Mj j)⁻¹ • p j
  have hwn : ∀ j, ‖w j - ek j‖ ≤ deltaK d ℓ k := by
    intro j
    have h1 : w j - ek j = (Mj j)⁻¹ • (p j - Mj j • ek j) := by
      simp only [w]
      rw [smul_sub, inv_smul_smul₀ (ne_of_gt (hMpos j))]
    rw [h1, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hMpos j)]
    calc (Mj j)⁻¹ * ‖p j - Mj j • ek j‖ ≤ (Mj j)⁻¹ * (deltaK d ℓ k * Mj j) :=
          mul_le_mul_of_nonneg_left (hp j).2.1 (inv_nonneg.mpr (hMpos j).le)
      _ = deltaK d ℓ k := by
          rw [mul_comm (deltaK d ℓ k) (Mj j), ← mul_assoc,
            inv_mul_cancel₀ (ne_of_gt (hMpos j)), one_mul]
  have hcone : exteriorPower.map k (modelProj (d := d) ℓ) (exteriorPower.ιMulti ℝ k w) ≠ 0 := by
    have h := cone_wedge_ne_zero (d := d) (Prop5Block.modelProjCL d ℓ)
      (fun x => Prop5Block.norm_modelProj_le ℓ x) (fun x => Prop5Block.modelProj_idem ℓ x)
      hδ0 (one_add_deltaK_pow_sub_one_lt d ℓ k hk1) ek (fun i => hekON.norm_eq_one i) ?_ w hwn
    · rwa [Prop5Block.modelProjCL_coe] at h
    · rw [Prop5Block.modelProjCL_coe]; exact hbig
  have hpne : exteriorPower.ιMulti ℝ k p ≠ 0 := by
    have hwne : exteriorPower.ιMulti ℝ k w ≠ 0 := by
      intro h0
      exact hcone (by rw [h0, map_zero])
    have hpw : p = fun j => Mj j • w j := by
      funext j
      simp only [w]
      rw [smul_inv_smul₀ (ne_of_gt (hMpos j))]
    rw [hpw, AlternatingMap.map_smul_univ]
    exact smul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun j _ => ne_of_gt (hMpos j))) hwne
  have hpLI : LinearIndependent ℝ p :=
    Commons.LinearAlgebra.ExteriorPower.iMulti_linearIndependent_of_ne_zero _ hpne
  -- transport to the integer family
  set g : RD d ≃ₗ[ℝ] RD d := (s : RD d ≃ₗ[ℝ] RD d).trans (eEquiv (d := d) ℓ t) with hg
  have hpmem : ∀ i, p i ∈ imageSpan (d := d) g := by
    intro i
    rw [show imageSpan (d := d) g = Λt from hΛt.symm]
    exact (hp i).1
  obtain ⟨m, hmint, hmg⟩ := LiftFamily.exists_int_lift g k p hpmem
  have hmLI : LinearIndependent ℝ m := LiftFamily.linearIndependent_of_lift g hmg hpLI
  have hgc : ((g : RD d →ₗ[ℝ] RD d)) = (DaniEndgame.eFlow d ℓ t) ∘ₗ (s : RD d →ₗ[ℝ] RD d) := by
    refine LinearMap.ext (fun x => ?_)
    show (eEquiv (d := d) ℓ t : RD d →ₗ[ℝ] RD d) ((s : RD d →ₗ[ℝ] RD d) x) =
      (DaniEndgame.eFlow d ℓ t : RD d →ₗ[ℝ] RD d) ((s : RD d →ₗ[ℝ] RD d) x)
    have he : (eEquiv (d := d) ℓ t : RD d →ₗ[ℝ] RD d) = DaniEndgame.eFlow d ℓ t := by
      rw [eEquiv_coe]; rfl
    exact congrArg (fun f : RD d →ₗ[ℝ] RD d => f ((s : RD d →ₗ[ℝ] RD d) x)) he
  have heq : DaniEndgame.eFlowK d ℓ k t
      (exteriorPower.map k (s : RD d →ₗ[ℝ] RD d) (exteriorPower.ιMulti ℝ k m)) =
      exteriorPower.ιMulti ℝ k p := by
    have h1 : exteriorPower.map k ((DaniEndgame.eFlow d ℓ t) ∘ₗ (s : RD d →ₗ[ℝ] RD d))
        (exteriorPower.ιMulti ℝ k m) =
        exteriorPower.map k (DaniEndgame.eFlow d ℓ t)
          (exteriorPower.map k (s : RD d →ₗ[ℝ] RD d) (exteriorPower.ιMulti ℝ k m)) := by
      rw [exteriorPower.map_comp]
      rfl
    rw [DaniEndgame.eFlowK, ← h1, ← hgc, ← LiftFamily.iMulti_lift g m]
    congr 1
    funext i
    exact hmg i
  refine ⟨t, htT, m, fun i => hmint i, hmLI, ?_, ?_⟩
  · show Dominates d ℓ k t (cK d ℓ k)
      (exteriorPower.map k (s : RD d →ₗ[ℝ] RD d) (exteriorPower.ιMulti ℝ k m))
    rw [DaniEndgame.Dominates, heq, WedgeBlockZero.blockElem_zero_eq_map_modelProj]
    exact hdom
  · rw [heq]; exact hwedge

end Submission.ProductionAssembly

end
