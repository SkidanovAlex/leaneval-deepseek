import Mathlib
import Submission.Work.Drive.analyticDensity
import Submission.Work.Drive.classRowVocab
import Submission.Work.Drive.linShearCharts
import Submission.Work.Drive.linCommonPoint
import Submission.Work.Drive.linShearIncidence
import Submission.Work.Drive.linGpDefs
import Submission.Work.Drive.linGpAux
import Submission.Work.Drive.exists_linVecC_smul_eq
import Submission.Work.Drive.analyticAt_gpDet

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

/-! ## The two halves of the general-position equivalence, and the witness at `t = 0` -/

/-- The transported linear family at `t = 0` is the repaired linear family. -/
lemma gpPsi_zero (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3) : gpPsi A k 0 = linBase A k := by
  ext x
  simp [gpPsi]

/-- The common point of three planes does not depend on the proof of general position. -/
lemma linCommonPt_congr (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl)
    (h h' : Module.finrank ℝ ↥(⨅ k : Fin 3, linSub (φ k)) = 1) :
    linCommonPt φ cl hcl h = linCommonPt φ cl hcl h' :=
  eq_linCommonPt φ cl hcl h (level_linCommonPt φ cl hcl h')
    (fun k => mem_projLine_linCommonPt φ cl hcl h' k)

/-- The common point of three planes is transported along an equality of the three charts: only the
planes and the level enter. -/
lemma linCommonPt_congr_fam {φ ψ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3} (hfam : ∀ i, φ i = ψ i) (cl : ℝ)
    (hcl : 0 < cl) (h : Module.finrank ℝ ↥(⨅ k : Fin 3, linSub (φ k)) = 1)
    (h' : Module.finrank ℝ ↥(⨅ k : Fin 3, linSub (ψ k)) = 1) :
    linCommonPt φ cl hcl h = linCommonPt ψ cl hcl h' := by
  refine eq_linCommonPt ψ cl hcl h' (level_linCommonPt φ cl hcl h) (fun j => ?_)
  have hj := mem_projLine_linCommonPt φ cl hcl h j
  have hψ : linSub (φ j) = linSub (ψ j) := by rw [hfam j]
  rwa [hψ] at hj

/-- **Independence of the four functionals implies the general-position clause.**  The three normal
functionals are independent (a subfamily), so the planes meet in a line; and if the boundary circle of
the `k`-th chart met the common point, then `Ψ k t (linVecC z)` would be a non-zero vector of the
common kernel of the four functionals. -/
theorem gp_generalPosition_of_linIndependent (A : Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl)
    (t : EuclideanSpace ℝ (Fin 12)) (h : ∀ k : Fin 3, LinearIndependent ℝ (gpFun A k t)) :
    ∃ hrank : Module.finrank ℝ ↥(⨅ k : Fin 3, linSub (gpPsi A k t)) = 1,
      ∀ (k : Fin 3) (z : ℂ), ‖z‖ = 1 →
        linPlaneChart (gpPsi A k t) cl hcl z ≠ linCommonPt (fun k => gpPsi A k t) cl hcl hrank := by
  have hLI3 : LinearIndependent ℝ (fun j : Fin 3 => linFun (gpPsi A j t)) := by
    have h3 : LinearIndependent ℝ (fun j : Fin 3 => gpFun A 0 t (Fin.castSucc j)) :=
      (h 0).comp Fin.castSucc (Fin.castSucc_injective 3)
    have hfun : (fun j : Fin 3 => gpFun A 0 t (Fin.castSucc j))
        = fun j : Fin 3 => linFun (gpPsi A j t) := by
      funext j
      fin_cases j <;> rfl
    rwa [hfun] at h3
  have hrank : Module.finrank ℝ ↥(⨅ k : Fin 3, linSub (gpPsi A k t)) = 1 :=
    (finrank_iInf_linSub_eq_one_iff_linearIndependent (fun k : Fin 3 => gpPsi A k t)).mpr hLI3
  refine ⟨hrank, ?_⟩
  intro k z hz heq
  have hvanish : ∀ j : Fin 3, linFun (gpPsi A j t) (gpPsi A k t (linVecC z)) = 0 :=
    fun j => gp_linFun_eq_zero_of_linPlaneChart_eq (fun k => gpPsi A k t) cl hcl hrank hz heq j
  have hmem : gpPsi A k t (linVecC z) ∈ (⨅ i : Fin 4, (gpFun A k t i).ker) := by
    rw [gp_iInf_ker_gpFun]
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Submodule.mem_iInf]
      intro j
      rw [← ker_linFun]
      exact LinearMap.mem_ker.mpr (hvanish j)
    · rw [LinearMap.mem_ker, gpCoordPull]
      show (coordFun 2) ((gpPsi A k t).symm ((gpPsi A k t) (linVecC z))) = 0
      rw [ContinuousLinearEquiv.symm_apply_apply, coordFun_apply, linVecC_apply_two, hz]
      norm_num
  have hbot : (⨅ i : Fin 4, (gpFun A k t i).ker) = ⊥ :=
    (iInf_ker_eq_bot_iff_linearIndependent (gpFun A k t) gpFun_card).mpr (h k)
  rw [hbot] at hmem
  have hzero : gpPsi A k t (linVecC z) = 0 := by simpa using hmem
  exact phi_linVecC_ne_zero (gpPsi A k t) z hzero

/-- **The general-position clause implies independence of the four functionals.**  If the common
kernel of the four functionals contained `u ≠ 0`, then `v = (Ψ k t)⁻¹ u` would be a non-zero vector of
the boundary plane `span {e₀, e₁}`; the unit circle carries a lift `linVecC z` on the ray of `v`, and
then `Ψ k t (linVecC z)` lies on all three planes, so the chart value at `z` is the common point. -/
theorem gp_linIndependent_of_generalPosition (A : Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl)
    (t : EuclideanSpace ℝ (Fin 12))
    (hrank : Module.finrank ℝ ↥(⨅ k : Fin 3, linSub (gpPsi A k t)) = 1)
    (hgen : ∀ (k : Fin 3) (z : ℂ), ‖z‖ = 1 →
        linPlaneChart (gpPsi A k t) cl hcl z
          ≠ linCommonPt (fun k => gpPsi A k t) cl hcl hrank) :
    ∀ k : Fin 3, LinearIndependent ℝ (gpFun A k t) := by
  intro k
  have hdisj : (⨅ j : Fin 3, linSub (gpPsi A j t)) ⊓ (gpCoordPull 2 (gpPsi A k t)).ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro u hu
    by_contra hune
    rw [Submodule.mem_inf] at hu
    obtain ⟨huV, huM⟩ := hu
    set v : Eucl 3 := (gpPsi A k t)⁻¹ u with hv
    have huv : u = gpPsi A k t v := by
      rw [hv]
      exact (ContinuousLinearEquiv.apply_symm_apply (gpPsi A k t) u).symm
    have hvne : v ≠ 0 := by
      intro h0
      apply hune
      rw [huv, h0, map_zero]
    have hvmem : v ∈ Submodule.span ℝ ({linE0, linE1} : Set (Eucl 3)) := by
      rw [mem_span_linE0_linE1_iff]
      constructor
      · have h := huM
        rw [LinearMap.mem_ker, gpCoordPull, LinearMap.comp_apply, coordFun_apply] at h
        rw [hv]
        show ((gpPsi A k t).symm u).ofLp 2 = 0
        exact h
      · have hk : u ∈ linSub (gpPsi A k t) :=
          (Submodule.mem_iInf (fun j : Fin 3 => linSub (gpPsi A j t))).mp huV k
        rw [← ker_linFun, LinearMap.mem_ker, linFun_apply] at hk
        rw [hv]
        show ((gpPsi A k t).symm u).ofLp 3 = 0
        exact hk
    obtain ⟨z, a, hz, ha, haz⟩ := exists_linVecC_smul_eq hvmem hvne
    have hzv : linVecC z = a⁻¹ • v := by
      rw [← haz, smul_smul, inv_mul_cancel₀ ha, one_smul]
    have hzmem : gpPsi A k t (linVecC z) ∈ (⨅ j : Fin 3, linSub (gpPsi A j t)) := by
      rw [hzv, map_smul, ← huv]
      exact Submodule.smul_mem _ _ huV
    have hvanish : ∀ j : Fin 3, linFun (gpPsi A j t) (gpPsi A k t (linVecC z)) = 0 := by
      intro j
      have h := (Submodule.mem_iInf (fun j : Fin 3 => linSub (gpPsi A j t))).mp hzmem j
      rwa [← ker_linFun, LinearMap.mem_ker] at h
    exact hgen k z hz
      (gp_linPlaneChart_eq_linCommonPt (fun k => gpPsi A k t) cl hcl hrank hz hvanish)
  have hbot : (⨅ i : Fin 4, (gpFun A k t i).ker) = ⊥ := by
    rw [gp_iInf_ker_gpFun, hdisj]
  exact (iInf_ker_eq_bot_iff_linearIndependent (gpFun A k t) gpFun_card).mp hbot


/-! **Rows C and D of `Work.Drive.classRowsLin_openDense`** (the review for this path approved the
statement and corroborated the route): the general-position clauses (`hrank` and `hgen`) of the
transported family `Ψ k := (linBase A k).trans (classEquiv (blk k t))`, on an open set of design
parameters dense at every point of the closed unit ball.

The third linear row `EndTripleReg lin₂lin₀lin₁` is *not* asked for here: it follows in one line from
`hrank` + `hgen` by `Work.Drive.endTripleReg_linPlaneCharts_uncond`.

Route: with `P k := (linSub (linBase A k)).map (classEquiv (blk k t))` (3-planes) and
`M k := (linBdry (linBase A k)).map (classEquiv (blk k t))` (2-planes), `linSub (Ψ k) = P k`
(`Work.Drive.linSub_trans`), and the sufficient conditions `P i ≠ P j`, `P i ⊓ P j ⊄ P k`,
`(P i ⊓ P j) ⊓ M k = 0` give `finrank = 1` (three 3-planes in `ℝ⁴` meet in dimension `≥ 1`) and
`V ⊓ M k = 0` for `V := ⨅ k P k`, which is `hgen` because the boundary circle of the disk model maps
onto the projective line of `M k` and `linCommonPt` is the unique capping point on `V`
(`Work.Drive.eq_linCommonPt`, `Work.Drive.mem_projLine_linCommonPt`,
`Work.Drive.level_linCommonPt`).  Each incidence condition is a finite conjunction/disjunction of
non-vanishing conditions `f ≠ 0` for analytic functions of `t` (the planes depend on `t` through the
affine map `classEquiv (blk k t)`), so `Work.Drive.isOpen_denseAtBall_ne_zero` gives openness and
density-at-ball, and finite conjunctions/unions preserve both.  Witnesses at `t = 0`:
`Work.Drive.finrank_iInf_linSub_linBase`, `Work.Drive.hgen_linBase`,
`Work.Drive.linIncidence_linBase`. -/
theorem rowCD_linTrans_generalPosition_openDense (A : Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3)
    (cl : ℝ) (hcl : 0 < cl) :
    ∃ R : Set (EuclideanSpace ℝ (Fin 12)), IsOpen R ∧ Work.Drive.DenseAtBall R ∧
      ∀ t ∈ R, ∃ hrank : Module.finrank ℝ ↥(⨅ k : Fin 3,
          Work.Drive.linSub ((Work.Drive.linBase A k).trans
            (Work.Drive.classEquiv ((Work.Drive.blk k) t)))) = 1,
        ∀ (k : Fin 3) (z : ℂ), ‖z‖ = 1 →
          Work.Drive.linPlaneChart ((Work.Drive.linBase A k).trans
              (Work.Drive.classEquiv ((Work.Drive.blk k) t))) cl hcl z
            ≠ Work.Drive.linCommonPt (fun k =>
                (Work.Drive.linBase A k).trans (Work.Drive.classEquiv ((Work.Drive.blk k) t)))
              cl hcl hrank := by
  have hana : ∀ k : Fin 3, ∀ t : EuclideanSpace ℝ (Fin 12),
      AnalyticAt ℝ (fun s : EuclideanSpace ℝ (Fin 12) => gpDet A k s) t :=
    fun k t => analyticAt_gpDet A k t
  have hwit : ∀ k : Fin 3, ∃ t : EuclideanSpace ℝ (Fin 12), gpDet A k t ≠ 0 := by
    intro k
    have hrank0 : Module.finrank ℝ ↥(⨅ j : Fin 3, linSub (gpPsi A j 0)) = 1 := by
      have h : (⨅ j : Fin 3, linSub (gpPsi A j 0)) = (⨅ j : Fin 3, linSub (linBase A j)) :=
        iInf_congr (fun j => by rw [gpPsi_zero])
      rw [h]
      exact finrank_iInf_linSub_linBase A
    have hgen0 : ∀ (j : Fin 3) (z : ℂ), ‖z‖ = 1 →
        linPlaneChart (gpPsi A j 0) cl hcl z
          ≠ linCommonPt (fun i : Fin 3 => gpPsi A i 0) cl hcl hrank0 := by
      intro j z hz hend
      have h := hgen_linBase A cl hcl j z hz
      have hlin : linPlaneChart (gpPsi A j 0) cl hcl z = linPlaneChart (linBase A j) cl hcl z := by
        rw [gpPsi_zero]
      exact h ((hlin.symm.trans hend).trans
        (linCommonPt_congr_fam (fun i => gpPsi_zero A i) cl hcl hrank0
          (finrank_iInf_linSub_linBase A)))
    refine ⟨0, ?_⟩
    rw [gpDet_ne_zero_iff_linIndependent]
    exact gp_linIndependent_of_generalPosition A cl hcl 0 hrank0 hgen0 k
  refine ⟨⋂ k : Fin 3, {t : EuclideanSpace ℝ (Fin 12) | gpDet A k t ≠ 0}, ?_, ?_, ?_⟩
  · exact isOpen_iInter_of_finite fun k => (isOpen_denseAtBall_ne_zero (hana k) (hwit k)).1
  · intro x hx δ hδ
    obtain ⟨x', hx'1, hx'd⟩ := exists_norm_lt_one_near x hx (by linarith : (0 : ℝ) < δ / 2)
    obtain ⟨y, hy, hyall⟩ := exists_mem_iInter_near_of_denseAtBall
      (fun k => (isOpen_denseAtBall_ne_zero (hana k) (hwit k)).1)
      (fun k => (isOpen_denseAtBall_ne_zero (hana k) (hwit k)).2) hx'1 (δ / 2) (by linarith)
    refine ⟨y, Set.mem_iInter.mpr hyall, ?_⟩
    calc ‖y - x‖ ≤ ‖y - x'‖ + ‖x' - x‖ := by
          have h := norm_add_le (y - x') (x' - x)
          rwa [sub_add_sub_cancel] at h
      _ < δ / 2 + δ / 2 := by linarith
      _ = δ := by ring
  · intro t ht
    have hLI : ∀ k : Fin 3, LinearIndependent ℝ (gpFun A k t) := fun k =>
      (gpDet_ne_zero_iff_linIndependent A k t).mp (Set.mem_iInter.mp ht k)
    exact gp_generalPosition_of_linIndependent A cl hcl t hLI

end Work.Drive
