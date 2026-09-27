import Mathlib
import Submission.Work.Drive.encFamQ0
import Submission.Work.Drive.surjective_pUp_of_blockRanges
import Submission.Work.Drive.hrichCore
import Submission.Work.Drive.encodedEndData
import Submission.Work.Drive.range_fderiv_chart_planeBlock
import Submission.Work.Drive.deriv_thetaS_ne_zero_of_eq
import Submission.Work.Drive.exists_chartPert
import Submission.Work.Drive.surjective_paramDeriv_encFamQ0_caseII

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# Case I of the richness `hrich` for the ends-clause family `encFamQ0`

At a zero `y` of the charted triple-difference map `TParity.chartDiff3 p (encFamQ0 H A B c₀ t)` at
which the time bump of block `0` does **not** vanish (`betaG ((bPartC 0 y) 2) ≠ 0`), the parameter
derivative of the charted triple-difference map is surjective onto `ℝ⁸`.

**Why.**  The perturbation parameter `p` of block `0` enters as `chartPert (betaG s • p)`, so with
`betaG s ≠ 0` the *class* reach of block `0` is **all** of `TℝP³` while its level is frozen at `c₀`:
hence `range D₀ = lift0 ⊤` (the local lemma `Work.Drive.chart_block0_alive_aux` below).  The two plane blocks have the reaches
`liftAll A'` and `liftAll B'`, with `A'`, `B'` the chart-transported class reaches
(`Work.Drive.range_fderiv_chart_planeBlock`, whose level direction is supplied by the twist through
`Work.Drive.deriv_thetaS_ne_zero_of_eq`).  At the meet `A (shear q₁ u₁) = B (shear q₂ u₂)`, so the two
reaches share the same change of coordinates `tcc` and `PairReg` gives `A' ⊔ B' = ⊤`; the coset lemma
`Work.Drive.exists_coset_mem_lift` (with `W₀ = ⊤`) then produces the coset condition, and the closer
`Work.Drive.surjective_pair_sub_of_coset` the surjectivity.

The shared vocabulary (the six block projections of `EncParQ0` as continuous linear maps, the
splitting of the source of `chr`, the differentiability of the charted block maps) is taken from
`Submission.Work.Drive.surjective_paramDeriv_encFamQ0_caseII`, where it is proved.
-/

namespace Work.Drive

open Manifold Set Function
open scoped Manifold ContDiff Topology

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false
set_option backward.isDefEq.respectTransparency false

section Helpers

attribute [local instance] Work.Drive.projCharted Work.Drive.isManifold_projCharted
  Work.Drive.projTimesLineCharted Work.Drive.isManifold_projTimesLineCharted

/-- The product charted structure on `ℝP³ × ℝ`, made a local instance so that instance search finds
it (it cannot see through the `def` `ModelProd`). -/
local instance ciProdCharted : ChartedSpace (EuclideanSpace ℝ (Fin 3) × ℝ)
    (Projectivization ℝ (Eucl 3) × ℝ) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) ℝ ℝ

private abbrev CI2 := EuclideanSpace ℝ (Fin 2)
private abbrev CI3 := EuclideanSpace ℝ (Fin 3)
private abbrev CI4 := EuclideanSpace ℝ (Fin 4)
private abbrev CIP3 := Projectivization ℝ (Eucl 3)

/-- **The block-`0` parameter `(p, q₀)`** (the class-perturbation parameter and the shear parameter
of block `0` of `EncParQ0`), as a continuous linear map. -/
def ciQ0Prj : EncParQ0 →L[ℝ] (CI4 × CI4) := q0PCLM.prod q0Q0CLM

@[simp] lemma ciQ0Prj_apply (t : EncParQ0) : ciQ0Prj t = (q0P t, q0Q0 t) := rfl

lemma surjective_ciQ0Prj : Function.Surjective ciQ0Prj :=
  fun z => ⟨⟨z.1, z.2, 0, 0, (0 : ℝ), 0⟩, rfl⟩

@[simp] lemma ciQ0Prj_q0Mix_self (u₀ u₁ u₂ : EncParQ0) :
    ciQ0Prj (q0Mix u₀ u₀ u₁ u₂) = ciQ0Prj u₀ := rfl

/-! ## The Case-I block-`0` reach: with the class perturbation alive

The supporting facts (`ci_mfderiv_eq_fderiv_chartAt_rp3`, `ci_surjective_mfderiv_classMap_param`,
`ci_hasFDerivAt_chartAt_comp_gen`, `ci_range_fderiv_psiLin_prod_const_gen`,
`ci_surjective_mfderiv_smul_id`) and then the reach `chart_block0_alive_aux` itself. -/

-- **The bridge between the manifold derivative into `ℝP³` and the Fréchet derivative of the chart
-- expression at the image point.**  For a map `G` from the model space `𝔼⁴` into a manifold modelled
-- on `𝔼³` (so that the extended chart at the source point is the identity),
-- `mfderiv G t = fderiv ℝ (chartAt 𝔼³ (G t) ∘ G) t`.
theorem ci_mfderiv_eq_fderiv_chartAt_rp3 {M : Type*} [TopologicalSpace M]
    [ChartedSpace CI3 M] [IsManifold (𝓡 3) Ctop M]
    (G : CI4 → M) (t : CI4) (hG : ContMDiff (𝓡 4) (𝓡 3) Ctop G) :
    mfderiv (𝓡 4) (𝓡 3) G t = fderiv ℝ (fun s => chartAt CI3 (G t) (G s)) t := by
  have h : MDifferentiableAt (𝓡 4) (𝓡 3) G t := (hG t).mdifferentiableAt (by simp)
  have hw : writtenInExtChartAt (𝓡 4) (𝓡 3) t G = fun s : CI4 => chartAt CI3 (G t) (G s) := by
    funext s
    simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_coe, modelWithCornersSelf_coe,
      Function.id_comp, id_eq]
    rw [extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe]
    simp
  rw [mfderiv, if_pos h, hw]
  rw [show Set.range (𝓡 4) = Set.univ from by
        simp only [modelWithCornersSelf_coe, Set.range_id], fderivWithin_univ,
    extChartAt_model_space_eq_id]
  rfl

-- **The parameter derivative of the class family is onto.**  `t ↦ classMap t c` is the
-- projectivised quaternionic action of the chart perturbation; its parameter derivative at every `t`
-- is surjective onto the tangent space of `ℝP³` at `classMap t c` (the class directions span a
-- complement of the line of the image point, `Work.Drive.classDeriv_surjective`).
theorem ci_surjective_mfderiv_classMap_param (c : CIP3) (t : CI4) :
    Function.Surjective (mfderiv (𝓡 4) (𝓡 3) (fun s : CI4 => classMap s c) t) := by
  have hG : ContMDiff (𝓡 4) (𝓡 3) Ctop (fun s : CI4 => classMap s c) :=
    fun t => contMDiffAt_classMap_param c t
  rw [ci_mfderiv_eq_fderiv_chartAt_rp3 (fun s : CI4 => classMap s c) t hG]
  rw [(hasFDerivAt_chartAt_classMap c t).fderiv]
  intro y
  obtain ⟨s, hs⟩ := classDeriv_surjective c.rep_nonzero t (projChartIndexOf (classMap t c))
    (classEquiv_ofLp_chartIndexOf_ne_zero t c) y
  exact ⟨s, hs⟩

-- **The derivative of a chart followed by a smooth curve**, in terms of the manifold derivative and
-- the change of coordinates `tangentCoordChange`: a domain-general version of
-- `Work.Drive.hasFDerivAt_chartAt_comp` (the statement is used here with the domain `𝔼⁴ × 𝔼⁴`).
theorem ci_hasFDerivAt_chartAt_comp_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace CI3 M] [IsManifold (𝓡 3) Ctop M]
    (C : E → M) (pp : M) {x : E}
    (hC : MDifferentiableAt (𝓘(ℝ, E)) (𝓡 3) C x)
    (hx : C x ∈ (chartAt CI3 pp).source) :
    HasFDerivAt (fun y => chartAt CI3 pp (C y))
      ((tangentCoordChange (𝓡 3) (C x) pp (C x)).comp (mfderiv (𝓘(ℝ, E)) (𝓡 3) C x)) x := by
  have hφ : MDifferentiableAt (𝓡 3) (𝓡 3) (chartAt CI3 pp : M → CI3) (C x) :=
    mdifferentiableAt_atlas (chart_mem_atlas _ _) hx
  have hcomp : MDifferentiableAt (𝓘(ℝ, E)) (𝓡 3) (fun y => chartAt CI3 pp (C y)) x :=
    hφ.comp x hC
  have hmf : mfderiv (𝓘(ℝ, E)) (𝓡 3) (fun y => chartAt CI3 pp (C y)) x
      = (tangentCoordChange (𝓡 3) (C x) pp (C x)).comp (mfderiv (𝓘(ℝ, E)) (𝓡 3) C x) := by
    have hmain := mfderiv_comp (g := (chartAt CI3 pp)) (f := C) x hφ hC
    rw [mfderiv_chartAt_eq_tangentCoordChange hx] at hmain
    exact hmain
  have hd : DifferentiableAt ℝ (fun y => chartAt CI3 pp (C y)) x := hcomp.differentiableAt
  have hfd : fderiv ℝ (fun y => chartAt CI3 pp (C y)) x
      = (tangentCoordChange (𝓡 3) (C x) pp (C x)).comp (mfderiv (𝓘(ℝ, E)) (𝓡 3) C x) := by
    rw [← mfderiv_eq_fderiv, hmf]
  have h := hd.hasFDerivAt
  rw [hfd] at h
  exact h

-- **The range of the derivative of `psiLin` applied to a pair with constant second component**:
-- the class reach with *zero* level.  Domain-general version of
-- `Work.Drive.range_fderiv_psiLin_prod_const`.
theorem ci_range_fderiv_psiLin_prod_const_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → CI3) (x : E) (c : ℝ) (hf : DifferentiableAt ℝ f x) :
    (fderiv ℝ (fun z : E => psiLin (f z, c)) x).range = lift0 (fderiv ℝ f x).range := by
  set L : E →L[ℝ] (CI3 × ℝ) :=
    (fderiv ℝ f x).prod (0 : E →L[ℝ] ℝ) with hLdef
  have hL : HasFDerivAt (fun z : E => (f z, c)) L x :=
    hf.hasFDerivAt.prodMk (hasFDerivAt_const c x)
  have hpsi : HasFDerivAt (fun y : CI3 × ℝ => psiLin y)
      (psiLin : (CI3 × ℝ) →L[ℝ] CI4) (f x, c) :=
    (psiLin : (CI3 × ℝ) →L[ℝ] CI4).hasFDerivAt
  have hF : HasFDerivAt (fun z : E => psiLin (f z, c))
      ((psiLin : (CI3 × ℝ) →L[ℝ] CI4).comp L) x := hpsi.comp x hL
  have hLrange : (L : E →ₗ[ℝ] (CI3 × ℝ)).range = (fderiv ℝ f x).range.prod ⊥ := by
    refine le_antisymm ?_ ?_
    · intro y hy
      obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hy
      refine Submodule.mem_prod.mpr ⟨LinearMap.mem_range.mpr ⟨z, rfl⟩, ?_⟩
      rw [Submodule.mem_bot]
      rfl
    · intro y hy
      obtain ⟨hy1, hy2⟩ := Submodule.mem_prod.mp hy
      obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hy1
      have hy2' : y.2 = 0 := by simpa using hy2
      refine LinearMap.mem_range.mpr ⟨w, ?_⟩
      exact Prod.ext hw hy2'.symm
  rw [hF.fderiv]
  rw [show ((psiLin : (CI3 × ℝ) →L[ℝ] CI4).comp L).range
      = Submodule.map (psiLin : (CI3 × ℝ) →ₗ[ℝ] CI4)
          (L : E →ₗ[ℝ] (CI3 × ℝ)).range from LinearMap.range_comp _ _]
  rw [hLrange, map_psiLin_prod_bot]


/-- The shrink map of the class parameter is onto. -/
theorem ci_surjective_mfderiv_smul_id (β : ℝ) (hβ : β ≠ 0) (P : CI4) :
    Function.Surjective (mfderiv (𝓡 4) (𝓡 4) (fun w : CI4 => β • w) P) := by
  rw [mfderiv_eq_fderiv]
  set sm : CI4 →L[ℝ] CI4 := β • ContinuousLinearMap.id ℝ CI4 with hsmdef
  rw [show fderiv ℝ (fun w : CI4 => β • w) P = sm from (sm.hasFDerivAt (x := P)).fderiv]
  intro y
  refine ⟨(β⁻¹ : ℝ) • y, ?_⟩
  show sm ((β⁻¹ : ℝ) • y) = y
  rw [hsmdef]
  show (β • ContinuousLinearMap.id ℝ CI4) ((β⁻¹ : ℝ) • y) = y
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_smul,
    mul_inv_cancel₀ hβ, one_smul]

-- **The Case-I block-`0` reach.**  With the class perturbation alive (`betaG (x 2) ≠ 0`) and the
-- level frozen at `c₀`, the parameter derivative of the charted block-`0` map
-- `z ↦ chr p (encFamQ0₀ H c₀ z.1 z.2 x)` is differentiable at `(P, Q)` and its range is `lift0 ⊤`:
-- the whole class space at level `0`.

-- The three steps: (i) `clsSh (chartPert t p₀) = classMap t (clsSh p₀)` reduces the class part to the
-- class family, whose parameter derivative is onto (`ci_surjective_mfderiv_classMap_param`) and whose
-- `z.1`-dependence is the isomorphism `w ↦ betaG (x 2) • w`
-- (`ci_surjective_mfderiv_smul_id`); (ii) restricting to the slice `z ↦ (z, Q)` and using the
-- Fréchet chain rule shows that the range of the charted class map `C` is `⊤`; (iii) the level is the
-- constant `c₀`, so the range of `psiLin (C ·, c₀)` is `lift0 ⊤`
-- (`ci_range_fderiv_psiLin_prod_const_gen`). -/
theorem chart_block0_alive_aux
    (H : ℝ × CI2 → CIP3) (x : CI3) (c₀ : ℝ) (p : CIP3 × ℝ) (P Q : CI4) :
    ContMDiff (𝓡 3) (𝓡 3) Ctop (fun x : CI3 => H (x 2, mk2 (x 0) (x 1))) →
    betaG (x 2) ≠ 0 →
    encFamQ0₀ H c₀ P Q x ∈ (chr p).source →
    DifferentiableAt ℝ (fun z : CI4 × CI4 => chr p (encFamQ0₀ H c₀ z.1 z.2 x)) (P, Q) ∧
    (fderiv ℝ (fun z : CI4 × CI4 => chr p (encFamQ0₀ H c₀ z.1 z.2 x)) (P, Q)).range =
      lift0 (⊤ : Submodule ℝ CI3) := by
  intro hH hβ hsrc
  set β : ℝ := betaG (x 2) with hβdef
  have hβ' : β ≠ 0 := by rw [hβdef]; exact hβ
  set u : CI2 := pt2 (x 0) (x 1) with hudef
  set cfun : CIP3 := H (x 2, shear Q u) with hcfundef
  set V : (CI4 × CI4) → CIP3 := fun z => classMap (β • z.1) (H (x 2, shear z.2 u)) with hVdef
  set C : (CI4 × CI4) → CI3 := fun z => chartAt CI3 p.1 (V z) with hCdef
  have hVsrc : V (P, Q) ∈ (chartAt CI3 p.1).source := by
    have h := q0_fst_mem_source hsrc
    simp only [encFamQ0₀] at h
    rw [clsSh_chartPert, clsSh_capOf] at h
    simp only [← hβdef, ← hudef] at h
    exact h
  have hGfun : (fun z : CI4 × CI4 => chr p (encFamQ0₀ H c₀ z.1 z.2 x))
      = fun z => psiLin (C z, c₀) := by
    funext z
    rw [hCdef, q0_chr_apply]
    congr 1
    refine Prod.ext ?_ ?_
    · show chartAt CI3 p.1 (encFamQ0₀ H c₀ z.1 z.2 x).1 = chartAt CI3 p.1 (V z)
      simp only [encFamQ0₀, clsSh_chartPert, clsSh_capOf, hVdef]
      simp only [← hβdef, ← hudef]
    · rfl
  -- differentiability of the class part
  have hslice : ContMDiff (𝓡 2) (𝓡 3) Ctop (fun y : CI2 => H (x 2, y)) :=
    contMDiff_slice H (x 2) hH
  have hshear2 : DifferentiableAt ℝ (fun z : CI4 × CI4 => shear z.2 u) (P, Q) := by
    have hcomp : DifferentiableAt ℝ ((fun q' : CI4 => shear q' u) ∘ (fun z : CI4 × CI4 => z.2))
        (P, Q) :=
      (differentiableAt_shear_param u Q).comp (P, Q) (differentiableAt_snd (p := (P, Q)))
    simpa only [Function.comp_def] using hcomp
  have h2 : MDifferentiableAt (𝓘(ℝ, CI4 × CI4)) (𝓡 3)
      (fun z : CI4 × CI4 => H (x 2, shear z.2 u)) (P, Q) :=
    (hslice.mdifferentiableAt (by simp)).comp (P, Q) hshear2.mdifferentiableAt
  have h1 : MDifferentiableAt (𝓘(ℝ, CI4 × CI4)) (𝓡 4)
      (fun z : CI4 × CI4 => β • z.1) (P, Q) :=
    (((β • ContinuousLinearMap.fst ℝ CI4 CI4)).differentiableAt (x := (P, Q))).mdifferentiableAt
  have hΓ : MDifferentiableAt (𝓘(ℝ, CI4 × CI4)) ((𝓡 4).prod (𝓡 3))
      (fun z : CI4 × CI4 => (β • z.1, H (x 2, shear z.2 u))) (P, Q) := h1.prodMk h2
  have hVmd : MDifferentiableAt (𝓘(ℝ, CI4 × CI4)) (𝓡 3) V (P, Q) := by
    rw [hVdef]
    exact ((contMDiffAt_classMap_prod (β • P) (H (x 2, shear Q u))).mdifferentiableAt
      (by simp)).comp (P, Q) hΓ
  have hCd : HasFDerivAt C ((tangentCoordChange (𝓡 3) (V (P, Q)) p.1 (V (P, Q))).comp
      (mfderiv (𝓘(ℝ, CI4 × CI4)) (𝓡 3) V (P, Q))) (P, Q) := by
    rw [hCdef]
    exact ci_hasFDerivAt_chartAt_comp_gen V p.1 hVmd hVsrc
  have hCdiff : DifferentiableAt ℝ C (P, Q) := hCd.differentiableAt
  have hGdiff : DifferentiableAt ℝ (fun z : CI4 × CI4 => chr p (encFamQ0₀ H c₀ z.1 z.2 x))
      (P, Q) := by
    rw [hGfun]
    exact psiLin.differentiableAt.comp (P, Q) (hCdiff.prodMk (differentiableAt_const c₀))
  -- the change of coordinates is onto
  set cstar : CIP3 := V (P, Q) with hcstardef
  set tcc' : CI3 →L[ℝ] CI3 := tangentCoordChange (𝓡 3) p.1 cstar cstar with htcc'def
  have hcstar_src : cstar ∈ (extChartAt (𝓡 3) p.1).source := by
    rw [extChartAt_source]; exact hVsrc
  have htcc_surj : Function.Surjective (tangentCoordChange (𝓡 3) (V (P, Q)) p.1 (V (P, Q))) := by
    intro v
    refine ⟨tcc' v, ?_⟩
    have h : cstar ∈ (extChartAt (𝓡 3) p.1).source ∩ (extChartAt (𝓡 3) cstar).source ∩
        (extChartAt (𝓡 3) p.1).source := ⟨⟨hcstar_src, mem_extChartAt_source cstar⟩, hcstar_src⟩
    have h2 := tangentCoordChange_comp (I := 𝓡 3) (w := p.1) (x := cstar) (y := p.1) (z := cstar)
      (v := v) h
    rw [tangentCoordChange_self (I := 𝓡 3) (x := p.1) (z := cstar) hcstar_src] at h2
    simpa only [hcstardef, htcc'def] using h2
  -- the one-variable class map V₁ and the charted C₁
  have hV₁surj : Function.Surjective (mfderiv (𝓡 4) (𝓡 3)
      (fun w : CI4 => classMap (β • w) (H (x 2, shear Q u))) P) := by
    have hV₁eq : (fun w : CI4 => classMap (β • w) (H (x 2, shear Q u)))
        = (fun t : CI4 => classMap t (H (x 2, shear Q u))) ∘ (fun w : CI4 => β • w) := by
      funext w; rfl
    rw [hV₁eq]
    have hsm_md : MDifferentiableAt (𝓡 4) (𝓡 4) (fun w : CI4 => β • w) P :=
      ((β • ContinuousLinearMap.id ℝ CI4).differentiableAt (x := P)).mdifferentiableAt
    have hcl_md : MDifferentiableAt (𝓡 4) (𝓡 3)
        (fun t : CI4 => classMap t (H (x 2, shear Q u))) (β • P) :=
      (contMDiffAt_classMap_param (H (x 2, shear Q u)) (β • P)).mdifferentiableAt (by simp)
    rw [mfderiv_comp (f := fun w : CI4 => β • w)
      (g := fun t : CI4 => classMap t (H (x 2, shear Q u))) P hcl_md hsm_md]
    exact (ci_surjective_mfderiv_classMap_param (H (x 2, shear Q u)) (β • P)).comp
      (ci_surjective_mfderiv_smul_id β hβ' P)
  have hC₁range : (fderiv ℝ (fun w : CI4 =>
      chartAt CI3 p.1 (classMap (β • w) (H (x 2, shear Q u)))) P).range = ⊤ := by
    have hsrc₁ : classMap (β • P) (H (x 2, shear Q u)) ∈ (chartAt CI3 p.1).source := hVsrc
    have hmd₁ : MDifferentiableAt (𝓡 4) (𝓡 3)
        (fun w : CI4 => classMap (β • w) (H (x 2, shear Q u))) P := by
      have hV₁eq : (fun w : CI4 => classMap (β • w) (H (x 2, shear Q u)))
          = (fun t : CI4 => classMap t (H (x 2, shear Q u))) ∘ (fun w : CI4 => β • w) := by
        funext w; rfl
      rw [hV₁eq]
      have hsm_md : MDifferentiableAt (𝓡 4) (𝓡 4) (fun w : CI4 => β • w) P :=
        ((β • ContinuousLinearMap.id ℝ CI4).differentiableAt (x := P)).mdifferentiableAt
      have hcl_md : MDifferentiableAt (𝓡 4) (𝓡 3)
          (fun t : CI4 => classMap t (H (x 2, shear Q u))) (β • P) :=
        (contMDiffAt_classMap_param (H (x 2, shear Q u)) (β • P)).mdifferentiableAt (by simp)
      exact hcl_md.comp P hsm_md
    have hcomp := ci_hasFDerivAt_chartAt_comp_gen
      (fun w : CI4 => classMap (β • w) (H (x 2, shear Q u))) p.1 hmd₁ hsrc₁
    rw [hcomp.fderiv]
    rw [show ((tangentCoordChange (𝓡 3) (classMap (β • P) (H (x 2, shear Q u))) p.1
            (classMap (β • P) (H (x 2, shear Q u)))).comp
          (mfderiv (𝓡 4) (𝓡 3) (fun w : CI4 => classMap (β • w) (H (x 2, shear Q u))) P)).range
        = Submodule.map (tangentCoordChange (𝓡 3) (classMap (β • P) (H (x 2, shear Q u))) p.1
            (classMap (β • P) (H (x 2, shear Q u)))).toLinearMap
            (mfderiv (𝓡 4) (𝓡 3) (fun w : CI4 => classMap (β • w) (H (x 2, shear Q u))) P).range
        from LinearMap.range_comp _ _]
    rw [LinearMap.range_eq_top.mpr hV₁surj, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr htcc_surj
  have hslice_link : (fderiv ℝ (fun w : CI4 =>
      chartAt CI3 p.1 (classMap (β • w) (H (x 2, shear Q u)))) P).range
      ≤ (fderiv ℝ C (P, Q)).range := by
    set inj : CI4 → (CI4 × CI4) := fun t => (t, Q) with hinjdef
    set lin : CI4 →L[ℝ] (CI4 × CI4) := (ContinuousLinearMap.id ℝ CI4).prod (0 : CI4 →L[ℝ] CI4)
      with hlindef
    have hinj_diff : DifferentiableAt ℝ inj P := by
      rw [hinjdef]; exact differentiableAt_id.prodMk (differentiableAt_const Q)
    have hinj_deriv : HasFDerivAt inj lin P := by
      rw [hinjdef, hlindef]
      exact (hasFDerivAt_id (x := P)).prodMk (hasFDerivAt_const Q P)
    have hfun : C ∘ inj
        = fun w : CI4 => chartAt CI3 p.1 (classMap (β • w) (H (x 2, shear Q u))) := by
      funext w
      simp only [Function.comp_def, hinjdef, hCdef, hVdef]
    have hchain : fderiv ℝ (C ∘ inj) P = (fderiv ℝ C (P, Q)).comp lin := by
      rw [fderiv_comp (f := inj) (g := C) P hCdiff hinj_diff, hinj_deriv.fderiv]
    rw [← hfun, hchain]
    rintro y ⟨x, rfl⟩
    exact ⟨lin x, rfl⟩
  have hCrange : (fderiv ℝ C (P, Q)).range = ⊤ := le_antisymm le_top (hC₁range ▸ hslice_link)
  have hGrangef : (fderiv ℝ (fun z : CI4 × CI4 => psiLin (C z, c₀)) (P, Q)).range =
      lift0 (⊤ : Submodule ℝ CI3) := by
    rw [ci_range_fderiv_psiLin_prod_const_gen C (P, Q) c₀ hCdiff, hCrange]
  exact ⟨hGdiff, by rw [hGfun]; exact hGrangef⟩

/-! ## The Case-I assembly -/

/-- **The Case-I assembly.**  Unlike Case II, the class perturbation `p` of block `0` is alive, so its
reach is the whole class space at level `0` (`lift0 ⊤`) and only `PairReg` at the meet is needed for
the coset condition. -/
private theorem caseI_body
    (H : ℝ × CI2 → CIP3)
    (A B : CI2 → CIP3)
    (c₀ : ℝ) (hc₀0 : 0 < c₀) (hc₀1 : c₀ < 1)
    (hAsm : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hBsm : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) B)
    (hfoldA : FoldFlat A) (hfoldB : FoldFlat B)
    (hpair : PairReg A B)
    (hHsm : ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : CI3 => H (x 2, mk2 (x 0) (x 1))))
    (p : CIP3 × ℝ) (t : EncParQ0) (y : EuclideanSpace ℝ (Fin 9))
    (u₀ u₁ u₂ : CI2) (v₁ v₂ : ℝ)
    (hu₀ : pt2 ((TParity.bPartC 0 y) 0) ((TParity.bPartC 0 y) 1) = u₀)
    (hu₁ : pt2 ((TParity.bPartC 1 y) 0) ((TParity.bPartC 1 y) 1) = u₁)
    (hu₂ : pt2 ((TParity.bPartC 2 y) 0) ((TParity.bPartC 2 y) 1) = u₂)
    (hv₁ : (TParity.bPartC 1 y) 2 = v₁) (hv₂ : (TParity.bPartC 2 y) 2 = v₂)
    (hsrc : ∀ k : Fin 3, encFamQ0 H A B c₀ t k (TParity.bPartC k y) ∈ (chr p).source)
    (hzero : TParity.chartDiff3 p (encFamQ0 H A B c₀ t) y = 0)
    (hβ : betaG ((TParity.bPartC 0 y) 2) ≠ 0) :
    Function.Surjective
      (fderiv ℝ (fun t' => TParity.chartDiff3 p (encFamQ0 H A B c₀ t') y) t) := by
  -- (0) the meet
  have hmeet : TParity.meet3 (encFamQ0 H A B c₀ t) y :=
    (TParity.chartDiff3_eq_zero_iff (p := p) (D := encFamQ0 H A B c₀ t) (x := y) hsrc).mp hzero
  -- (1) the value-level identifications of the three blocks
  have hval0 : ∀ t' : EncParQ0, encFamQ0 H A B c₀ t' 0 (TParity.bPartC 0 y)
      = (clsSh (chartPert (betaG ((TParity.bPartC 0 y) 2) • q0P t')
          (capOf (H ((TParity.bPartC 0 y) 2, shear (q0Q0 t')
            (pt2 ((TParity.bPartC 0 y) 0) ((TParity.bPartC 0 y) 1)))))), c₀) := by
    intro t'
    simp only [encFamQ0_apply_zero, encFamQ0₀]
  have hval1 : ∀ t' : EncParQ0, encFamQ0 H A B c₀ t' 1 (TParity.bPartC 1 y)
      = (A (shear (q0Q1 t') u₁), thetaS (q0R1 t') v₁) := by
    intro t'
    simp only [encFamQ0_apply_one, hu₁, hv₁]
  have hval2 : ∀ t' : EncParQ0, encFamQ0 H A B c₀ t' 2 (TParity.bPartC 2 y)
      = (B (shear (q0Q2 t') u₂), thetaS (q0R2 t') v₂) := by
    intro t'
    simp only [encFamQ0_apply_two, hu₂, hv₂]
  -- (2) the class and level equalities at the meet
  set cstar : CIP3 := (encFamQ0₀ H c₀ (q0P t) (q0Q0 t) (TParity.bPartC 0 y)).1
    with hcstardef
  have hclass1 : A (shear (q0Q1 t) u₁) = cstar := by
    have h := congrArg Prod.fst hmeet.1
    rw [hval0 t, hval1 t] at h
    exact h.symm
  have hclass2 : B (shear (q0Q2 t) u₂) = cstar := by
    have h := congrArg Prod.fst hmeet.2
    rw [hval0 t, hval2 t] at h
    exact h.symm
  have hlevel1 : thetaS (q0R1 t) v₁ = c₀ := by
    have h := congrArg Prod.snd hmeet.1
    rw [hval0 t, hval1 t] at h
    exact h.symm
  have hlevel2 : thetaS (q0R2 t) v₂ = c₀ := by
    have h := congrArg Prod.snd hmeet.2
    rw [hval0 t, hval2 t] at h
    exact h.symm
  -- (3) the sources of the projective chart
  have hsrcC0 : encFamQ0₀ H c₀ (q0P t) (q0Q0 t) (TParity.bPartC 0 y) ∈ (chr p).source := by
    have h := hsrc 0
    rwa [encFamQ0_apply_zero] at h
  have hsrcC1 : A (shear (q0Q1 t) u₁) ∈ (chartAt CI3 p.1).source := by
    have h := hsrc 1
    rw [hval1 t] at h
    exact q0_fst_mem_source h
  have hsrcC2 : B (shear (q0Q2 t) u₂) ∈ (chartAt CI3 p.1).source := by
    have h := hsrc 2
    rw [hval2 t] at h
    exact q0_fst_mem_source h
  -- (4) the block maps on the parameter space
  have hblock0fun : (fun t' : EncParQ0 =>
        chr p (encFamQ0₀ H c₀ (q0P t') (q0Q0 t') (TParity.bPartC 0 y)))
      = (fun t' : EncParQ0 => chr p (encFamQ0 H A B c₀ t' 0 (TParity.bPartC 0 y))) := by
    funext t'
    simp only [encFamQ0_apply_zero]
  have hblock1fun : (fun t' : EncParQ0 =>
        chr p (A (shear (q0Q1CLM t') u₁), thetaS (q0R1CLM t') v₁))
      = (fun t' : EncParQ0 => chr p (encFamQ0 H A B c₀ t' 1 (TParity.bPartC 1 y))) := by
    funext t'
    simp only [hval1 t', q0Q1CLM_apply, q0R1CLM_apply]
  have hblock2fun : (fun t' : EncParQ0 =>
        chr p (B (shear (q0Q2CLM t') u₂), thetaS (q0R2CLM t') v₂))
      = (fun t' : EncParQ0 => chr p (encFamQ0 H A B c₀ t' 2 (TParity.bPartC 2 y))) := by
    funext t'
    simp only [hval2 t', q0Q2CLM_apply, q0R2CLM_apply]
  -- (5) the parameter derivatives of the three blocks
  set E₀ : (CI4 × CI4) →L[ℝ] Tgt 4 :=
    fderiv ℝ (fun z : CI4 × CI4 =>
      chr p (encFamQ0₀ H c₀ z.1 z.2 (TParity.bPartC 0 y))) (q0P t, q0Q0 t) with hE₀def
  set E₁ : (CI4 × ℝ) →L[ℝ] Tgt 4 :=
    fderiv ℝ (fun z : CI4 × ℝ => chr p (A (shear z.1 u₁), thetaS z.2 v₁)) (q0Q1 t, q0R1 t)
    with hE₁def
  set E₂ : (CI4 × ℝ) →L[ℝ] Tgt 4 :=
    fderiv ℝ (fun z : CI4 × ℝ => chr p (B (shear z.1 u₂), thetaS z.2 v₂)) (q0Q2 t, q0R2 t)
    with hE₂def
  set D0 : EncParQ0 →L[ℝ] Tgt 4 := E₀.comp ciQ0Prj with hD0def
  set D1 : EncParQ0 →L[ℝ] Tgt 4 := E₁.comp (q0Q1CLM.prod q0R1CLM) with hD1def
  set D2 : EncParQ0 →L[ℝ] Tgt 4 := E₂.comp (q0Q2CLM.prod q0R2CLM) with hD2def
  obtain ⟨hE₀diff, hE₀rangef⟩ :=
    chart_block0_alive_aux H (TParity.bPartC 0 y) c₀ p (q0P t) (q0Q0 t) hHsm hβ hsrcC0
  have hD0 : HasFDerivAt
      (fun t' : EncParQ0 => chr p (encFamQ0 H A B c₀ t' 0 (TParity.bPartC 0 y))) D0 t := by
    have h0 := hE₀diff.hasFDerivAt.comp t ciQ0Prj.hasFDerivAt
    simp only [Function.comp_def, ciQ0Prj_apply] at h0
    rw [hblock0fun] at h0
    exact h0
  have hD1 : HasFDerivAt
      (fun t' : EncParQ0 => chr p (encFamQ0 H A B c₀ t' 1 (TParity.bPartC 1 y))) D1 t := by
    have h1 := (differentiableAt_chr_planeBlock A hAsm u₁ (q0Q1 t) (q0R1 t) v₁ p hsrcC1).hasFDerivAt.comp
      t (q0Q1CLM.prod q0R1CLM).hasFDerivAt
    simp only [Function.comp_def, ContinuousLinearMap.prod_apply] at h1
    rw [hblock1fun] at h1
    exact h1
  have hD2 : HasFDerivAt
      (fun t' : EncParQ0 => chr p (encFamQ0 H A B c₀ t' 2 (TParity.bPartC 2 y))) D2 t := by
    have h2 := (differentiableAt_chr_planeBlock B hBsm u₂ (q0Q2 t) (q0R2 t) v₂ p hsrcC2).hasFDerivAt.comp
      t (q0Q2CLM.prod q0R2CLM).hasFDerivAt
    simp only [Function.comp_def, ContinuousLinearMap.prod_apply] at h2
    rw [hblock2fun] at h2
    exact h2
  -- (6) the change of coordinates and the three reaches
  set tcc : CI3 →L[ℝ] CI3 := tangentCoordChange (𝓡 3) cstar p.1 cstar with htccdef
  set tcc' : CI3 →L[ℝ] CI3 := tangentCoordChange (𝓡 3) p.1 cstar cstar with htcc'def
  set rA : Submodule ℝ CI3 := (mfderiv (𝓡 2) (𝓡 3) A (shear (q0Q1 t) u₁)).range with hrAdef
  set rB : Submodule ℝ CI3 := (mfderiv (𝓡 2) (𝓡 3) B (shear (q0Q2 t) u₂)).range with hrBdef
  set A' : Submodule ℝ CI3 := Submodule.map tcc.toLinearMap rA with hA'def
  set B' : Submodule ℝ CI3 := Submodule.map tcc.toLinearMap rB with hB'def
  have hcstar_src : cstar ∈ (extChartAt (𝓡 3) p.1).source := by
    rw [extChartAt_source]
    exact q0_fst_mem_source hsrcC0
  have htcc'_tcc : ∀ v : CI3, tcc' (tcc v) = v := by
    intro v
    have h : cstar ∈ (extChartAt (𝓡 3) cstar).source ∩ (extChartAt (𝓡 3) p.1).source ∩
        (extChartAt (𝓡 3) cstar).source :=
      ⟨⟨mem_extChartAt_source cstar, hcstar_src⟩, mem_extChartAt_source cstar⟩
    have h2 := tangentCoordChange_comp (I := 𝓡 3) (w := cstar) (x := p.1) (y := cstar) (z := cstar)
      (v := v) h
    rw [tangentCoordChange_self (I := 𝓡 3) (x := cstar) (z := cstar)
      (mem_extChartAt_source cstar)] at h2
    simpa only [htccdef, htcc'def] using h2
  have htcc_tcc' : ∀ v : CI3, tcc (tcc' v) = v := by
    intro v
    have h : cstar ∈ (extChartAt (𝓡 3) p.1).source ∩ (extChartAt (𝓡 3) cstar).source ∩
        (extChartAt (𝓡 3) p.1).source :=
      ⟨⟨hcstar_src, mem_extChartAt_source cstar⟩, hcstar_src⟩
    have h2 := tangentCoordChange_comp (I := 𝓡 3) (w := p.1) (x := cstar) (y := p.1) (z := cstar)
      (v := v) h
    rw [tangentCoordChange_self (I := 𝓡 3) (x := p.1) (z := cstar) hcstar_src] at h2
    simpa only [htccdef, htcc'def] using h2
  have htcc_surj : Function.Surjective tcc := fun v => ⟨tcc' v, htcc_tcc' v⟩
  obtain ⟨hfA0, hfA1⟩ := (foldFlat_iff A).mp hfoldA
  obtain ⟨hfB0, hfB1⟩ := (foldFlat_iff B).mp hfoldB
  have hderiv1 : deriv (fun r' : ℝ => thetaS r' v₁) (q0R1 t) ≠ 0 :=
    deriv_thetaS_ne_zero_of_eq v₁ (q0R1 t) c₀ hc₀0 hc₀1 hlevel1
  have hderiv2 : deriv (fun r' : ℝ => thetaS r' v₂) (q0R2 t) ≠ 0 :=
    deriv_thetaS_ne_zero_of_eq v₂ (q0R2 t) c₀ hc₀0 hc₀1 hlevel2
  have hE₀range : E₀.range = lift0 (⊤ : Submodule ℝ CI3) := by
    rw [hE₀def]
    exact hE₀rangef
  have hE₁range : E₁.range = liftAll A' := by
    have h := range_fderiv_chart_planeBlock A u₁ (q0Q1 t) (q0R1 t) v₁ p hAsm hfA0 hfA1 hderiv1 hsrcC1
    rw [hE₁def]
    rw [hclass1] at h
    simpa only [hA'def, htccdef, hrAdef] using h
  have hE₂range : E₂.range = liftAll B' := by
    have h := range_fderiv_chart_planeBlock B u₂ (q0Q2 t) (q0R2 t) v₂ p hBsm hfB0 hfB1 hderiv2 hsrcC2
    rw [hE₂def]
    rw [hclass2] at h
    simpa only [hB'def, htccdef, hrBdef] using h
  have hD0range : D0.range = lift0 (⊤ : Submodule ℝ CI3) := by
    have hle1 : (E₀.comp ciQ0Prj).range ≤ E₀.range := by
      rintro y ⟨u, rfl⟩
      exact ⟨ciQ0Prj u, rfl⟩
    have hle2 : E₀.range ≤ (E₀.comp ciQ0Prj).range := by
      rintro y ⟨w, rfl⟩
      obtain ⟨u, rfl⟩ := surjective_ciQ0Prj w
      exact ⟨u, rfl⟩
    rw [hD0def]
    exact (le_antisymm hle1 hle2).trans hE₀range
  have hD1range : D1.range = liftAll A' := by
    have hle1 : (E₁.comp (q0Q1CLM.prod q0R1CLM)).range ≤ E₁.range := by
      rintro y ⟨u, rfl⟩
      exact ⟨(q0Q1CLM.prod q0R1CLM) u, rfl⟩
    have hle2 : E₁.range ≤ (E₁.comp (q0Q1CLM.prod q0R1CLM)).range := by
      rintro y ⟨w, rfl⟩
      obtain ⟨u, rfl⟩ := surjective_q0Q1R1 w
      exact ⟨u, rfl⟩
    rw [hD1def]
    exact (le_antisymm hle1 hle2).trans hE₁range
  have hD2range : D2.range = liftAll B' := by
    have hle1 : (E₂.comp (q0Q2CLM.prod q0R2CLM)).range ≤ E₂.range := by
      rintro y ⟨u, rfl⟩
      exact ⟨(q0Q2CLM.prod q0R2CLM) u, rfl⟩
    have hle2 : E₂.range ≤ (E₂.comp (q0Q2CLM.prod q0R2CLM)).range := by
      rintro y ⟨w, rfl⟩
      obtain ⟨u, rfl⟩ := surjective_q0Q2R2 w
      exact ⟨u, rfl⟩
    rw [hD2def]
    exact (le_antisymm hle1 hle2).trans hE₂range
  -- (7) the linear algebra of the reaches: `PairReg` gives `A' ⊔ B' = ⊤`
  have hAB : A' ⊔ B' = ⊤ := by
    have hp : rA ⊔ rB = ⊤ := hpair (shear (q0Q1 t) u₁) (shear (q0Q2 t) u₂)
      (hclass1.trans hclass2.symm)
    rw [hA'def, hB'def, ← Submodule.map_sup, hp, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr htcc_surj
  -- (8) the coset condition, realisability and the closer
  have hcoset : ∀ w₁ w₂ : Tgt 4,
      ∃ a ∈ lift0 (⊤ : Submodule ℝ CI3), a - w₁ ∈ liftAll A' ∧ a - w₂ ∈ liftAll B' :=
    fun w₁ w₂ => exists_coset_mem_lift (⊤ : Submodule ℝ CI3) A' B' hAB (by simp) w₁ w₂
  have hreal : ∀ a ∈ lift0 (⊤ : Submodule ℝ CI3), ∀ b ∈ liftAll A', ∀ c ∈ liftAll B',
      ∃ u : EncParQ0, D0 u = a ∧ D1 u = b ∧ D2 u = c := by
    intro a ha b hb c hc
    have h0 : a ∈ D0.range := by rw [hD0range]; exact ha
    have h1 : b ∈ D1.range := by rw [hD1range]; exact hb
    have h2 : c ∈ D2.range := by rw [hD2range]; exact hc
    obtain ⟨u₀', hu₀'⟩ := LinearMap.mem_range.mp h0
    obtain ⟨u₁', hu₁'⟩ := LinearMap.mem_range.mp h1
    obtain ⟨u₂', hu₂'⟩ := LinearMap.mem_range.mp h2
    refine ⟨q0Mix u₀' u₀' u₁' u₂', ?_, ?_, ?_⟩
    · have hmix : D0 (q0Mix u₀' u₀' u₁' u₂') = D0 u₀' := by
        rw [hD0def]
        show E₀ (ciQ0Prj (q0Mix u₀' u₀' u₁' u₂')) = E₀ (ciQ0Prj u₀')
        rw [ciQ0Prj_q0Mix_self]
      exact hmix.trans hu₀'
    · have hmix : D1 (q0Mix u₀' u₀' u₁' u₂') = D1 u₁' := by
        rw [hD1def]
        show E₁ ((q0Q1CLM.prod q0R1CLM) (q0Mix u₀' u₀' u₁' u₂')) =
          E₁ ((q0Q1CLM.prod q0R1CLM) u₁')
        rw [ContinuousLinearMap.prod_apply, ContinuousLinearMap.prod_apply,
          q0Q1CLM_q0Mix, q0R1CLM_q0Mix]
      exact hmix.trans hu₁'
    · have hmix : D2 (q0Mix u₀' u₀' u₁' u₂') = D2 u₂' := by
        rw [hD2def]
        show E₂ ((q0Q2CLM.prod q0R2CLM) (q0Mix u₀' u₀' u₁' u₂')) =
          E₂ ((q0Q2CLM.prod q0R2CLM) u₂')
        rw [ContinuousLinearMap.prod_apply, ContinuousLinearMap.prod_apply,
          q0Q2CLM_q0Mix, q0R2CLM_q0Mix]
      exact hmix.trans hu₂'
  have hsurj : Function.Surjective (fun u : EncParQ0 => (D0 u - D1 u, D0 u - D2 u)) :=
    surjective_pair_sub_of_coset D0 D1 D2 (lift0 (⊤ : Submodule ℝ CI3)) (liftAll A') (liftAll B')
      (le_of_eq hD0range) (le_of_eq hD1range) (le_of_eq hD2range) hreal hcoset
  -- (9) the derivative of the charted triple-difference map
  have hpUp_surj : Function.Surjective TParity.pUpCLM := fun w =>
    ⟨(TParity.fst8 w, TParity.snd8 w), by
      rw [TParity.pUpCLM_apply, TParity.pUp_fst8_snd8]⟩
  have hpairHD : HasFDerivAt (fun t' : EncParQ0 =>
      (((chr p) (encFamQ0 H A B c₀ t' 0 (TParity.bPartC 0 y)) -
          (chr p) (encFamQ0 H A B c₀ t' 1 (TParity.bPartC 1 y))),
        ((chr p) (encFamQ0 H A B c₀ t' 0 (TParity.bPartC 0 y)) -
          (chr p) (encFamQ0 H A B c₀ t' 2 (TParity.bPartC 2 y)))))
      ((D0 - D1).prod (D0 - D2)) t :=
    (hD0.sub hD1).prodMk (hD0.sub hD2)
  have hcompHD : HasFDerivAt (fun t' : EncParQ0 =>
      TParity.pUp
        ((chr p) (encFamQ0 H A B c₀ t' 0 (TParity.bPartC 0 y)) -
          (chr p) (encFamQ0 H A B c₀ t' 1 (TParity.bPartC 1 y)))
        ((chr p) (encFamQ0 H A B c₀ t' 0 (TParity.bPartC 0 y)) -
          (chr p) (encFamQ0 H A B c₀ t' 2 (TParity.bPartC 2 y))))
      (TParity.pUpCLM.comp ((D0 - D1).prod (D0 - D2))) t := by
    have h1 := TParity.pUpCLM.hasFDerivAt.comp t hpairHD
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t' => ?_))
    exact (TParity.pUpCLM_apply _ _).symm
  have hfinal : HasFDerivAt (fun t' => TParity.chartDiff3 p (encFamQ0 H A B c₀ t') y)
      (TParity.pUpCLM.comp ((D0 - D1).prod (D0 - D2))) t :=
    hcompHD.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t' => rfl))
  rw [hfinal.fderiv]
  exact hpUp_surj.comp hsurj

end Helpers

end

theorem surjective_paramDeriv_encFamQ0_caseI
    (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (c₀ : ℝ) (hc₀0 : 0 < c₀) (hc₀1 : c₀ < 1) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) :=
      Work.Drive.projCharted 3
    letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Projectivization ℝ (Eucl 3)) :=
      Work.Drive.isManifold_projCharted 3
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) (Projectivization ℝ (Eucl 3) × ℝ) :=
      Work.Drive.projTimesLineCharted
    letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Projectivization ℝ (Eucl 3) × ℝ) :=
      Work.Drive.isManifold_projTimesLineCharted
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => H (x 2, mk2 (x 0) (x 1))) →
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞) A →
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞) B →
    Work.Drive.FoldFlat A → Work.Drive.FoldFlat B →
    Work.Drive.PairReg A B →
    (p : Projectivization ℝ (Eucl 3) × ℝ) → (t : Work.Drive.EncParQ0) →
    (y : EuclideanSpace ℝ (Fin 9)) →
    (∀ k : Fin 3, Work.Drive.encFamQ0 H A B c₀ t k (Work.Drive.TParity.bPartC k y)
      ∈ (Work.Drive.chr p).source) →
    Work.Drive.TParity.chartDiff3 p (Work.Drive.encFamQ0 H A B c₀ t) y = 0 →
    Work.Drive.betaG ((Work.Drive.TParity.bPartC 0 y) 2) ≠ 0 →
    Function.Surjective
      (fderiv ℝ (fun t' => Work.Drive.TParity.chartDiff3 p
        (Work.Drive.encFamQ0 H A B c₀ t') y) t) := by
  intro hHsm hAsm hBsm hfoldA hfoldB hpair p t y9 hsrc hzero hbeta
  exact caseI_body H A B c₀ hc₀0 hc₀1 hAsm hBsm hfoldA hfoldB hpair hHsm p t y9
    (pt2 ((TParity.bPartC 0 y9) 0) ((TParity.bPartC 0 y9) 1))
    (pt2 ((TParity.bPartC 1 y9) 0) ((TParity.bPartC 1 y9) 1))
    (pt2 ((TParity.bPartC 2 y9) 0) ((TParity.bPartC 2 y9) 1))
    ((TParity.bPartC 1 y9) 2) ((TParity.bPartC 2 y9) 2)
    rfl rfl rfl rfl rfl hsrc hzero hbeta

end Work.Drive
