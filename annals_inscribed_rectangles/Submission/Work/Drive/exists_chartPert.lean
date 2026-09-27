import Mathlib
import Submission.Work.Drive.sideGerm
import Submission.Work.Drive.chartPertData
import Submission.Work.Drive.fderiv_chartAt_halfLineProjective_gen
import Submission.Work.Drive.contDiffAt_projCoordFun_classEquiv
import Submission.Work.Drive.contMDiffAt_classMap_prod
import Submission.Work.Drive.contMDiff_rotCapping_family

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# The `ChartPert` instance

`Work.Drive.ChartPert Q m Ξ` (`Submission/Work/Drive/sideGerm.lean`) asks for a smooth `m`-parameter
family of self-maps of the capping space `Y = Work.Drive.CappingSpace` with `Ξ 0 = id` whose
parameter-derivative is onto at every parameter and every point of the chart's disk.  This file
provides the instance, with `m = 4`:

`Ξ t p = Φ⁻¹ (exp (exp⁻¹ r + t 0), [(1 + L (t)) v])` for `Φ p = (r, [v])`, where `Φ` is the
homeomorphism `Work.Drive.cappingSpaceHomeoProj : CappingSpace ≃ₜ (0,∞) × ℝP³` and `L (t)` is left
multiplication by the imaginary quaternion with coordinates `(t 1, t 2, t 3)`
(`Submission/Work/Drive/chartPertData.lean`).

The two mathematical facts that make the construction work are

* `Work.Drive.classGen_classGen` (`L (t) ∘ L (t) = -‖t‖²`, whence `1 + L (t)` is an isomorphism with
  an explicit inverse), and
* `Work.Drive.classDeriv_surjective` (`Submission/Work/Drive/chartPertData.lean`): the class
  directions at `t` span a complement of the line of the image point, so the class component of the
  parameter-derivative is onto — the level component supplies the fourth direction.

Smoothness of the family is `Work.Drive.contMDiffAt_chartPert`, which reduces along `Φ` to the
componentwise criterion `Work.Drive.contMDiffAt_halfLineProjective_iff_general`
(`Submission/Work/Drive/contMDiffAt_halfLineProjective_iff_general.lean`), the level component being
the (smooth) sum `exp⁻¹ r + t 0` and the class component being the smooth action
`Work.Drive.contMDiffAt_classMap_prod` (`Submission/Work/Drive/contMDiffAt_classMap_prod.lean`).
-/

namespace Work.Drive

open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Manifold Topology Filter

noncomputable section

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.projCharted

instance : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Set.Ioi (0 : ℝ)) :=
  Homeomorph.chartedSpace expHomeo

instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) := projCharted 3

instance : ChartedSpace (EuclideanSpace ℝ (Fin 4))
    (Set.Ioi (0:ℝ) × Projectivization ℝ (Eucl 3)) := halfLineProjectiveCharted

set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-! ## Auxiliary facts -/

lemma eucl1_eq_smul_e1 (y : EuclideanSpace ℝ (Fin 1)) :
    y = (y.ofLp 0) • (e1 : EuclideanSpace ℝ (Fin 1)) := by
  refine WithLp.ofLp_injective 2 ?_
  funext i
  fin_cases i
  simp [e1, WithLp.ofLp_toLp]

lemma cproj_smulRight_e1_apply (s : Eucl 3) :
    ((cproj 0).smulRight (e1 : EuclideanSpace ℝ (Fin 1))) s = (s 0) • (e1 : EuclideanSpace ℝ (Fin 1)) := by
  rw [ContinuousLinearMap.smulRight_apply, cproj, PiLp.proj_apply]

/-- The bridge: the manifold derivative of a curve into the capping space is the Fréchet derivative
of its chart expression at its own point. -/
theorem mfderiv_eq_fderiv_chartAt (G : Eucl 3 → CappingSpace) (t : Eucl 3)
    (hG : ContMDiff (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) G) :
    mfderiv (𝓡 4) (𝓡 4) G t
      = fderiv ℝ (fun s => chartAt (EuclideanSpace ℝ (Fin 4)) (G t) (G s)) t := by
  have h : MDifferentiableAt (𝓡 4) (𝓡 4) G t := (hG t).mdifferentiableAt (by simp)
  have hw : writtenInExtChartAt (𝓡 4) (𝓡 4) t G
      = fun s : Eucl 3 => chartAt (EuclideanSpace ℝ (Fin 4)) (G t) (G s) := by
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

/-- The charted derivative of the level scaling is the first coordinate. -/
lemma fderiv_chartAt_levelScale (x : Set.Ioi (0 : ℝ)) (t : Eucl 3) :
    fderiv ℝ (fun s : Eucl 3 =>
        chartAt (EuclideanSpace ℝ (Fin 1)) (levelScale t x) (levelScale s x)) t
      = (cproj 0).smulRight (e1 : EuclideanSpace ℝ (Fin 1)) := by
  have hcont : ContinuousAt (fun s : Eucl 3 => levelScale s x) t :=
    (expHomeo.continuous.continuousAt.comp (by
      have : ContinuousAt (fun s : Eucl 3 =>
          expHomeo.symm x + (s 0) • (e1 : EuclideanSpace ℝ (Fin 1))) t := by fun_prop
      exact this)).congr (Filter.Eventually.of_forall (fun s => by simp [levelScale]))
  have hev : (fun s : Eucl 3 =>
        chartAt (EuclideanSpace ℝ (Fin 1)) (levelScale t x) (levelScale s x))
      =ᶠ[𝓝 t] (fun s : Eucl 3 =>
        chartAt (EuclideanSpace ℝ (Fin 1)) (expHomeo.symm (levelScale t x))
          (expHomeo.symm (levelScale s x))) :=
    eventuallyEq_chartAt_homeomorph_chartedSpace_self expHomeo (fun s => levelScale s x) t hcont
  rw [hev.fderiv_eq]
  have hid : (fun s : Eucl 3 =>
        chartAt (EuclideanSpace ℝ (Fin 1)) (expHomeo.symm (levelScale t x))
          (expHomeo.symm (levelScale s x)))
      = fun s : Eucl 3 => expHomeo.symm (levelScale s x) := by
    funext s
    rw [chartAt_self_eq, OpenPartialHomeomorph.refl_apply]
    rfl
  rw [hid, fderiv_expHomeo_symm_levelScale]

/-- The chart of `classMap t q` in the transparent projective structure. -/
lemma classMap_rep_eq (t : Eucl 3) (q : Projectivization ℝ (Eucl 3)) :
    classMap t q
      = Projectivization.mk ℝ (classEquiv t q.rep) (classEquiv_ne_zero q.rep_nonzero) := by
  conv_lhs => rw [← Projectivization.mk_rep q]
  exact classMap_mk t q.rep q.rep_nonzero

/-- The `i`-th coordinate of the representative of a point of the `i`-th projective chart is
non-zero. -/
lemma classEquiv_ofLp_chartIndexOf_ne_zero (t : Eucl 3) (q : Projectivization ℝ (Eucl 3)) :
    (classEquiv t q.rep).ofLp (projChartIndexOf (classMap t q)) ≠ 0 := by
  have hmem : Projectivization.mk ℝ (classEquiv t q.rep) (classEquiv_ne_zero q.rep_nonzero)
      ∈ projChartSource (projChartIndexOf (classMap t q)) := by
    rw [← classMap_rep_eq t q]
    exact projChartIndexOf_spec (n := 3) (classMap t q)
  exact (mem_projChartSource_iff' (classEquiv_ne_zero q.rep_nonzero)).mp hmem

/-- The `j`-th coordinate of the representative of a point of the `j`-th projective chart is
non-zero. -/
lemma classEquiv_ofLp_ne_zero {t : Eucl 3} {q : Projectivization ℝ (Eucl 3)} {j : Fin 4}
    (hj : classMap t q ∈ projChartSource j) : (classEquiv t q.rep).ofLp j ≠ 0 := by
  have hmem : Projectivization.mk ℝ (classEquiv t q.rep) (classEquiv_ne_zero q.rep_nonzero)
      ∈ projChartSource j := by
    rw [← classMap_rep_eq t q]
    exact hj
  exact (mem_projChartSource_iff' (classEquiv_ne_zero q.rep_nonzero)).mp hmem

/-- Smoothness of the class family in the parameter. -/
lemma contMDiffAt_classMap_param (q : Projectivization ℝ (Eucl 3)) (t : Eucl 3) :
    ContMDiffAt (𝓡 4) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun s : Eucl 3 => classMap s q) t := by
  set F₂ : Eucl 3 × Projectivization ℝ (Eucl 3) → Projectivization ℝ (Eucl 3) :=
    fun u => classMap u.1 u.2 with hF₂
  have h1 : ContMDiffAt (𝓡 4) ((𝓡 4).prod (𝓡 3)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun s : Eucl 3 => (s, q)) t :=
    ContMDiffAt.prodMk contMDiffAt_id (contMDiffAt_const (c := q))
  have h2 : ContMDiffAt ((𝓡 4).prod (𝓡 3)) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) F₂ (t, q) := by
    have h := contMDiffAt_classMap_prod t q
    simpa only [hF₂] using h
  have hcomp := h2.comp t h1
  simpa only [F₂, Function.comp_def] using hcomp

/-- The charted derivative of the class family: the projective chart differential composed with the
class evaluation. -/
lemma fderiv_chartAt_classMap (q : Projectivization ℝ (Eucl 3)) (t : Eucl 3) :
    fderiv ℝ (fun s : Eucl 3 =>
        chartAt (EuclideanSpace ℝ (Fin 3)) (classMap t q) (classMap s q)) t
      = (projCoordFunDerivE (projChartIndexOf (classMap t q)) (classEquiv t q.rep)).comp
        (classEvalCLM q.rep) := by
  have hchart : (chartAt (EuclideanSpace ℝ (Fin 3)) (classMap t q) :
      OpenPartialHomeomorph (Projectivization ℝ (Eucl 3)) (EuclideanSpace ℝ (Fin 3)))
      = projChart (projChartIndexOf (classMap t q)) :=
    projCharted_chartAt_eq_projChart (classMap t q)
  have hfun : (fun s : Eucl 3 =>
        chartAt (EuclideanSpace ℝ (Fin 3)) (classMap t q) (classMap s q))
      = fun s : Eucl 3 => projCoordFun (projChartIndexOf (classMap t q))
          (classEquiv s q.rep) := by
    funext s
    rw [hchart, projChart_apply, classMap_rep_eq s q]
    exact projChartMap_mk _ _ _
  rw [hfun]
  have h2 : HasFDerivAt (projCoordFun (projChartIndexOf (classMap t q)))
      (projCoordFunDerivE (projChartIndexOf (classMap t q)) (classEquiv t q.rep))
      (classEquiv t q.rep) :=
    hasFDerivAt_projCoordFun (classEquiv_ofLp_chartIndexOf_ne_zero t q)
  have h1 : HasFDerivAt (fun s : Eucl 3 => classEquiv s q.rep) (classEvalCLM q.rep) t :=
    hasFDerivAt_classEquiv t q.rep
  have h := h2.comp t h1
  simp only [Function.comp_def] at h
  rw [h.fderiv]

/-- **The pair (level, class) is onto.**  The level direction (the first coordinate of the parameter)
and the class directions (the last three) are independent, and each of the two maps is onto. -/
theorem surjective_prod_level_class (x : Set.Ioi (0 : ℝ)) (q : Projectivization ℝ (Eucl 3))
    (t : Eucl 3) :
    Function.Surjective
      (((cproj 0).smulRight (e1 : EuclideanSpace ℝ (Fin 1))).prod
        ((projCoordFunDerivE (projChartIndexOf (classMap t q)) (classEquiv t q.rep)).comp
          (classEvalCLM q.rep))) := by
  have hjw : (classEquiv t q.rep).ofLp (projChartIndexOf (classMap t q)) ≠ 0 :=
    classEquiv_ofLp_chartIndexOf_ne_zero t q
  intro y
  obtain ⟨s', hs'⟩ := classDeriv_surjective q.rep_nonzero t
    (projChartIndexOf (classMap t q)) hjw y.2
  refine ⟨s' + (y.1.ofLp 0 - s' 0) • (e0 : Eucl 3), ?_⟩
  have hker : classEvalCLM q.rep ((y.1.ofLp 0 - s' 0) • (e0 : Eucl 3)) = 0 := by
    rw [classEvalCLM_apply, ← classEval_apply]
    exact classEval_smul_e0 q.rep _
  have h2 : ((projCoordFunDerivE (projChartIndexOf (classMap t q)) (classEquiv t q.rep)).comp
        (classEvalCLM q.rep)) (s' + (y.1.ofLp 0 - s' 0) • (e0 : Eucl 3)) = y.2 := by
    simp only [ContinuousLinearMap.comp_apply, map_add, hker, map_zero, add_zero,
      classEvalCLM_apply]
    exact hs'
  have h1 : ((cproj 0).smulRight (e1 : EuclideanSpace ℝ (Fin 1)))
      (s' + (y.1.ofLp 0 - s' 0) • (e0 : Eucl 3)) = y.1 := by
    rw [cproj_smulRight_e1_apply]
    have h0 : (s' + (y.1.ofLp 0 - s' 0) • (e0 : Eucl 3)) 0 = y.1.ofLp 0 := by
      simp [e0, WithLp.ofLp_toLp]
    rw [h0, eucl1_eq_smul_e1 y.1]
    simp [e1, WithLp.ofLp_toLp]
  rw [ContinuousLinearMap.prod_apply]
  exact Prod.ext h1 h2

/-- `HasFDerivAt` form of the charted level derivative. -/
lemma hasFDerivAt_chartAt_levelScale (x : Set.Ioi (0 : ℝ)) (t : Eucl 3) :
    HasFDerivAt (fun s : Eucl 3 =>
        chartAt (EuclideanSpace ℝ (Fin 1)) (levelScale t x) (levelScale s x))
      ((cproj 0).smulRight (e1 : EuclideanSpace ℝ (Fin 1))) t := by
  have hcont : ContinuousAt (fun s : Eucl 3 => levelScale s x) t :=
    (expHomeo.continuous.continuousAt.comp (by
      have : ContinuousAt (fun s : Eucl 3 =>
          expHomeo.symm x + (s 0) • (e1 : EuclideanSpace ℝ (Fin 1))) t := by fun_prop
      exact this)).congr (Filter.Eventually.of_forall (fun s => by simp [levelScale]))
  have hev : (fun s : Eucl 3 =>
        chartAt (EuclideanSpace ℝ (Fin 1)) (levelScale t x) (levelScale s x))
      =ᶠ[𝓝 t] (fun s : Eucl 3 =>
        chartAt (EuclideanSpace ℝ (Fin 1)) (expHomeo.symm (levelScale t x))
          (expHomeo.symm (levelScale s x))) :=
    eventuallyEq_chartAt_homeomorph_chartedSpace_self expHomeo (fun s => levelScale s x) t hcont
  have hev2 : (fun s : Eucl 3 =>
        chartAt (EuclideanSpace ℝ (Fin 1)) (expHomeo.symm (levelScale t x))
          (expHomeo.symm (levelScale s x)))
      =ᶠ[𝓝 t] (fun s : Eucl 3 => expHomeo.symm (levelScale s x)) := by
    filter_upwards with s
    rw [chartAt_self_eq, OpenPartialHomeomorph.refl_apply]
    rfl
  have hbase : HasFDerivAt (fun s : Eucl 3 => expHomeo.symm (levelScale s x))
      ((cproj 0).smulRight (e1 : EuclideanSpace ℝ (Fin 1))) t := by
    have h := HasFDerivAt.const_add (expHomeo.symm x)
      (((cproj 0).smulRight (e1 : EuclideanSpace ℝ (Fin 1))).hasFDerivAt (x := t))
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => ?_))
    simp only [ContinuousLinearMap.smulRight_apply, expHomeo_symm_levelScale, cproj,
      PiLp.proj_apply]
  exact hbase.congr_of_eventuallyEq (hev.trans hev2)

/-- `HasFDerivAt` form of the charted class derivative. -/
lemma hasFDerivAt_chartAt_classMap (q : Projectivization ℝ (Eucl 3)) (t : Eucl 3) :
    HasFDerivAt (fun s : Eucl 3 =>
        chartAt (EuclideanSpace ℝ (Fin 3)) (classMap t q) (classMap s q))
      ((projCoordFunDerivE (projChartIndexOf (classMap t q)) (classEquiv t q.rep)).comp
        (classEvalCLM q.rep)) t := by
  have hchart : (chartAt (EuclideanSpace ℝ (Fin 3)) (classMap t q) :
      OpenPartialHomeomorph (Projectivization ℝ (Eucl 3)) (EuclideanSpace ℝ (Fin 3)))
      = projChart (projChartIndexOf (classMap t q)) :=
    projCharted_chartAt_eq_projChart (classMap t q)
  have hfun : (fun s : Eucl 3 =>
        chartAt (EuclideanSpace ℝ (Fin 3)) (classMap t q) (classMap s q))
      = fun s : Eucl 3 => projCoordFun (projChartIndexOf (classMap t q))
          (classEquiv s q.rep) := by
    funext s
    rw [hchart, projChart_apply, classMap_rep_eq s q]
    exact projChartMap_mk _ _ _
  rw [hfun]
  have h2 : HasFDerivAt (projCoordFun (projChartIndexOf (classMap t q)))
      (projCoordFunDerivE (projChartIndexOf (classMap t q)) (classEquiv t q.rep))
      (classEquiv t q.rep) :=
    hasFDerivAt_projCoordFun (classEquiv_ofLp_chartIndexOf_ne_zero t q)
  have h1 : HasFDerivAt (fun s : Eucl 3 => classEquiv s q.rep) (classEvalCLM q.rep) t :=
    hasFDerivAt_classEquiv t q.rep
  have h := h2.comp t h1
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => ?_))
  simp only [Function.comp_apply]

/-- **The parameter derivative of the chart perturbation family is onto.** -/
theorem surjective_mfderiv_chartPert (p : CappingSpace)
    (hsm : ContMDiff ((𝓡 4).prod (𝓡 4)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : Eucl 3 × CappingSpace => chartPert q.1 q.2))
    (t : Eucl 3) :
    Function.Surjective (mfderiv (𝓡 4) (𝓡 4) (fun s : Eucl 3 => chartPert s p) t) := by
  -- keep the family opaque so that the elaboration does not unfold `chartPert`
  set FJ : Eucl 3 × CappingSpace → CappingSpace := fun q => chartPert q.1 q.2 with hFJ
  have hsmJ : ContMDiff ((𝓡 4).prod (𝓡 4)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) FJ := by
    rw [hFJ] at hsm ⊢
    exact hsm
  have hGJ : ContMDiff (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : Eucl 3 => FJ (s, p)) :=
    hsmJ.comp (ContMDiff.prodMk contMDiff_id contMDiff_const)
  have hfun : (fun s : Eucl 3 => chartPert s p) = fun s : Eucl 3 => FJ (s, p) := by
    funext s
    rw [hFJ]
  rw [hfun]
  rw [mfderiv_eq_fderiv_chartAt (fun s : Eucl 3 => FJ (s, p)) t hGJ]
  have hev := eventuallyEq_chartAt_homeomorph_chartedSpace_self (H := EuclideanSpace ℝ (Fin 4))
    cappingSpaceHomeoProj.symm (fun s : Eucl 3 => FJ (s, p)) t (hGJ.continuous.continuousAt)
  rw [hev.fderiv_eq]
  set x : Set.Ioi (0:ℝ) × Projectivization ℝ (Eucl 3) := cappingSpaceHomeoProj p with hx
  have hFs : ∀ s : Eucl 3, cappingSpaceHomeoProj (FJ (s, p)) = coordFam s x := by
    intro s
    rw [hFJ, hx]
    simp only [cappingSpaceHomeoProj_chartPert]
  have hchart : (fun s : Eucl 3 =>
        chartAt (EuclideanSpace ℝ (Fin 4)) (cappingSpaceHomeoProj (FJ (t, p)))
          (cappingSpaceHomeoProj (FJ (s, p))))
      = fun s : Eucl 3 =>
          chartAt (EuclideanSpace ℝ (Fin 4)) (coordFam t x) (coordFam s x) := by
    funext s
    rw [hFs s, hFs t]
  simp only [Homeomorph.symm_symm]
  rw [hchart]
  rw [fderiv_chartAt_halfLineProjective_gen (fun s : Eucl 3 => coordFam s x) t (coordFam t x)
    (by simpa only [coordFam] using (hasFDerivAt_chartAt_levelScale x.1 t).differentiableAt)
    (by simpa only [coordFam] using (hasFDerivAt_chartAt_classMap x.2 t).differentiableAt)]
  rw [show fderiv ℝ (fun u : Eucl 3 =>
        chartAt (EuclideanSpace ℝ (Fin 1)) (coordFam t x).1 (coordFam u x).1) t
      = (cproj 0).smulRight (e1 : EuclideanSpace ℝ (Fin 1)) from
    fderiv_chartAt_levelScale x.1 t]
  rw [show fderiv ℝ (fun u : Eucl 3 =>
        chartAt (EuclideanSpace ℝ (Fin 3)) (coordFam t x).2 (coordFam u x).2) t
      = (projCoordFunDerivE (projChartIndexOf (classMap t x.2)) (classEquiv t x.2.rep)).comp
          (classEvalCLM x.2.rep) from
    fderiv_chartAt_classMap x.2 t]
  have hL := surjective_prod_level_class x.1 x.2 t
  have hpsi : Function.Surjective fun z : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3) =>
      (psiEquiv : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3)) →L[ℝ]
        EuclideanSpace ℝ (Fin 4)) z :=
    fun y => ⟨psiEquiv.symm y, psiEquiv.apply_symm_apply y⟩
  exact hpsi.comp hL

/-! ## Joint smoothness of the family -/

/-- **The chart perturbation family is `C^∞` at every point.** -/
theorem contMDiffAt_chartPert (t₀ : Eucl 3) (p₀ : CappingSpace) :
    ContMDiffAt ((𝓡 4).prod (𝓡 4)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : Eucl 3 × CappingSpace => chartPert q.1 q.2) (t₀, p₀) := by
  letI : ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 4)) (EuclideanSpace ℝ (Fin 3)))
      (Eucl 3 × Projectivization ℝ (Eucl 3)) :=
    prodChartedSpace (EuclideanSpace ℝ (Fin 4)) (EuclideanSpace ℝ (Fin 4))
      (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3))
  set F : Eucl 3 × CappingSpace → CappingSpace := fun q => chartPert q.1 q.2 with hF
  set x₀ : Projectivization ℝ (Eucl 3) := (cappingSpaceHomeoProj p₀).2 with hx₀
  -- the unperturbed family and its two components
  have hG₀ : ContMDiffAt ((𝓡 4).prod (𝓡 4)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : Eucl 3 × CappingSpace => cappingSpaceHomeoProj q.2) (t₀, p₀) :=
    (contMDiffAt_cappingSpaceHomeoProj p₀).comp (t₀, p₀)
      (contMDiffAt_snd (n := ((⊤ : ℕ∞) : WithTop ℕ∞)))
  obtain ⟨hrad₀, hproj₀⟩ := (contMDiffAt_halfLineProjective_iff_general
    (((𝓡 4).prod (𝓡 4)))
    (fun q : Eucl 3 × CappingSpace => cappingSpaceHomeoProj q.2) (t₀, p₀)).mp hG₀
  -- the perturbed family, componentwise
  have hG : ContMDiffAt ((𝓡 4).prod (𝓡 4)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : Eucl 3 × CappingSpace => cappingSpaceHomeoProj (F q)) (t₀, p₀) := by
    refine (contMDiffAt_halfLineProjective_iff_general ((𝓡 4).prod (𝓡 4))
      (fun q : Eucl 3 × CappingSpace => cappingSpaceHomeoProj (F q)) (t₀, p₀)).mpr ⟨?_, ?_⟩
    · -- the level component
      have hfun : (fun q : Eucl 3 × CappingSpace =>
            expHomeo.symm ((cappingSpaceHomeoProj (F q)).1))
          = fun q : Eucl 3 × CappingSpace =>
              expHomeo.symm ((cappingSpaceHomeoProj q.2).1)
                + (q.1 0) • (e1 : EuclideanSpace ℝ (Fin 1)) := by
        funext q
        rw [hF]
        simp only [cappingSpaceHomeoProj_chartPert, coordFam_fst, expHomeo_symm_levelScale]
      rw [hfun]
      refine hrad₀.add ?_
      have hfst : ContMDiffAt ((𝓡 4).prod (𝓡 4)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : Eucl 3 × CappingSpace => q.1) (t₀, p₀) := contMDiffAt_fst
      exact ((cproj 0).smulRight (e1 : EuclideanSpace ℝ (Fin 1))).contMDiff.contMDiffAt.comp
        (t₀, p₀) hfst
    · -- the class component
      have hfun : (fun q : Eucl 3 × CappingSpace =>
            (cappingSpaceHomeoProj (F q)).2)
          = fun q : Eucl 3 × CappingSpace =>
              classMap q.1 ((cappingSpaceHomeoProj q.2).2) := by
        funext q
        rw [hF]
        simp only [cappingSpaceHomeoProj_chartPert, coordFam_snd]
      rw [hfun]
      have hInner : ContMDiffAt ((𝓡 4).prod (𝓡 4)) ((𝓡 4).prod (𝓡 3)) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : Eucl 3 × CappingSpace => (q.1, (cappingSpaceHomeoProj q.2).2)) (t₀, p₀) :=
        (contMDiffAt_prod_iff _).mpr ⟨contMDiffAt_fst, hproj₀⟩
      let F₂ : Eucl 3 × Projectivization ℝ (Eucl 3) → Projectivization ℝ (Eucl 3) :=
        fun q => classMap q.1 q.2
      have hF₂ : ContMDiffAt ((𝓡 4).prod (𝓡 3)) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) F₂ (t₀, x₀) := by
        have h := contMDiffAt_classMap_prod t₀ x₀
        simpa only [F₂] using h
      have hcomp := hF₂.comp (I := (𝓡 4).prod (𝓡 4)) (I' := (𝓡 4).prod (𝓡 3))
        (t₀, p₀) hInner
      simpa only [F₂, Function.comp_def, hx₀] using hcomp
  -- transport back to the capping space
  refine (chartedStructure_contMDiffWithinAt
    (I := 𝓡 4) (I' := ((𝓡 4).prod (𝓡 4)))
    (M := Set.Ioi (0:ℝ) × Projectivization ℝ (Eucl 3)) (M' := CappingSpace)
    (e := cappingSpaceHomeoProj.symm) (Z := Eucl 3 × CappingSpace)
    (f := F) Set.univ (t₀, p₀)).mpr ?_
  show ContMDiffWithinAt ((𝓡 4).prod (𝓡 4)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun y : Eucl 3 × CappingSpace => cappingSpaceHomeoProj (F y)) Set.univ (t₀, p₀)
  simpa only [contMDiffWithinAt_univ] using hG

/-- The family is jointly `C^∞`. -/
theorem contMDiff_chartPert :
    ContMDiff ((𝓡 4).prod (𝓡 4)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : Eucl 3 × CappingSpace => chartPert q.1 q.2) :=
  fun q => contMDiffAt_chartPert q.1 q.2

/-- **The family is `C^∞` in the parameter at a fixed point.** -/
theorem contMDiffAt_chartPert_param (p : CappingSpace) (t : Eucl 3) :
    ContMDiffAt (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : Eucl 3 => chartPert s p) t := by
  set x : Set.Ioi (0:ℝ) × Projectivization ℝ (Eucl 3) := cappingSpaceHomeoProj p with hx
  refine (chartedStructure_contMDiffWithinAt
    (I := 𝓡 4) (I' := 𝓡 4)
    (M := Set.Ioi (0:ℝ) × Projectivization ℝ (Eucl 3)) (M' := CappingSpace)
    (e := cappingSpaceHomeoProj.symm) (Z := Eucl 3)
    (f := fun s : Eucl 3 => chartPert s p) Set.univ t).mpr ?_
  have hcoord : (fun s : Eucl 3 => cappingSpaceHomeoProj (chartPert s p))
      = fun s : Eucl 3 => coordFam s x := by
    funext s
    simp only [cappingSpaceHomeoProj_chartPert, hx]
  simp only [Homeomorph.symm_symm]
  rw [hcoord, contMDiffWithinAt_univ]
  refine (contMDiffAt_halfLineProjective_iff_general (𝓡 4)
    (fun s : Eucl 3 => coordFam s x) t).mpr ⟨?_, ?_⟩
  · have hfun : (fun s : Eucl 3 => expHomeo.symm ((coordFam s x).1))
        = fun s : Eucl 3 =>
            expHomeo.symm x.1 + (s 0) • (e1 : EuclideanSpace ℝ (Fin 1)) := by
      funext s
      simp only [coordFam_fst, expHomeo_symm_levelScale]
    rw [hfun]
    exact contMDiffAt_iff_contDiffAt.mpr
      ((contDiff_const.add ((cproj 0).smulRight (e1 : EuclideanSpace ℝ (Fin 1))).contDiff).contDiffAt)
  · have hclass : ContMDiffAt (𝓡 4) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s : Eucl 3 => classMap s x.2) t := contMDiffAt_classMap_param x.2 t
    simpa only [coordFam_snd] using hclass

/-- **The family is `C^∞` in the parameter.** -/
theorem contMDiff_chartPert_param (p : CappingSpace) :
    ContMDiff (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : Eucl 3 => chartPert s p) :=
  fun t => contMDiffAt_chartPert_param p t

/-! ## The `ChartPert` instance -/

/-- **Every plane chart admits a chart perturbation** (the item (e) of the lead's message): the
family `chartPert` with `m = 4`. -/
theorem exists_chartPert (Q : ℂ → CappingSpace) :
    ∃ m : ℕ, ∃ Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace, ChartPert Q m Ξ := by
  refine ⟨4, chartPert, chartPert_zero, contMDiff_chartPert, ?_⟩
  intro t p
  exact surjective_mfderiv_chartPert p contMDiff_chartPert t

end

end Work.Drive
