import Mathlib
import Submission.Work.RTOwed.FillAtlas
import Submission.Work.RTOwed.jTransCore.Basic
import Submission.Work.RTOwed.jTransCore.Deriv
import Submission.Work.RTOwed.coreTrans
import Submission.Work.RTOwed.flatModel_polar_change
import Submission.Work.RTOwed.jTransCollAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Filter
open scoped Real RealInnerProductSpace

namespace Work.RTOwed
theorem mem_jkTransSrc (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (W : Set Work.Cusp.E2) (hW : IsOpen W)
    (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y')
    (q : Work.Cusp.E4) :
    q ∈ jkTransSrc a D (fun w => (D w).tor) v P W hW hsec ↔
      q ∈ jBoxR a v P ∧ (jChart a D v P).symm q
        ∈ (kChartOf a (fun w => (D w).tor) v W hW hsec).source := by
  rw [jkTransSrc, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    jChart_target]
  rfl

theorem mem_kjTransSrc (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (W : Set Work.Cusp.E2) (hW : IsOpen W)
    (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y')
    (q : Work.Cusp.E4) :
    q ∈ kjTransSrc a D (fun w => (D w).tor) v P W hW hsec ↔
      q ∈ Work.Cusp.coreBoxSect W ∧
        (kChartOf a (fun w => (D w).tor) v W hW hsec).symm q
          ∈ (jChart a D v P).source := by
  rw [kjTransSrc, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    kChartOf_target]
  rfl

/-! ## The junction → core transition is a rotation of the polar map -/

theorem kk_ofInt2_apply' (m : Fin 2 → ℤ) (i : Fin 2) :
    Work.Cusp.ofInt2 m i = ((m i : ℤ) : ℝ) := by
  fin_cases i <;> simp [Work.Cusp.ofInt2]

/-- **The source data of the junction→core transition**: a point of the source is below the junction
layer, and there is an integer lattice vector `m` such that the transition is, near the point, the
lattice rotation `kkShift v m` of the polar map. -/
theorem jkTransSrc_data (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (W : Set Work.Cusp.E2) (hW : IsOpen W)
    (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y')
    {q : Work.Cusp.E4} (hq : q ∈ jkTransSrc a D (fun w => (D w).tor) v P W hW hsec) :
    q 0 < 1/2 ∧ ∃ m : Fin 2 → ℤ,
      (jkTransMap a D (fun w => (D w).tor) v P W hW hsec q = kkShift v m (jPolMap q)) ∧
      ((fun q' => jkTransMap a D (fun w => (D w).tor) v P W hW hsec q')
        =ᶠ[𝓝 q] (fun q' => kkShift v m (jPolMap q'))) := by
  classical
  obtain ⟨hqR, hqin⟩ := (mem_jkTransSrc a D v P W hW hsec q).mp hq
  rw [jChart_symm a D v P hqR, kChartOf_source, Set.image_univ] at hqin
  obtain ⟨x, hx⟩ := hqin
  have hq0pos : 0 < q 0 := by
    have := (jBox_subset_polarBox v P.cU P.k P.W P.kx P.δ hqR.1).1; linarith
  have hle : q 0 ≤ Work.Cusp.rJ := by
    by_contra hlt
    exact jCoordM_of_gt_ne_coreCoordM a D v P W hqR.1 hlt x.2 hx.symm
  rw [jCoordM_of_le a v (D v) P.cU P.k P.W P.kx P.δ hqR.1 hle] at hx
  simp only [Work.Cusp.coreCoordM] at hx
  have hpair := a.incW_injective v hx.symm
  have hsq : (Work.Cusp.cuspInvInner v q).1 = (Work.Cusp.cuspInvCore v (x : Work.Cusp.E4)).1 := by
    have := congrArg (fun z : Work.Space.SquarePt × a.Torus v =>
      ((z.1 : Work.Space.SquarePt) : Work.Cusp.E2)) hpair
    simpa using this
  have hcl : ∀ i : Fin 2,
      (((Work.Cusp.cuspInvCore v (x : Work.Cusp.E4)).2 i : ℝ) : AddCircle (1 : ℝ))
        = (((Work.Cusp.cuspInvInner v q).2 i : ℝ) : AddCircle (1 : ℝ)) := by
    intro i
    have h := congrArg (fun z : Work.Space.SquarePt × a.Torus v => z.2) hpair
    have h2 : (fun i => (((Work.Cusp.cuspInvCore v (x : Work.Cusp.E4)).2 i : ℝ) :
        AddCircle (1 : ℝ)))
        = (fun i => (((Work.Cusp.cuspInvInner v q).2 i : ℝ) : AddCircle (1 : ℝ))) := by
      have h3 := congrArg (fun t : a.Torus v => (D v).tor t) h
      simpa using h3.symm
    exact congrFun h2 i
  have hmi : ∀ i : Fin 2, ∃ k : ℤ,
      (Work.Cusp.cuspInvCore v (x : Work.Cusp.E4)).2 i
        - (Work.Cusp.cuspInvInner v q).2 i = (k : ℝ) := by
    intro i
    have h0 : ((((Work.Cusp.cuspInvCore v (x : Work.Cusp.E4)).2 i
        - (Work.Cusp.cuspInvInner v q).2 i : ℝ)) : AddCircle (1 : ℝ)) = 0 := by
      rw [AddCircle.coe_sub, hcl i, sub_self]
    rw [AddCircle.coe_eq_zero_iff] at h0
    obtain ⟨k, hk⟩ := h0
    exact ⟨k, by rw [← hk, zsmul_one]⟩
  let m : Fin 2 → ℤ := fun i => Classical.choose (hmi i)
  have hm : ∀ i, (Work.Cusp.cuspInvCore v (x : Work.Cusp.E4)).2 i
      - (Work.Cusp.cuspInvInner v q).2 i = (m i : ℝ) :=
    fun i => Classical.choose_spec (hmi i)
  have hyx : (Work.Cusp.cuspInvCore v (x : Work.Cusp.E4)).2
      = (Work.Cusp.cuspInvInner v q).2 + Work.Cusp.ofInt2 m := by
    ext i
    simp only [PiLp.add_apply, kk_ofInt2_apply']
    linarith [hm i]
  have hq0 : q 0 < 1/2 := by
    have hlt : Work.Cusp.nrm (Work.Cusp.cuspInvInner v q).1 < 1/12 := by
      rw [hsq]
      exact Work.Cusp.cuspInvCore_mem_coreStratum v (x : Work.Cusp.E4) x.2.1
    exact cuspInvInner_nrm_lt_half v
      (jBox_subset_polarBox v P.cU P.k P.W P.kx P.δ hqR.1) hlt
  have hcbox : jPolMap q ∈ Work.Cusp.coreBox := by
    rw [Work.Cusp.coreBox, Set.mem_ofPred_eq, jPolMap_apply_zero, jPolMap_apply_one,
      sqrt_cos_sin_sq (q 0) (q 1) (le_of_lt hq0pos)]
    exact hq0
  have hqq : (!₂[q 0, q 1, q 2, q 3] : Work.Cusp.E4) = q := by ext i; fin_cases i <;> rfl
  have hp : Work.Cusp.cuspInvCore v (jPolMap q) = Work.Cusp.cuspInvInner v q := by
    have h1 := cuspInvInner_polar_eq_core v (q 0) (q 1) (q 2) (q 3) hq0pos
    rw [hqq] at h1
    exact h1.symm
  have hj : jPolMap q = Work.Cusp.ThetaCore v (Work.Cusp.cuspInvInner v q).1
      (Work.Cusp.cuspInvInner v q).2 := by
    rw [← hp]
    exact (Work.Cusp.ThetaCore_cuspInvCore v (jPolMap q) hcbox).symm
  have hxeq : (x : Work.Cusp.E4) = kkShift v m (jPolMap q) := by
    calc (x : Work.Cusp.E4)
        = Work.Cusp.ThetaCore v (Work.Cusp.cuspInvCore v (x : Work.Cusp.E4)).1
            (Work.Cusp.cuspInvCore v (x : Work.Cusp.E4)).2 :=
          (Work.Cusp.ThetaCore_cuspInvCore v (x : Work.Cusp.E4) x.2.1).symm
      _ = Work.Cusp.ThetaCore v (Work.Cusp.cuspInvInner v q).1
            ((Work.Cusp.cuspInvInner v q).2 + Work.Cusp.ofInt2 m) := by rw [hsq.symm, hyx]
      _ = kkShift v m (Work.Cusp.ThetaCore v (Work.Cusp.cuspInvInner v q).1
            (Work.Cusp.cuspInvInner v q).2) :=
          ThetaCore_kkShift v (Work.Cusp.cuspInvInner v q).1 (Work.Cusp.cuspInvInner v q).2 m
      _ = kkShift v m (jPolMap q) := by rw [← hj]
  -- the open set on which the model applies
  have h3open : IsOpen {q' : Work.Cusp.E4 |
      kkShift v m (jPolMap q') ∈ Work.Cusp.coreBoxSect W} :=
    (Work.Cusp.CoreChartM.ccm_isOpen_coreBoxSect W hW).preimage
      ((continuous_kkShift v m).comp continuous_jPolMap)
  have hopen : IsOpen {q' : Work.Cusp.E4 | q' ∈ jBoxR a v P ∧ 0 < q' 0 ∧ q' 0 < 1/2 ∧
      kkShift v m (jPolMap q') ∈ Work.Cusp.coreBoxSect W} := by
    have h1 : IsOpen {q' : Work.Cusp.E4 | 0 < q' 0} :=
      isOpen_lt continuous_const (by fun_prop : Continuous fun q' : Work.Cusp.E4 => q' 0)
    have h2 : IsOpen {q' : Work.Cusp.E4 | q' 0 < 1/2} :=
      isOpen_lt (by fun_prop : Continuous fun q' : Work.Cusp.E4 => q' 0) continuous_const
    exact (isOpen_jBoxR a v P).inter (h1.inter (h2.inter h3open))
  have hmem : {q' : Work.Cusp.E4 | q' ∈ jBoxR a v P ∧ 0 < q' 0 ∧ q' 0 < 1/2 ∧
      kkShift v m (jPolMap q') ∈ Work.Cusp.coreBoxSect W} ∈ 𝓝 q :=
    hopen.mem_nhds ⟨hqR, hq0pos, hq0, by rw [← hxeq]; exact x.2⟩
  have hval : jkTransMap a D (fun w => (D w).tor) v P W hW hsec q
      = kkShift v m (jPolMap q) := by
    simp only [jkTransMap]
    rw [jChart_symm a D v P hqR,
      jCoordM_eq_coreCoordM_shift a D v P W hqR.1 hq0pos hq0 m
        (by rw [← hxeq]; exact x.2)]
    exact kChartOf_apply a (fun w => (D w).tor) v W hW hsec (kkShift v m (jPolMap q))
      (by rw [← hxeq]; exact x.2)
  refine ⟨hq0, m, hval, ?_⟩
  refine Filter.eventually_of_mem hmem ?_
  intro q' hq'
  obtain ⟨hq'R, hq'pos, hq'half, hq'sect⟩ := hq'
  simp only [jkTransMap]
  rw [jChart_symm a D v P hq'R,
    jCoordM_eq_coreCoordM_shift a D v P W hq'R.1 hq'pos hq'half m hq'sect]
  exact kChartOf_apply a (fun w => (D w).tor) v W hW hsec (kkShift v m (jPolMap q')) hq'sect

/-- The model of the junction→core transition is smooth. -/
theorem contDiff_kkShift_jPolMap (v : Work.Space.Cusp) (m : Fin 2 → ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Work.Cusp.E4 => kkShift v m (jPolMap z)) :=
  ((contDiff_kkShift v m).comp contDiff_jPolMap)

/-- The lattice rotation is an isometry of the flat model, in the form of the transition. -/
theorem flatModel_kkShift_jPolMap (h₀ : ℝ) (v : Work.Space.Cusp) (m : Fin 2 → ℤ)
    (q u w : Work.Cusp.E4) :
    Work.RTInstance.flatModel h₀ (kkShift v m (jPolMap q))
        (fderiv ℝ (fun z : Work.Cusp.E4 => kkShift v m (jPolMap z)) q u)
        (fderiv ℝ (fun z : Work.Cusp.E4 => kkShift v m (jPolMap z)) q w)
      = Work.RTInstance.flatModel h₀ (jPolMap q) (fderiv ℝ jPolMap q u)
          (fderiv ℝ jPolMap q w) := by
  have hfd : fderiv ℝ (fun z : Work.Cusp.E4 => kkShift v m (jPolMap z)) q
      = (kkLin (Real.cos (kkAng v m)) (Real.sin (kkAng v m))).comp (fderiv ℝ jPolMap q) := by
    rw [show (fun z : Work.Cusp.E4 => kkShift v m (jPolMap z)) = (kkShift v m) ∘ jPolMap from rfl,
      fderiv_comp q ((contDiff_kkShift v m).differentiable (by simp)).differentiableAt
        (contDiff_jPolMap.differentiable (by simp)).differentiableAt,
      fderiv_kkShift]
  rw [hfd]
  simp only [ContinuousLinearMap.comp_apply]
  exact flatModel_kkShift h₀ v m (jPolMap q) (fderiv ℝ jPolMap q u) (fderiv ℝ jPolMap q w)

theorem jkTrans_iso (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (W : Set Work.Cusp.E2) (hW : IsOpen W)
    (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    TransIso2 (jLayer v).model (kLayer v).model
      (jkTransMap a D (fun w => (D w).tor) v P W hW hsec)
      (jkTransSrc a D (fun w => (D w).tor) v P W hW hsec) := by
  constructor
  · intro q hq
    obtain ⟨hq0, m, hval, hev⟩ := jkTransSrc_data a D v P W hW hsec hq
    have hcd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : Work.Cusp.E4 => kkShift v m (jPolMap z)) q :=
      (contDiff_kkShift_jPolMap v m).contDiffAt
    exact (hcd.congr_of_eventuallyEq hev).contDiffWithinAt
  · intro q hq u w
    obtain ⟨hq0, m, hval, hev⟩ := jkTransSrc_data a D v P W hW hsec hq
    have hqR : q ∈ jBoxR a v P := ((mem_jkTransSrc a D v P W hW hsec q).mp hq).1
    have hq14 : (1:ℝ)/4 < q 0 := (jBox_subset_polarBox v P.cU P.k P.W P.kx P.δ hqR.1).1
    have hq18 : (1:ℝ)/8 ≤ q 0 := by linarith
    have hfd : fderiv ℝ (jkTransMap a D (fun w => (D w).tor) v P W hW hsec) q
        = fderiv ℝ (fun z : Work.Cusp.E4 => kkShift v m (jPolMap z)) q :=
      Filter.EventuallyEq.fderiv_eq hev
    rw [hfd, hval]
    show Work.RTInstance.flatModel (Work.RTOwed.fillProf v).h₀
        (kkShift v m (jPolMap q))
        (fderiv ℝ (fun z : Work.Cusp.E4 => kkShift v m (jPolMap z)) q u)
        (fderiv ℝ (fun z : Work.Cusp.E4 => kkShift v m (jPolMap z)) q w)
      = Work.RTInstance.warpedModelA (Work.RTOwed.fillProf v).f (Work.RTOwed.fillProf v).h q u w
    rw [flatModel_kkShift_jPolMap, flatModel_jPolMap, Work.RTInstance.warpedModelA_apply,
      Work.RTInstance.diagQuad_apply,
      Work.RTInstance.posExt_eq (by norm_num) hq18,
      fillProf_f_core v (le_of_lt hq0), fillProf_h_core v (le_of_lt hq0)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.cons_val_three]
    ring

/-! ## The lattice rotation as a linear isometry, and the inverse transition -/

/-- The composition `kkLin c s ∘ kkLin c (-s)` is the identity. -/
theorem kkLin_comp_neg (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (x : Work.Cusp.E4) :
    kkLin c s (kkLin c (-s) x) = x := by
  rw [kkLin_apply, kkLin_apply]
  ext i
  fin_cases i <;> simp <;> ring_nf
  · linear_combination (x 0) * hcs
  · linear_combination (x 1) * hcs

/-- The composition `kkLin c (-s) ∘ kkLin c s` is the identity. -/
theorem kkLin_neg_comp (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (x : Work.Cusp.E4) :
    kkLin c (-s) (kkLin c s x) = x := by
  rw [kkLin_apply, kkLin_apply]
  ext i
  fin_cases i <;> simp <;> ring_nf
  · linear_combination (x 0) * hcs
  · linear_combination (x 1) * hcs

/-- The lattice rotation `kkLin` as a continuous linear equivalence. -/
noncomputable def kkLinEquiv (v : Work.Space.Cusp) (m : Fin 2 → ℤ) :
    Work.Cusp.E4 ≃L[ℝ] Work.Cusp.E4 :=
  ContinuousLinearEquiv.equivOfInverse
    (kkLin (Real.cos (kkAng v m)) (Real.sin (kkAng v m)))
    (kkLin (Real.cos (kkAng v m)) (-(Real.sin (kkAng v m))))
    (fun x => kkLin_neg_comp _ _ (Real.cos_sq_add_sin_sq _) x)
    (fun x => kkLin_comp_neg _ _ (Real.cos_sq_add_sin_sq _) x)

theorem kkLinEquiv_apply (v : Work.Space.Cusp) (m : Fin 2 → ℤ) (x : Work.Cusp.E4) :
    kkLinEquiv v m x = kkLin (Real.cos (kkAng v m)) (Real.sin (kkAng v m)) x :=
  ContinuousLinearEquiv.equivOfInverse_apply _ _ _ _ x

theorem kkLinEquiv_coe (v : Work.Space.Cusp) (m : Fin 2 → ℤ) :
    ((kkLinEquiv v m : Work.Cusp.E4 ≃L[ℝ] Work.Cusp.E4) :
      Work.Cusp.E4 →L[ℝ] Work.Cusp.E4)
      = kkLin (Real.cos (kkAng v m)) (Real.sin (kkAng v m)) :=
  ContinuousLinearMap.ext fun x => kkLinEquiv_apply v m x

theorem cle_trans_coe (e₁ e₂ : Work.Cusp.E4 ≃L[ℝ] Work.Cusp.E4) :
    ((e₁.trans e₂ : Work.Cusp.E4 ≃L[ℝ] Work.Cusp.E4) : Work.Cusp.E4 →L[ℝ] Work.Cusp.E4)
      = (e₂ : Work.Cusp.E4 →L[ℝ] Work.Cusp.E4).comp
          (e₁ : Work.Cusp.E4 →L[ℝ] Work.Cusp.E4) :=
  ContinuousLinearMap.ext fun u => ContinuousLinearEquiv.trans_apply e₁ e₂ u

/-- The derivative of the shifted polar map, as a continuous linear equivalence. -/
noncomputable def kkShiftJPolDerivEquiv (v : Work.Space.Cusp) (m : Fin 2 → ℤ)
    (q : Work.Cusp.E4) (hq : q 0 ≠ 0) : Work.Cusp.E4 ≃L[ℝ] Work.Cusp.E4 :=
  (jPolDerivEquiv q hq).trans (kkLinEquiv v m)

theorem kkShiftJPolDerivEquiv_coe (v : Work.Space.Cusp) (m : Fin 2 → ℤ)
    (q : Work.Cusp.E4) (hq : q 0 ≠ 0) :
    ((kkShiftJPolDerivEquiv v m q hq : Work.Cusp.E4 ≃L[ℝ] Work.Cusp.E4) :
      Work.Cusp.E4 →L[ℝ] Work.Cusp.E4)
      = (kkLin (Real.cos (kkAng v m)) (Real.sin (kkAng v m))).comp
          (fderiv ℝ jPolMap q) := by
  rw [kkShiftJPolDerivEquiv, cle_trans_coe, jPolDerivEquiv_coe, kkLinEquiv_coe]

/-! ## The two transitions are inverse to each other -/

/-- The junction→core transition followed by the core→junction transition is the identity on the
source of the latter. -/
theorem kjTransMap_jkTransMap (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (W : Set Work.Cusp.E2) (hW : IsOpen W)
    (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y')
    {z : Work.Cusp.E4} (hz : z ∈ jkTransSrc a D (fun w => (D w).tor) v P W hW hsec) :
    kjTransMap a D (fun w => (D w).tor) v P W hW hsec
      (jkTransMap a D (fun w => (D w).tor) v P W hW hsec z) = z := by
  obtain ⟨hzR, hzin⟩ := (mem_jkTransSrc a D v P W hW hsec z).mp hz
  have h1 : (kChartOf a (fun w => (D w).tor) v W hW hsec).symm
      ((kChartOf a (fun w => (D w).tor) v W hW hsec) ((jChart a D v P).symm z))
      = (jChart a D v P).symm z :=
    OpenPartialHomeomorph.left_inv _ hzin
  show (jChart a D v P)
      ((kChartOf a (fun w => (D w).tor) v W hW hsec).symm
        ((kChartOf a (fun w => (D w).tor) v W hW hsec) ((jChart a D v P).symm z))) = z
  rw [h1]
  exact OpenPartialHomeomorph.right_inv (jChart a D v P) (by rwa [jChart_target])

/-- The core→junction transition followed by the junction→core transition is the identity on the
source of the latter. -/
theorem jkTransMap_kjTransMap (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (W : Set Work.Cusp.E2) (hW : IsOpen W)
    (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y')
    {x : Work.Cusp.E4} (hx : x ∈ kjTransSrc a D (fun w => (D w).tor) v P W hW hsec) :
    jkTransMap a D (fun w => (D w).tor) v P W hW hsec
      (kjTransMap a D (fun w => (D w).tor) v P W hW hsec x) = x := by
  obtain ⟨hxbox, hxin⟩ := (mem_kjTransSrc a D v P W hW hsec x).mp hx
  show (kChartOf a (fun w => (D w).tor) v W hW hsec)
      ((jChart a D v P).symm
        (jChart a D v P ((kChartOf a (fun w => (D w).tor) v W hW hsec).symm x))) = x
  rw [OpenPartialHomeomorph.left_inv (jChart a D v P) hxin]
  exact OpenPartialHomeomorph.right_inv (kChartOf a (fun w => (D w).tor) v W hW hsec)
    (by rwa [kChartOf_target])


/-- **The source data of the core→junction transition**, together with the fact that the base point
lies in the source of the junction→core transition. -/
theorem kjTransSrc_exists (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (W : Set Work.Cusp.E2) (hW : IsOpen W)
    (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y')
    {x : Work.Cusp.E4} (hx : x ∈ kjTransSrc a D (fun w => (D w).tor) v P W hW hsec) :
    ∃ (m : Fin 2 → ℤ) (y : Work.Cusp.E4),
      y ∈ jkTransSrc a D (fun w => (D w).tor) v P W hW hsec ∧
      y ∈ jBoxR a v P ∧ y 0 < 1/2 ∧
      kkShift v m (jPolMap y) = x ∧
      kjTransMap a D (fun w => (D w).tor) v P W hW hsec x = y ∧
      (∀ᶠ z in 𝓝 y, jkTransMap a D (fun w => (D w).tor) v P W hW hsec z
        = kkShift v m (jPolMap z)) := by
  obtain ⟨hxbox, hxin⟩ := (mem_kjTransSrc a D v P W hW hsec x).mp hx
  rw [kChartOf_symm_apply a (fun w => (D w).tor) v W hW hsec x hxbox, jChart_source] at hxin
  obtain ⟨y, hyR, hy⟩ := hxin
  have hyy : y = ⟨(y : Work.Cusp.E4), hyR.1⟩ := Subtype.ext rfl
  rw [hyy] at hy
  have hyS : (y : Work.Cusp.E4) ∈ jkTransSrc a D (fun w => (D w).tor) v P W hW hsec := by
    rw [mem_jkTransSrc]
    refine ⟨hyR, ?_⟩
    rw [jChart_symm a D v P hyR, kChartOf_source]
    exact ⟨⟨x, hxbox⟩, Set.mem_univ _, hy.symm⟩
  obtain ⟨hy0, m, hval, hev⟩ := jkTransSrc_data a D v P W hW hsec hyS
  have hkj : kjTransMap a D (fun w => (D w).tor) v P W hW hsec x = (y : Work.Cusp.E4) := by
    simp only [kjTransMap]
    rw [kChartOf_symm_apply a (fun w => (D w).tor) v W hW hsec x hxbox, ← hy]
    exact jChart_apply a D v P (y : Work.Cusp.E4) hyR
  have hmod : kkShift v m (jPolMap (y : Work.Cusp.E4)) = x := by
    rw [← hval]
    simp only [jkTransMap]
    rw [jChart_symm a D v P hyR, hy, kChartOf_apply a (fun w => (D w).tor) v W hW hsec x hxbox]
  exact ⟨m, (y : Work.Cusp.E4), hyS, hyR, hy0, hmod, hkj, hev⟩

/-- **The core→junction transition is a smooth isometry of the flat/warped model pair.** -/
theorem kjTrans_iso (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (W : Set Work.Cusp.E2) (hW : IsOpen W)
    (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    TransIso2 (kLayer v).model (jLayer v).model
      (kjTransMap a D (fun w => (D w).tor) v P W hW hsec)
      (kjTransSrc a D (fun w => (D w).tor) v P W hW hsec) := by
  have hopen : IsOpen (kjTransSrc a D (fun w => (D w).tor) v P W hW hsec) :=
    OpenPartialHomeomorph.open_source _
  have hopenJK : IsOpen (jkTransSrc a D (fun w => (D w).tor) v P W hW hsec) :=
    OpenPartialHomeomorph.open_source _
  have hcd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (kjTransMap a D (fun w => (D w).tor) v P W hW hsec)
      (kjTransSrc a D (fun w => (D w).tor) v P W hW hsec) := by
    intro x hx
    obtain ⟨m, y, hyS, hyR, hy0, hmod, hkj, hev⟩ := kjTransSrc_exists a D v P W hW hsec hx
    have hy0ne : y 0 ≠ 0 := by
      have := (jBox_subset_polarBox v P.cU P.k P.W P.kx P.δ hyR.1).1
      linarith
    have hcontF : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : Work.Cusp.E4 => kkShift v m (jPolMap z)) y :=
      (contDiff_kkShift_jPolMap v m).contDiffAt
    have hFdiff : HasFDerivAt (fun z : Work.Cusp.E4 => kkShift v m (jPolMap z))
        ((kkShiftJPolDerivEquiv v m y hy0ne) : Work.Cusp.E4 →L[ℝ] Work.Cusp.E4) y := by
      have h1 : HasFDerivAt (fun z : Work.Cusp.E4 => kkShift v m (jPolMap z))
          ((kkLin (Real.cos (kkAng v m)) (Real.sin (kkAng v m))).comp
            (fderiv ℝ jPolMap y)) y := by
        have hg1 : HasFDerivAt (kkShift v m) (fderiv ℝ (kkShift v m) (jPolMap y))
            (jPolMap y) :=
          ((contDiff_kkShift v m).contDiffAt.differentiableAt (by simp)).hasFDerivAt
        have h := hg1.comp y (hasFDerivAt_jPolMap y)
        rw [fderiv_kkShift] at h
        exact h
      rw [kkShiftJPolDerivEquiv_coe]
      exact h1
    have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
    have hg : ∀ᶠ z in 𝓝 y, kjTransMap a D (fun w => (D w).tor) v P W hW hsec
        (kkShift v m (jPolMap z)) = z := by
      filter_upwards [hev, hopenJK.mem_nhds hyS] with z hz hzS
      rw [← hz]
      exact kjTransMap_jkTransMap a D v P W hW hsec hzS
    have hlocal : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (hcontF.localInverse hFdiff hn) (kkShift v m (jPolMap y)) :=
      hcontF.to_localInverse hFdiff hn
    have huniq : (kjTransMap a D (fun w => (D w).tor) v P W hW hsec)
        =ᶠ[𝓝 (kkShift v m (jPolMap y))] (hcontF.localInverse hFdiff hn) := by
      have h := (hcontF.hasStrictFDerivAt' hFdiff hn).localInverse_unique hg
      exact h
    have hcat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (kjTransMap a D (fun w => (D w).tor) v P W hW hsec) (kkShift v m (jPolMap y)) :=
      hlocal.congr_of_eventuallyEq huniq
    rw [hmod] at hcat
    exact hcat.contDiffWithinAt
  refine ⟨hcd, ?_⟩
  intro x hx u w
  obtain ⟨m, y, hyS, hyR, hy0, hmod, hkj, hev⟩ := kjTransSrc_exists a D v P W hW hsec hx
  have hdiffkj_x : DifferentiableAt ℝ (kjTransMap a D (fun w => (D w).tor) v P W hW hsec) x :=
    (hcd.contDiffAt (hopen.mem_nhds hx)).differentiableAt (by simp)
  have hjk_y : jkTransMap a D (fun w => (D w).tor) v P W hW hsec y = x :=
    (show (fun z => jkTransMap a D (fun w => (D w).tor) v P W hW hsec z)
        =ᶠ[𝓝 y] (fun z => kkShift v m (jPolMap z)) from hev).eq_of_nhds.trans hmod
  have hdiffjk_y' : DifferentiableAt ℝ
      (jkTransMap a D (fun w => (D w).tor) v P W hW hsec) y :=
    ((jkTrans_iso a D v P W hW hsec).1.contDiffAt
      ((OpenPartialHomeomorph.open_source _).mem_nhds hyS)).differentiableAt (by simp)
  have hdiffjk_y : DifferentiableAt ℝ (jkTransMap a D (fun w => (D w).tor) v P W hW hsec)
      (kjTransMap a D (fun w => (D w).tor) v P W hW hsec x) := by
    rw [hkj]; exact hdiffjk_y'
  have hcomp : (fun z => jkTransMap a D (fun w => (D w).tor) v P W hW hsec
      (kjTransMap a D (fun w => (D w).tor) v P W hW hsec z)) =ᶠ[𝓝 x] id := by
    filter_upwards [hopen.mem_nhds hx] with z hz
    exact jkTransMap_kjTransMap a D v P W hW hsec hz
  have hchain : (fderiv ℝ (jkTransMap a D (fun w => (D w).tor) v P W hW hsec) y).comp
      (fderiv ℝ (kjTransMap a D (fun w => (D w).tor) v P W hW hsec) x)
      = ContinuousLinearMap.id ℝ Work.Cusp.E4 := by
    have h1 : fderiv ℝ ((jkTransMap a D (fun w => (D w).tor) v P W hW hsec) ∘
        (kjTransMap a D (fun w => (D w).tor) v P W hW hsec)) x
        = (fderiv ℝ (jkTransMap a D (fun w => (D w).tor) v P W hW hsec)
              (kjTransMap a D (fun w => (D w).tor) v P W hW hsec x)).comp
            (fderiv ℝ (kjTransMap a D (fun w => (D w).tor) v P W hW hsec) x) :=
      fderiv_comp x hdiffjk_y hdiffkj_x
    rw [hkj] at h1
    rw [← h1]
    rw [show ((jkTransMap a D (fun w => (D w).tor) v P W hW hsec) ∘
        (kjTransMap a D (fun w => (D w).tor) v P W hW hsec))
        = (fun z => jkTransMap a D (fun w => (D w).tor) v P W hW hsec
            (kjTransMap a D (fun w => (D w).tor) v P W hW hsec z)) from rfl,
      hcomp.fderiv_eq, fderiv_id]
  have hBAu : fderiv ℝ (jkTransMap a D (fun w => (D w).tor) v P W hW hsec) y
      (fderiv ℝ (kjTransMap a D (fun w => (D w).tor) v P W hW hsec) x u) = u := by
    have := DFunLike.congr_fun hchain u; simpa using this
  have hBAw : fderiv ℝ (jkTransMap a D (fun w => (D w).tor) v P W hW hsec) y
      (fderiv ℝ (kjTransMap a D (fun w => (D w).tor) v P W hW hsec) x w) = w := by
    have := DFunLike.congr_fun hchain w; simpa using this
  have hkey := (jkTrans_iso a D v P W hW hsec).2 hyS
    (fderiv ℝ (kjTransMap a D (fun w => (D w).tor) v P W hW hsec) x u)
    (fderiv ℝ (kjTransMap a D (fun w => (D w).tor) v P W hW hsec) x w)
  rw [hjk_y, hBAu, hBAw] at hkey
  rw [hkj]
  exact hkey.symm

theorem jkTransIso2 (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : Work.RTOwed.JPin a v) (W : Set Work.Cusp.E2) (hW : IsOpen W)
    (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    Work.RTOwed.TransIso2 (Work.RTOwed.jLayer v).model (Work.RTOwed.kLayer v).model
        (Work.RTOwed.jkTransMap a D (fun w => (D w).tor) v P W hW hsec)
        (Work.RTOwed.jkTransSrc a D (fun w => (D w).tor) v P W hW hsec) ∧
      Work.RTOwed.TransIso2 (Work.RTOwed.kLayer v).model (Work.RTOwed.jLayer v).model
        (Work.RTOwed.kjTransMap a D (fun w => (D w).tor) v P W hW hsec)
        (Work.RTOwed.kjTransSrc a D (fun w => (D w).tor) v P W hW hsec) :=
  ⟨jkTrans_iso a D v P W hW hsec, kjTrans_iso a D v P W hW hsec⟩

end Work.RTOwed
