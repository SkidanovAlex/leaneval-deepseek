import Mathlib
import Submission.Work.RTOwed.jTransCollAux
import Submission.Work.RTOwed.cuspCoordMTop_high_diff
import Submission.Work.RTOwed.cusp_polarToUHS_isometry

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section
open Set Topology Function
open scoped RealInnerProductSpace

namespace Work.RTOwed


/-! ## The forward value analysis -/

def intVec4 (m : Fin 3 → ℤ) : Work.Cusp.E4 := !₂[(m 0 : ℝ), (m 1 : ℝ), (m 2 : ℝ), 0]

theorem intVec4_castSucc (m : Fin 3 → ℤ) (i : Fin 3) :
    intVec4 m (Fin.castSucc i) = (m i : ℝ) := by
  fin_cases i <;> simp [intVec4]

theorem intVec4_three (m : Fin 3 → ℤ) : (intVec4 m) 3 = 0 := by simp [intVec4]

def IsIntVec (y : Work.Cusp.E4) : Prop := ∃ m : Fin 3 → ℤ, y = intVec4 m

theorem int_eq_of_abs_sub_lt_half {n n' : ℤ} (h : |(n:ℝ) - (n':ℝ)| < 1/2) : n = n' := by
  have h1 : |(n:ℝ) - (n':ℝ)| < 1 := by linarith
  have h2 : ((|n - n'| : ℤ) : ℝ) < 1 := by rw [Int.cast_abs]; push_cast; exact h1
  have h3 : |n - n'| < 1 := by exact_mod_cast h2
  have h4 : n - n' = 0 := Int.abs_lt_one_iff.mp h3
  omega

theorem IsIntVec.eq_of_close {y y' : Work.Cusp.E4} (hy : IsIntVec y) (hy' : IsIntVec y')
    (hclose : ∀ i : Fin 4, |y i - y' i| < 1/2) : y = y' := by
  obtain ⟨m, rfl⟩ := hy
  obtain ⟨m', rfl⟩ := hy'
  congr 1
  funext i
  have h := hclose (Fin.castSucc i)
  rw [intVec4_castSucc, intVec4_castSucc] at h
  have := int_eq_of_abs_sub_lt_half h
  rw [this]

theorem exp_nine_twentieth_gt : (3/2:ℝ) < Real.exp (9/20) := by
  have h1 : ∑ i ∈ Finset.range 4, ((9:ℝ)/20)^i / (i.factorial:ℝ) ≤ Real.exp (9/20) :=
    Real.sum_le_exp_of_nonneg (by norm_num) 4
  have h2 : (3/2:ℝ) < ∑ i ∈ Finset.range 4, ((9:ℝ)/20)^i / (i.factorial:ℝ) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  linarith

theorem polarToUHS_above_beta (v : Work.Space.Cusp)
    (a : Work.Space.Assembly) (P : JPin a v)
    {q : Work.Cusp.E4} (hq : q ∈ jBoxR a v P) :
    Work.Cusp.beta (Work.Cusp.xOf (Work.Cusp.polarToUHS v q)) < (Work.Cusp.polarToUHS v q) 3 := by
  have h3 : (Work.Cusp.polarToUHS v q) 3 = Real.exp (Work.Cusp.R0 - q 0) := rfl
  have hR : Work.Cusp.R0 - rCut = 9/20 := by rw [Work.Cusp.R0, rCut]; norm_num
  have hqcut : q 0 < rCut := hq.2
  have hlt : Work.Cusp.R0 - rCut < Work.Cusp.R0 - q 0 := by linarith
  have hexp : Real.exp (9/20) < Real.exp (Work.Cusp.R0 - q 0) := by
    rw [← hR]; exact Real.exp_lt_exp.mpr hlt
  have hb : Work.Cusp.beta (Work.Cusp.xOf (Work.Cusp.polarToUHS v q)) ≤ 3/2 :=
    Work.Cusp.beta_le_max _
  rw [h3]
  linarith [exp_nine_twentieth_gt, hexp, hb]

theorem jcTransMap_mem_cBoxR (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ})
    {q : Work.Cusp.E4} (hq : q ∈ jcTransSrc a D v P c δ hδ hne) :
    jcTransMap a D v P c δ hδ hne q ∈ cBoxR v c δ := by
  rw [mem_jcTransSrc] at hq
  have hmaps := OpenPartialHomeomorph.map_source (cChart a D v c δ hδ hne) hq.2
  rwa [cChart_target] at hmaps

theorem jcTransMap_int (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ})
    {q : Work.Cusp.E4} (hq : q ∈ jcTransSrc a D v P c δ hδ hne) :
    IsIntVec (jcTransMap a D v P c δ hδ hne q - Work.Cusp.polarToUHS v q) := by
  obtain ⟨hqR, hqin⟩ := (mem_jcTransSrc a D v P c δ hδ hne q).mp hq
  have hgt : Work.Cusp.rJ < q 0 := jcTransSrc_gt a D v P c δ hδ hne hq
  have hxR : jcTransMap a D v P c δ hδ hne q ∈ cBoxR v c δ :=
    jcTransMap_mem_cBoxR a D v P c δ hδ hne hq
  have hbox : ∀ i, |Work.Cusp.xOf (Work.Cusp.polarToUHS v q) i - P.kx i| < P.δ := hqR.1.2.2.2.2.2
  have hub : q 0 < rBig := hqR.1.2.1
  have hmemP : Work.Cusp.polarToUHS v q ∈ Work.Cusp.cuspBoxTop v P.kx P.δ :=
    polarToUHS_mem_cuspBoxTop v P.kx P.δ hbox hgt hub
  have hyge : Work.Cusp.beta (Work.Cusp.xOf (Work.Cusp.polarToUHS v q))
      ≤ (Work.Cusp.polarToUHS v q) 3 := le_of_lt (polarToUHS_above_beta v a P hqR)
  have hchain1 : Work.Cusp.cuspCoordMTop a v (D v) c δ ⟨jcTransMap a D v P c δ hδ hne q, hxR.1⟩
      = (jChart a D v P).symm q := by
    rw [← cChart_symm a D v c δ hδ hne hxR]
    exact OpenPartialHomeomorph.left_inv (cChart a D v c δ hδ hne) hqin
  have hchain2 : (jChart a D v P).symm q
      = Work.Cusp.cuspCoordMTop a v (D v) P.kx P.δ ⟨Work.Cusp.polarToUHS v q, hmemP⟩ := by
    rw [jChart_symm a D v P hqR]
    rw [jCoordM_of_gt (a := a) (v := v) (D := D v) (cU := P.cU) (k := P.k) (W := P.W)
      (kx := P.kx) (δ := P.δ) hqR.1 (not_le.mpr hgt)]
  have heq : Work.Cusp.cuspCoordMTop a v (D v) c δ ⟨jcTransMap a D v P c δ hδ hne q, hxR.1⟩
      = Work.Cusp.cuspCoordMTop a v (D v) P.kx P.δ ⟨Work.Cusp.polarToUHS v q, hmemP⟩ :=
    hchain1.trans hchain2
  have hxge : Work.Cusp.beta (Work.Cusp.xOf (jcTransMap a D v P c δ hδ hne q))
      ≤ (jcTransMap a D v P c δ hδ hne q) 3 := by
    by_contra hcon
    have hlt : (jcTransMap a D v P c δ hδ hne q) 3
        < Work.Cusp.beta (Work.Cusp.xOf (jcTransMap a D v P c δ hδ hne q)) := not_le.mp hcon
    rw [cuspCoordMTop_of_lt a v (D v) c δ ⟨_, hxR.1⟩ hlt,
      cuspCoordMTop_of_ge a v (D v) P.kx P.δ ⟨_, hmemP⟩ (not_lt.mpr hyge)] at heq
    exact a.incMbar_ne_incY
      (fun ⟨hxTset, _⟩ => (D v).mbarLow_not_TsetTop c δ hxR.1 hlt hxTset) heq
  obtain ⟨m, hm⟩ := Work.RTOWed.cuspCoordMTop_high_diff a v (D v) hxR.1 hmemP hxge hyge heq
  exact ⟨m, by rw [hm]; abel⟩

/-! ## Continuity -/

theorem continuousOn_jcTransMap (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) :
    ContinuousOn (jcTransMap a D v P c δ hδ hne) (jcTransSrc a D v P c δ hδ hne) := by
  have hsym : ContinuousOn ((jChart a D v P).symm) (jcTransSrc a D v P c δ hδ hne) :=
    (OpenPartialHomeomorph.continuousOn_symm (jChart a D v P)).mono
      (fun q hq => by
        rw [jChart_target]
        exact ((mem_jcTransSrc a D v P c δ hδ hne q).mp hq).1)
  have hcc : ContinuousOn (cChart a D v c δ hδ hne) (cChart a D v c δ hδ hne).source :=
    OpenPartialHomeomorph.continuousOn _
  have hmt : MapsTo ((jChart a D v P).symm) (jcTransSrc a D v P c δ hδ hne)
      (cChart a D v c δ hδ hne).source := fun q hq => ((mem_jcTransSrc a D v P c δ hδ hne q).mp hq).2
  exact hcc.comp hsym hmt

/-! ## Local constancy of the value of the transition -/

theorem eventually_jcTransMap_eq (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ})
    {q₀ : Work.Cusp.E4} (hq₀ : q₀ ∈ jcTransSrc a D v P c δ hδ hne) :
    ∃ m : Fin 3 → ℤ, ∀ᶠ q in 𝓝 q₀, jcTransMap a D v P c δ hδ hne q
      = Work.Cusp.polarToUHS v q + intVec4 m := by
  have hsrcopen : IsOpen (jcTransSrc a D v P c δ hδ hne) :=
    OpenPartialHomeomorph.open_source _
  obtain ⟨m₀, hm₀⟩ := jcTransMap_int a D v P c δ hδ hne hq₀
  refine ⟨m₀, ?_⟩
  have hcont : ContinuousOn (fun q => jcTransMap a D v P c δ hδ hne q - Work.Cusp.polarToUHS v q)
      (jcTransSrc a D v P c δ hδ hne) :=
    (continuousOn_jcTransMap a D v P c δ hδ hne).sub
      ((cusp_polarToUHS_contDiff v).continuous.continuousOn)
  have hcat : ContinuousAt (fun q => jcTransMap a D v P c δ hδ hne q - Work.Cusp.polarToUHS v q) q₀ :=
    hcont.continuousAt (hsrcopen.mem_nhds hq₀)
  have hev : ∀ᶠ q in 𝓝 q₀, jcTransMap a D v P c δ hδ hne q - Work.Cusp.polarToUHS v q
      = jcTransMap a D v P c δ hδ hne q₀ - Work.Cusp.polarToUHS v q₀ := by
    have hclose : ∀ᶠ q in 𝓝 q₀, ∀ i : Fin 4,
        |(jcTransMap a D v P c δ hδ hne q - Work.Cusp.polarToUHS v q) i
          - (jcTransMap a D v P c δ hδ hne q₀ - Work.Cusp.polarToUHS v q₀) i| < 1/2 := by
      rw [Filter.eventually_all]
      intro i
      have hci : ContinuousAt (fun q => (jcTransMap a D v P c δ hδ hne q - Work.Cusp.polarToUHS v q) i) q₀ :=
        ((EuclideanSpace.proj i : Work.Cusp.E4 →L[ℝ] ℝ).continuous.continuousAt).comp hcat
      have hc : ContinuousAt (fun q => |(jcTransMap a D v P c δ hδ hne q - Work.Cusp.polarToUHS v q) i
          - (jcTransMap a D v P c δ hδ hne q₀ - Work.Cusp.polarToUHS v q₀) i|) q₀ :=
        (hci.sub continuousAt_const).abs
      refine hc.eventually (isOpen_Iio.mem_nhds ?_)
      simp
    filter_upwards [hsrcopen.mem_nhds hq₀, hclose] with q hqsrc hqall
    exact IsIntVec.eq_of_close (jcTransMap_int a D v P c δ hδ hne hqsrc)
      (jcTransMap_int a D v P c δ hδ hne hq₀) hqall
  filter_upwards [hev] with q hq
  exact sub_eq_iff_eq_add'.mp (by rw [hq, hm₀])

/-! ## The forward transition is an isometry -/

theorem uhsModel_add_of_three_eq_zero (δ : ℝ) {x v : Work.Cusp.E4} (hv : v 3 = 0) :
    Work.RTInstance.uhsModel δ (x + v) = Work.RTInstance.uhsModel δ x := by
  have h3 : (x + v) 3 = x 3 := by rw [PiLp.add_apply, hv, add_zero]
  simp only [Work.RTInstance.uhsModel, h3]

theorem polarToUHS_ge_cδ (v : Work.Space.Cusp) (a : Work.Space.Assembly) (P : JPin a v)
    {q : Work.Cusp.E4} (hq : q ∈ jBoxR a v P) :
    cδ ≤ (Work.Cusp.polarToUHS v q) 3 := by
  have h3 : (Work.Cusp.polarToUHS v q) 3 = Real.exp (Work.Cusp.R0 - q 0) := rfl
  have hR : Work.Cusp.R0 - rCut = 9/20 := by rw [Work.Cusp.R0, rCut]; norm_num
  have hqcut : q 0 < rCut := hq.2
  have hlt : Work.Cusp.R0 - rCut < Work.Cusp.R0 - q 0 := by linarith
  have hexp : Real.exp (9/20) < Real.exp (Work.Cusp.R0 - q 0) := by
    rw [← hR]; exact Real.exp_lt_exp.mpr hlt
  have hc : cδ = 11/10 := rfl
  rw [h3, hc]
  linarith [exp_nine_twentieth_gt, hexp]

theorem contDiffOn_jcTransMap (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (jcTransMap a D v P c δ hδ hne)
      (jcTransSrc a D v P c δ hδ hne) := by
  intro q hq
  obtain ⟨m, hm⟩ := eventually_jcTransMap_eq a D v P c δ hδ hne hq
  have hcd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q => Work.Cusp.polarToUHS v q + intVec4 m) q :=
    ((cusp_polarToUHS_contDiff v).add contDiff_const).contDiffAt
  exact (hcd.congr_of_eventuallyEq hm).contDiffWithinAt

theorem jcTransMap_metric (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ})
    {q : Work.Cusp.E4} (hq : q ∈ jcTransSrc a D v P c δ hδ hne) (u w : Work.Cusp.E4) :
    (cLayer.model (jcTransMap a D v P c δ hδ hne q)
        (fderiv ℝ (jcTransMap a D v P c δ hδ hne) q u)
        (fderiv ℝ (jcTransMap a D v P c δ hδ hne) q w))
      = (jLayer v).model q u w := by
  obtain ⟨hqR, -⟩ := (mem_jcTransSrc a D v P c δ hδ hne q).mp hq
  have hgt : Work.Cusp.rJ < q 0 := jcTransSrc_gt a D v P c δ hδ hne hq
  have hq14 : (1/4 : ℝ) < q 0 := hqR.1.1
  have hq18 : (1/8 : ℝ) ≤ q 0 := by linarith
  have h3 : (3:ℝ) ≤ q 0 := by rw [Work.Cusp.rJ] at hgt; linarith
  obtain ⟨m, hm⟩ := eventually_jcTransMap_eq a D v P c δ hδ hne hq
  have hmE : jcTransMap a D v P c δ hδ hne =ᶠ[𝓝 q] (fun q => Work.Cusp.polarToUHS v q + intVec4 m) := hm
  have hqm : jcTransMap a D v P c δ hδ hne q = Work.Cusp.polarToUHS v q + intVec4 m :=
    hmE.eq_of_nhds
  have hf : fderiv ℝ (jcTransMap a D v P c δ hδ hne) q
      = fderiv ℝ (Work.Cusp.polarToUHS v) q := by
    rw [hmE.fderiv_eq]
    exact fderiv_add_const (intVec4 m)
  have hLHS : Work.RTInstance.uhsModel cδ (Work.Cusp.polarToUHS v q + intVec4 m)
      (fderiv ℝ (Work.Cusp.polarToUHS v) q u) (fderiv ℝ (Work.Cusp.polarToUHS v) q w)
      = Work.Curvature.warpedMetric (fun r => fillC v * Real.exp r)
          (fun r => fillD * Real.exp r) q u w := by
    rw [uhsModel_add_of_three_eq_zero cδ (intVec4_three m)]
    rw [Work.RTInstance.uhsModel_eq_uhsMetric cδ_pos (polarToUHS_ge_cδ v a P hqR)]
    exact Work.RTOWed.cusp_polarToUHS_isometry v q u w
  have hRHS : (jLayer v).model q u w
      = Work.Curvature.warpedMetric (fun r => fillC v * Real.exp r)
          (fun r => fillD * Real.exp r) q u w := by
    rw [show (jLayer v).model q u w
        = Work.RTInstance.warpedModelA (fillProf v).f (fillProf v).h q u w from rfl]
    rw [Work.RTInstance.warpedModelA_eq_warpedMetric hq18]
    simp only [Work.Curvature.warpedMetric_apply]
    rw [fillProf_f_cusp v h3, fillProf_h_cusp v h3]
  rw [hf, hqm, hRHS]
  exact hLHS

theorem jcTransIso2 (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) :
    TransIso2 (jLayer v).model cLayer.model
      (jcTransMap a D v P c δ hδ hne) (jcTransSrc a D v P c δ hδ hne) :=
  ⟨contDiffOn_jcTransMap a D v P c δ hδ hne, fun q hq u w =>
    jcTransMap_metric a D v P c δ hδ hne hq u w⟩

/-! ## The reverse transition -/

theorem continuousOn_cjTransMap (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) :
    ContinuousOn (cjTransMap a D v P c δ hδ hne) (cjTransSrc a D v P c δ hδ hne) := by
  have hsym : ContinuousOn ((cChart a D v c δ hδ hne).symm) (cjTransSrc a D v P c δ hδ hne) :=
    (OpenPartialHomeomorph.continuousOn_symm (cChart a D v c δ hδ hne)).mono
      (fun q hq => by
        rw [cChart_target]
        exact ((mem_cjTransSrc a D v P c δ hδ hne q).mp hq).1)
  have hjc : ContinuousOn (jChart a D v P) (jChart a D v P).source :=
    OpenPartialHomeomorph.continuousOn _
  have hmt : MapsTo ((cChart a D v c δ hδ hne).symm) (cjTransSrc a D v P c δ hδ hne)
      (jChart a D v P).source := fun q hq => ((mem_cjTransSrc a D v P c δ hδ hne q).mp hq).2
  exact hjc.comp hsym hmt

theorem cjTransMap_mem_jcTransSrc (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ})
    {y : Work.Cusp.E4} (hy : y ∈ cjTransSrc a D v P c δ hδ hne) :
    cjTransMap a D v P c δ hδ hne y ∈ jcTransSrc a D v P c δ hδ hne := by
  obtain ⟨hyR, hyp⟩ := (mem_cjTransSrc a D v P c δ hδ hne y).mp hy
  rw [mem_jcTransSrc]
  constructor
  · show (jChart a D v P) ((cChart a D v c δ hδ hne).symm y) ∈ jBoxR a v P
    rw [← jChart_target]
    exact OpenPartialHomeomorph.map_source (jChart a D v P) hyp
  · show (jChart a D v P).symm ((jChart a D v P) ((cChart a D v c δ hδ hne).symm y))
      ∈ (cChart a D v c δ hδ hne).source
    have hleft : (jChart a D v P).symm ((jChart a D v P) ((cChart a D v c δ hδ hne).symm y))
        = (cChart a D v c δ hδ hne).symm y := OpenPartialHomeomorph.left_inv (jChart a D v P) hyp
    rw [hleft]
    refine OpenPartialHomeomorph.map_source ((cChart a D v c δ hδ hne).symm) ?_
    rw [OpenPartialHomeomorph.symm_source, cChart_target]
    exact hyR

theorem cjTransMap_int (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ})
    {y : Work.Cusp.E4} (hy : y ∈ cjTransSrc a D v P c δ hδ hne) :
    IsIntVec (y - Work.Cusp.polarToUHS v (cjTransMap a D v P c δ hδ hne y)) := by
  obtain ⟨hyR, hyp⟩ := (mem_cjTransSrc a D v P c δ hδ hne y).mp hy
  set q' : Work.Cusp.E4 := jChart a D v P ((cChart a D v c δ hδ hne).symm y) with hq'def
  have hq'tgt : q' ∈ jBoxR a v P := by
    rw [← jChart_target]
    exact OpenPartialHomeomorph.map_source (jChart a D v P) hyp
  have hp_symm : (jChart a D v P).symm q' = (cChart a D v c δ hδ hne).symm y :=
    OpenPartialHomeomorph.left_inv (jChart a D v P) hyp
  have hp_eq : (cChart a D v c δ hδ hne).symm y
      = Work.Cusp.cuspCoordMTop a v (D v) c δ ⟨y, hyR.1⟩ := cChart_symm a D v c δ hδ hne hyR
  -- q' 0 > rJ
  have hq'gt : Work.Cusp.rJ < q' 0 := by
    by_contra hle
    have hle' : q' 0 ≤ Work.Cusp.rJ := not_lt.mp hle
    have hj : (jChart a D v P).symm q' = jCoordM a v (D v) P.cU P.k P.W P.kx P.δ ⟨q', hq'tgt.1⟩ :=
      jChart_symm a D v P hq'tgt
    rw [hj] at hp_symm
    rw [hp_eq] at hp_symm
    by_cases hylt : y 3 < Work.Cusp.beta (Work.Cusp.xOf y)
    · rw [cuspCoordMTop_of_lt a v (D v) c δ ⟨y, hyR.1⟩ hylt,
        jCoordM_of_le (a := a) (v := v) (D := D v) (cU := P.cU) (k := P.k) (W := P.W)
          (kx := P.kx) (δ := P.δ) hq'tgt.1 hle'] at hp_symm
      exact a.incMbar_ne_incY
        (fun ⟨hyTset, _⟩ => (D v).mbarLow_not_TsetTop c δ hyR.1 hylt hyTset) hp_symm.symm
    · have hyge : Work.Cusp.beta (Work.Cusp.xOf y) ≤ y 3 := not_lt.mp hylt
      have hysrc : y ∈ Work.Cusp.cuspSourceTop v c δ := ⟨hyR.1, hyge⟩
      have hnrmY : 1/2 < Work.Cusp.nrm (Work.Cusp.cuspInvOuter v y).1 :=
        nrm_cuspInvOuter_gt_half v c δ hysrc hyR.2
      rw [cuspCoordMTop_of_ge a v (D v) c δ ⟨y, hyR.1⟩ hylt,
        jCoordM_of_le (a := a) (v := v) (D := D v) (cU := P.cU) (k := P.k) (W := P.W)
          (kx := P.kx) (δ := P.δ) hq'tgt.1 hle'] at hp_symm
      have hpair := a.incW_injective v hp_symm.symm
      have hnrmX : Work.Cusp.nrm (Work.Cusp.cuspInvInner v q').1 ≤ 1/2 :=
        nrm_cuspInvInner_le_half v (jBox_subset_polarBox v P.cU P.k P.W P.kx P.δ hq'tgt.1) hle'
      have hnrmeq : Work.Cusp.nrm (Work.Cusp.cuspInvOuter v y).1
          = Work.Cusp.nrm (Work.Cusp.cuspInvInner v q').1 := by
        have h := congrArg (fun z : Work.Space.SquarePt × a.Torus v =>
          Work.Cusp.nrm ((z.1 : Work.Space.SquarePt) : Work.Cusp.E2)) hpair
        simpa using h
      linarith
  -- the two cusp coordinates of the same point
  have hbox : ∀ i, |Work.Cusp.xOf (Work.Cusp.polarToUHS v q') i - P.kx i| < P.δ := hq'tgt.1.2.2.2.2.2
  have hub : q' 0 < rBig := hq'tgt.1.2.1
  have hmemP : Work.Cusp.polarToUHS v q' ∈ Work.Cusp.cuspBoxTop v P.kx P.δ :=
    polarToUHS_mem_cuspBoxTop v P.kx P.δ hbox hq'gt hub
  have hyge : Work.Cusp.beta (Work.Cusp.xOf (Work.Cusp.polarToUHS v q'))
      ≤ (Work.Cusp.polarToUHS v q') 3 := le_of_lt (polarToUHS_above_beta v a P hq'tgt)
  have heq : Work.Cusp.cuspCoordMTop a v (D v) c δ ⟨y, hyR.1⟩
      = Work.Cusp.cuspCoordMTop a v (D v) P.kx P.δ ⟨Work.Cusp.polarToUHS v q', hmemP⟩ := by
    rw [← hp_eq, ← hp_symm]
    rw [jChart_symm a D v P hq'tgt]
    rw [jCoordM_of_gt (a := a) (v := v) (D := D v) (cU := P.cU) (k := P.k) (W := P.W)
      (kx := P.kx) (δ := P.δ) hq'tgt.1 (not_le.mpr hq'gt)]
  have hyge' : Work.Cusp.beta (Work.Cusp.xOf y) ≤ y 3 := by
    by_contra hcon
    have hlt : y 3 < Work.Cusp.beta (Work.Cusp.xOf y) := not_le.mp hcon
    rw [cuspCoordMTop_of_lt a v (D v) c δ ⟨y, hyR.1⟩ hlt,
      cuspCoordMTop_of_ge a v (D v) P.kx P.δ ⟨_, hmemP⟩ (not_lt.mpr hyge)] at heq
    exact a.incMbar_ne_incY
      (fun ⟨hyTset, _⟩ => (D v).mbarLow_not_TsetTop c δ hyR.1 hlt hyTset) heq
  obtain ⟨m, hm⟩ := Work.RTOWed.cuspCoordMTop_high_diff a v (D v) hyR.1 hmemP hyge' hyge heq
  refine ⟨m, ?_⟩
  rw [show cjTransMap a D v P c δ hδ hne y = q' from rfl]
  rw [hm]
  simp only [intVec4]
  abel

theorem continuousOn_cjTransMap_comp (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) :
    ContinuousOn (fun y => y - Work.Cusp.polarToUHS v (cjTransMap a D v P c δ hδ hne y))
      (cjTransSrc a D v P c δ hδ hne) := by
  have hcomp : ContinuousOn (fun y => Work.Cusp.polarToUHS v (cjTransMap a D v P c δ hδ hne y))
      (cjTransSrc a D v P c δ hδ hne) :=
    ((cusp_polarToUHS_contDiff v).continuous.continuousOn).comp
      (continuousOn_cjTransMap a D v P c δ hδ hne) (fun y hy => Set.mem_univ _)
  exact continuousOn_id.sub hcomp

theorem eventually_cjTransMap_eq (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ})
    {y₀ : Work.Cusp.E4} (hy₀ : y₀ ∈ cjTransSrc a D v P c δ hδ hne) :
    ∃ m : Fin 3 → ℤ, ∀ᶠ y in 𝓝 y₀,
      cjTransMap a D v P c δ hδ hne y = polarToUHSInv v (y - intVec4 m) := by
  have hsrcopen : IsOpen (cjTransSrc a D v P c δ hδ hne) :=
    OpenPartialHomeomorph.open_source _
  obtain ⟨m₀, hm₀⟩ := cjTransMap_int a D v P c δ hδ hne hy₀
  refine ⟨m₀, ?_⟩
  have hcont := continuousOn_cjTransMap_comp a D v P c δ hδ hne
  have hcat : ContinuousAt (fun y => y - Work.Cusp.polarToUHS v (cjTransMap a D v P c δ hδ hne y)) y₀ :=
    hcont.continuousAt (hsrcopen.mem_nhds hy₀)
  have hev : ∀ᶠ y in 𝓝 y₀, cjTransMap a D v P c δ hδ hne y
      = polarToUHSInv v (y - intVec4 m₀) := by
    have hclose : ∀ᶠ y in 𝓝 y₀, ∀ i : Fin 4,
        |(y - Work.Cusp.polarToUHS v (cjTransMap a D v P c δ hδ hne y)) i
          - (y₀ - Work.Cusp.polarToUHS v (cjTransMap a D v P c δ hδ hne y₀)) i| < 1/2 := by
      rw [Filter.eventually_all]
      intro i
      have hci : ContinuousAt (fun y =>
          (y - Work.Cusp.polarToUHS v (cjTransMap a D v P c δ hδ hne y)) i) y₀ :=
        ((EuclideanSpace.proj i : Work.Cusp.E4 →L[ℝ] ℝ).continuous.continuousAt).comp hcat
      have hc : ContinuousAt (fun y =>
          |(y - Work.Cusp.polarToUHS v (cjTransMap a D v P c δ hδ hne y)) i
            - (y₀ - Work.Cusp.polarToUHS v (cjTransMap a D v P c δ hδ hne y₀)) i|) y₀ :=
        (hci.sub continuousAt_const).abs
      refine hc.eventually (isOpen_Iio.mem_nhds ?_)
      simp
    filter_upwards [hsrcopen.mem_nhds hy₀, hclose] with y hy hclose_all
    rw [hm₀] at hclose_all
    have hH : y - Work.Cusp.polarToUHS v (cjTransMap a D v P c δ hδ hne y) = intVec4 m₀ :=
      IsIntVec.eq_of_close (cjTransMap_int a D v P c δ hδ hne hy) ⟨m₀, rfl⟩ hclose_all
    rw [← polarToUHSInv_polarToUHS v (cjTransMap a D v P c δ hδ hne y)]
    congr 1
    rw [← hH]; abel
  exact hev

theorem contDiffOn_cjTransMap (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cjTransMap a D v P c δ hδ hne)
      (cjTransSrc a D v P c δ hδ hne) := by
  intro y hy
  obtain ⟨m, hm⟩ := eventually_cjTransMap_eq a D v P c δ hδ hne hy
  have hy3 : 0 < (y - intVec4 m) 3 := by
    have hyR := ((mem_cjTransSrc a D v P c δ hδ hne y).mp hy).1
    rw [PiLp.sub_apply, intVec4_three, sub_zero]
    exact lt_trans (by norm_num [Work.Cusp.s1]) hyR.1.2.1
  have hg : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Work.Cusp.E4 => polarToUHSInv v z) (y - intVec4 m) :=
    (polarToUHSInv_contDiffOn v).contDiffAt
      ((isOpen_lt continuous_const (by fun_prop : Continuous fun q : Work.Cusp.E4 => q 3)).mem_nhds hy3)
  have hf : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : Work.Cusp.E4 => y - intVec4 m) y := by fun_prop
  have hcd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => polarToUHSInv v (y - intVec4 m)) y :=
    ContDiffAt.comp (f := fun y : Work.Cusp.E4 => y - intVec4 m)
      (g := fun z : Work.Cusp.E4 => polarToUHSInv v z) y hg hf
  exact (hcd.congr_of_eventuallyEq hm).contDiffWithinAt

theorem cjTransMap_metric (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ})
    {y : Work.Cusp.E4} (hy : y ∈ cjTransSrc a D v P c δ hδ hne) (u w : Work.Cusp.E4) :
    (jLayer v).model (cjTransMap a D v P c δ hδ hne y)
        (fderiv ℝ (cjTransMap a D v P c δ hδ hne) y u)
        (fderiv ℝ (cjTransMap a D v P c δ hδ hne) y w)
      = cLayer.model y u w := by
  have hxmem : cjTransMap a D v P c δ hδ hne y ∈ jcTransSrc a D v P c δ hδ hne :=
    cjTransMap_mem_jcTransSrc a D v P c δ hδ hne hy
  have hsrcopen : IsOpen (cjTransSrc a D v P c δ hδ hne) :=
    OpenPartialHomeomorph.open_source _
  have hsrcopenjc : IsOpen (jcTransSrc a D v P c δ hδ hne) :=
    OpenPartialHomeomorph.open_source _
  -- the round trip `jcTransMap (cjTransMap y) = y` near `y`
  have hcomp : (fun y' => jcTransMap a D v P c δ hδ hne (cjTransMap a D v P c δ hδ hne y')) =ᶠ[𝓝 y] id := by
    filter_upwards [hsrcopen.mem_nhds hy] with y' hy'
    obtain ⟨hy'R, hy'p⟩ := (mem_cjTransSrc a D v P c δ hδ hne y').mp hy'
    rw [show cjTransMap a D v P c δ hδ hne y' = (jChart a D v P) ((cChart a D v c δ hδ hne).symm y') from rfl]
    rw [show jcTransMap a D v P c δ hδ hne ((jChart a D v P) ((cChart a D v c δ hδ hne).symm y'))
        = (cChart a D v c δ hδ hne)
            ((jChart a D v P).symm ((jChart a D v P) ((cChart a D v c δ hδ hne).symm y'))) from rfl]
    rw [OpenPartialHomeomorph.left_inv (jChart a D v P) hy'p]
    exact OpenPartialHomeomorph.right_inv (cChart a D v c δ hδ hne) (by rwa [cChart_target])
  have hfderivc : fderiv ℝ (fun y' => jcTransMap a D v P c δ hδ hne (cjTransMap a D v P c δ hδ hne y')) y
      = ContinuousLinearMap.id ℝ Work.Cusp.E4 := by
    rw [hcomp.fderiv_eq]; exact fderiv_id
  have hdiffg : DifferentiableAt ℝ (cjTransMap a D v P c δ hδ hne) y :=
    ((contDiffOn_cjTransMap a D v P c δ hδ hne).contDiffAt (hsrcopen.mem_nhds hy)).differentiableAt
      (by simp)
  have hdifff : DifferentiableAt ℝ (jcTransMap a D v P c δ hδ hne)
      (cjTransMap a D v P c δ hδ hne y) :=
    ((contDiffOn_jcTransMap a D v P c δ hδ hne).contDiffAt (hsrcopenjc.mem_nhds hxmem)).differentiableAt
      (by simp)
  have hchain : (fderiv ℝ (jcTransMap a D v P c δ hδ hne) (cjTransMap a D v P c δ hδ hne y)).comp
      (fderiv ℝ (cjTransMap a D v P c δ hδ hne) y) = ContinuousLinearMap.id ℝ Work.Cusp.E4 := by
    rw [← show fderiv ℝ (fun y' => jcTransMap a D v P c δ hδ hne (cjTransMap a D v P c δ hδ hne y')) y
        = (fderiv ℝ (jcTransMap a D v P c δ hδ hne) (cjTransMap a D v P c δ hδ hne y)).comp
          (fderiv ℝ (cjTransMap a D v P c δ hδ hne) y) from by
      rw [show (fun y' => jcTransMap a D v P c δ hδ hne (cjTransMap a D v P c δ hδ hne y'))
          = (fun z => jcTransMap a D v P c δ hδ hne z) ∘ (fun y' => cjTransMap a D v P c δ hδ hne y') from rfl]
      exact fderiv_comp y hdifff hdiffg]
    exact hfderivc
  have hcompAt : (jcTransMap a D v P c δ hδ hne) (cjTransMap a D v P c δ hδ hne y) = y :=
    hcomp.eq_of_nhds
  have hAu : fderiv ℝ (jcTransMap a D v P c δ hδ hne) (cjTransMap a D v P c δ hδ hne y)
      (fderiv ℝ (cjTransMap a D v P c δ hδ hne) y u) = u := by
    have := DFunLike.congr_fun hchain u; simpa using this
  have hAv : fderiv ℝ (jcTransMap a D v P c δ hδ hne) (cjTransMap a D v P c δ hδ hne y)
      (fderiv ℝ (cjTransMap a D v P c δ hδ hne) y w) = w := by
    have := DFunLike.congr_fun hchain w; simpa using this
  have hkey := jcTransMap_metric a D v P c δ hδ hne hxmem
    (fderiv ℝ (cjTransMap a D v P c δ hδ hne) y u)
    (fderiv ℝ (cjTransMap a D v P c δ hδ hne) y w)
  rw [hcompAt, hAu, hAv] at hkey
  exact hkey.symm

theorem cjTransIso2 (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) :
    TransIso2 cLayer.model (jLayer v).model
      (cjTransMap a D v P c δ hδ hne) (cjTransSrc a D v P c δ hδ hne) :=
  ⟨contDiffOn_cjTransMap a D v P c δ hδ hne, fun q hq u w =>
    cjTransMap_metric a D v P c δ hδ hne hq u w⟩

theorem jTrans_coll_iso_aux (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) :
    TransIso2 (jLayer v).model cLayer.model
        (jcTransMap a D v P c δ hδ hne) (jcTransSrc a D v P c δ hδ hne) ∧
      TransIso2 cLayer.model (jLayer v).model
        (cjTransMap a D v P c δ hδ hne) (cjTransSrc a D v P c δ hδ hne) :=
  ⟨jcTransIso2 a D v P c δ hδ hne, cjTransIso2 a D v P c δ hδ hne⟩


theorem jTrans_coll_iso (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : Work.RTOwed.JPin a v) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) :
    Work.RTOwed.TransIso2 (Work.RTOwed.jLayer v).model Work.RTOwed.cLayer.model
        (Work.RTOwed.jcTransMap a D v P c δ hδ hne) (Work.RTOwed.jcTransSrc a D v P c δ hδ hne) ∧
      Work.RTOwed.TransIso2 Work.RTOwed.cLayer.model (Work.RTOwed.jLayer v).model
        (Work.RTOwed.cjTransMap a D v P c δ hδ hne) (Work.RTOwed.cjTransSrc a D v P c δ hδ hne) := by
  exact jTrans_coll_iso_aux a D v P c δ hδ hne

end Work.RTOwed
