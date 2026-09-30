import Mathlib
import Submission.Work.RTOwed.FillBigDefs
import Submission.Work.RTOwed.cuspInvOuter_polarToUHS_eq
import Submission.Work.RTOwed.polarToUHS_isOpenEmbedding
import Submission.Work.Cusp.cuspCoordMTop_continuous
import Submission.Work.Cusp.cuspInvInner_continuousOn
import Submission.Work.Cusp.cuspInvInner_mem_polarStratum
import Submission.Work.Cusp.abs_le_nrm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section
open Set Topology Function

namespace Work.RTOWed

open Work.Cusp Work.RTOwed

/-! ### Auxiliary lemmas for the continuity of the junction coordinate inclusion -/

/-- `R₀ − log sTop < rJ`: the junction `r = rJ` lies strictly inside the collar height window. -/
lemma jcR0_sub_log_sTop_lt_rJ : R0 - Real.log sTop < rJ := by
  have hsJ : Real.exp (1 / 2 : ℝ) < sTop := by simpa [sJ] using sJ_lt_sTop
  have hlog : (1 / 2 : ℝ) < Real.log sTop := by
    rw [← Real.log_exp (1 / 2)]
    exact Real.log_lt_log (Real.exp_pos _) hsJ
  have h1 : R0 - rJ = 1 / 2 := by norm_num [R0, rJ]
  linarith

/-- `s₁ < exp (R₀ − rBig)`. -/
lemma jcexp_R0_sub_rBig_gt_s1 : s1 < Real.exp (R0 - rBig) := by
  rw [R0_sub_rBig]; exact exp_one_tenth_gt_s1

/-- A point of the polar stratum of the filling square lies in the square. -/
lemma jc_mem_sq_of_polarStratum {p : E2} (hp : p ∈ polarStratum) : p ∈ Work.Space.Sq :=
  ⟨le_trans (abs_le_nrm p 0) hp.2, le_trans (abs_le_nrm p 1) hp.2⟩

/-- **The image of the upper part of the junction box lies in the collar box.**  If `q` is a point
of the junction box with `R₀ − log sTop < q 0`, then `polarToUHS v q ∈ cuspBoxTop v kx δ`. -/
lemma jcPolarToUHS_mem_cuspBoxTop_lt (v : Work.Space.Cusp) (cU : ℝ) (k : Fin 4) (W : Set E2)
    (kx : E3) (δ : ℝ) {q : E4} (hq : q ∈ jBox v cU k W kx δ)
    (h : R0 - Real.log sTop < q 0) : polarToUHS v q ∈ cuspBoxTop v kx δ := by
  obtain ⟨h1, h2, -, -, -, hbox⟩ := hq
  refine ⟨hbox, ?_, ?_⟩
  · calc s1 < Real.exp (R0 - rBig) := jcexp_R0_sub_rBig_gt_s1
      _ < Real.exp (R0 - q 0) := Real.exp_lt_exp.mpr (by linarith)
  · have h3 : Real.exp (R0 - q 0) < Real.exp (Real.log sTop) := Real.exp_lt_exp.mpr (by linarith)
    rwa [Real.exp_log sTop_pos] at h3

/-- The same for the closed collar half `q 0 ≥ rJ`. -/
lemma jcPolarToUHS_mem_cuspBoxTop_of_ge (v : Work.Space.Cusp) (cU : ℝ) (k : Fin 4) (W : Set E2)
    (kx : E3) (δ : ℝ) {q : E4} (hq : q ∈ jBox v cU k W kx δ) (h : rJ ≤ q 0) :
    polarToUHS v q ∈ cuspBoxTop v kx δ :=
  jcPolarToUHS_mem_cuspBoxTop_lt v cU k W kx δ hq (lt_of_lt_of_le jcR0_sub_log_sTop_lt_rJ h)

/-- **The polar branch** of `jCoordM`: the point of the filling piece recovered by the inverse
polar chart from a point `q` of the polar box with `q 0 ≤ rJ`. -/
def jcInnerFun (a : Work.Space.Assembly) (v : Work.Space.Cusp) (D : CuspGlueData a v)
    (q : E4) (hq : q ∈ polarBox) (h : q 0 ≤ rJ) : a.Mhat :=
  a.incW v
    ((⟨(cuspInvInner v q).1,
        jc_mem_sq_of_polarStratum (cuspInvInner_mem_polarStratum v q hq h)⟩ :
        Work.Space.SquarePt),
      D.tor.symm (fun i => (((cuspInvInner v q).2 i : ℝ) : AddCircle (1 : ℝ))))

/-- `jCoordM` is the polar branch below the junction. -/
theorem jcCoordM_eq_innerFun (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (cU : ℝ) (k : Fin 4) (W : Set E2) (kx : E3) (δ : ℝ)
    {q : E4} (hq : q ∈ jBox v cU k W kx δ) (h : q 0 ≤ rJ) :
    jCoordM a v D cU k W kx δ ⟨q, hq⟩
      = jcInnerFun a v D q (jBox_subset_polarBox v cU k W kx δ hq) h := by
  unfold jCoordM jcInnerFun
  rw [dif_pos h]

/-- `jCoordM` is the collar branch strictly above the junction. -/
theorem jcCoordM_eq_collarFun (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (cU : ℝ) (k : Fin 4) (W : Set E2) (kx : E3) (δ : ℝ)
    {q : E4} (hq : q ∈ jBox v cU k W kx δ) (h : ¬ q 0 ≤ rJ)
    (hx : polarToUHS v q ∈ cuspBoxTop v kx δ) :
    jCoordM a v D cU k W kx δ ⟨q, hq⟩ = cuspCoordMTop a v D kx δ ⟨polarToUHS v q, hx⟩ := by
  unfold jCoordM
  rw [dif_neg h]

/-- **The two branches of `jCoordM` agree at the junction** `q 0 = rJ`. -/
theorem jcCoordM_eq_collarFun_at_junction (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (cU : ℝ) (k : Fin 4) (W : Set E2) (kx : E3) (δ : ℝ)
    {q : E4} (hq : q ∈ jBox v cU k W kx δ) (h : q 0 = rJ)
    (hx : polarToUHS v q ∈ cuspBoxTop v kx δ) :
    jCoordM a v D cU k W kx δ ⟨q, hq⟩ = cuspCoordMTop a v D kx δ ⟨polarToUHS v q, hx⟩ := by
  rw [jcCoordM_eq_innerFun a v D cU k W kx δ hq (le_of_eq h)]
  have h3 : (polarToUHS v q).ofLp 3 = sJ := by
    rw [polarToUHS_three, h, R0, rJ, sJ]; norm_num
  have hge : beta (xOf (polarToUHS v q)) ≤ (polarToUHS v q).ofLp 3 := by
    rw [h3]
    exact le_of_lt (lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ)
  rw [cuspCoordMTop_eq_ge a v D kx δ ⟨polarToUHS v q, hx⟩ hge]
  rw [cuspCoordMTopUp]
  unfold jcInnerFun
  have key := (cuspInvOuter_polarToUHS_eq v (le_of_eq h.symm)).symm
  refine congrArg (a.incW v) ?_
  exact Prod.ext (Subtype.ext (congrArg Prod.fst key))
    (congrArg (fun z : E2 => D.tor.symm (fun i => (((z i : ℝ)) : AddCircle (1 : ℝ))))
      (congrArg Prod.snd key))

/-! ### Continuity of `jCoordM` -/

theorem jCoordM_continuous (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : Work.Cusp.CuspGlueData a v) (cU : ℝ) (k : Fin 4) (W : Set Work.Cusp.E2)
    (kx : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2) (hW : IsOpen W)
    (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    Continuous (Work.RTOwed.jCoordM a v D cU k W kx δ) := by
  let X := {q : E4 // q ∈ jBox v cU k W kx δ}
  have hfirst : Continuous fun q : X => q.1 0 :=
    (by fun_prop : Continuous fun q : E4 => q 0).comp continuous_subtype_val
  have hA : IsClosed {q : X | q.1 0 ≤ rJ} := isClosed_le hfirst continuous_const
  have hB : IsClosed {q : X | rJ ≤ q.1 0} := isClosed_le continuous_const hfirst
  have hle : ContinuousOn (fun q : X => jCoordM a v D cU k W kx δ q) {q : X | q.1 0 ≤ rJ} := by
    rw [continuousOn_iff_continuous_domRestrict]
    show Continuous fun r : {q : X // q.1 0 ≤ rJ} => jCoordM a v D cU k W kx δ r.1
    have hInner : Continuous (fun r : {q : X // q.1 0 ≤ rJ} =>
        jcInnerFun a v D r.1.1 (jBox_subset_polarBox v cU k W kx δ r.1.2) r.2) := by
      unfold jcInnerFun
      have hci : Continuous (fun r : {q : X // q.1 0 ≤ rJ} => cuspInvInner v r.1.1) :=
        (continuous_cuspInvInner v).comp (continuous_subtype_val.comp continuous_subtype_val)
      have hSq : Continuous (fun r : {q : X // q.1 0 ≤ rJ} =>
          (⟨(cuspInvInner v r.1.1).1,
            jc_mem_sq_of_polarStratum (cuspInvInner_mem_polarStratum v r.1.1
              (jBox_subset_polarBox v cU k W kx δ r.1.2) r.2)⟩ : Work.Space.SquarePt)) :=
        hci.fst.subtype_mk
          (fun r => jc_mem_sq_of_polarStratum (cuspInvInner_mem_polarStratum v r.1.1
            (jBox_subset_polarBox v cU k W kx δ r.1.2) r.2))
      have hTor : Continuous (fun r : {q : X // q.1 0 ≤ rJ} =>
          D.tor.symm (fun i => (((cuspInvInner v r.1.1).2 i : ℝ) : AddCircle (1 : ℝ)))) := by
        apply D.tor.symm.continuous.comp
        fun_prop
      exact (a.continuous_incW v).comp (hSq.prodMk hTor)
    refine Continuous.congr hInner (fun r => ?_)
    exact (jcCoordM_eq_innerFun a v D cU k W kx δ r.1.2 r.2).symm
  have hge : ContinuousOn (fun q : X => jCoordM a v D cU k W kx δ q) {q : X | rJ ≤ q.1 0} := by
    rw [continuousOn_iff_continuous_domRestrict]
    show Continuous fun r : {q : X // rJ ≤ q.1 0} => jCoordM a v D cU k W kx δ r.1
    have hCollar : Continuous (fun r : {q : X // rJ ≤ q.1 0} =>
        cuspCoordMTop a v D kx δ ⟨polarToUHS v r.1.1,
          jcPolarToUHS_mem_cuspBoxTop_of_ge v cU k W kx δ r.1.2 r.2⟩) := by
      have hval : Continuous fun r : {q : X // rJ ≤ q.1 0} => (r.1.1 : E4) :=
        continuous_subtype_val.comp continuous_subtype_val
      have hptu : Continuous fun r : {q : X // rJ ≤ q.1 0} => polarToUHS v r.1.1 :=
        (by unfold polarToUHS; fun_prop : Continuous fun q : E4 => polarToUHS v q).comp hval
      refine (cuspCoordMTop_continuous a v D kx δ).comp ?_
      exact Continuous.subtype_mk hptu
        (fun r => jcPolarToUHS_mem_cuspBoxTop_of_ge v cU k W kx δ r.1.2 r.2)
    refine Continuous.congr hCollar (fun r => ?_)
    rcases lt_or_eq_of_le r.2 with hlt | heq
    · exact (jcCoordM_eq_collarFun a v D cU k W kx δ r.1.2 (not_le.mpr hlt)
        (jcPolarToUHS_mem_cuspBoxTop_of_ge v cU k W kx δ r.1.2 r.2)).symm
    · exact (jcCoordM_eq_collarFun_at_junction a v D cU k W kx δ r.1.2 heq.symm
        (jcPolarToUHS_mem_cuspBoxTop_of_ge v cU k W kx δ r.1.2 r.2)).symm
  have hunion : {q : X | q.1 0 ≤ rJ} ∪ {q : X | rJ ≤ q.1 0} = Set.univ := by
    ext q; simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact le_total _ _
  rw [← continuousOn_univ, ← hunion]
  exact hle.union_of_isClosed hge hA hB

end Work.RTOWed
