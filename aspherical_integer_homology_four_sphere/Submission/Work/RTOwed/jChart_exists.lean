import Mathlib
import Submission.Work.RTOwed.FillBigDefs
import Submission.Work.Cusp.isOpenEmbedding_polarCoordM
import Submission.Work.Cusp.isOpenEmbedding_cuspCoordMTop
import Submission.Work.Cusp.isOpenEmbedding_incW_interior
import Submission.Work.Cusp.isOpenEmbedding_layerPtI
import Submission.Work.Cusp.isOpen_cuspBoxTop
import Submission.Work.Cusp.cuspInvOuter_mem_SqTop
import Submission.Work.Cusp.cuspInvInner_mem_polarStratum
import Submission.Work.Cusp.TopBox
import Submission.Work.Cusp.TopLayer
import Submission.Work.Cusp.cuspTopUp_eq
import Submission.Work.Cusp.cuspCoordMTop_continuous
import Submission.Work.Cusp.cuspCoordMTop_injective
import Submission.Work.Cusp.abs_le_nrm
import Submission.Work.Cusp.polarBoxSect_aux
import Submission.Work.Cusp.ThetaPolarS_cuspInvInner
import Submission.Work.RTOwed.jCoordM_continuous
import Submission.Work.RTOwed.jCoordM_injective
import Submission.Work.RTOwed.jCoordM_isOpenMap
import Submission.Work.Cusp.isOpen_polarTargetS

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

open Work.Cusp

/-- The first (`p`-part) component of the filling point associated with the polar coordinate `q`. -/
def jPolPt (v : Work.Space.Cusp) (q : E4) : E2 := (cuspInvInner v q).1

/-- The second (`y`-part) component of the filling point associated with the polar coordinate `q`. -/
def jPolY (v : Work.Space.Cusp) (q : E4) : E2 := (cuspInvInner v q).2

theorem jPolPt_def (v : Work.Space.Cusp) (q : E4) : jPolPt v q = (cuspInvInner v q).1 := rfl
theorem jPolY_def (v : Work.Space.Cusp) (q : E4) : jPolY v q = (cuspInvInner v q).2 := rfl

theorem continuous_jPolPt (v : Work.Space.Cusp) : Continuous (jPolPt v) :=
  continuous_fst.comp (continuous_cuspInvInner v)

theorem continuous_jPolY (v : Work.Space.Cusp) : Continuous (jPolY v) :=
  continuous_snd.comp (continuous_cuspInvInner v)

section BoxOpen

/-- The wedge pinning of `jBox` is a single open condition. -/
theorem jBox_wedge_iff (a : ℝ) (k : Fin 4) :
    (a ∈ Set.Ico (0 : ℝ) 1 ∧ Int.fract a ∈ Set.Ioo ((k : ℝ) / 4) (((k : ℝ) + 1) / 4))
      ↔ a ∈ Set.Ioo ((k : ℝ) / 4) (((k : ℝ) + 1) / 4) := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) / 4 := by positivity
  have hk1 : ((k : ℝ) + 1) / 4 ≤ 1 := by
    have hk3 : (k : ℝ) ≤ 3 := by exact_mod_cast Nat.le_of_lt_succ k.isLt
    linarith
  constructor
  · rintro ⟨hu, hf⟩
    rwa [Int.fract_eq_self.mpr hu] at hf
  · intro hf
    have h0 : 0 ≤ a := by linarith [hf.1, hk0]
    have h1 : a < 1 := by linarith [hf.2, hk1]
    exact ⟨⟨h0, h1⟩, by rw [Int.fract_eq_self.mpr ⟨h0, h1⟩]; exact hf⟩

/-- The `i`-th horizontal coordinate of `polarToUHS v q` is continuous in `q`. -/
theorem continuous_xOf_polarToUHS_apply (v : Work.Space.Cusp) (i : Fin 3) :
    Continuous (fun q : Work.Cusp.E4 => Work.Cusp.xOf (Work.Cusp.polarToUHS v q) i) := by
  unfold Work.Cusp.xOf Work.Cusp.polarToUHS
  fun_prop

/-- The box `jBox` of a junction chart is open. -/
theorem isOpen_jBox (v : Work.Space.Cusp) (cU : ℝ) (k : Fin 4) (W : Set Work.Cusp.E2)
    (kx : Work.Cusp.E3) (δ : ℝ) (hW : IsOpen W) :
    IsOpen (jBox v cU k W kx δ) := by
  have h1 : IsOpen {q : Work.Cusp.E4 | 1/4 < q 0 ∧ q 0 < rBig} := by
    have hcont : Continuous (fun q : Work.Cusp.E4 => q 0) :=
      PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 0
    have h : {q : Work.Cusp.E4 | 1/4 < q 0 ∧ q 0 < rBig}
        = (fun q : Work.Cusp.E4 => q 0) ⁻¹' Set.Ioo (1/4) rBig := rfl
    rw [h]
    exact isOpen_Ioo.preimage hcont
  have h2 : IsOpen {q : Work.Cusp.E4 | (!₂[q 2, q 3] : Work.Cusp.E2) ∈ W} :=
    hW.preimage (by fun_prop)
  have h3 : IsOpen {q : Work.Cusp.E4 |
      Work.Cusp.uqOf v q - cU ∈ Set.Ioo ((k : ℝ) / 4) (((k : ℝ) + 1) / 4)} :=
    isOpen_Ioo.preimage ((Work.Cusp.polarTargetS_continuous_uqOf v).sub continuous_const)
  have h4 : IsOpen {q : Work.Cusp.E4 |
      ∀ i, |Work.Cusp.xOf (Work.Cusp.polarToUHS v q) i - kx i| < δ} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt (((continuous_xOf_polarToUHS_apply v i).sub continuous_const).abs) continuous_const
  have hdecomp : jBox v cU k W kx δ =
      {q : Work.Cusp.E4 | 1/4 < q 0 ∧ q 0 < rBig}
        ∩ {q : Work.Cusp.E4 | (!₂[q 2, q 3] : Work.Cusp.E2) ∈ W}
        ∩ {q : Work.Cusp.E4 |
            Work.Cusp.uqOf v q - cU ∈ Set.Ioo ((k : ℝ) / 4) (((k : ℝ) + 1) / 4)}
        ∩ {q : Work.Cusp.E4 | ∀ i, |Work.Cusp.xOf (Work.Cusp.polarToUHS v q) i - kx i| < δ} := by
    ext q
    simp only [jBox, Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨a, b, c, d, e, f⟩
      exact ⟨⟨⟨⟨a, b⟩, c⟩, (jBox_wedge_iff (Work.Cusp.uqOf v q - cU) k).mp ⟨d, e⟩⟩, f⟩
    · rintro ⟨⟨⟨a, b⟩, c⟩, d⟩
      exact ⟨a.1, a.2, b, ((jBox_wedge_iff (Work.Cusp.uqOf v q - cU) k).mpr c).1,
        ((jBox_wedge_iff (Work.Cusp.uqOf v q - cU) k).mpr c).2, d⟩
  rw [hdecomp]
  exact (((h1.inter h2).inter h3).inter h4)

end BoxOpen


section Branch

variable (a : Work.Space.Assembly) (v : Work.Space.Cusp) (D : Work.Cusp.CuspGlueData a v)
  (cU : ℝ) (k : Fin 4) (W : Set Work.Cusp.E2) (kx : Work.Cusp.E3) (δ : ℝ)

/-- The polar branch of `jCoordM`. -/
theorem jCoordM_of_le {q : Work.Cusp.E4} (hq : q ∈ jBox v cU k W kx δ) (h : q 0 ≤ rJ) :
    jCoordM a v D cU k W kx δ ⟨q, hq⟩ =
      a.incW v
        ((⟨(cuspInvInner v q).1, by
            have h1 : q ∈ polarBox := jBox_subset_polarBox v cU k W kx δ hq
            have hstr := cuspInvInner_mem_polarStratum v q h1 h
            simp only [polarStratum, Set.mem_ofPred_eq] at hstr
            refine ⟨le_trans (abs_le_nrm _ 0) ?_, le_trans (abs_le_nrm _ 1) ?_⟩ <;>
              linarith [hstr.2]⟩ : Work.Space.SquarePt),
          D.tor.symm (fun i => (((cuspInvInner v q).2 i : ℝ) : AddCircle (1 : ℝ)))) := by
  unfold jCoordM
  rw [dif_pos h]

/-- The collar branch of `jCoordM`. -/
theorem jCoordM_of_gt {q : Work.Cusp.E4} (hq : q ∈ jBox v cU k W kx δ) (h : ¬ q 0 ≤ rJ) :
    jCoordM a v D cU k W kx δ ⟨q, hq⟩ =
      cuspCoordMTop a v D kx δ ⟨polarToUHS v q, by
        obtain ⟨-, hub, -, -, -, hbox⟩ := hq
        exact polarToUHS_mem_cuspBoxTop v kx δ hbox (not_le.mp h) hub⟩ := by
  unfold jCoordM
  rw [dif_neg h]

end Branch

theorem jChart_exists (a : Work.Space.Assembly) (v : Work.Space.Cusp) (D : Work.Cusp.CuspGlueData a v)
    (cU : ℝ) (k : Fin 4) (W : Set Work.Cusp.E2)
    (kx : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2) (hW : IsOpen W)
    (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    ∃ Ψ : OpenPartialHomeomorph a.Mhat Work.Cusp.E4,
      Ψ.source = Work.RTOwed.jCoordM a v D cU k W kx δ '' (Set.univ : Set {q : Work.Cusp.E4 // q ∈ Work.RTOwed.jBox v cU k W kx δ}) ∧
      Ψ.target = Work.RTOwed.jBox v cU k W kx δ ∧
      ∀ (q : Work.Cusp.E4) (hq : q ∈ Work.RTOwed.jBox v cU k W kx δ),
        Ψ (Work.RTOwed.jCoordM a v D cU k W kx δ ⟨q, hq⟩) = q := by
  have hf : Topology.IsOpenEmbedding (jCoordM a v D cU k W kx δ) :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      (Work.RTOWed.jCoordM_continuous a v D cU k W kx δ hδ hW hsec)
      (Work.RTOWed.jCoordM_injective a v D cU k W kx δ hδ hW hsec)
      (Work.RTOWed.jCoordM_isOpenMap a v D cU k W kx δ hδ hW hsec)
  have hbox : IsOpen (jBox v cU k W kx δ) := isOpen_jBox v cU k W kx δ hW
  by_cases hne : (jBox v cU k W kx δ).Nonempty
  · let BB : TopologicalSpace.Opens Work.Cusp.E4 := ⟨jBox v cU k W kx δ, hbox⟩
    let e : OpenPartialHomeomorph BB Work.Cusp.E4 :=
      BB.openPartialHomeomorphSubtypeCoe hne.to_subtype
    have hesrc : e.source = (Set.univ : Set BB) :=
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source BB hne.to_subtype
    have hetgt : e.target = jBox v cU k W kx δ :=
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target BB hne.to_subtype
    have hecoe : (e : BB → Work.Cusp.E4) = Subtype.val :=
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_coe BB hne.to_subtype
    refine ⟨e.lift_openEmbedding hf, ?_, ?_, ?_⟩
    · rw [OpenPartialHomeomorph.lift_openEmbedding_source, hesrc]
    · rw [OpenPartialHomeomorph.lift_openEmbedding_target, hetgt]
    · intro q hq
      rw [OpenPartialHomeomorph.lift_openEmbedding_apply, hecoe]
  · have hBe : jBox v cU k W kx δ = ∅ := not_nonempty_iff_eq_empty.mp hne
    have hEmpty : IsEmpty {q : Work.Cusp.E4 // q ∈ jBox v cU k W kx δ} :=
      (isEmpty_subtype _).mpr (fun x hx => by rw [hBe] at hx; exact hx)
    refine ⟨{ toFun := fun _ => (0 : Work.Cusp.E4)
              invFun := fun _ => Classical.arbitrary a.Mhat
              source := ∅
              target := ∅
              map_source' := by simp
              map_target' := by simp
              left_inv' := by simp
              right_inv' := by simp
              open_source := isOpen_empty
              open_target := isOpen_empty
              continuousOn_toFun := continuousOn_empty _
              continuousOn_invFun := continuousOn_empty _ }, ?_, ?_, ?_⟩
    · rw [Set.image_eq_empty.mpr (univ_eq_empty_iff.mpr hEmpty)]
    · exact hBe.symm
    · intro q hq
      rw [hBe] at hq
      exact absurd hq (by simp)

end Work.RTOwed
