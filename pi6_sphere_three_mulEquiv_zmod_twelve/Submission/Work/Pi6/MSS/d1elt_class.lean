import Mathlib
import Submission.Work.Pi6.MSS.e2FinalDefs
import Submission.Work.Pi6.MSS.E1B.homIsoH_hom_cyclesMk
import Submission.Work.Pi6.MSS.E1B.homIsoH_inv
import Submission.Work.SSSR.kF_eq_of_lift
import Submission.Work.SSSR.homologyMap_cyclesMk
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits HomologicalComplex

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- Consecutive differentials of a chain complex of `𝕜`-modules kill every element. -/
private lemma d1elt_dcd {𝕜 : Type} [Field 𝕜] (C : ChainComplex (ModuleCat 𝕜) ℕ) (i j k : ℕ)
    (x : C.X i) : (ModuleCat.Hom.hom (C.d j k)) ((ModuleCat.Hom.hom (C.d i j)) x) = 0 := by
  have h := congrArg (fun (g : C.X i ⟶ C.X k) => (ModuleCat.Hom.hom g) x)
    (HomologicalComplex.d_comp_d C i j k)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h

/-- The inverse of the identification `H_n ≅ Z_n ⧸ B_n` on the class of an explicit cycle. -/
private lemma d1elt_e2Hb_inv_mkQ {𝕜 : Type} [Field 𝕜] {K : ChainComplex (ModuleCat 𝕜) ℕ} (n : ℕ)
    (x : ↥(Work.StemsB.fdZ 𝕜 K n)) :
    (e2Hb 𝕜 K n).inv.hom ((Work.StemsB.fdH 𝕜 K n).mkQ x)
      = (K.homologyπ n).hom (K.cyclesMk (x : K.X n) ((ComplexShape.down ℕ).next n) rfl
          (by rw [Work.Cohomology.down_next]; exact x.2)) :=
  E1B.homIsoH_inv n (x : K.X n) x.2

/-- The identification `H_n ≅ Z_n ⧸ B_n` on the homology class of an explicit cycle. -/
private lemma d1elt_e2Hb_hom_cyclesMk {𝕜 : Type} [Field 𝕜] {K : ChainComplex (ModuleCat 𝕜) ℕ}
    (n : ℕ) (z : K.X n) (hz : (ModuleCat.Hom.hom (K.d n (n-1))) z = 0)
    (hz' : (ModuleCat.Hom.hom (K.d n ((ComplexShape.down ℕ).next n))) z = 0) :
    (e2Hb 𝕜 K n).hom.hom ((K.homologyπ n).hom
        (K.cyclesMk z ((ComplexShape.down ℕ).next n) rfl hz'))
      = (Work.StemsB.fdH 𝕜 K n).mkQ ⟨z, hz⟩ := by
  have hcan : (ModuleCat.Hom.hom (K.d n ((ComplexShape.down ℕ).next n))) z = 0 := by
    rw [Work.Cohomology.down_next]; exact hz
  rw [show K.cyclesMk z ((ComplexShape.down ℕ).next n) rfl hz'
      = K.cyclesMk z ((ComplexShape.down ℕ).next n) rfl hcan from by
        rw [Subsingleton.elim hz' hcan]]
  exact E1B.homIsoH_hom_cyclesMk n z hz

/-- The identification `H_n ≅ Z_n ⧸ B_n` on the image under `homologyMap` of the class of an
explicit cycle. -/
private lemma d1elt_e2Hb_hom_homologyMap_cyclesMk {𝕜 : Type} [Field 𝕜]
    {K L : ChainComplex (ModuleCat 𝕜) ℕ} (φ : K ⟶ L) (n : ℕ) (z : K.X n)
    (hz' : (ModuleCat.Hom.hom (K.d n ((ComplexShape.down ℕ).next n))) z = 0)
    (hz'' : (ModuleCat.Hom.hom (L.d n (n-1))) ((ModuleCat.Hom.hom (φ.f n)) z) = 0)
    (hz''' : (ModuleCat.Hom.hom (L.d n ((ComplexShape.down ℕ).next n)))
      ((ModuleCat.Hom.hom (φ.f n)) z) = 0) :
    (e2Hb 𝕜 L n).hom.hom
        ((HomologicalComplex.homologyMap φ n)
          ((K.homologyπ n).hom (K.cyclesMk z ((ComplexShape.down ℕ).next n) rfl hz')))
      = (Work.StemsB.fdH 𝕜 L n).mkQ ⟨(ModuleCat.Hom.hom (φ.f n)) z, hz''⟩ := by
  rw [← Work.SSSR.hmcm_homologyπ_map φ n (K.cyclesMk z ((ComplexShape.down ℕ).next n) rfl hz')]
  rw [Work.SSSR.hmcm_cyclesMap_cyclesMk φ rfl z hz' hz''']
  exact d1elt_e2Hb_hom_cyclesMk n ((ModuleCat.Hom.hom (φ.f n)) z) hz'' hz'''

/-- The `jF` of the exact couple of the Serre filtration `e1cFilt 𝕜 p`, in the vocabulary of the
graded pieces `Kg`. -/
private lemma d1elt_jF_e1cFilt (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s t : ℕ) :
    Work.SSSR.jF (e1cFilt 𝕜 p) s t
      = HomologicalComplex.homologyMap (Kgπ 𝕜 p s) (s + t) := by
  cases s with
  | zero =>
      rw [Work.SSSR.jF, Kgπ_zero]
      exact (HomologicalComplex.homologyMap_id ((Work.SSSR.serF 𝕜 (sF p)).obj 0) (0 + t)).symm
  | succ k => rfl

theorem d1elt_class (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (s q : ℕ)
    (w : ↥(Work.StemsB.fdZ 𝕜 (Work.Pi6.MSS.Kg 𝕜 p (s + 1)) ((s + 1) + q)))
    (v : ↥((Work.Pi6.MSS.Cc 𝕜 p (s + 1)).X (s + q)))
    (hv : (ModuleCat.Hom.hom ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (Work.Pi6.MSS.sF p)) s).f (s + q))) v
          = (ModuleCat.Hom.hom ((Work.Pi6.MSS.Cc 𝕜 p (s + 2)).d ((s + 1) + q) (s + q)))
              (Work.Pi6.MSS.grSecX 𝕜 p (s + 1) ((s + 1) + q)
                (w : (Work.Pi6.MSS.Kg 𝕜 p (s + 1)).X ((s + 1) + q))))
    (hb : (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kg 𝕜 p s).d (s + q) ((s + q) - 1)))
          ((ModuleCat.Hom.hom ((Work.Pi6.MSS.Kgπ 𝕜 p s).f (s + q))) v) = 0) :
    Work.Pi6.MSS.d1elt 𝕜 p s q w
      = (Work.StemsB.fdH 𝕜 (Work.Pi6.MSS.Kg 𝕜 p s) (s + q)).mkQ
          (⟨(ModuleCat.Hom.hom ((Work.Pi6.MSS.Kgπ 𝕜 p s).f (s + q))) v, hb⟩ :
            ↥(Work.StemsB.fdZ 𝕜 (Work.Pi6.MSS.Kg 𝕜 p s) (s + q))) := by
  rw [d1elt]
  -- the differential of the `E¹`-row complex is `d¹ = kF ≫ jF`
  have hEd : (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).d (s + 1) s
      = Work.SSSR.d1 (e1cFilt 𝕜 p) s q :=
    ChainComplex.of_d (fun s => Work.SSSR.E1 (e1cFilt 𝕜 p) s q)
      (fun s => Work.SSSR.d1 (e1cFilt 𝕜 p) s q) s
  have hstep : (ConcreteCategory.hom ((Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).d (s + 1) s))
        (e1elt 𝕜 p (s + 1) q w)
      = (ModuleCat.Hom.hom (Work.SSSR.jF (e1cFilt 𝕜 p) s q))
          ((ModuleCat.Hom.hom (Work.SSSR.kF (e1cFilt 𝕜 p) s q)) (e1elt 𝕜 p (s + 1) q w)) := by
    refine Eq.trans (congrArg (fun m => (ConcreteCategory.hom m) (e1elt 𝕜 p (s + 1) q w)) hEd) ?_
    refine Eq.trans (congrArg (fun m => (ConcreteCategory.hom m) (e1elt 𝕜 p (s + 1) q w))
      (show Work.SSSR.d1 (e1cFilt 𝕜 p) s q = Work.SSSR.kF (e1cFilt 𝕜 p) s q
          ≫ Work.SSSR.jF (e1cFilt 𝕜 p) s q from rfl)) ?_
    rfl
  rw [hstep]
  -- the `E¹`-class of `w` is the homology class of the cycle `w`
  have hzcan : (ModuleCat.Hom.hom ((Kg 𝕜 p (s+1)).d ((s+1)+q)
      ((ComplexShape.down ℕ).next ((s+1)+q)))) (w : (Kg 𝕜 p (s+1)).X ((s+1)+q)) = 0 := by
    rw [Work.Cohomology.down_next]; exact w.2
  have h1 : e1elt 𝕜 p (s + 1) q w
      = (Kg 𝕜 p (s + 1)).homologyπ ((s + 1) + q)
          ((Kg 𝕜 p (s + 1)).cyclesMk (w : (Kg 𝕜 p (s + 1)).X ((s + 1) + q))
            ((ComplexShape.down ℕ).next ((s + 1) + q)) rfl hzcan) :=
    d1elt_e2Hb_inv_mkQ ((s + 1) + q) w
  rw [h1]
  -- the two hypotheses, in the `serF`-vocabulary of `kF_eq_of_lift`
  have hv' : (ModuleCat.Hom.hom ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (sF p)) s).f (s + q))) v
      = (ModuleCat.Hom.hom (((Work.SSSR.serF 𝕜 (sF p)).obj (s + 1)).d ((s + 1) + q) (s + q)))
          (grSecX 𝕜 p (s + 1) ((s + 1) + q) (w : (Kg 𝕜 p (s + 1)).X ((s + 1) + q))) := hv
  have hw' : (ModuleCat.Hom.hom ((cokernel.π (Work.SSSR.incF (Work.SSSR.serF 𝕜 (sF p)) s)).f
        ((s+1)+q)))
        (grSecX 𝕜 p (s+1) ((s+1)+q) (w : (Kg 𝕜 p (s+1)).X ((s+1)+q)))
      = (w : (Kg 𝕜 p (s+1)).X ((s+1)+q)) :=
    Kgπ_grSecX_apply 𝕜 p (s+1) ((s+1)+q) (w : (Kg 𝕜 p (s+1)).X ((s+1)+q))
  -- `v` is a cycle of `C_*(A_{s+1})`
  have hvcyc : (ModuleCat.Hom.hom (((Work.SSSR.serF 𝕜 (sF p)).obj s).d (s + q)
        ((ComplexShape.down ℕ).next (s + q)))) v = 0 := by
    have hcomm := Work.SSSR.chainMap_comm_apply_elem
      (Work.SSSR.incF (Work.SSSR.serF 𝕜 (sF p)) s) (i := s+q)
      (j := (ComplexShape.down ℕ).next (s+q)) v
    rw [hv'] at hcomm
    have hdd := d1elt_dcd ((Work.SSSR.serF 𝕜 (sF p)).obj (s+1)) ((s+1)+q) (s+q)
      ((ComplexShape.down ℕ).next (s+q))
      (grSecX 𝕜 p (s+1) ((s+1)+q) (w : (Kg 𝕜 p (s+1)).X ((s+1)+q)))
    rw [hdd] at hcomm
    have hmonoF : Mono (Work.SSSR.incF (Work.SSSR.serF 𝕜 (sF p)) s) :=
      Work.SSSR.mono_serreChainFiltration_map 𝕜 (sF p)
        (Work.SSSR.natShift.map (homOfLE (Nat.le_succ s)))
    haveI := hmonoF
    have hinj : Function.Injective (ModuleCat.Hom.hom
        ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (sF p)) s).f ((ComplexShape.down ℕ).next (s+q)))) :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    exact hinj (by rw [hcomm.symm, map_zero])
  -- the connecting map `kF` on the class of `w`
  have hkF : (ModuleCat.Hom.hom (Work.SSSR.kF (e1cFilt 𝕜 p) s q))
        ((ModuleCat.Hom.hom ((Kg 𝕜 p (s+1)).homologyπ ((s+1)+q)))
          ((Kg 𝕜 p (s+1)).cyclesMk (w : (Kg 𝕜 p (s+1)).X ((s+1)+q))
            ((ComplexShape.down ℕ).next ((s+1)+q)) rfl hzcan))
      = (ModuleCat.Hom.hom ((Cc 𝕜 p (s+1)).homologyπ (s+q)))
          ((Cc 𝕜 p (s+1)).cyclesMk v ((ComplexShape.down ℕ).next (s+q)) rfl hvcyc) :=
    Work.SSSR.kF_eq_of_lift (ξ := e1cFilt 𝕜 p) s q
      (w : (Kg 𝕜 p (s+1)).X ((s+1)+q)) hzcan
      (grSecX 𝕜 p (s+1) ((s+1)+q) (w : (Kg 𝕜 p (s+1)).X ((s+1)+q)))
      hw' v hv' hvcyc
  rw [hkF]
  rw [d1elt_jF_e1cFilt 𝕜 p s q]
  have hx' : (ModuleCat.Hom.hom ((Kg 𝕜 p s).d (s+q) ((ComplexShape.down ℕ).next (s+q))))
      ((ModuleCat.Hom.hom ((Kgπ 𝕜 p s).f (s+q))) v) = 0 := by
    rw [Work.Cohomology.down_next]; exact hb
  show (ModuleCat.Hom.hom (e2Hb 𝕜 (Kg 𝕜 p s) (s+q)).hom)
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Kgπ 𝕜 p s) (s+q)))
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ ((Work.SSSR.serF 𝕜 (sF p)).obj s)
            (s+q)))
          (((Work.SSSR.serF 𝕜 (sF p)).obj s).cyclesMk v ((ComplexShape.down ℕ).next (s+q))
            rfl hvcyc)))
    = (Work.StemsB.fdH 𝕜 (Kg 𝕜 p s) (s+q)).mkQ
        ⟨(ModuleCat.Hom.hom ((Kgπ 𝕜 p s).f (s+q))) v, hb⟩
  rw [d1elt_e2Hb_hom_homologyMap_cyclesMk (K := (Work.SSSR.serF 𝕜 (sF p)).obj s)
    (Kgπ 𝕜 p s) (s+q) v hvcyc hb hx']

end

end Work.Pi6.MSS
