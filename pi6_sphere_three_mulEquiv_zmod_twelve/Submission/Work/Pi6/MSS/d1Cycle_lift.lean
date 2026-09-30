import Mathlib
import Submission.Work.Pi6.MSS.e2FinalDefs
import Submission.Work.Pi6.MSS.jF_ker_decomp
import Submission.Work.Pi6.MSS.E1B.homIsoH_inv
import Submission.Work.SSSR.homologyMap_cyclesMk
import Submission.Work.SSSR.kF_eq_of_lift
import Submission.Work.SSSR.jF_eq_grFi
import Submission.Work.SSSR.hornCok_d_faceLift
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The lifting step of `d¹ = 0` to the chain level

Given a cycle `w` of the graded piece `Kg 𝕜 p s = F_s/F_{s-1}` of the Serre filtration of a map
`p : E → B`, whose class in `E¹_{s,q}` is killed by `d¹`, we show that the boundary of the chosen
lift `grSecX 𝕜 p s (s+q) w` of `w` to `F_s = Cc 𝕜 p (s+1)` lies, inside the ambient chain complex,
in the image of `Cc 𝕜 p (s-1)` plus the boundary of `Cc 𝕜 p s`.

The proof transports the chain level cycle attached to `w` to the degree `s+q` used by the exact
couple of the filtration (`kF`, `jF`), where the elementwise description of `jF` on its kernel
(`jF_ker_decomp`) applies, and then transports the resulting decomposition back.

## Main ingredients

* `Work.SSSR.kF_eq_of_lift` — the connecting map `kF` on a cycle class;
* `Work.Pi6.MSS.jF_ker_decomp` — the elementwise decomposition of `ker jF`;
* `Work.Pi6.MSS.E1B.homIsoH_inv` — the class `Z_n ⧸ B_n` of a cycle is its homology class;
* the transport lemmas below, for moving chain level data along an equality of degrees.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Work.Pi6.MSS

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-! ## Transport of chain level data along an equality of degrees -/

/-- `homologyπ` commutes with the transport of cycles along an equality of degrees. -/
private lemma eqToHom_homologyπ {𝕜 : Type} [Field 𝕜] (K : ChainComplex (ModuleCat 𝕜) ℕ)
    {a b : ℕ} (h : a = b) (x : ↥(K.cycles a)) :
    (eqToHom (congrArg (fun n => K.homology n) h)).hom ((K.homologyπ a).hom x)
      = (K.homologyπ b).hom ((eqToHom (congrArg (fun n => K.cycles n) h)).hom x) := by
  cases h; simp

/-- The transport of a chain map along an equality of degrees. -/
private lemma eqToHom_comp_map {𝕜 : Type} [Field 𝕜] {K L : ChainComplex (ModuleCat 𝕜) ℕ}
    (φ : K ⟶ L) {a b : ℕ} (h : a = b) (x : ↥(K.X a)) :
    (eqToHom (congrArg (fun n => L.X n) h)).hom ((ModuleCat.Hom.hom (φ.f a)) x)
      = (ModuleCat.Hom.hom (φ.f b)) ((eqToHom (congrArg (fun n => K.X n) h)).hom x) := by
  cases h; simp

/-- The transport of the differential of a chain complex along an equality of degrees. -/
private lemma eqToHom_d_map {𝕜 : Type} [Field 𝕜] (K : ChainComplex (ModuleCat 𝕜) ℕ)
    {i j i' j' : ℕ} (hi : i = i') (hj : j = j') (x : ↥(K.X i)) :
    (eqToHom (congrArg (fun n => K.X n) hj)).hom ((ModuleCat.Hom.hom (K.d i j)) x)
      = (ModuleCat.Hom.hom (K.d i' j')) ((eqToHom (congrArg (fun n => K.X n) hi)).hom x) := by
  cases hi; cases hj; simp

/-- Transporting back and forth along an equality of degrees is the identity. -/
private lemma eqToHom_symm_apply {𝕜 : Type} [Field 𝕜] (K : ChainComplex (ModuleCat 𝕜) ℕ)
    {a b : ℕ} (h : a = b) (y : ↥(K.X b)) :
    (eqToHom (congrArg (fun n => K.X n) h)).hom
      ((eqToHom (congrArg (fun n => K.X n) h.symm)).hom y) = y := by
  cases h; simp

/-- Two consecutive differentials kill every element. -/
private lemma d_comp_d_apply {𝕜 : Type} [Field 𝕜] (K : ChainComplex (ModuleCat 𝕜) ℕ)
    (i j k : ℕ) (x : ↥(K.X i)) :
    (ModuleCat.Hom.hom (K.d j k)) ((ModuleCat.Hom.hom (K.d i j)) x) = 0 := by
  have hdd := congrArg (fun (g : K.X i ⟶ K.X k) => (ModuleCat.Hom.hom g) x)
    (HomologicalComplex.d_comp_d K i j k)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using hdd

/-- The structure maps of the Serre filtration are injective in every degree. -/
private lemma incF_mono_f (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (k n : ℕ) :
    Mono ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (sF p)) k).f n) := by
  have hmonoF : Mono (Work.SSSR.incF (Work.SSSR.serF 𝕜 (sF p)) k) :=
    Work.SSSR.mono_serreChainFiltration_map 𝕜 (sF p)
      (Work.SSSR.natShift.map (homOfLE (Nat.le_succ k)))
  haveI := hmonoF
  infer_instance

private theorem d1Cycle_lift_core (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (k q : ℕ)
    (v : ↥((Cc 𝕜 p (k+2)).X ((k+1)+q)))
    (w : ↥(Work.StemsB.fdZ 𝕜 (Kg 𝕜 p (k+1)) ((k+1)+q)))
    (hw : (ModuleCat.Hom.hom ((Kgπ 𝕜 p (k+1)).f ((k+1)+q))) v
      = (w : (Kg 𝕜 p (k+1)).X ((k+1)+q)))
    (h : (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).d (k+1) k (e1elt 𝕜 p (k+1) q w) = 0) :
    ∃ Y : ↥((Cc 𝕜 p k).X ((k+1)+q-1)), ∃ Z : ↥((Cc 𝕜 p (k+1)).X ((k+1)+q)),
      (inclL 𝕜 p (k+2)).f ((k+1)+q-1)
          (((Cc 𝕜 p (k+2)).d ((k+1)+q) ((k+1)+q-1)).hom v)
        = (inclL 𝕜 p k).f ((k+1)+q-1) Y
          + (inclL 𝕜 p (k+1)).f ((k+1)+q-1)
              (((Cc 𝕜 p (k+1)).d ((k+1)+q) ((k+1)+q-1)).hom Z) := by
  have e : (k+1)+q-1 = k+q := by omega
  have hKgx : (ModuleCat.Hom.hom ((Kgπ 𝕜 p (k+1)).f ((k+1)+q-1)))
      ((ModuleCat.Hom.hom ((Cc 𝕜 p (k+2)).d ((k+1)+q) ((k+1)+q-1))) v) = 0 := by
    have hcomm := Work.SSSR.chainMap_comm_apply_elem (Kgπ 𝕜 p (k+1))
      (i := (k+1)+q) (j := (k+1)+q-1) v
    rw [hw] at hcomm
    rw [w.property] at hcomm
    exact hcomm.symm
  have hKgx' : (ModuleCat.Hom.hom ((Kgπ 𝕜 p (k+1)).f (k+q)))
      ((eqToHom (congrArg (fun n => (Cc 𝕜 p (k+2)).X n) e)).hom
        ((ModuleCat.Hom.hom ((Cc 𝕜 p (k+2)).d ((k+1)+q) ((k+1)+q-1))) v)) = 0 := by
    erw [← eqToHom_comp_map (Kgπ 𝕜 p (k+1)) e
      ((ModuleCat.Hom.hom ((Cc 𝕜 p (k+2)).d ((k+1)+q) ((k+1)+q-1))) v)]
    rw [hKgx]
    exact map_zero _
  have hmem : (eqToHom (congrArg (fun n => (Cc 𝕜 p (k+2)).X n) e)).hom
        ((ModuleCat.Hom.hom ((Cc 𝕜 p (k+2)).d ((k+1)+q) ((k+1)+q-1))) v)
      ∈ LinearMap.range (grIncl 𝕜 p (k+1) (k+q)).hom :=
    (ker_Kgπ_le_grIncl 𝕜 p (k+1) (k+q)) (LinearMap.mem_ker.mpr hKgx')
  obtain ⟨v'', hv''⟩ := LinearMap.mem_range.mp hmem
  have hx'' : (eqToHom (congrArg (fun n => (Cc 𝕜 p (k+2)).X n) e)).hom
      ((ModuleCat.Hom.hom ((Cc 𝕜 p (k+2)).d ((k+1)+q) ((k+1)+q-1))) v)
      = (ModuleCat.Hom.hom ((Cc 𝕜 p (k+2)).d ((k+1)+q) (k+q))) v := by
    simpa using eqToHom_d_map (Cc 𝕜 p (k+2)) (i := (k+1)+q) (j := (k+1)+q-1)
      (i' := (k+1)+q) (j' := k+q) rfl e v
  have hv''c : (ModuleCat.Hom.hom ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (sF p)) k).f (k+q))) v''
      = (eqToHom (congrArg (fun n => (Cc 𝕜 p (k+2)).X n) e)).hom
          ((ModuleCat.Hom.hom ((Cc 𝕜 p (k+2)).d ((k+1)+q) ((k+1)+q-1))) v) := hv''
  have hvcyc : (ModuleCat.Hom.hom ((Cc 𝕜 p (k+1)).d (k+q)
      ((ComplexShape.down ℕ).next (k+q)))) v'' = 0 := by
    have hinj : Function.Injective (ModuleCat.Hom.hom
        ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (sF p)) k).f
          ((ComplexShape.down ℕ).next (k+q)))) :=
      (ModuleCat.mono_iff_injective _).mp (incF_mono_f 𝕜 p k ((ComplexShape.down ℕ).next (k+q)))
    have hcomm := Work.SSSR.chainMap_comm_apply_elem (Work.SSSR.incF (Work.SSSR.serF 𝕜 (sF p)) k)
      (i := k+q) (j := (ComplexShape.down ℕ).next (k+q)) v''
    have hzero : (ModuleCat.Hom.hom ((Cc 𝕜 p (k+2)).d (k+q)
        ((ComplexShape.down ℕ).next (k+q)))) ((ModuleCat.Hom.hom
          ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (sF p)) k).f (k+q))) v'') = 0 := by
      rw [hv''c, hx'']
      exact d_comp_d_apply (Cc 𝕜 p (k+2)) ((k+1)+q) (k+q)
        ((ComplexShape.down ℕ).next (k+q)) v
    exact hinj (by erw [← hcomm]; exact hzero.trans (map_zero _).symm)
  have hz : (ModuleCat.Hom.hom ((Kg 𝕜 p (k+1)).d ((k+1)+q)
      ((ComplexShape.down ℕ).next ((k+1)+q)))) (w : (Kg 𝕜 p (k+1)).X ((k+1)+q)) = 0 := by
    rw [Work.Cohomology.down_next]
    exact w.property
  have hv : (ModuleCat.Hom.hom ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (e1cF p)) k).f (k+q))) v''
      = (ModuleCat.Hom.hom ((Cc 𝕜 p (k+2)).d ((k+1)+q) (k+q))) v := hv''c.trans hx''
  have hkf := Work.SSSR.kF_eq_of_lift (R := 𝕜) (e1cFilt 𝕜 p) k q
    (w : (Kg 𝕜 p (k+1)).X ((k+1)+q)) hz v hw v'' hv hvcyc
  have helt : e1elt 𝕜 p (k+1) q w
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyπ (Kg 𝕜 p (k+1)) ((k+1)+q)))
          (HomologicalComplex.cyclesMk (Kg 𝕜 p (k+1)) (w : (Kg 𝕜 p (k+1)).X ((k+1)+q))
            ((ComplexShape.down ℕ).next ((k+1)+q)) rfl hz) :=
    Work.Pi6.MSS.E1B.homIsoH_inv ((k+1)+q) (w : (Kg 𝕜 p (k+1)).X ((k+1)+q)) w.property
  have hkf2 : (ModuleCat.Hom.hom (Work.SSSR.kF (e1cFilt 𝕜 p) k q)) (e1elt 𝕜 p (k+1) q w)
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyπ (Cc 𝕜 p (k+1)) (k+q)))
          (HomologicalComplex.cyclesMk (Cc 𝕜 p (k+1)) v''
            ((ComplexShape.down ℕ).next (k+q)) rfl hvcyc) := by
    erw [helt, hkf]
    rfl
  have h2 : (ModuleCat.Hom.hom (Work.SSSR.jF (e1cFilt 𝕜 p) k q))
      ((ModuleCat.Hom.hom (Work.SSSR.kF (e1cFilt 𝕜 p) k q)) (e1elt 𝕜 p (k+1) q w)) = 0 := by
    have hd1 : (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).d (k+1) k
        = Work.SSSR.d1 (e1cFilt 𝕜 p) k q :=
      ChainComplex.of_d (fun s => Work.SSSR.E1 (e1cFilt 𝕜 p) s q)
        (fun s => Work.SSSR.d1 (e1cFilt 𝕜 p) s q) k
    have hh := h
    rw [hd1] at hh
    exact hh
  have hker : (ModuleCat.Hom.hom (Work.SSSR.jF (Work.SSSR.xiCan (R := 𝕜) p) k q))
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (Cc 𝕜 p (k+1)) (k+q)))
        (HomologicalComplex.cyclesMk (Cc 𝕜 p (k+1)) v''
          ((ComplexShape.down ℕ).next (k+q)) rfl hvcyc)) = 0 := by
    erw [← hkf2]
    exact h2
  obtain ⟨Y'', Z, hYZ⟩ := jF_ker_decomp 𝕜 E B p k q v'' hvcyc hker
  refine ⟨(eqToHom (congrArg (fun n => (Cc 𝕜 p k).X n) e.symm)).hom Y'', Z, ?_⟩
  have hLHS : (inclL 𝕜 p (k+2)).f ((k+1)+q-1)
        (((Cc 𝕜 p (k+2)).d ((k+1)+q) ((k+1)+q-1)).hom v)
      = (eqToHom (congrArg (fun n => (Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).X n) e.symm)).hom
          ((inclL 𝕜 p (k+1)).f (k+q) v'') := by
    have h1 := eqToHom_comp_map (inclL 𝕜 p (k+2)) e.symm
      ((eqToHom (congrArg (fun n => (Cc 𝕜 p (k+2)).X n) e)).hom
        ((ModuleCat.Hom.hom ((Cc 𝕜 p (k+2)).d ((k+1)+q) ((k+1)+q-1))) v))
    rw [eqToHom_symm_apply (Cc 𝕜 p (k+2)) e.symm] at h1
    erw [← h1]
    congr 1
    rw [← hv'']
    exact inclL_comp_apply 𝕜 p k (k+q) v''
  rw [hLHS, hYZ, map_add]
  congr 1
  · exact eqToHom_comp_map (inclL 𝕜 p k) e.symm Y''
  · have hZ := eqToHom_comp_map (inclL 𝕜 p (k+1)) e.symm
      ((ModuleCat.Hom.hom ((Cc 𝕜 p (k+1)).d ((k+1)+q) (k+q))) Z)
    rw [eqToHom_d_map (Cc 𝕜 p (k+1)) (i := (k+1)+q) (j := k+q)
      (i' := (k+1)+q) (j' := (k+1)+q-1) rfl e.symm Z] at hZ
    exact hZ

/-- **`Work.Pi6.MSS.d1Cycle_lift`**: the lifting of the vanishing of `d¹` on a class of the first
page to a chain level decomposition. -/
theorem d1Cycle_lift (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (s q : ℕ) (w : ↥(Work.StemsB.fdZ 𝕜 (Kg 𝕜 p s) (s + q)))
    (h : (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).d s (s - 1) (e1elt 𝕜 p s q w) = 0) :
    ∃ Y : ↥((Cc 𝕜 p (s - 1)).X (s + q - 1)), ∃ Z : ↥((Cc 𝕜 p s).X (s + q)),
      (inclL 𝕜 p (s + 1)).f (s + q - 1)
          (((Cc 𝕜 p (s + 1)).d (s + q) (s + q - 1)).hom
            (grSecX 𝕜 p s (s + q) (w : (Kg 𝕜 p s).X (s + q))))
        = (inclL 𝕜 p (s - 1)).f (s + q - 1) Y
          + (inclL 𝕜 p s).f (s + q - 1) (((Cc 𝕜 p s).d (s + q) (s + q - 1)).hom Z) := by
  rcases s with _ | k
  · refine ⟨0, 0, ?_⟩
    have h0 : (ModuleCat.Hom.hom ((Cc 𝕜 p 1).d (0+q) (0+q-1)))
        (grSecX 𝕜 p 0 (0+q) (w : (Kg 𝕜 p 0).X (0+q))) = 0 := by
      show (ModuleCat.Hom.hom ((Kg 𝕜 p 0).d (0+q) (0+q-1)))
        (w : (Kg 𝕜 p 0).X (0+q)) = 0
      exact w.property
    rw [h0]
    simp
  · refine d1Cycle_lift_core 𝕜 p k q
      (grSecX 𝕜 p (k+1) ((k+1)+q) (w : (Kg 𝕜 p (k+1)).X ((k+1)+q))) w ?_ ?_
    · exact Kgπ_grSecX_apply 𝕜 p (k+1) ((k+1)+q) (w : (Kg 𝕜 p (k+1)).X ((k+1)+q))
    · exact h

end

end Work.Pi6.MSS
