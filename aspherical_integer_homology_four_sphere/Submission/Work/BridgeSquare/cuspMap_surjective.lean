
/-
# `BridgeSquare/cuspMap_surjective.lean` — `H_k(cuspMap)` is surjective for `k = 1, 2, 3`

The map `H_k(τ) : H_k(⊔_v (∂[-1,1]² × T²_v)) → H_k(M̄)` induced by the cusp parametrisation
`Work.BridgeSquare.cuspMap` is surjective in degrees `1, 2, 3` — the geometric input **(c)** of
the Mayer–Vietoris bridge (`Submission/Work/NOTES_LEAD_aspherical_bridge.md` §2.3–2.6, WP-F).
-/
import Mathlib
import Submission.Work.BridgeSquare.Data
import Submission.Work.BridgeSquare.CuspLift
import Submission.Work.BridgeSquare.mbarCx_cycles_gen
import Submission.Work.BridgeSquare.singChain_map_injective
import Submission.Work.BridgeSquare.PsiM_truncCell_mem_range

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Work.Certificates
open Work.HomologyIso.Gen (mbarDim mbarB mbarBd mbarCx)
open scoped BigOperators

namespace Work.BridgeSquare

noncomputable section

attribute [local instance 100] ZSMul.toSMul
attribute [local instance 100] instMulActionIntOfSubtractionMonoid

/-! ## §1  The abstract criterion -/

/-- **A cycle-lifting criterion for surjectivity on homology.** -/
private theorem homologyMap_surjective_of_cycle_lift
    {C T S : ChainComplex (ModuleCat.{0, 0} ℤ) ℕ} (f : T ⟶ S) (ψ : C ⟶ S) (k : ℕ)
    (hψ : IsIso (HomologicalComplex.homologyMap ψ k))
    (hinj : Function.Injective (f.f ((ComplexShape.down ℕ).next k)).hom)
    (hlift : ∀ z : ↑(C.X k), (C.d k ((ComplexShape.down ℕ).next k)).hom z = 0 →
        ∃ (γ : ↑(T.X k)) (δ : ↑(S.X (k + 1))),
          (ψ.f k).hom z = (f.f k).hom γ + (S.d (k + 1) k).hom δ) :
    Function.Surjective (HomologicalComplex.homologyMap f k).hom := by
  intro y
  let y' : ↑(C.homology k) := (asIso (HomologicalComplex.homologyMap ψ k)).inv.hom y
  have hy' : (HomologicalComplex.homologyMap ψ k).hom y' = y := by
    have h := congrArg (fun φ => φ.hom y) (IsIso.inv_hom_id (HomologicalComplex.homologyMap ψ k))
    simpa [y'] using h
  obtain ⟨zc, hzc⟩ := (ModuleCat.epi_iff_surjective (C.homologyπ k)).mp inferInstance y'
  set z : ↑(C.X k) := (C.iCycles k).hom zc with hzdef
  have hzcyc : (C.d k ((ComplexShape.down ℕ).next k)).hom z = 0 := by
    have h : ((C.iCycles k ≫ C.d k ((ComplexShape.down ℕ).next k)).hom) zc = 0 := by
      rw [HomologicalComplex.iCycles_d, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    simpa only [hzdef] using h
  obtain ⟨g, d, hgd⟩ := hlift z hzcyc
  have hgcyc : (T.d k ((ComplexShape.down ℕ).next k)).hom g = 0 := by
    apply hinj
    rw [map_zero]
    have hcomm : (S.d k ((ComplexShape.down ℕ).next k)).hom ((f.f k).hom g)
        = (f.f ((ComplexShape.down ℕ).next k)).hom
            ((T.d k ((ComplexShape.down ℕ).next k)).hom g) := by
      have h : ((f.f k ≫ S.d k ((ComplexShape.down ℕ).next k)).hom) g
          = (f.f ((ComplexShape.down ℕ).next k)).hom
              ((T.d k ((ComplexShape.down ℕ).next k)).hom g) := by
        rw [HomologicalComplex.Hom.comm f k ((ComplexShape.down ℕ).next k),
          ModuleCat.hom_comp, LinearMap.comp_apply]
      rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      exact h
    rw [← hcomm]
    have h1 : (S.d k ((ComplexShape.down ℕ).next k)).hom ((ψ.f k).hom z) = 0 := by
      have h : ((ψ.f k ≫ S.d k ((ComplexShape.down ℕ).next k)).hom) z
          = (ψ.f ((ComplexShape.down ℕ).next k)).hom
              ((C.d k ((ComplexShape.down ℕ).next k)).hom z) := by
        rw [HomologicalComplex.Hom.comm ψ k ((ComplexShape.down ℕ).next k),
          ModuleCat.hom_comp, LinearMap.comp_apply]
      rw [ModuleCat.hom_comp, LinearMap.comp_apply, hzcyc, map_zero] at h
      exact h
    have h2 : (S.d k ((ComplexShape.down ℕ).next k)).hom ((S.d (k + 1) k).hom d) = 0 := by
      have h : ((S.d (k + 1) k ≫ S.d k ((ComplexShape.down ℕ).next k)).hom) d = 0 := by
        rw [HomologicalComplex.d_comp_d S (k + 1) k ((ComplexShape.down ℕ).next k),
          ModuleCat.hom_zero, LinearMap.zero_apply]
      rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      exact h
    have hsplit : (f.f k).hom g = (ψ.f k).hom z - (S.d (k + 1) k).hom d := by
      rw [hgd]; abel
    rw [hsplit, map_sub, h1, h2, sub_zero]
  let A : ModuleCat.{0, 0} ℤ := ModuleCat.of ℤ ℤ
  let mkT : ↑(T.X k) → (A ⟶ T.X k) :=
    fun m => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ↑(T.X k) m)
  have hmkT : ∀ m, (mkT m).hom (1 : ℤ) = m := by
    intro m
    simp only [mkT, ModuleCat.hom_ofHom]
    exact one_smul ℤ m
  have hcycT : mkT g ≫ T.d k ((ComplexShape.down ℕ).next k) = 0 := by
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, ModuleCat.hom_zero]
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    rw [hmkT g, hgcyc]
  let zT : A ⟶ T.cycles k := T.liftCycles (mkT g) ((ComplexShape.down ℕ).next k) rfl hcycT
  have hzTi : (T.iCycles k).hom (zT.hom (1 : ℤ)) = g := by
    have h : ((zT ≫ T.iCycles k).hom) (1 : ℤ) = ((mkT g).hom) (1 : ℤ) := by
      rw [HomologicalComplex.liftCycles_i]
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, hmkT g] at h
    exact h
  refine ⟨(T.homologyπ k).hom (zT.hom (1 : ℤ)), ?_⟩
  rw [← hy', ← hzc]
  have hnatF : (homologyMap f k).hom ((T.homologyπ k).hom (zT.hom (1 : ℤ)))
      = (S.homologyπ k).hom ((cyclesMap f k).hom (zT.hom (1 : ℤ))) := by
    have h : ((T.homologyπ k ≫ homologyMap f k).hom) (zT.hom (1 : ℤ))
        = ((cyclesMap f k ≫ S.homologyπ k).hom) (zT.hom (1 : ℤ)) := by
      rw [HomologicalComplex.homologyπ_naturality]
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply] at h
    exact h
  rw [hnatF]
  have hnatΨ : (homologyMap ψ k).hom ((C.homologyπ k).hom zc)
      = (S.homologyπ k).hom ((cyclesMap ψ k).hom zc) := by
    have h : ((C.homologyπ k ≫ homologyMap ψ k).hom) zc
        = ((cyclesMap ψ k ≫ S.homologyπ k).hom) zc := by
      rw [HomologicalComplex.homologyπ_naturality]
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply] at h
    exact h
  rw [hnatΨ]
  have hcycEq : (cyclesMap ψ k).hom zc
      = (cyclesMap f k).hom (zT.hom (1 : ℤ)) + (S.toCycles (k + 1) k).hom d := by
    apply (ModuleCat.mono_iff_injective (S.iCycles k)).mp inferInstance
    rw [map_add]
    have hL : (S.iCycles k).hom ((cyclesMap ψ k).hom zc) = (ψ.f k).hom z := by
      have h : ((cyclesMap ψ k ≫ S.iCycles k).hom) zc = ((C.iCycles k ≫ ψ.f k).hom) zc := by
        rw [HomologicalComplex.cyclesMap_i]
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply] at h
      rw [h, hzdef]
    have hF : (S.iCycles k).hom ((cyclesMap f k).hom (zT.hom (1 : ℤ))) = (f.f k).hom g := by
      have h : ((cyclesMap f k ≫ S.iCycles k).hom) (zT.hom (1 : ℤ))
          = ((T.iCycles k ≫ f.f k).hom) (zT.hom (1 : ℤ)) := by
        rw [HomologicalComplex.cyclesMap_i]
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply] at h
      rw [h, hzTi]
    have hD : (S.iCycles k).hom ((S.toCycles (k + 1) k).hom d) = (S.d (k + 1) k).hom d := by
      have h : ((S.toCycles (k + 1) k ≫ S.iCycles k).hom) d = ((S.d (k + 1) k).hom) d := by
        rw [HomologicalComplex.toCycles_i]
      rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      exact h
    rw [hL, hF, hD, hgd]
  rw [hcycEq, map_add]
  have hkill : (S.homologyπ k).hom ((S.toCycles (k + 1) k).hom d) = 0 := by
    have h : ((S.toCycles (k + 1) k ≫ S.homologyπ k).hom) d = 0 := by
      rw [HomologicalComplex.toCycles_comp_homologyπ, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h
  rw [hkill, add_zero]

/-! ## §2  Auxiliary facts about the cell complex `mbarCx` -/

/-- The differential of `mbarCx.toChainComplex`, evaluated. -/
private theorem mbarCx_d_apply (n : ℕ) (z : Fin (mbarDim (n + 1)) → ℤ) :
    ((mbarCx.toChainComplex).d (n + 1) n).hom z = (mbarBd n).toLin z := by
  rw [show ((mbarCx.toChainComplex).d (n + 1) n)
      = ModuleCat.ofHom (Matrix.toLin' ((mbarBd n).toMatrix)) from ?_]
  · rfl
  · simp only [Work.Certificates.FinChainCx.toChainComplex]
    rw [ChainComplex.of_d]
    rfl

/-- If the `e`-th component of a sparse vector is nonzero, then the index `e` occurs in it. -/
private theorem svec_exists_of_toFun_ne_zero {n : ℕ} (v : SVec n) (e : Fin n)
    (h : v.toFun e ≠ 0) : ∃ p ∈ v, p.1 = e := by
  induction v with
  | nil => simp [SVec.toFun] at h
  | cons p ps ih =>
      rw [SVec.toFun_cons_apply] at h
      by_cases hp : p.1 = e
      · exact ⟨p, by simp, hp⟩
      · have h' : SVec.toFun ps e ≠ 0 := by
          intro h0
          apply h
          rw [h0, if_neg hp, add_zero]
        obtain ⟨q, hq, hqe⟩ := ih h'
        exact ⟨q, by simp [hq], hqe⟩

/-- Any `ℤ`-linear combination of the columns of `bdryGen` is supported on truncation cells. -/
private theorem bdryGen_toLin_truncSupported (k : ℕ) (hk : 1 ≤ k ∧ k ≤ 3)
    (a : Fin (mbarB k) → ℤ) :
    ∀ e : Fin (mbarDim k), ((bdryGen k).toLin a) e ≠ 0 → isTruncCell k e = true := by
  intro e he
  rw [Work.BridgeSquare.toLin_eq_mulVec, Matrix.mulVec_apply] at he
  obtain ⟨j, hj⟩ : ∃ j, (bdryGen k).toMatrix e j * a j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact he (Finset.sum_eq_zero fun j _ => hcon j)
  have h1 : ((bdryGen k).img j).toFun e ≠ 0 := by
    intro h0
    exact hj (by rw [SOp.toMatrix, h0, zero_mul])
  obtain ⟨p, hp, hpe⟩ := svec_exists_of_toFun_ne_zero ((bdryGen k).img j) e h1
  have h2 := Work.BridgeSquare.bdryGen_supp k hk j
  rw [List.all_eq_true] at h2
  rw [← hpe]
  exact h2 p hp

/-- The cycle condition of `mbarCx.toChainComplex` in degree `k ∈ {1,2,3}` is the sparse cycle
condition `bdryGenBd k` of `Data.lean`. -/
private theorem bdryGenBd_toLin_of_cycle (k : ℕ) (hk : 1 ≤ k ∧ k ≤ 3)
    (z : Fin (mbarDim k) → ℤ)
    (hz : ((mbarCx.toChainComplex).d k ((ComplexShape.down ℕ).next k)).hom z = 0) :
    (bdryGenBd k).toLin z = 0 := by
  obtain ⟨h1, h3⟩ := hk
  interval_cases k
  · rw [show (ComplexShape.down ℕ).next 1 = 0 from ComplexShape.next_eq' _ (by rfl)] at hz
    rw [mbarCx_d_apply 0 z] at hz
    exact hz
  · rw [show (ComplexShape.down ℕ).next 2 = 1 from ComplexShape.next_eq' _ (by rfl)] at hz
    rw [mbarCx_d_apply 1 z] at hz
    exact hz
  · rw [show (ComplexShape.down ℕ).next 3 = 2 from ComplexShape.next_eq' _ (by rfl)] at hz
    rw [mbarCx_d_apply 2 z] at hz
    exact hz

/-! ## §3  Truncation-supported chains -/

/-- **A truncation-supported chain lifts to `Cop`.** -/
private theorem PsiM_truncSupported_mem_range (n : ℕ) (c : Fin (mbarDim n) → ℤ)
    (hc : ∀ e : Fin (mbarDim n), c e ≠ 0 → isTruncCell n e = true) :
    ∃ γ : (singCxFun.obj (Cop (rt := Work.RTOwed.rtData))).X n,
      ((singCxFun.map (cuspMap (rt := Work.RTOwed.rtData))).f n) γ
        = (Work.BridgeSquare.PsiM.f n) c := by
  have hdecomp : c = ∑ e : Fin (mbarDim n),
      c e • (Pi.single e (1 : ℤ) : Fin (mbarDim n) → ℤ) := by
    funext i
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hsum : (Work.BridgeSquare.PsiM.f n) c
      = ∑ e : Fin (mbarDim n), (Work.BridgeSquare.PsiM.f n)
          (c e • (Pi.single e (1 : ℤ) : Fin (mbarDim n) → ℤ)) := by
    conv_lhs => rw [hdecomp]
    rw [map_sum]
  have hmem : (Work.BridgeSquare.PsiM.f n) c ∈
      LinearMap.range ((singCxFun.map (cuspMap (rt := Work.RTOwed.rtData))).f n).hom := by
    rw [hsum]
    refine Submodule.sum_mem _ fun e _ => ?_
    by_cases h : c e = 0
    · rw [h, zero_smul, map_zero]
      exact Submodule.zero_mem _
    · obtain ⟨γ, hγ⟩ := PsiM_truncCell_mem_range n e (hc e h)
      refine ⟨c e • γ, ?_⟩
      have hsm1 : (ConcreteCategory.hom
            ((singCxFun.map (cuspMap (rt := Work.RTOwed.rtData))).f n)) (c e • γ)
          = c e • (ConcreteCategory.hom
              ((singCxFun.map (cuspMap (rt := Work.RTOwed.rtData))).f n)) γ :=
        LinearMap.map_smul _ _ _
      have hsm2 : (ConcreteCategory.hom (Work.BridgeSquare.PsiM.f n))
            (c e • (Pi.single e (1 : ℤ) : Fin (mbarDim n) → ℤ))
          = c e • (ConcreteCategory.hom (Work.BridgeSquare.PsiM.f n))
              (Pi.single e (1 : ℤ) : Fin (mbarDim n) → ℤ) :=
        LinearMap.map_smul _ _ _
      rw [hsm1, hγ, ← hsm2]
  obtain ⟨γ, hγ⟩ := hmem
  exact ⟨γ, hγ⟩

/-! ## §4  The cycle-lifting hypothesis and the main theorem -/

/-- **The cycle-lifting hypothesis.** -/
private theorem cusp_cycle_lift (k : ℕ) (hk : 1 ≤ k ∧ k ≤ 3) (z : Fin (mbarDim k) → ℤ)
    (hz : (bdryGenBd k).toLin z = 0) :
    ∃ (γ : (singCxFun.obj (Cop (rt := Work.RTOwed.rtData))).X k)
      (δ : (singCxFun.obj (Mop (rt := Work.RTOwed.rtData))).X (k + 1)),
      (Work.BridgeSquare.PsiM.f k) z
        = (singCxFun.map (cuspMap (rt := Work.RTOwed.rtData))).f k γ
          + ((singCxFun.obj (Mop (rt := Work.RTOwed.rtData))).d (k + 1) k) δ := by
  obtain ⟨a, w, hzw⟩ := mbarCx_cycles_gen k (by omega) z hz
  obtain ⟨γ, hγ⟩ := PsiM_truncSupported_mem_range k ((bdryGen k).toLin a)
    (bdryGen_toLin_truncSupported k hk a)
  refine ⟨γ, (Work.BridgeSquare.PsiM.f (k + 1)) w, ?_⟩
  have hcomm := HomologicalComplex.Hom.comm (Work.BridgeSquare.PsiM) (k + 1) k
  have h2' : (ConcreteCategory.hom
        ((Work.HomologyMV.singCx (TopCat.of Work.FoldInst.Mbar)).d (k + 1) k))
        ((ConcreteCategory.hom (Work.BridgeSquare.PsiM.f (k + 1))) w)
      = (ConcreteCategory.hom (Work.BridgeSquare.PsiM.f k)) ((mbarBd k).toLin w) := by
    have hc := ConcreteCategory.congr_hom hcomm w
    simp only [ConcreteCategory.comp_apply] at hc
    rw [hc]
    congr 1
    exact mbarCx_d_apply k w
  have h2 : (((singCxFun.obj (Mop (rt := Work.RTOwed.rtData))).d (k + 1) k)
        ((Work.BridgeSquare.PsiM.f (k + 1)) w))
      = (Work.BridgeSquare.PsiM.f k) ((mbarBd k).toLin w) := h2'
  rw [hzw, map_add, ← hγ, ← h2]

theorem cuspMap_surjective (k : ℕ) (hk : 1 ≤ k ∧ k ≤ 3) :
    Function.Surjective (Work.BridgeSquare.homMap
      (Work.BridgeSquare.cuspMap (rt := Work.RTOwed.rtData)) k).hom := by
  haveI hq : QuasiIsoAt (Work.BridgeSquare.PsiM) k := PsiM_quasiIso.quasiIsoAt k
  haveI hI : IsIso (HomologicalComplex.homologyMap (Work.BridgeSquare.PsiM) k) := inferInstance
  show Function.Surjective (HomologicalComplex.homologyMap
    (singCxFun.map (cuspMap (rt := Work.RTOwed.rtData))) k).hom
  refine homologyMap_surjective_of_cycle_lift
    (C := Work.HomologyIso.Gen.mbarCx.toChainComplex)
    (T := singCxFun.obj (Cop (rt := Work.RTOwed.rtData)))
    (S := singCxFun.obj (Mop (rt := Work.RTOwed.rtData)))
    (f := singCxFun.map (cuspMap (rt := Work.RTOwed.rtData)))
    (ψ := Work.BridgeSquare.PsiM) k hI ?_ ?_
  · exact singChain_map_injective (cuspMap (rt := Work.RTOwed.rtData))
      (cuspLift_injective) ((ComplexShape.down ℕ).next k)
  · intro z hz
    exact cusp_cycle_lift k hk z (bdryGenBd_toLin_of_cycle k hk z hz)

end

end Work.BridgeSquare
