import Mathlib
import Submission.Work.SSGRoute.BaseChangeAggregator
import Submission.Work.SSGRoute.LPBCDefs
import Submission.Work.SSGRoute.Y3DevData
import Submission.Work.SSGRoute.E7bZ8Step2Aux2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory SSGRoute.PTExt

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

/-- **Y3 (change of base field `k ⊆ k' ⊆ K` for the local tower).**  Put
`S := image of D_w(K/k') in D_w(K/k)` (via `AlgEquiv.restrictScalars`).  Then `D_w(K/k') ≃* S`, and
there is ONE additive equivalence `eE : Ext¹_S(res M, res K_wˣ) ≃+ Ext¹_{D_w(K/k')}(res M, K_wˣ)`
such that at every level `L ⊇ K` Galois over `k` (hence over `k'`), with the canonical data
`(f, ι)` over `k` and `(f', ι')` over `k'`: `|D_{w'}(L/k')| = |S'|` for `S' = f⁻¹ S`, the
`p`-torsion of `H²(S', L_{w'}ˣ)` and of `H²(D_{w'}(L/k'), L_{w'}ˣ)` have the same size, and the
pairings correspond under `eE` and additive equivalences `eH`, `eB` on the `H¹` and `H²` sides.
Content: `D_w(K/k') → D_w(K/k)`, `σ ↦ σ.restrictScalars k`, is injective with image `S`; the
`localUnitsRep` actions agree along it (`NK.HassePrinciple.localUnitsEquiv` only sees the
underlying ring automorphism); transport of `Abelian.Ext` along an isomorphism of groups and of
representations (cf. `Work.SSGRoute.ext_res_mulEquiv`, `Work.SSGRoute.extH_congr` in the E7a lane,
and `Work.SSGRoute.SylowDesc.classesK_baseChangeIso` for the `C_K` analogue). -/

theorem levelPair_baseChange_in (p : ℕ) [Fact p.Prime] (k k' K : Type) [Field k] [NumberField k]
    [Field k'] [NumberField k'] [Field K] [NumberField K] [Algebra k K] [Algebra k' K]
    [Algebra k k'] [IsScalarTower k k' K] [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k' K] [IsGalois k' K]
    (w : NK.GlobalCFT.Place K) (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) :
    let S : Subgroup (SSGRoute.PTExt.decompK (k := k) w) :=
      ((SSGRoute.PTExt.decompK (k := k') w).map (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K))).comap
        (SSGRoute.PTExt.decompK (k := k) w).subtype
    Nonempty (SSGRoute.PTExt.decompK (k := k') w ≃* S) ∧
    ∃ eE : CategoryTheory.Abelian.Ext (Rep.res S.subtype (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype M))
        (Rep.res S.subtype (SSGRoute.PTExt.localUnitsK (k := k) w)) 1 ≃+
      CategoryTheory.Abelian.Ext (Rep.res (SSGRoute.PTExt.decompK (k := k') w).subtype
        (Rep.res (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K)) M))
        (SSGRoute.PTExt.localUnitsK (k := k') w) 1,
    ∀ (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L] [Algebra k' L] [IsScalarTower k' K L]
      [IsScalarTower k k' L] [FiniteDimensional k' L] [IsGalois k' L]
      (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
      (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* SSGRoute.PTExt.decompK (k := k) w)
      (hf : ∀ σ, ((f σ : SSGRoute.PTExt.decompK (k := k) w) : K ≃ₐ[k] K) = SSGRoute.PTExt.galRes k K L (σ : L ≃ₐ[k] L))
      (ι : Rep.res f (SSGRoute.PTExt.localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k L w')
      (hι : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
        ι.hom (Additive.ofMul u) =
          Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u))
      (f' : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* SSGRoute.PTExt.decompK (k := k') w)
      (hf' : ∀ σ, ((f' σ : SSGRoute.PTExt.decompK (k := k') w) : K ≃ₐ[k'] K) = SSGRoute.PTExt.galRes k' K L (σ : L ≃ₐ[k'] L))
      (ι' : Rep.res f' (SSGRoute.PTExt.localUnitsK (k := k') w) ⟶ NK.HassePrinciple.localUnitsRep k' L w')
      (hι' : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
        ι'.hom (Additive.ofMul u) =
          Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u)),
      Nat.card (MulAction.stabilizer (L ≃ₐ[k'] L) w') = Nat.card (S.comap f) ∧
      Nat.card {x : SSGRoute.PTExt.extH (Rep.res (S.comap f).subtype
          (NK.HassePrinciple.localUnitsRep k L w')) 2 // p • x = 0} =
        Nat.card {x : SSGRoute.PTExt.extH (NK.HassePrinciple.localUnitsRep k' L w') 2 // p • x = 0} ∧
      ∃ (eH : SSGRoute.PTExt.extH (Rep.res (f.subgroupComap S)
            (Rep.res S.subtype (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype M))) 1 ≃+
          SSGRoute.PTExt.extH (Rep.res f' (Rep.res (SSGRoute.PTExt.decompK (k := k') w).subtype
            (Rep.res (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K)) M))) 1)
        (eB : SSGRoute.PTExt.extH (Rep.res (S.comap f).subtype (NK.HassePrinciple.localUnitsRep k L w')) 2 ≃+
          SSGRoute.PTExt.extH (NK.HassePrinciple.localUnitsRep k' L w') 2),
        ∀ z h, SSGRoute.PTExt.levelPair f' ι' (eE z) (eH h) =
          eB (SSGRoute.PTExt.levelPair (A := Rep.res S.subtype (SSGRoute.PTExt.localUnitsK (k := k) w))
            (B := Rep.res (S.comap f).subtype (NK.HassePrinciple.localUnitsRep k L w'))
            (f.subgroupComap S) (Rep.resMap (S.comap f).subtype ι) z h) := by
  classical
  let S : Subgroup (SSGRoute.PTExt.decompK (k := k) w) :=
    ((SSGRoute.PTExt.decompK (k := k') w).map (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K))).comap
      (SSGRoute.PTExt.decompK (k := k) w).subtype
  refine ⟨⟨Work.SSGRoute.Y3Dev.baseChangeMulEquiv k k' K w⟩, ?_⟩
  let e : SSGRoute.PTExt.decompK (k := k') w ≃* S := Work.SSGRoute.Y3Dev.baseChangeMulEquiv k k' K w
  let M₂ : Rep SSGRoute.PTExt.Coeff S :=
    Rep.res S.subtype (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype M)
  let A₂ : Rep SSGRoute.PTExt.Coeff S :=
    Rep.res S.subtype (SSGRoute.PTExt.localUnitsK (k := k) w)
  let M₁ : Rep SSGRoute.PTExt.Coeff (SSGRoute.PTExt.decompK (k := k') w) :=
    Rep.res (SSGRoute.PTExt.decompK (k := k') w).subtype
      (Rep.res (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K)) M)
  let A₁ : Rep SSGRoute.PTExt.Coeff (SSGRoute.PTExt.decompK (k := k') w) :=
    SSGRoute.PTExt.localUnitsK (k := k') w
  refine ⟨Work.SSGRoute.LPBC.extResEquiv e M₂ A₂ 1, ?_⟩
  intro L _ _ _ _ _ _ _ _ _ _ _ _ w' hw' f hf ι hι f' hf' ι' hι'
  let j : MulAction.stabilizer (L ≃ₐ[k'] L) w' ≃* S.comap f :=
    Work.SSGRoute.Y3Dev.levelEquiv k k' K L w' w f hf f' hf'
  let B₂' : Rep SSGRoute.PTExt.Coeff (S.comap f) :=
    Rep.res (S.comap f).subtype (NK.HassePrinciple.localUnitsRep k L w')
  let A₂' : Rep SSGRoute.PTExt.Coeff (S.comap f) := Rep.res (f.subgroupComap S) M₂
  let ι₂' : Rep.res (f.subgroupComap S) A₂ ⟶ B₂' := Rep.resMap (S.comap f).subtype ι
  let eB0 : Rep.res j.toMonoidHom B₂' ≅ NK.HassePrinciple.localUnitsRep k' L w' :=
    Work.SSGRoute.Y3Dev.rep_res_levelEquiv_localUnits (k := k) (k' := k') (K := K) (L := L)
      (w' := w') (w := w) (f := f) (hf := hf) (f' := f') (hf' := hf')
  -- the level map compatibility
  have hsq : (f.subgroupComap S).comp j.toMonoidHom = e.toMonoidHom.comp f' := by
      refine MonoidHom.ext fun σ => Subtype.ext ?_
      refine Subtype.ext ?_
      show ((f (j σ) : SSGRoute.PTExt.decompK (k := k) w) : K ≃ₐ[k] K)
          = ((e (f' σ) : S) : K ≃ₐ[k] K)
      rw [hf (j σ)]
      rw [show (j σ : MulAction.stabilizer (L ≃ₐ[k] L) w')
          = Work.SSGRoute.Y3Dev.thetaLMap k k' L w' σ from
        Work.SSGRoute.Y3Dev.levelEquiv_apply k k' K L w' w f hf f' hf' σ]
      rw [Work.SSGRoute.Y3Dev.thetaLMap_apply]
      rw [show (((e (f' σ) : S) : SSGRoute.PTExt.decompK (k := k) w) : K ≃ₐ[k] K)
          = (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K))
              ((f' σ : SSGRoute.PTExt.decompK (k := k') w) : K ≃ₐ[k'] K) from rfl]
      rw [hf' σ]
      rw [show (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K))
            ((SSGRoute.PTExt.galRes k' K L) (σ : L ≃ₐ[k'] L))
          = (SSGRoute.PTExt.galRes k K L) (AlgEquiv.restrictScalars k (σ : L ≃ₐ[k'] L)) from
        congrArg (fun (g : (L ≃ₐ[k'] L) →* (K ≃ₐ[k] K)) => g (σ : L ≃ₐ[k'] L))
          (Work.SSGRoute.Y3Dev.galRes_restrictScalars k k' K L)]
  have hsq_pt : ∀ σ : MulAction.stabilizer (L ≃ₐ[k'] L) w',
      (f.subgroupComap S) (j σ) = e (f' σ) := fun σ => DFunLike.congr_fun hsq σ
  have hmem : ∀ σ : MulAction.stabilizer (L ≃ₐ[k'] L) w',
      (((f.subgroupComap S) (j σ) : S) : K ≃ₐ[k] K)
        = AlgEquiv.restrictScalars k (((f' σ) : SSGRoute.PTExt.decompK (k := k') w) : K ≃ₐ[k'] K) := by
    intro σ
    rw [hsq_pt σ]
    rfl
  have helem : ∀ σ : MulAction.stabilizer (L ≃ₐ[k'] L) w',
      (↑((f.subgroupComap S) (j σ)) : SSGRoute.PTExt.decompK (k := k) w)
        = (⟨AlgEquiv.restrictScalars k
              (((f' σ) : SSGRoute.PTExt.decompK (k := k') w) : K ≃ₐ[k'] K),
            (by
              rw [MulAction.mem_stabilizer_iff]
              rw [Work.SSGRoute.Y3Dev.restrictScalars_smul_place_K]
              exact (f' σ : SSGRoute.PTExt.decompK (k := k') w).2)⟩ :
            SSGRoute.PTExt.decompK (k := k) w) := by
    intro σ
    apply Subtype.ext
    exact hmem σ
  -- coefficient identification for the base-level local units
  let eAg : Rep.res ((f.subgroupComap S).comp j.toMonoidHom) A₂ ≅ Rep.res f' A₁ :=
    { hom := Rep.ofHom ⟨LinearMap.id, fun σ => by
        apply LinearMap.ext
        intro x
        show (SSGRoute.PTExt.localUnitsK (k := k) w).ρ
            (↑((f.subgroupComap S) (j σ)) : SSGRoute.PTExt.decompK (k := k) w) x
          = (SSGRoute.PTExt.localUnitsK (k := k') w).ρ (f' σ) x
        rw [helem σ]
        rfl⟩
      inv := Rep.ofHom ⟨LinearMap.id, fun σ => by
        apply LinearMap.ext
        intro x
        show (SSGRoute.PTExt.localUnitsK (k := k') w).ρ (f' σ) x
          = (SSGRoute.PTExt.localUnitsK (k := k) w).ρ
              (↑((f.subgroupComap S) (j σ)) : SSGRoute.PTExt.decompK (k := k) w) x
        rw [helem σ]
        rfl⟩
      hom_inv_id := by
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro x
        rfl
      inv_hom_id := by
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro x
        rfl }
  -- coefficient identification for `M`
  let eMg : Rep.res ((f.subgroupComap S).comp j.toMonoidHom) M₂ ≅ Rep.res f' M₁ :=
    Work.SSGRoute.Y3Dev.rep_res_levelEquiv_M (k := k) (k' := k') (K := K) (L := L)
      (w' := w') (w := w) (M := M) (f := f) (hf := hf) (f' := f') (hf' := hf')
  let TB : SSGRoute.PTExt.extH B₂' 2 ≃+ SSGRoute.PTExt.extH (NK.HassePrinciple.localUnitsRep k' L w') 2 :=
    (Work.SSGRoute.LPBC.extHMapEquiv j B₂' 2).trans
      (Work.SSGRoute.LPBC.extCongrIso (Iso.refl (SSGRoute.PTExt.unitRep
        (MulAction.stabilizer (L ≃ₐ[k'] L) w'))) eB0 2)
  let eH : SSGRoute.PTExt.extH A₂' 1 ≃+ SSGRoute.PTExt.extH (Rep.res f' M₁) 1 :=
    (Work.SSGRoute.LPBC.extHMapEquiv j A₂' 1).trans
      (Work.SSGRoute.LPBC.extCongrIso (Iso.refl (SSGRoute.PTExt.unitRep
        (MulAction.stabilizer (L ≃ₐ[k'] L) w'))) eMg 1)
  have hcompat : eAg.hom ≫ ι' = Rep.resMap j.toMonoidHom ι₂' ≫ eB0.hom := by
    letI := (Rep.res ((f.subgroupComap S).comp j.toMonoidHom) A₂).hV2
    letI := (NK.HassePrinciple.localUnitsRep k' L w').hV2
    refine Rep.hom_ext ?_
    refine Representation.IntertwiningMap.ext ?_
    ext x
    obtain ⟨u, rfl⟩ := Additive.ofMul.surjective x
    show ι'.hom (eAg.hom (Additive.ofMul u))
      = eB0.hom ((Rep.resMap j.toMonoidHom ι₂').hom (Additive.ofMul u))
    rw [show eAg.hom (Additive.ofMul u) = Additive.ofMul u from rfl]
    rw [show (Rep.resMap j.toMonoidHom ι₂').hom (Additive.ofMul u) = ι.hom (Additive.ofMul u) from by
      show (Rep.resMap j.toMonoidHom (Rep.resMap (S.comap f).subtype ι)).hom (Additive.ofMul u)
        = ι.hom (Additive.ofMul u)
      rw [Rep.resMap_hom_apply, Rep.resMap_hom_apply]]
    rw [show eB0.hom (ι.hom (Additive.ofMul u)) = ι.hom (Additive.ofMul u) from rfl]
    exact (hι' u).trans (hι u).symm
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.card_congr j.toEquiv
  · exact Work.SSGRoute.LPBC.card_pTorsion_addEquiv p TB
  · refine ⟨eH, TB, ?_⟩
    intro z h
    have hB := Work.SSGRoute.LPBC.levelPair_iso e f'
      ((f.subgroupComap S).comp j.toMonoidHom) hsq
      (Iso.refl (Rep.res e.toMonoidHom M₂)) (Iso.refl (Rep.res e.toMonoidHom A₂))
      eB0 eMg eAg
      (fun x => by rw [CategoryTheory.Functor.mapIso_refl]; rfl)
      (fun x => by rw [CategoryTheory.Functor.mapIso_refl]; rfl)
      (Rep.resMap j.toMonoidHom ι₂') ι' hcompat z
      (Work.SSGRoute.LPBC.extHMapEquiv j A₂' 1 h)
    have hA' := Work.SSGRoute.LPBC.levelPair_Hstep j (f.subgroupComap S) ι₂' eB0 z h
    rw [show TB (SSGRoute.PTExt.levelPair (A := A₂) (B := B₂') (f.subgroupComap S) ι₂' z h)
        = Work.SSGRoute.LPBC.extCongrIso (Iso.refl (SSGRoute.PTExt.unitRep
            (MulAction.stabilizer (L ≃ₐ[k'] L) w'))) eB0 2
            (Work.SSGRoute.LPBC.extHMapEquiv j B₂' 2
              (SSGRoute.PTExt.levelPair (A := A₂) (B := B₂') (f.subgroupComap S) ι₂' z h)) from rfl]
    rw [hA']
    rw [← hB]
    rw [Work.SSGRoute.LPBC.extCongrIso_refl_apply]
    rw [show eH h = Work.SSGRoute.LPBC.extCongrIso (Iso.refl (SSGRoute.PTExt.unitRep
        (MulAction.stabilizer (L ≃ₐ[k'] L) w'))) eMg 1
        (Work.SSGRoute.LPBC.extHMapEquiv j A₂' 1 h) from rfl]
    congr 1

end Work.SSGRoute
