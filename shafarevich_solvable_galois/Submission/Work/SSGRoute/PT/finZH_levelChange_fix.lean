import Mathlib
import Submission.Work.SSGRoute.PT.finHalfData
import Submission.Work.SSGRoute.extHMap_gammaHom_eq
import Submission.Work.SSGRoute.PT.cocycle_levelChange_agree
import Submission.Work.SSGRoute.PT.gammaZ1_transport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option linter.style.haveILetI false

set_option backward.isDefEq.respectTransparency false in
lemma modRep_res_res_aux2 {H G G' : Type} [Group H] [Group G] [Group G'] (X : Type)
    [AddCommGroup X] [DistribMulAction G X] (A : DistribMulAction H X)
    (f : G' →* G) (g : H →* G') (hA : A = DistribMulAction.compHom X (f.comp g)) :
    @modRep H X _ _ A = Rep.res g (Rep.res f (modRep G X)) := by
  subst hA
  rfl

lemma smulCommClass_compHom_aux {H G X R : Type} [Monoid H] [Monoid G] [AddMonoid X]
    [DistribMulAction G X] [SMul R X] [SMulCommClass G R X] (f : H →* G) :
    @SMulCommClass H R X (DistribMulAction.compHom X f).toSMul _ := by
  letI : SMul H X := (DistribMulAction.compHom X f).toSMul
  exact ⟨fun h r x => smul_comm (f h) r x⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- **Level change of `gammaZ1` in the factorised `Rep.res` spelling.** -/
theorem gammaZ1_levelChange_aux {H G G' : Type} [Group H] [Group G] [Group G']
    (X : Type) [AddCommGroup X] [DistribMulAction G X] [SMulCommClass G Coeff X]
    (f : G' →* G) (g₁ g₂ : H →* G') (hg : g₁ = g₂)
    (hres : Rep.res g₂ (Rep.res f (modRep G X)) = Rep.res g₁ (Rep.res f (modRep G X)))
    (z₁ : @Work.GroupCohomology.Z1 H X _ _ (DistribMulAction.compHom X (f.comp g₁)))
    (z₂ : @Work.GroupCohomology.Z1 H X _ _ (DistribMulAction.compHom X (f.comp g₂)))
    (hψ : ∀ h, z₁.1 h = z₂.1 h)
    (C₁ : @SMulCommClass H Coeff X (DistribMulAction.compHom X (f.comp g₁)).toSMul _)
    (C₂ : @SMulCommClass H Coeff X (DistribMulAction.compHom X (f.comp g₂)).toSMul _) :
    @Work.SSGRoute.ExtH1.gammaZ1 H _ X _ (DistribMulAction.compHom X (f.comp g₁)) C₁
        (Work.SSGRoute.augSES_shortExact H) z₁
      = (@Work.SSGRoute.ExtH1.gammaZ1 H _ X _ (DistribMulAction.compHom X (f.comp g₂)) C₂
          (Work.SSGRoute.augSES_shortExact H) z₂).comp
        (Abelian.Ext.mk₀ (eqToHom hres)) (add_zero 1) := by
  subst hg
  have hz : z₁ = z₂ := Subtype.ext (funext hψ)
  subst hz
  rw [show hres = rfl from Subsingleton.elim _ _]
  simp only [eqToHom_refl]
  rw [Abelian.Ext.comp_mk₀_id]

/-- **Level change of the local class `finZH`.**  Same statement as
`Work.SSGRoute.PT.finZH_levelChange` (whose proof **still contains a `sorry`** in
`Submission/Work/SSGRoute/PT/finZH_levelChange.lean`; do NOT use that declaration).

RECIPE, with the pieces already proved on disk.
* `simp only [SSGRoute.PT.finZH, SSGRoute.PT.finLevelClass]` collapses both sides to
  `gammaHom (H1π ⟨fun σ => b₀ ↑σ, _⟩)` at the two levels (the `▸` transports of `finLevelClass`
  vanish); the goal becomes
  `extHMap ρ 𝟙 (gammaHom H_L X _) = (gammaHom H_L' X _).comp (mk₀ (eqToHom _)) (add_zero 1)`.
* First half: `Work.SSGRoute.extHMap_gammaHom_eq` computes the left side as
  `gammaHom H_L' X (H1π ⟨ψ_L ∘ ρ, _⟩)` with the `H_L'`-action pulled back along `ρ`.
  The instance arguments are *not* in the instance-search space (they are `letI`s of
  `finLevelClass`'s body), so introduce them with `letI`
  (`DistribMulAction.compHom X ((decompK (ofFinite (finQ K A hA))).subtype.comp (finZF hKL A hA))`
  for `H_L`, and the same with `finZF hKL' A hA` for `H_L'`, plus the two
  `SMulCommClass H Coeff X` instances, which can be built by `⟨fun g c m => smul_comm _ c m⟩`).
* Second half: the goal left over is exactly the shape of the PROVED
  `Work.SSGRoute.PT.gammaZ1_eqToHom_transport` (`SSGRoute/PT/gammaZ1_transport.lean`) — apply it
  with `φ₁ := (decompK (ofFinite (finQ K A hA))).subtype.comp ((finZF hKL A hA).comp ρ)`,
  `φ₂ := (decompK (ofFinite (finQ K A hA))).subtype.comp (finZF hKL' A hA)`,
  `hφ := by rw [MonoidHom.comp_assoc]; exact (congrArg (fun t => _subtype.comp t) hZF).symm`,
  `G := ↥K ≃ₐ[k] ↥K`, `X := DualMod p (M ⊗[ZMod p] T)`.
* The cocycle comparison `hψ` is the PROVED `Work.SSGRoute.PT.cocycle_levelChange_agree`
  (`b₀' ↑τ = b₀ ↑(ρ τ)`) and `hres` is the goal's own `eqToHom` argument (let unification fill it).
* Use `set_option backward.isDefEq.respectTransparency false` — without it the
  `modRep H X` / `Rep.res φ Y` spellings are not seen as definitionally equal. -/
theorem finZH_levelChange_fix {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    {K L L' : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    [NumberField L'] [FiniteDimensional k L'] [IsGalois k L']
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    [Algebra ↥K ↥L'] [IsScalarTower k ↥K ↥L'] [IsScalarTower ↥K ↥L' Ω]
    [Algebra ↥L ↥L'] [IsScalarTower k ↥L ↥L'] [IsScalarTower ↥L ↥L' Ω]
    [IsScalarTower ↥K ↥L ↥L']
    (p : ℕ) [Fact p.Prime]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (hKL : K ≤ L) (hKL' : K ≤ L') (hLL : L ≤ L')
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (b₀' : (↥L' ≃ₐ[k] ↥L') → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ))
    (hb₀' : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀' (AlgEquiv.restrictNormalHom L' σ))
    (hw' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite
      (SSGRoute.PT.finQW L' A hA))
      (NK.GlobalCFT.Place.ofFinite (SSGRoute.PT.finQW L A hA)))
    (hZF : SSGRoute.PT.finZF hKL' A hA = (SSGRoute.PT.finZF hKL A hA).comp
      (SSGRoute.decompKRestrict k (↥L) (↥L')
        (NK.GlobalCFT.Place.ofFinite (SSGRoute.PT.finQW L A hA))
        (NK.GlobalCFT.Place.ofFinite (SSGRoute.PT.finQW L' A hA)) hw')) :
    SSGRoute.PTExt.extHMap
        (SSGRoute.decompKRestrict k (↥L) (↥L')
          (NK.GlobalCFT.Place.ofFinite (SSGRoute.PT.finQW L A hA))
          (NK.GlobalCFT.Place.ofFinite (SSGRoute.PT.finQW L' A hA)) hw')
        (CategoryTheory.CategoryStruct.id _)
        (SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀ hb₀)
      = (SSGRoute.PT.finZH p K T M L' hKL' A hA b hb b₀' hb₀').comp
        (CategoryTheory.Abelian.Ext.mk₀ (CategoryTheory.eqToHom (congrArg (fun t =>
          Rep.res t
          (Rep.res (SSGRoute.PTExt.decompK (k := k)
            (NK.GlobalCFT.Place.ofFinite (SSGRoute.PT.finQ K A hA))).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))) hZF)))
        (add_zero 1) := by
  simp only [SSGRoute.PT.finZH, SSGRoute.PT.finLevelClass]
  let X := Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)
  let Gal := ↥K ≃ₐ[k] ↥K
  let DW := ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite (SSGRoute.PT.finQW L A hA)))
  let DW' := ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite (SSGRoute.PT.finQW L' A hA)))
  let Dq := ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite (SSGRoute.PT.finQ K A hA)))
  let ρ : DW' →* DW := SSGRoute.decompKRestrict k (↥L) (↥L')
      (NK.GlobalCFT.Place.ofFinite (SSGRoute.PT.finQW L A hA))
      (NK.GlobalCFT.Place.ofFinite (SSGRoute.PT.finQW L' A hA)) hw'
  let sub : Dq →* Gal := (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite (SSGRoute.PT.finQ K A hA))).subtype
  let φL : DW →* Gal := sub.comp (SSGRoute.PT.finZF hKL A hA)
  let φL' : DW' →* Gal := sub.comp (SSGRoute.PT.finZF hKL' A hA)
  haveI hCommZ : SMulCommClass Gal ℤ X :=
    ⟨fun g n m => map_zsmul (AddMonoidHom.mk' (fun m => g • m) (fun a b => smul_add g a b)) n m⟩
  haveI hCommC : SMulCommClass Gal Coeff X := ⟨fun g c m => smul_comm g c.down m⟩
  letI hL : DistribMulAction DW X := DistribMulAction.compHom X φL
  letI hL' : DistribMulAction DW' X := DistribMulAction.compHom X φL'
  -- FIRST HALF
  refine (Work.SSGRoute.extHMap_gammaHom_eq
    (r := SSGRoute.decompKRestrict k (↥L) (↥L')
        (NK.GlobalCFT.Place.ofFinite (SSGRoute.PT.finQW L A hA))
        (NK.GlobalCFT.Place.ofFinite (SSGRoute.PT.finQW L' A hA)) hw')
    (M := X) (ψ := ⟨fun σ => b₀ ((σ : ↥L ≃ₐ[k] ↥L)), ?_⟩)).trans ?_
  rw [Work.SSGRoute.ExtH1.gammaHom_H1π, Work.SSGRoute.ExtH1.gammaHom_H1π]
  -- SECOND HALF
  let φ₁ : DW' →* Gal := φL.comp ρ
  have hres := congrArg (fun t => Rep.res t
    (Rep.res (SSGRoute.PTExt.decompK (k := k)
      (NK.GlobalCFT.Place.ofFinite (SSGRoute.PT.finQ K A hA))).subtype
      (SSGRoute.PTExt.modRep Gal X))) hZF
  have hφ : φ₁ = φL' := by
    simp only [φ₁, φL, φL', sub, ρ]
    rw [MonoidHom.comp_assoc, hZF.symm]
  let g₁ : DW' →* Dq := (SSGRoute.PT.finZF hKL A hA).comp ρ
  let g₂ : DW' →* Dq := SSGRoute.PT.finZF hKL' A hA
  have hg : g₁ = g₂ := hZF.symm
  have hres := congrArg (fun t => Rep.res t (Rep.res sub (SSGRoute.PTExt.modRep Gal X))) hZF
  have hzL : (fun σ : DW => b₀ ((σ : ↥L ≃ₐ[k] ↥L))) ∈ Work.GroupCohomology.Z1 DW X := by
    rw [Work.GroupCohomology.mem_Z1_iff, Work.GroupCohomology.IsCrossedHom]
    intro g h
    rw [factorised_isCrossedHom p k Ω K L hKL A hA (SSGRoute.PT.finQ K A hA) (fun x => SSGRoute.PT.finQ_spec K A hA x)
      (SSGRoute.PT.finQW L A hA) (fun y => SSGRoute.PT.finQW_spec L A hA y) (SSGRoute.PT.finQW_glue L A hA)
      (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) b hb b₀ hb₀ g h]
    show b₀ ((g : ↥L ≃ₐ[k] ↥L)) + (SSGRoute.PTExt.galRes k (↥K) (↥L) (g : ↥L ≃ₐ[k] ↥L)) • b₀ ((h : ↥L ≃ₐ[k] ↥L))
      = (((SSGRoute.PT.finZF hKL A hA) g : ↥(SSGRoute.PTExt.decompK (k := k)
          (NK.GlobalCFT.Place.ofFinite (SSGRoute.PT.finQ K A hA)))) : ↥K ≃ₐ[k] ↥K) • b₀ ((h : ↥L ≃ₐ[k] ↥L))
        + b₀ ((g : ↥L ≃ₐ[k] ↥L))
    rw [SSGRoute.PT.finZF_spec hKL A hA g]
    abel
  have hz₁ : @Work.GroupCohomology.Z1 DW' X _ _ (DistribMulAction.compHom X (sub.comp g₁)) := by
    refine ⟨fun h => b₀ ((ρ h : DW) : ↥L ≃ₐ[k] ↥L), ?_⟩
    rw [Work.GroupCohomology.mem_Z1_iff, Work.GroupCohomology.IsCrossedHom]
    intro g h
    have h1 := (Work.GroupCohomology.mem_Z1_iff _ _ _).mp hzL (ρ g) (ρ h)
    show b₀ (((ρ (g * h) : DW) : ↥L ≃ₐ[k] ↥L))
      = (sub.comp g₁ g) • b₀ (((ρ h : DW) : ↥L ≃ₐ[k] ↥L)) + b₀ (((ρ g : DW) : ↥L ≃ₐ[k] ↥L))
    rw [map_mul]
    exact h1
  let hz₂ : @Work.GroupCohomology.Z1 DW' X _ _ (DistribMulAction.compHom X (sub.comp g₂)) :=
    ⟨fun σ => b₀' ((σ : ↥L' ≃ₐ[k] ↥L')), by
      rw [Work.GroupCohomology.mem_Z1_iff, Work.GroupCohomology.IsCrossedHom]
      intro g h
      rw [factorised_isCrossedHom p k Ω K L' hKL' A hA (SSGRoute.PT.finQ K A hA) (fun x => SSGRoute.PT.finQ_spec K A hA x)
        (SSGRoute.PT.finQW L' A hA) (fun y => SSGRoute.PT.finQW_spec L' A hA y) (SSGRoute.PT.finQW_glue L' A hA)
        (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) b hb b₀' hb₀' g h]
      show b₀' ((g : ↥L' ≃ₐ[k] ↥L')) + (SSGRoute.PTExt.galRes k (↥K) (↥L') (g : ↥L' ≃ₐ[k] ↥L')) • b₀' ((h : ↥L' ≃ₐ[k] ↥L'))
        = (((SSGRoute.PT.finZF hKL' A hA) g : ↥(SSGRoute.PTExt.decompK (k := k)
            (NK.GlobalCFT.Place.ofFinite (SSGRoute.PT.finQ K A hA)))) : ↥K ≃ₐ[k] ↥K) • b₀' ((h : ↥L' ≃ₐ[k] ↥L'))
          + b₀' ((g : ↥L' ≃ₐ[k] ↥L'))
      rw [SSGRoute.PT.finZF_spec hKL' A hA g]
      abel⟩
  refine (gammaZ1_levelChange_aux (H := DW') (G := Gal) (G' := Dq) X sub g₁ g₂ hg hres
      _ hz₂ ?_ ?_ ?_).trans ?_
  · intro h
    exact (Work.SSGRoute.PT.cocycle_levelChange_agree A hA b hb b₀ b₀' hb₀ hb₀' hw' h).symm
  · exact smulCommClass_compHom_aux (X := X) (R := Coeff) (sub.comp g₂)
  · rfl


end Work.SSGRoute.PT
