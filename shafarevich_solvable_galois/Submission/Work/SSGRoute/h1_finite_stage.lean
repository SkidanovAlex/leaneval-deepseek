import Mathlib.Tactic.Have
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.exists_finite_stable_submodule_family
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped TensorProduct
open CategoryTheory

namespace Work.SSGRoute

/-- `i ⊗ id` is equivariant for the diagonal `G`-action on tensor products whenever `i` is. -/
theorem rTensor_diag_smul (p : ℕ) {G E₂₀ E₂ T : Type}
    [Group G]
    [AddCommGroup E₂₀] [Module (ZMod p) E₂₀] [DistribMulAction G E₂₀]
      [SMulCommClass G (ZMod p) E₂₀]
    [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction G E₂]
      [SMulCommClass G (ZMod p) E₂]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
      [SMulCommClass G (ZMod p) T]
    (i : E₂₀ →ₗ[ZMod p] E₂) (hi : ∀ (g : G) (m : E₂₀), i (g • m) = g • i m)
    (g : G) (x : TensorProduct (ZMod p) E₂₀ T) :
    i.rTensor T
        ((Representation.ofDistribMulAction (ZMod p) G (TensorProduct (ZMod p) E₂₀ T)) g x)
      = (Representation.ofDistribMulAction (ZMod p) G (TensorProduct (ZMod p) E₂ T)) g
          (i.rTensor T x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m n =>
      simp only [Representation.ofDistribMulAction_apply_apply,
        Work.Shrinking.diagTensor_smul_tmul, LinearMap.rTensor_tmul, hi]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The underlying `1`-cycle of `mapCycles₁` is the coefficientwise image of the underlying
`1`-cycle, with the indices pushed forward along `φ`. -/
theorem mapCycles₁_coe_eq (p : ℕ) {G₁ G₂ : Type} [Group G₁] [Group G₂] (φ : G₁ →* G₂)
    {A : Rep (ZMod p) G₁} {B : Rep (ZMod p) G₂} (F : A ⟶ Rep.res φ B)
    (z : groupHomology.cycles₁ A) :
    ((groupHomology.mapCycles₁ φ F z).1 : G₂ →₀ B.V)
      = Finsupp.mapRange F.hom.toLinearMap (map_zero _) (Finsupp.mapDomain φ z.1) := by
  rw [groupHomology.coe_mapCycles₁]
  rw [show groupHomology.chainsMap₁ φ F
      = ModuleCat.ofHom (Finsupp.mapRange.linearMap F.hom.toLinearMap ∘ₗ
          Finsupp.lmapDomain A.V (ZMod p) φ) from rfl]
  rw [ModuleCat.ofHom_apply, LinearMap.comp_apply, Finsupp.lmapDomain_apply,
    Finsupp.mapRange.linearMap_apply]

/-- `d₂₁` is natural with respect to a morphism of coefficient representations. -/
theorem d₂₁_mapRange_natural (p : ℕ) {G : Type} [Group G] {A B : Rep (ZMod p) G} (Ψ : A ⟶ B)
    (x : G × G →₀ A.V) :
    groupHomology.d₂₁ B (Finsupp.mapRange Ψ.hom.toLinearMap (map_zero _) x)
      = Finsupp.mapRange Ψ.hom.toLinearMap (map_zero _) ((groupHomology.d₂₁ A) x) := by
  have hlin : (Finsupp.mapRange.linearMap Ψ.hom.toLinearMap) ∘ₗ (groupHomology.d₂₁ A).hom
      = (groupHomology.d₂₁ B).hom ∘ₗ (Finsupp.mapRange.linearMap Ψ.hom.toLinearMap) := by
    refine Finsupp.lhom_ext fun g a => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    show (Finsupp.mapRange.linearMap Ψ.hom.toLinearMap)
          ((groupHomology.d₂₁ A).hom (Finsupp.single g a))
        = (groupHomology.d₂₁ B).hom
          ((Finsupp.mapRange.linearMap Ψ.hom.toLinearMap) (Finsupp.single g a))
    rw [groupHomology.d₂₁_single]
    rw [map_add, map_sub]
    repeat rw [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single]
    repeat rw [groupHomology.d₂₁_single]
    rw [show (Rep.Hom.hom Ψ).toLinearMap ((A.ρ g.1⁻¹) a)
          = (B.ρ g.1⁻¹) ((Rep.Hom.hom Ψ).toLinearMap a)
        from Rep.hom_comm_apply Ψ (g.1⁻¹) a]
  exact (LinearMap.congr_fun hlin x).symm

/-- **The finite stage of a vanishing class.** -/
theorem exists_finite_stage_factor
    (p : ℕ) [Fact p.Prime]
    {G₁ G₂ : Type} [Group G₁] [Group G₂] [Fintype G₂] (φ : G₁ →* G₂)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G₂ T]
      [SMulCommClass G₂ (ZMod p) T]
    (M₁ : Rep (ZMod p) G₁) [Finite M₁.V]
    (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction G₂ E₂]
      [SMulCommClass G₂ (ZMod p) E₂]
    (E₂₀ : Type) [AddCommGroup E₂₀] [Module (ZMod p) E₂₀] [DistribMulAction G₂ E₂₀]
      [SMulCommClass G₂ (ZMod p) E₂₀] [Finite E₂₀]
    (i : E₂₀ →ₗ[ZMod p] E₂) (hi : Function.Injective i)
    (hiG : ∀ (g : G₂) (m : E₂₀), i (g • m) = g • i m)
    (F : M₁ ⟶ Rep.res φ
      (Rep.of (Representation.ofDistribMulAction (ZMod p) G₂ (TensorProduct (ZMod p) E₂ T))))
    (z : groupHomology.cycles₁ M₁)
    (B : G₂ × G₂ →₀ TensorProduct (ZMod p) E₂ T)
    (hB : (groupHomology.d₂₁ (Rep.of (Representation.ofDistribMulAction (ZMod p) G₂
        (TensorProduct (ZMod p) E₂ T)))).hom B = (groupHomology.mapCycles₁ φ F z).1)
    (hB0 : ∀ q : G₂ × G₂, B q ∈ LinearMap.range (i.rTensor T))
    (hF0 : ∀ v : M₁.V, F.hom v ∈ LinearMap.range (i.rTensor T)) :
    ∃ F₀ : M₁ ⟶ Rep.res φ
        (Rep.of (Representation.ofDistribMulAction (ZMod p) G₂ (TensorProduct (ZMod p) E₂₀ T))),
      (∀ v : M₁.V, F.hom v = i.rTensor T (F₀.hom v)) ∧
      (ModuleCat.Hom.hom (groupHomology.map φ F₀ 1)) (groupHomology.H1π M₁ z) = 0 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let ρE : Representation (ZMod p) G₂ (TensorProduct (ZMod p) E₂ T) :=
    Representation.ofDistribMulAction (ZMod p) G₂ (TensorProduct (ZMod p) E₂ T)
  let RT : Rep (ZMod p) G₂ := Rep.of ρE
  let ρW : Representation (ZMod p) G₂ (TensorProduct (ZMod p) E₂₀ T) :=
    Representation.ofDistribMulAction (ZMod p) G₂ (TensorProduct (ZMod p) E₂₀ T)
  let RW : Rep (ZMod p) G₂ := Rep.of ρW
  have hψsmul : ∀ (g : G₂) (y : TensorProduct (ZMod p) E₂₀ T),
      i.rTensor T (ρW g y) = ρE g (i.rTensor T y) :=
    fun g y => rTensor_diag_smul p i hiG g y
  have hinj : Function.Injective (i.rTensor T) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := T) i hi
  obtain ⟨B', hB'⟩ : ∃ B' : G₂ × G₂ →₀ TensorProduct (ZMod p) E₂₀ T,
      Finsupp.mapRange (i.rTensor T) (map_zero _) B' = B := by
    have hmem : B ∈ Set.range (Finsupp.mapRange (α := G₂ × G₂) (i.rTensor T) (map_zero _)) := by
      rw [Finsupp.range_mapRange]
      exact fun q => hB0 q
    exact hmem
  let e : TensorProduct (ZMod p) E₂₀ T ≃ₗ[ZMod p] LinearMap.range (i.rTensor T) :=
    LinearEquiv.ofInjective (i.rTensor T) hinj
  let F₀lin : M₁.V →ₗ[ZMod p] TensorProduct (ZMod p) E₂₀ T :=
    e.symm.toLinearMap ∘ₗ (F.hom.toLinearMap).codRestrict (LinearMap.range (i.rTensor T)) hF0
  have hkey : ∀ v : M₁.V, i.rTensor T (F₀lin v) = F.hom v := by
    intro v
    have h1 : (i.rTensor T) ((LinearEquiv.ofInjective (i.rTensor T) hinj).symm
          ((F.hom.toLinearMap).codRestrict (LinearMap.range (i.rTensor T)) hF0 v))
        = F.hom.toLinearMap v := by
      rw [LinearEquiv.ofInjective_symm_apply, LinearMap.codRestrict_apply]
    have h2 : F₀lin v = (LinearEquiv.ofInjective (i.rTensor T) hinj).symm
          ((F.hom.toLinearMap).codRestrict (LinearMap.range (i.rTensor T)) hF0 v) := rfl
    rw [h2]
    exact h1
  have hF₀eq : ∀ (g : G₁) (v : M₁.V), F₀lin (M₁.ρ g v) = ρW (φ g) (F₀lin v) := by
    intro g v
    apply hinj
    rw [hψsmul]
    repeat rw [hkey]
    exact Rep.hom_comm_apply F g v
  let Ψ : RW ⟶ RT :=
    Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap ρW ρE (i.rTensor T)
      (fun g y => hψsmul g y))
  let F₀ : M₁ ⟶ Rep.res φ RW :=
    Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap M₁.ρ (ρW.comp φ) F₀lin
      (fun g v => hF₀eq g v))
  have hFF : F = F₀ ≫ Rep.resMap φ Ψ := by
    have hfun : ∀ v : M₁.V, F.hom v = (F₀ ≫ Rep.resMap φ Ψ).hom v := by
      intro v
      rw [show ((F₀ ≫ Rep.resMap φ Ψ).hom) v = (Rep.resMap φ Ψ).hom (F₀.hom v) from rfl]
      rw [Rep.resMap_hom_apply]
      change F.hom v = i.rTensor T (F₀lin v)
      exact (hkey v).symm
    exact Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext hfun))
  have hF2 : Finsupp.mapRange (i.rTensor T) (map_zero _) ((groupHomology.mapCycles₁ φ F₀ z).1)
      = (groupHomology.mapCycles₁ φ F z).1 := by
    rw [mapCycles₁_coe_eq p φ F z, mapCycles₁_coe_eq p φ F₀ z]
    ext g
    simp only [Finsupp.mapRange_apply]
    show i.rTensor T (F₀lin (Finsupp.mapDomain φ z.1 g)) = F.hom (Finsupp.mapDomain φ z.1 g)
    exact hkey (Finsupp.mapDomain φ z.1 g)
  have hnat : (groupHomology.d₂₁ RT).hom (Finsupp.mapRange (i.rTensor T) (map_zero _) B')
      = Finsupp.mapRange (i.rTensor T) (map_zero _) ((groupHomology.d₂₁ RW).hom B') :=
    d₂₁_mapRange_natural p Ψ B'
  have hfin : (groupHomology.d₂₁ RW).hom B' = (groupHomology.mapCycles₁ φ F₀ z).1 := by
    apply Finsupp.mapRange_injective (i.rTensor T) (map_zero _) hinj
    rw [← hnat, hB', hF2]
    exact hB
  refine ⟨F₀, fun v => (hkey v).symm, ?_⟩
  rw [groupHomology.H1π_comp_map_apply φ F₀ z]
  rw [groupHomology.H1π_eq_zero_iff]
  exact LinearMap.mem_range.mpr ⟨B', hfin⟩

theorem h1_finite_stage (p : ℕ) [Fact p.Prime]
    {G₁ G₂ : Type} [Group G₁] [Group G₂] [Fintype G₂] (φ : G₁ →* G₂)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G₂ T]
      [SMulCommClass G₂ (ZMod p) T]
    (M₁ : Rep (ZMod p) G₁) [Finite M₁.V]
    (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction G₂ E₂]
      [SMulCommClass G₂ (ZMod p) E₂]
    (F : M₁ ⟶ Rep.res φ
      (Rep.of (Representation.ofDistribMulAction (ZMod p) G₂ (TensorProduct (ZMod p) E₂ T))))
    (x : groupHomology.H1 M₁)
    (hx : (ModuleCat.Hom.hom (groupHomology.map φ F 1)) x = 0) :
    ∃ (E₂₀ : Type) (_ : AddCommGroup E₂₀) (_ : Module (ZMod p) E₂₀) (_ : DistribMulAction G₂ E₂₀)
      (_ : SMulCommClass G₂ (ZMod p) E₂₀) (_ : Finite E₂₀)
      (i : E₂₀ →ₗ[ZMod p] E₂) (_ : Function.Injective i)
      (_ : ∀ (g : G₂) (m : E₂₀), i (g • m) = g • i m)
      (F₀ : M₁ ⟶ Rep.res φ
        (Rep.of (Representation.ofDistribMulAction (ZMod p) G₂ (TensorProduct (ZMod p) E₂₀ T)))),
      (∀ z : M₁.V, F.hom z = i.rTensor T (F₀.hom z)) ∧
      (ModuleCat.Hom.hom (groupHomology.map φ F₀ 1)) x = 0 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Fintype M₁.V := Fintype.ofFinite M₁.V
  revert hx
  refine groupHomology.H1_induction_on x ?_
  intro z hz
  let RT : Rep (ZMod p) G₂ :=
    Rep.of (Representation.ofDistribMulAction (ZMod p) G₂ (TensorProduct (ZMod p) E₂ T))
  have hY : ((groupHomology.mapCycles₁ φ F z).1 : G₂ →₀ TensorProduct (ZMod p) E₂ T)
      ∈ groupHomology.boundaries₁ RT := by
    rw [← groupHomology.H1π_eq_zero_iff]
    rw [← groupHomology.H1π_comp_map_apply φ F z]
    exact hz
  obtain ⟨B, hB⟩ := LinearMap.mem_range.mp hY
  let ι : Type := M₁.V ⊕ G₂ ⊕ (G₂ × G₂)
  haveI : Fintype ι := inferInstanceAs (Fintype (M₁.V ⊕ G₂ ⊕ (G₂ × G₂)))
  let mm : ι → TensorProduct (ZMod p) E₂ T := fun i => match i with
    | Sum.inl v => F.hom v
    | Sum.inr (Sum.inl g) =>
        ((groupHomology.mapCycles₁ φ F z).1 : G₂ →₀ TensorProduct (ZMod p) E₂ T) g
    | Sum.inr (Sum.inr q) => B q
  obtain ⟨W, -, hWstab, hWfin, m', hm'⟩ :=
    exists_finite_stable_submodule_family p G₂ E₂ T (∅ : Set E₂) Set.finite_empty mm
  -- The instances on `↥W` are installed with `letI` (not `haveI`): `letI` inlines the
  -- *value* of the instance, so that the SMul on `↥W` used inside the goal is literally
  -- the one written here.  They are also written in the exact "projection path" shape
  -- produced by typeclass synthesis in the *statement* of `h1_finite_stage` (where `E₂₀`
  -- is abstract), namely
  -- `SMulZeroClass.toSMul (DistribSMul.toSMulZeroClass (DistribMulAction.toDistribSMul _))`,
  -- so that the instances supplied here are definitionally the ones the existential
  -- statement expects (this reconciles the subtype-specific instances such as
  -- `AddSubgroupClass.instZModSMul` with the generic path chosen for an abstract `E₂₀`).
  letI hDM : DistribMulAction G₂ ↥W :=
    { smul := fun (g : G₂) (x : ↥W) => ⟨g • (x : E₂), hWstab g x x.2⟩
      one_smul := fun x => Subtype.ext (one_smul G₂ (x : E₂))
      mul_smul := fun g h x => Subtype.ext (mul_smul g h (x : E₂))
      smul_zero := fun g => Subtype.ext (smul_zero g)
      smul_add := fun g x y => Subtype.ext (smul_add g (x : E₂) (y : E₂)) }
  letI hsmG : SMul G₂ ↥W :=
    @SMulZeroClass.toSMul G₂ ↥W _
      (@DistribSMul.toSMulZeroClass G₂ ↥W _
        (@DistribMulAction.toDistribSMul G₂ ↥W _ _ hDM))
  letI hsmZ : SMul (ZMod p) ↥W :=
    @SMulZeroClass.toSMul (ZMod p) ↥W _
      (@DistribSMul.toSMulZeroClass (ZMod p) ↥W _
        (@DistribMulAction.toDistribSMul (ZMod p) ↥W _ _
          (@Module.toDistribMulAction (ZMod p) ↥W _ _ (inferInstance : Module (ZMod p) ↥W))))
  letI hSC : SMulCommClass G₂ (ZMod p) ↥W :=
    @Function.Injective.smulCommClass G₂ (ZMod p) ↥W E₂ hsmG hsmZ _ _ _
      (Subtype.val : ↥W → E₂) Subtype.val_injective
      (fun g x => rfl) (fun c x => rfl)
  have hFrange : ∀ v : M₁.V, F.hom v ∈ LinearMap.range (W.subtype.rTensor T) := by
    intro v
    refine ⟨m' (Sum.inl v), ?_⟩
    have h := hm' (Sum.inl v)
    simpa [mm, LinearMap.rTensor_def] using h
  have hBrange : ∀ q : G₂ × G₂, B q ∈ LinearMap.range (W.subtype.rTensor T) := by
    intro q
    refine ⟨m' (Sum.inr (Sum.inr q)), ?_⟩
    have h := hm' (Sum.inr (Sum.inr q))
    simpa [mm, LinearMap.rTensor_def] using h
  obtain ⟨F₀, hF₀1, hF₀2⟩ :=
    exists_finite_stage_factor (p := p) (φ := φ) (T := T) (M₁ := M₁) (E₂ := E₂) (E₂₀ := ↥W)
      (i := W.subtype) (hi := fun a b h => Subtype.ext h)
      (hiG := fun g m => rfl) (F := F) (z := z) (B := B)
      (hB := hB) (hB0 := hBrange) (hF0 := hFrange)
  exact ⟨↥W, inferInstance, inferInstance, hDM, hSC, hWfin, W.subtype,
    (fun a b h => Subtype.ext h), (fun g m => rfl), F₀, hF₀1, hF₀2⟩

end Work.SSGRoute
