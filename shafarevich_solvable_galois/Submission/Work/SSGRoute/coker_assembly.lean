import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.naturality_gluing
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.h1_bridge
import Submission.Work.SSGRoute.H1Pair.Clauses
import Submission.Work.SSGRoute.H1Pair.omega_contra
import Submission.Work.SSGRoute.H1Pair.exists_x
import Submission.Work.SSGRoute.H1Pair.DualRestrict
import Submission.Work.SSGRoute.h1_finite_stage
import Submission.Work.SSGRoute.selmer_dual_inflated
import Submission.Work.SSGRoute.H1Pair.horth
import Submission.Work.SSGRoute.coker_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped TensorProduct
open CategoryTheory

namespace Work.SSGRoute

/-! ## Elementary pushforwards of the local predicates -/

section Pushforward

variable {Γ G M N : Type} [Group Γ] [TopologicalSpace Γ] [Group G] [AddCommGroup M]
  [DistribMulAction G M] [AddCommGroup N] [DistribMulAction G N]

/-- The local constancy predicate pushes forward along any function. -/
theorem IsLocConstOn.comp {H : Subgroup Γ} {f : Γ → M} (hf : SSGRoute.IsLocConstOn H f)
    (φ : M → N) : SSGRoute.IsLocConstOn H (fun x => φ (f x)) := by
  obtain ⟨U, hU, h⟩ := hf
  exact ⟨U, hU, fun g hg u hu huH => by
    show φ (f (g * u)) = φ (f g)
    rw [h g hg u hu huH]⟩

/-- The cocycle condition pushes forward along an additive, equivariant map. -/
theorem IsCocycleOn.comp (act : Γ →* G) {H : Subgroup Γ} {f : Γ → M}
    (hf : SSGRoute.IsCocycleOn act H f) (φ : M →+ N)
    (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) :
    SSGRoute.IsCocycleOn act H (fun x => φ (f x)) := by
  intro g hg h hh
  show φ (f (g * h)) = φ (f g) + act g • φ (f h)
  rw [hf g hg h hh, map_add, hφ]

/-- The coboundary condition pushes forward along an additive, equivariant map. -/
theorem IsCoboundaryOn.comp (act : Γ →* G) {H : Subgroup Γ} {f : Γ → M}
    (hf : SSGRoute.IsCoboundaryOn act H f) (φ : M →+ N)
    (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) :
    SSGRoute.IsCoboundaryOn act H (fun x => φ (f x)) := by
  obtain ⟨m, hm⟩ := hf
  exact ⟨φ m, fun g hg => by
    show φ (f g) = act g • φ m - φ m
    rw [hm g hg, map_sub, hφ]⟩

end Pushforward

/-! ## Finiteness of the Tate twist of a finite module by a line -/

/-- A one-dimensional `𝔽_p`-module is finite as a type. -/
theorem finite_of_finrank_eq_one (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T]
    [Module (ZMod p) T] (h : Module.finrank (ZMod p) T = 1) : Finite T := by
  haveI : Module.Free (ZMod p) T := inferInstance
  haveI : Module.Finite (ZMod p) T := Module.finite_of_finrank_pos (by omega)
  have hfr : Module.finrank (ZMod p) T = Module.finrank (ZMod p) (ZMod p) := by
    rw [h, Module.finrank_self]
  exact Finite.of_injective (LinearEquiv.ofFinrankEq T (ZMod p) hfr : T ≃ₗ[ZMod p] ZMod p)
    (LinearEquiv.injective _)

/-- `E ⊗ T` is a finite type when `E` is finite and `T` is a line. -/
theorem finite_tensor_of_finrank_eq_one (p : ℕ) [Fact p.Prime] (E T : Type) [AddCommGroup E]
    [Module (ZMod p) E] [Finite E] [AddCommGroup T] [Module (ZMod p) T]
    (h : Module.finrank (ZMod p) T = 1) : Finite (E ⊗[ZMod p] T) := by
  haveI : Module.Free (ZMod p) T := inferInstance
  haveI : Module.Finite (ZMod p) T := Module.finite_of_finrank_pos (by omega)
  have hfr : Module.finrank (ZMod p) T = Module.finrank (ZMod p) (ZMod p) := by
    rw [h, Module.finrank_self]
  have e : E ⊗[ZMod p] T ≃ₗ[ZMod p] E ⊗[ZMod p] (ZMod p) :=
    TensorProduct.congr (LinearEquiv.refl (ZMod p) E)
      (LinearEquiv.ofFinrankEq T (ZMod p) hfr : T ≃ₗ[ZMod p] ZMod p)
  have e₂ : E ⊗[ZMod p] (ZMod p) ≃ₗ[ZMod p] E := TensorProduct.rid (ZMod p) E
  exact Finite.of_injective ((e.trans e₂ : E ⊗[ZMod p] T ≃ₗ[ZMod p] E) : E ⊗[ZMod p] T → E)
    (LinearEquiv.injective _)

/-! ## A functional separating a point from a submodule (over `𝔽_p`) -/

/-- Over a field, a vector outside a submodule is separated from it by a linear functional:
there is `φ` vanishing on `S` with `φ x ≠ 0`. -/
theorem exists_dual_eq_zero_on_of_notMem (p : ℕ) [Fact p.Prime] {A : Type} [AddCommGroup A]
    [Module (ZMod p) A] (S : Submodule (ZMod p) A) {x : A} (hx : x ∉ S) :
    ∃ φ : A →ₗ[ZMod p] ZMod p, (∀ y ∈ S, φ y = 0) ∧ φ x ≠ 0 := by
  have hx0 : x ≠ 0 := fun h => hx (h ▸ S.zero_mem)
  have hxq : (Submodule.Quotient.mk (p := S) x : A ⧸ S) ≠ 0 := fun h =>
    hx ((Submodule.Quotient.mk_eq_zero S).mp h)
  set L : Submodule (ZMod p) (A ⧸ S) := Submodule.span (ZMod p)
    ({Submodule.Quotient.mk (p := S) x} : Set (A ⧸ S)) with hL
  have hxL : Submodule.Quotient.mk (p := S) x ∈ L := Submodule.subset_span (by simp)
  let ψ : ZMod p →ₗ[ZMod p] L :=
    (LinearMap.toSpanSingleton (ZMod p) (A ⧸ S) (Submodule.Quotient.mk (p := S) x)).codRestrict L
      (fun c => by
        have h : c • (Submodule.Quotient.mk (p := S) x) ∈ L := Submodule.smul_mem _ c hxL
        simpa using h)
  have hψapply : ∀ c : ZMod p, ((ψ c : L) : A ⧸ S) = c • Submodule.Quotient.mk (p := S) x := by
    intro c
    rfl
  have hψbij : Function.Bijective ψ := by
    constructor
    · intro a b hab
      have h : a • (Submodule.Quotient.mk (p := S) x) = b • (Submodule.Quotient.mk (p := S) x) := by
        rw [← hψapply a, ← hψapply b, hab]
      have h1 : (a - b) • (Submodule.Quotient.mk (p := S) x) = 0 := by
        rw [sub_smul]
        exact sub_eq_zero.mpr h
      rcases (smul_eq_zero.mp h1) with h2 | h2
      · exact sub_eq_zero.mp h2
      · exact absurd h2 hxq
    · intro y
      have hy : (y : A ⧸ S) ∈ Submodule.span (ZMod p)
          ({Submodule.Quotient.mk (p := S) x} : Set (A ⧸ S)) := y.2
      rw [Submodule.mem_span_singleton] at hy
      obtain ⟨c, hc⟩ := hy
      refine ⟨c, Subtype.ext ?_⟩
      rw [hψapply]
      exact hc
  obtain ⟨Φ, hΦ⟩ := LinearMap.exists_extend (p := L)
    (f := (LinearEquiv.ofBijective ψ hψbij).symm.toLinearMap)
  refine ⟨Φ.comp (Submodule.mkQ S), ?_, ?_⟩
  · intro y hy
    show Φ (Submodule.mkQ S y) = 0
    have h0 : Submodule.mkQ S y = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hy
    rw [h0, map_zero]
  · have hψ1 : ψ (1 : ZMod p) = (⟨Submodule.Quotient.mk (p := S) x, hxL⟩ : L) := by
      apply Subtype.ext
      rw [hψapply, one_smul]
    have h2 : (LinearEquiv.ofBijective ψ hψbij).symm
        (⟨Submodule.Quotient.mk (p := S) x, hxL⟩ : L) = 1 := by
      rw [← hψ1]
      exact (LinearEquiv.ofBijective ψ hψbij).symm_apply_apply 1
    have h1 : Submodule.mkQ S x = (⟨Submodule.Quotient.mk (p := S) x, hxL⟩ : L) := by
      rw [Submodule.mkQ_apply]
    show Φ (Submodule.mkQ S x) ≠ 0
    rw [h1]
    have hΦy : Φ ((⟨Submodule.Quotient.mk (p := S) x, hxL⟩ : L) : A ⧸ S)
        = (LinearEquiv.ofBijective ψ hψbij).symm ⟨Submodule.Quotient.mk (p := S) x, hxL⟩ := by
      have h := congrArg (fun (g : L →ₗ[ZMod p] ZMod p) => g ⟨Submodule.Quotient.mk (p := S) x, hxL⟩) hΦ
      simpa [LinearMap.comp_apply] using h
    rw [hΦy, h2]
    exact one_ne_zero

end Work.SSGRoute



namespace Work.SSGRoute

/-! ## Step 5: factoring the coefficient map through the finite stage -/

section StageFactorization

variable {p : ℕ} {K : Type} [Group K]

/-- **The factorization of an equivariant pushforward through a finite stage.**

Let `i : W →ₗ E₂` be an injective `K`-equivariant map of `𝔽_p[K]`-modules, `f : E →ₗ E₂` a
`K`-equivariant map and `T` a nontrivial `K`-module.  If the `𝔽_p`-linear map
`F₀ : E ⊗ T →ₗ W ⊗ T` satisfies `(i ⊗ id_T) ∘ F₀ = f ⊗ id_T` on pure tensors, then `f` factors
through `i` by a `K`-equivariant `f₀ : E →ₗ W`, and `F₀ = f₀ ⊗ id_T`.

`[Nontrivial T]` is needed: for `T = 0` the tensor hypothesis is vacuous while the conclusion can
fail.  The proof separates `f e` from `range i` with a functional `λ` killing `i` (using a nonzero
`t : T` and `smul_eq_zero` over the field `𝔽_p`). -/
theorem exists_f0_of_rTensor_eq (p : ℕ) [Fact p.Prime] (K : Type) [Group K]
    (E W E₂ T : Type)
    [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction K E] [SMulCommClass K (ZMod p) E]
    [AddCommGroup W] [Module (ZMod p) W] [DistribMulAction K W] [SMulCommClass K (ZMod p) W]
    [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction K E₂] [SMulCommClass K (ZMod p) E₂]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction K T] [SMulCommClass K (ZMod p) T]
    [Nontrivial T]
    (i : W →ₗ[ZMod p] E₂) (hi : Function.Injective i)
    (hiK : ∀ (g : K) (w : W), i (g • w) = g • i w)
    (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K) (e : E), f (g • e) = g • f e)
    (F₀ : TensorProduct (ZMod p) E T →ₗ[ZMod p] TensorProduct (ZMod p) W T)
    (hF₀ : ∀ (e : E) (t : T), (LinearMap.rTensor T i) (F₀ (e ⊗ₜ[ZMod p] t))
        = f e ⊗ₜ[ZMod p] t) :
    ∃ f₀ : E →ₗ[ZMod p] W,
      (∀ (g : K) (e : E), f₀ (g • e) = g • f₀ e) ∧
      (∀ e : E, i (f₀ e) = f e) ∧
      (∀ (e : E) (t : T), F₀ (e ⊗ₜ[ZMod p] t) = f₀ e ⊗ₜ[ZMod p] t) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hinj : Function.Injective ((LinearMap.rTensor T) i) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := T) i hi
  have hcoe : ∀ y : LinearMap.range i,
      i ((LinearEquiv.ofInjective i hi).symm y) = (y : E₂) :=
    fun y => LinearEquiv.ofInjective_symm_apply i y
  have hmem : ∀ e : E, f e ∈ LinearMap.range i := by
    intro e
    by_contra hmem
    obtain ⟨lam, hlam0, hlamx⟩ :=
      exists_dual_eq_zero_on_of_notMem p (LinearMap.range i) hmem
    have hcomp : (lam ∘ₗ i) = 0 := LinearMap.ext (fun y => hlam0 (i y) ⟨y, rfl⟩)
    obtain ⟨t₀, ht₀⟩ := exists_ne (0 : T)
    have hzero : (lam (f e)) ⊗ₜ[ZMod p] t₀ = 0 := by
      have h1 : ((LinearMap.rTensor T) lam)
          (((LinearMap.rTensor T) i) (F₀ (e ⊗ₜ[ZMod p] t₀))) = 0 := by
        rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hcomp, LinearMap.rTensor_zero,
          LinearMap.zero_apply]
      rw [hF₀ e t₀, LinearMap.rTensor_tmul] at h1
      exact h1
    rw [← (TensorProduct.lid (ZMod p) T).injective.eq_iff, map_zero,
      TensorProduct.lid_tmul] at hzero
    rcases (smul_eq_zero.mp hzero) with h' | h'
    · exact hlamx h'
    · exact ht₀ h'
  let f₀ : E →ₗ[ZMod p] W :=
    (LinearEquiv.ofInjective i hi).symm.toLinearMap ∘ₗ
      (f.codRestrict (LinearMap.range i) hmem)
  have hf₀ : ∀ e : E, i (f₀ e) = f e := by
    intro e
    show i ((LinearEquiv.ofInjective i hi).symm
        ((f.codRestrict (LinearMap.range i) hmem) e)) = f e
    rw [hcoe, LinearMap.codRestrict_apply]
  have hf₀K : ∀ (g : K) (e : E), f₀ (g • e) = g • f₀ e := by
    intro g e
    apply hi
    rw [hf₀, hiK, hf₀, hf]
  have hF₀' : ∀ (e : E) (t : T), F₀ (e ⊗ₜ[ZMod p] t) = f₀ e ⊗ₜ[ZMod p] t := by
    intro e t
    apply hinj
    rw [hF₀ e t]
    simp only [LinearMap.rTensor_tmul, hf₀]
  exact ⟨f₀, hf₀K, hf₀, hF₀'⟩

end StageFactorization

/-! ## The finite stage as a module over the smaller group -/

/-- **The finite stage, with the coefficient module seen as a module over the smaller group.**

Variant of `Work.SSGRoute.h1_finite_stage` in which the ambient coefficient module `E₂` carries a
`K`-module structure and the `G₂`-module structure used by the finite-stage construction is the
pullback of it along `π₂ : G₂ →* K`.  The output `E₂₀` is a finite `K`-module, `i` is `K`-equivariant
and the `G₂`-action on `E₂₀` is (definitionally) the pullback of the `K`-action, so that
`F₀ : M₁ ⟶ Rep.res φ (Rep.res π₂ (of (K, E₂₀ ⊗ T)))` literally has the required type.

The proof repeats the construction of `h1_finite_stage` with the actions on the finite stage `↥W`
defined as the restrictions of those on `E₂`; `hπ₂` (surjectivity of `π₂`) makes the `G₂`-stable
submodule `W` also `K`-stable. -/
theorem exists_finite_stage_K (p : ℕ) [Fact p.Prime]
    {G₁ G₂ : Type} [Group G₁] [Group G₂] [Fintype G₂]
    (K : Type) [Group K] (π₂ : G₂ →* K) (hπ₂ : Function.Surjective π₂)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T]
      [DistribMulAction K T] [SMulCommClass K (ZMod p) T]
    (M₁ : Rep (ZMod p) G₁) [Finite M₁.V]
    (φ : G₁ →* G₂)
    (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂]
      [DistribMulAction K E₂] [SMulCommClass K (ZMod p) E₂]
    (F : M₁ ⟶ Rep.res φ (Rep.res π₂ (Rep.of
      (Representation.ofDistribMulAction (ZMod p) K (TensorProduct (ZMod p) E₂ T)))))
    (x : groupHomology.H1 M₁)
    (hx : (ModuleCat.Hom.hom (groupHomology.map φ F 1)) x = 0) :
    ∃ (E₂₀ : Type) (_ : AddCommGroup E₂₀) (_ : Module (ZMod p) E₂₀)
      (_ : DistribMulAction K E₂₀) (_ : SMulCommClass K (ZMod p) E₂₀) (_ : Finite E₂₀)
      (i : E₂₀ →ₗ[ZMod p] E₂) (_ : Function.Injective i)
      (_ : ∀ (g : K) (m : E₂₀), i (g • m) = g • i m)
      (F₀ : M₁ ⟶ Rep.res φ (Rep.res π₂ (Rep.of
        (Representation.ofDistribMulAction (ZMod p) K (TensorProduct (ZMod p) E₂₀ T))))),
      (∀ z : M₁.V, F.hom z = (LinearMap.rTensor T i) (F₀.hom z)) ∧
      (ModuleCat.Hom.hom (groupHomology.map φ F₀ 1)) x = 0 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI hGE₂ : DistribMulAction G₂ E₂ := DistribMulAction.compHom E₂ π₂
  letI hGT : DistribMulAction G₂ T := DistribMulAction.compHom T π₂
  letI hSCE₂ : SMulCommClass G₂ (ZMod p) E₂ := ⟨fun g c e => by
    show (π₂ g) • (c • e) = c • ((π₂ g) • e)
    rw [smul_comm]⟩
  letI hSCT : SMulCommClass G₂ (ZMod p) T := ⟨fun g c t => by
    show (π₂ g) • (c • t) = c • ((π₂ g) • t)
    rw [smul_comm]⟩
  haveI : Fintype M₁.V := Fintype.ofFinite M₁.V
  revert hx
  refine groupHomology.H1_induction_on x ?_
  intro z hz
  have hY : ((groupHomology.mapCycles₁ φ F z).1 : G₂ →₀ TensorProduct (ZMod p) E₂ T)
      ∈ groupHomology.boundaries₁ (Rep.res π₂ (Rep.of (Representation.ofDistribMulAction
          (ZMod p) K (TensorProduct (ZMod p) E₂ T)))) := by
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
  -- `W` is also `K`-stable, because `G₂` acts through the surjection `π₂`
  have hKstab : ∀ (g : K) (w : E₂), w ∈ W → g • w ∈ W := by
    intro g w hw
    obtain ⟨γ, rfl⟩ := hπ₂ g
    exact hWstab γ w hw
  letI hDMK : DistribMulAction K ↥W :=
    { smul := fun (g : K) (x : ↥W) => ⟨g • (x : E₂), hKstab g x x.2⟩
      one_smul := fun x => Subtype.ext (one_smul K (x : E₂))
      mul_smul := fun g h x => Subtype.ext (mul_smul g h (x : E₂))
      smul_zero := fun g => Subtype.ext (smul_zero g)
      smul_add := fun g x y => Subtype.ext (smul_add g (x : E₂) (y : E₂)) }
  letI hsmK : SMul K ↥W :=
    @SMulZeroClass.toSMul K ↥W _
      (@DistribSMul.toSMulZeroClass K ↥W _
        (@DistribMulAction.toDistribSMul K ↥W _ _ hDMK))
  letI hsmZ : SMul (ZMod p) ↥W :=
    @SMulZeroClass.toSMul (ZMod p) ↥W _
      (@DistribSMul.toSMulZeroClass (ZMod p) ↥W _
        (@DistribMulAction.toDistribSMul (ZMod p) ↥W _ _
          (@Module.toDistribMulAction (ZMod p) ↥W _ _ (inferInstance : Module (ZMod p) ↥W))))
  letI hSCK : SMulCommClass K (ZMod p) ↥W :=
    @Function.Injective.smulCommClass K (ZMod p) ↥W E₂ hsmK hsmZ _ _ _
      (Subtype.val : ↥W → E₂) Subtype.val_injective
      (fun g x => rfl) (fun c x => rfl)
  letI hDMG : DistribMulAction G₂ ↥W := DistribMulAction.compHom ↥W π₂
  letI hsmG : SMul G₂ ↥W :=
    @SMulZeroClass.toSMul G₂ ↥W _
      (@DistribSMul.toSMulZeroClass G₂ ↥W _
        (@DistribMulAction.toDistribSMul G₂ ↥W _ _ hDMG))
  letI hSCG : SMulCommClass G₂ (ZMod p) ↥W :=
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
  exact ⟨↥W, inferInstance, inferInstance, hDMK, hSCK, hWfin, W.subtype,
    (fun a b h => Subtype.ext h), (fun g m => rfl), F₀, hF₀1, hF₀2⟩

end Work.SSGRoute

/-! ## The assembly -/

section Assembly

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (πN : (N ≃ₐ[k] N) →* (K ≃ₐ[k] K))
    (hπN : ∀ σ : Ω ≃ₐ[k] Ω, πN (SSGRoute.res k N σ) = SSGRoute.res k K σ)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (C : Finset (Ω ≃ₐ[k] Ω)) (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (hC : ∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C, ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹)
    (hCdisj : ∀ c ∈ C, ∀ c' ∈ C, (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c')
    (α : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → E)
    (hα : ∀ A ∈ S, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (α A) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (α A))
    (β : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
    (hβ : ∀ c ∈ C, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (β c))

/-- Shorthand for the coefficient module of the assembly. -/
noncomputable abbrev cokerM₁ : Rep (ZMod p) (N ≃ₐ[k] N) :=
  Rep.res πN (Rep.of (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K) (E ⊗[ZMod p] T)))

end Assembly

namespace Work.SSGRoute

/-- **The assembly of `coker_obstruction`.**  All of the formal content of the theorem, given the
two arithmetic inputs: a family of local pairings with clauses (1),(2),(3),(5) (`pair`, `hadd₁`,
`hadd₂`, `hcob`, `hnat`) and the realizability statement `hreal` of Poitou--Tate at `H¹` (SW
Lemma 10, relaxed at `cs(N)`). -/
theorem coker_obstruction_of_inputs (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (πN : (N ≃ₐ[k] N) →* (K ≃ₐ[k] K))
    (hπN : ∀ σ : Ω ≃ₐ[k] Ω, πN (SSGRoute.res k N σ) = SSGRoute.res k K σ)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (C : Finset (Ω ≃ₐ[k] Ω)) (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (hC : ∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C, ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹)
    (hCdisj : ∀ c ∈ C, ∀ c' ∈ C, (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c')
    (α : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → E)
    (hα : ∀ A ∈ S, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (α A) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (α A))
    (β : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
    (hβ : ∀ c ∈ C, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (β c))
    (pair : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
          ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) → ZMod p)
    (hloc : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (H : Subgroup (Ω ≃ₐ[k] Ω)),
        Work.SSGRoute.H1Pair.IsLocalGroup k Ω H →
          Work.SSGRoute.H1Pair.PairClauses p K T M (fun a b => pair M H a b) H)
    (hnat : ∀ (M M₂ : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction (K ≃ₐ[k] K) M₂]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂] [Finite M₂]
        (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (m : M), f (g • m) = g • f m)
        (f' : Work.SSGRoute.DualMod p (M₂ ⊗[ZMod p] T) →ₗ[ZMod p]
          Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
        (hff' : ∀ (φ : Work.SSGRoute.DualMod p (M₂ ⊗[ZMod p] T)) (e : M) (t : T),
          f' φ (e ⊗ₜ[ZMod p] t) = φ (f e ⊗ₜ[ZMod p] t))
        (H : Subgroup (Ω ≃ₐ[k] Ω)) (a : (Ω ≃ₐ[k] Ω) → M)
        (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M₂ ⊗[ZMod p] T)),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
        pair M₂ H (fun σ => f (a σ)) b = pair M H a (fun σ => f' (b σ)))
    (hreal : ∀ (N₂ : IntermediateField k Ω) [FiniteDimensional k N₂] [IsGalois k N₂]
        (hKN₂ : K ≤ N₂)
        (hSram₂ : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
          (SSGRoute.IsRamifiedIn k N₂ B ∨ B.valuation (p : Ω) < 1) →
          ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
        (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (α' : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → M) (β' : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)
        (hα' : ∀ A ∈ S, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (α' A) ∧
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (α' A))
        (hβ' : ∀ c ∈ C, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (β' c))
        (horth : ∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T),
          SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
          (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
            (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k N₂ B →
            SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k B) b) →
          (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
            (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N₂ B →
            ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → b σ = 0) →
          ∑ A ∈ S, pair M (SSGRoute.decomp k A) (α' A) b +
            ∑ c ∈ C, pair M (Subgroup.zpowers c) (β' c) b = 0),
        ∃ ε : (Ω ≃ₐ[k] Ω) → M,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ ε ∧ SSGRoute.IsLocConstOn ⊤ ε ∧
          (∀ A ∈ S, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A)
            (fun σ => ε σ - α' A σ)) ∧
          (∀ c ∈ C, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c)
            (fun σ => ε σ - β' c σ)) ∧
          ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
            (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N₂ B →
            ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → ε σ = 0) :
    ∃ x : groupHomology.H1 (Rep.res πN
        (Rep.of (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K) (E ⊗[ZMod p] T)))),
      ∀ (N₂ : IntermediateField k Ω) [FiniteDimensional k N₂] [IsGalois k N₂],
        K ≤ N₂ → N₂ ≤ N →
        ∀ (q : (N ≃ₐ[k] N) →* (N₂ ≃ₐ[k] N₂)),
        (∀ σ : Ω ≃ₐ[k] Ω, q (SSGRoute.res k N σ) = SSGRoute.res k N₂ σ) →
        ∀ (π₂ : (N₂ ≃ₐ[k] N₂) →* (K ≃ₐ[k] K)),
        (∀ σ : Ω ≃ₐ[k] Ω, π₂ (SSGRoute.res k N₂ σ) = SSGRoute.res k K σ) →
        ∀ (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂]
          (f : E →ₗ[ZMod p] E₂), (∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e) →
        ∀ (F : Rep.res πN
              (Rep.of (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K) (E ⊗[ZMod p] T))) ⟶
            Rep.res q (Rep.res π₂
              (Rep.of (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K) (E₂ ⊗[ZMod p] T))))),
        (∀ z : E ⊗[ZMod p] T, F.hom z = f.rTensor T z) →
        (groupHomology.map q F 1).hom x = 0 →
        ∃ ε : (Ω ≃ₐ[k] Ω) → E₂,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ ε ∧ SSGRoute.IsLocConstOn ⊤ ε ∧
          (∀ A ∈ S, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A)
            (fun σ => ε σ - f (α A σ))) ∧
          (∀ c ∈ C, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c)
            (fun σ => ε σ - f (β c σ))) ∧
          ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
            (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N₂ B →
            ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → ε σ = 0 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI hfinET : Finite (E ⊗[ZMod p] T) :=
    finite_tensor_of_finrank_eq_one p E T hT.1
  -- ## Step 1: the obstruction functional `ω` on the level-`N` cocycles
  obtain ⟨Φ, hΦcob, hΦform⟩ :=
    Work.SSGRoute.H1Pair.omega_functional_contra p k Ω K N hKN ζ hζ hζK E T hT πN hπN
      (pair E) (hloc E) S hSfin C hCinv α hα β hβ
  -- ## Step 2: the class `x` of `H₁` which is Tate-dual to `ω`
  obtain ⟨x, hx⟩ :=
    Work.SSGRoute.H1Pair.exists_x_of_Phi p
      (Rep.res πN (Rep.of (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K) (E ⊗[ZMod p] T))))
      Φ hΦcob
  refine ⟨x, ?_⟩
  intro N₂ _ _ hKN₂ hN₂N q hq π₂ hπ₂ E₂ _ _ _ _ f hf F hF hmap
  -- ## Step 3: the finite stage of the coefficient module, as a `Gal(K/k)`-module
  -- (`π₂` is surjective because it intertwines `π₂` with the surjections `res k ·`)
  have hπ₂surj : Function.Surjective π₂ := by
    intro g
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (E := Ω) (K₁ := ↥K) g
    exact ⟨SSGRoute.res k N₂ σ, by rw [hπ₂ σ]; exact hσ⟩
  obtain ⟨W, _, _, _, _, _, i, hi, hiK, F₀, hF₀F, hF₀x⟩ :=
    Work.SSGRoute.exists_finite_stage_K (p := p) (K := K ≃ₐ[k] K) (π₂ := π₂) (hπ₂ := hπ₂surj)
      (φ := q) (T := T)
      (M₁ := Rep.res πN (Rep.of (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K)
        (E ⊗[ZMod p] T)))) (E₂ := E₂) F x hmap
  -- ## Step 4: the factorization of `f` through the finite stage
  haveI hNT : Nontrivial T :=
    Module.nontrivial_of_finrank_pos (R := ZMod p) (by rw [hT.1]; norm_num)
  have hF₀lin : ∀ z : E ⊗[ZMod p] T, F.hom z = (LinearMap.rTensor T i) (F₀.hom.toLinearMap z) :=
    fun z => hF₀F z
  obtain ⟨f₀, hf₀K, hf₀i, hf₀F⟩ :=
    Work.SSGRoute.exists_f0_of_rTensor_eq (p := p) (K := K ≃ₐ[k] K) (E := E) (W := W) (E₂ := E₂)
      (T := T) i hi hiK f hf F₀.hom.toLinearMap (fun e t => by
        rw [← hF₀lin (e ⊗ₜ[ZMod p] t), hF (e ⊗ₜ[ZMod p] t), LinearMap.rTensor_tmul])
  -- ## Step 5: the level-`N₂` vanishing of the functional (`H1Pair.transfer_sum_eq_zero`)
  have hΦ' : ∀ b : ↥(groupCohomology.cocycles₁ (Work.SSGRoute.H1Pair.contra (Rep.res πN (Rep.of
        (Representation.ofDistribMulAction (ZMod p) (K ≃ₐ[k] K) (E ⊗[ZMod p] T)))))),
      Φ b =
        S.sum (fun A => pair E (SSGRoute.decomp k A) (α A)
          (fun σ => (b : (N ≃ₐ[k] N) → Work.SSGRoute.DualMod p (E ⊗[ZMod p] T))
            (SSGRoute.res k N σ))) +
        C.sum (fun c => pair E (Subgroup.zpowers c) (β c)
          (fun σ => (b : (N ≃ₐ[k] N) → Work.SSGRoute.DualMod p (E ⊗[ZMod p] T))
            (SSGRoute.res k N σ))) :=
    fun b => hΦform b.1 b.2
  have htrans := Work.SSGRoute.H1Pair.transfer_sum_eq_zero (p := p) (k := k) (Ω := Ω)
    (K := K) (N := N) (N₂ := N₂) (E := E) (T := T) (πN := πN) (hπN := hπN) (q := q) (hq := hq)
    (π₂ := π₂) (hπ₂ := hπ₂) (M₂ := W) (f₀ := f₀) (hf₀ := hf₀K) (pair := pair) (hnat := hnat)
    (S := S) (hSfin := hSfin) (C := C) (hCinv := hCinv) (α := α) (hα := hα) (β := β) (hβ := hβ)
    (X := x) (Φ := Φ) (hΦ := hΦ') (hX := hx) (F₀ := F₀) (hF₀tmul := hf₀F) (hF₀zero := hF₀x)
  -- ## Step 6: the orthogonality hypothesis of Poitou--Tate (`H1Pair.horth_of_level_vanishing`)
  have horth := Work.SSGRoute.H1Pair.horth_of_level_vanishing (p := p) (k := k) (Ω := Ω)
    (K := K) (N₂ := N₂) (hKN₂ := hKN₂) (M₂ := W) (π₂ := π₂) (hπ₂ := hπ₂) (T := T) (E := E)
    (f₀ := f₀) (hf₀ := hf₀K) (pair := pair) (S := S) (hSfin := hSfin) (C := C) (hCinv := hCinv)
    (α := α) (β := β) (htransfer := htrans)
  -- ## Step 7: the Poitou--Tate input at the level `N₂` with the finite stage `W`
  have hSram₂ : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N₂ B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B := by
    intro B hB h
    exact hSram B hB (h.imp (fun hr => Work.SSGRoute.isRamifiedIn_of_le hN₂N hr) id)
  have hα' : ∀ A ∈ S, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A)
        (fun σ => f₀ (α A σ)) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (fun σ => f₀ (α A σ)) := by
    intro A hA
    exact ⟨Work.SSGRoute.IsCocycleOn.comp (SSGRoute.res k K) (hα A hA).1 f₀.toAddMonoidHom
        (fun g m => hf₀K g m),
      Work.SSGRoute.IsLocConstOn.comp (hα A hA).2 (fun m => f₀ m)⟩
  have hβ' : ∀ c ∈ C, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c)
        (fun σ => f₀ (β c σ)) := by
    intro c hc
    exact Work.SSGRoute.IsCocycleOn.comp (SSGRoute.res k K) (hβ c hc) f₀.toAddMonoidHom
      (fun g m => hf₀K g m)
  obtain ⟨ε₀, hε₀coc, hε₀lc, hε₀cobS, hε₀cobC, hε₀iner⟩ :=
    hreal N₂ hKN₂ hSram₂ W (fun A σ => f₀ (α A σ)) (fun c σ => f₀ (β c σ)) hα' hβ' horth
  -- ## Step 8: push the global solution forward along the stage inclusion
  refine ⟨fun σ => i (ε₀ σ), ?_, ?_, ?_, ?_, ?_⟩
  · exact Work.SSGRoute.IsCocycleOn.comp (SSGRoute.res k K) hε₀coc i.toAddMonoidHom
      (fun g m => hiK g m)
  · exact Work.SSGRoute.IsLocConstOn.comp hε₀lc (fun m => i m)
  · intro A hA
    have h := Work.SSGRoute.IsCoboundaryOn.comp (SSGRoute.res k K) (hε₀cobS A hA)
      i.toAddMonoidHom (fun g m => hiK g m)
    have hfe : (fun σ : Ω ≃ₐ[k] Ω => i (ε₀ σ) - f (α A σ))
        = fun σ => i (ε₀ σ - f₀ (α A σ)) := by
      funext σ
      rw [map_sub, hf₀i]
    rw [hfe]
    exact h
  · intro c hc
    have h := Work.SSGRoute.IsCoboundaryOn.comp (SSGRoute.res k K) (hε₀cobC c hc)
      i.toAddMonoidHom (fun g m => hiK g m)
    have hfe : (fun σ : Ω ≃ₐ[k] Ω => i (ε₀ σ) - f (β c σ))
        = fun σ => i (ε₀ σ - f₀ (β c σ)) := by
      funext σ
      rw [map_sub, hf₀i]
    rw [hfe]
    exact h
  · intro B hB hconj hsplit σ hσ
    show i (ε₀ σ) = 0
    rw [hε₀iner B hB hconj hsplit σ hσ, map_zero]

end Work.SSGRoute
