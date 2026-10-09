import Mathlib
import Submission.Work.SSGRoute.ExtChain.ChainGamma
import Submission.Work.SSGRoute.ExtChain.e1aCoeffH2_natural
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The canonical coefficient identification `E ≃+ DualMod p (DualMod p (E ⊗ T))` for (A3)

`Submission/Work/SSGRoute/ArchSplit2/archSplit2_canonical.lean` (A3 of the split-place archimedean
branch) needs a *canonical*, coefficient-natural identification

  `archSplit2Phi : E ≃+ DualMod p (DualMod p (E ⊗ T))`

which converts the double dual `DualMod p (DualMod p (E ⊗ T))` — the target of the lift·2 functional
`ell E` of A1 (`ArchSplit2.ell_bot_family`) — into the coefficient module `E`.

The point of the particular choice made here is that it is *compatible with the sign computation*
A2 (`ArchSplit2.archSplit2_square_sign`): A2 is stated with the canonical Kummer identification
`e1aCoeffNat … : E ≃+ Hom_ℤ(E', Ωˣ)` (`E' = DualMod p (E ⊗ T)`), and the only way to turn its
*vanishing criterion* `ell E X m = 0 ↔ e1aCoeffNat … E e m = 0` into an honest equality is to build
`archSplit2Phi` out of the same chosen `e1aCoeffNat`:

  `archSplit2Phi E := e1aCoeffNat … E ≫ (dualEquiv_zpow p ζu hζu (DualMod p (E ⊗ T)))⁻¹`,

where `ζu = (hζ.isUnit _).unit` and `dualEquiv_zpow p ζu hζu M : DualMod p M ≃+ (M →+ Additive Ωˣ)`
is the zeta-power duality (`Submission/Work/SSGRoute/dualPairingEquiv.lean`).  Then

* `archSplit2Phi_eq_zero_iff` computes the *sign* of `archSplit2Phi`: because `dualEquiv_zpow` is
  `u ↦ (m ↦ ζu ^ (u m))` and `ζu` is a primitive `p`-th root of unity, a value vanishes exactly when
  the corresponding double-dual value vanishes (`zetaPowHom_eq_zero_iff`);
* `archSplit2Phi_natural_apply` is the naturality of `archSplit2Phi` in the coefficient, obtained
  from the naturality of the chosen `e1aCoeffNat` (`e1aCoeffNat_natural_aux`) together with the
  naturality of `dualEquiv_zpow.symm` under precomposition
  (`dualEquiv_zpow_symm_natural_apply`).

The choice `archSplit2Phi` is forced by the vanishing criterion: any other natural identification
would differ from it on `μ_p`-valued data and would break the square clause of A3.
-/

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

namespace Work.SSGRoute.ArchSplit2

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-- **The zeta-power map vanishes only at `0`.**  For `ζu` a primitive `p`-th root of unity of a
commutative ring `A`, `zetaPowHom ζu hζu : ZMod p →+ Additive Aˣ` (the map `x ↦ ζu ^ x`) is
injective; equivalently its value is the unit `1` only at `x = 0`. -/
theorem zetaPowHom_eq_zero_iff {A : Type*} [CommRing A] {p : ℕ} (ζu : Aˣ)
    (hζu : IsPrimitiveRoot ζu p) (x : ZMod p) :
    Work.SSGRoute.zetaPowHom ζu hζu x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  have hinj : Function.Injective (Work.SSGRoute.zetaPowHom ζu hζu) := by
    have hcoe : ∀ y : ZMod p, Additive.toMul (Work.SSGRoute.zetaPowHom ζu hζu y)
        = ((Additive.toMul (hζu.zmodEquivZPowers y) : ↥(Subgroup.zpowers ζu)) : Aˣ) :=
      fun y => rfl
    intro a b hab
    have h2 : ((Additive.toMul (hζu.zmodEquivZPowers a) : ↥(Subgroup.zpowers ζu)) : Aˣ)
        = ((Additive.toMul (hζu.zmodEquivZPowers b) : ↥(Subgroup.zpowers ζu)) : Aˣ) :=
      (hcoe a).symm.trans ((congrArg Additive.toMul hab).trans (hcoe b))
    exact hζu.zmodEquivZPowers.injective
      (Additive.toMul.injective (Subtype.val_injective h2))
  exact hinj (h.trans (map_zero (Work.SSGRoute.zetaPowHom ζu hζu)).symm)

/-- The injectivity form of `zetaPowHom_eq_zero_iff`. -/
theorem zetaPowHom_sub_eq_zero_iff {A : Type*} [CommRing A] {p : ℕ} (ζu : Aˣ)
    (hζu : IsPrimitiveRoot ζu p) (a b : ZMod p) :
    Work.SSGRoute.zetaPowHom ζu hζu a = Work.SSGRoute.zetaPowHom ζu hζu b ↔ a = b := by
  have hinj : Function.Injective (Work.SSGRoute.zetaPowHom ζu hζu) := by
    intro a b hab
    have h : Work.SSGRoute.zetaPowHom ζu hζu (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have h' := (zetaPowHom_eq_zero_iff ζu hζu (a - b)).mp h
    exact sub_eq_zero.mp h'
  exact ⟨fun h => hinj h, fun h => by rw [h]⟩

/-- **Naturality of the zeta-power duality in its argument** (pointwise form).  For `𝔽_p`-modules
`X₁, X₂`, an *additive* map `T : X₂ →+ X₁` (in the application `T = (F'.hom).toAddMonoidHom` is the
transpose of a coefficient map, which is only additive because `Rep`-homs are `ℤ`-linear) and any
`φ : X₁ →+ Additive Aˣ`, the inverse of the zeta-power duality
`Dᵢ := dualEquiv_zpow p ζu hζu Xᵢ` satisfies `(D₂⁻¹ (φ ∘ T)) x = (D₁⁻¹ φ) (T x)`. -/
theorem dualEquiv_zpow_symm_natural_apply (p : ℕ) [Fact p.Prime] {A : Type*} [CommRing A]
    [IsDomain A] (ζu : Aˣ) (hζu : IsPrimitiveRoot ζu p)
    (X₁ X₂ : Type*) [AddCommGroup X₁] [Module (ZMod p) X₁] [AddCommGroup X₂] [Module (ZMod p) X₂]
    (T : X₂ →+ X₁) (φ : X₁ →+ Additive Aˣ) (x : X₂) :
    ((Work.SSGRoute.dualEquiv_zpow p ζu hζu X₂).symm (φ.comp T)) x
      = ((Work.SSGRoute.dualEquiv_zpow p ζu hζu X₁).symm φ) (T x) := by
  refine (zetaPowHom_sub_eq_zero_iff ζu hζu _ _).mp ?_
  rw [← Work.SSGRoute.dualEquiv_zpow_apply p ζu hζu X₂
        ((Work.SSGRoute.dualEquiv_zpow p ζu hζu X₂).symm (φ.comp T)) x,
      AddEquiv.apply_symm_apply]
  rw [← Work.SSGRoute.dualEquiv_zpow_apply p ζu hζu X₁
        ((Work.SSGRoute.dualEquiv_zpow p ζu hζu X₁).symm φ) (T x),
      AddEquiv.apply_symm_apply]
  rfl

/-- **`ZMod p` with `p = 2` is the two-element set.**  Two elements of `ZMod p` whose vanishing is
equivalent are equal: the archimedean sign computations produce values in this two-element set, so a
criterion `x = 0 ↔ y = 0` upgrades to an equality. -/
theorem zmod_two_dichotomy_aux {p : ℕ} (hp : p = 2) : ∀ a b : ZMod p, (a = 0 ↔ b = 0) → a = b := by
  subst hp
  decide

/-- **The canonical coefficient identification** used in (A3):
`E ≃+ DualMod p (DualMod p (E ⊗ T))`, obtained by composing the *chosen* Kummer identification
`e1aCoeffNat … E : E ≃+ Hom_ℤ(E', Ωˣ)` with the inverse of the zeta-power duality
`dualEquiv_zpow p ζu hζu (DualMod p (E ⊗ T))`. -/
noncomputable def archSplit2Phi (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] :
    E ≃+ Work.SSGRoute.DualMod p (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)) :=
  (Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E).trans
    (Work.SSGRoute.dualEquiv_zpow p (Work.SSGRoute.PT.e1aZetaUnit p Ω ζ hζ)
      (Work.SSGRoute.PT.e1aZetaUnit_isPrimitiveRoot p Ω ζ hζ)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))).symm

/-- The computation rule for `archSplit2Phi`: `archSplit2Phi E e` is the inverse `ζ`-power duality
image of `e1aCoeffNat … E e`. -/
theorem archSplit2Phi_apply (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] (e : E) :
    archSplit2Phi p k Ω K ζ hζ hζK T hT E e
      = (Work.SSGRoute.dualEquiv_zpow p (Work.SSGRoute.PT.e1aZetaUnit p Ω ζ hζ)
          (Work.SSGRoute.PT.e1aZetaUnit_isPrimitiveRoot p Ω ζ hζ)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))).symm
        (Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E e) := rfl

/-- **The sign of `archSplit2Phi`**: a double-dual value vanishes exactly when the corresponding
`e1aCoeffNat`-value is the unit `1`.  This is the bridge between the vanishing criterion of A2 and
the double dual on which the lift·2 functional `ell E` of A1 takes its values. -/
theorem archSplit2Phi_eq_zero_iff (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] (e : E)
    (m : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)) :
    archSplit2Phi p k Ω K ζ hζ hζK T hT E e m = 0 ↔
      Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E e m = 0 := by
  have hDPhi : (Work.SSGRoute.dualEquiv_zpow p (Work.SSGRoute.PT.e1aZetaUnit p Ω ζ hζ)
        (Work.SSGRoute.PT.e1aZetaUnit_isPrimitiveRoot p Ω ζ hζ)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
      (archSplit2Phi p k Ω K ζ hζ hζK T hT E e)
      = Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E e := by
    rw [archSplit2Phi_apply]
    exact AddEquiv.apply_symm_apply _ _
  have hpt : Work.SSGRoute.zetaPowHom (Work.SSGRoute.PT.e1aZetaUnit p Ω ζ hζ)
        (Work.SSGRoute.PT.e1aZetaUnit_isPrimitiveRoot p Ω ζ hζ)
        (archSplit2Phi p k Ω K ζ hζ hζK T hT E e m)
      = Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E e m :=
    (Work.SSGRoute.dualEquiv_zpow_apply p (Work.SSGRoute.PT.e1aZetaUnit p Ω ζ hζ)
        (Work.SSGRoute.PT.e1aZetaUnit_isPrimitiveRoot p Ω ζ hζ)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))
        (archSplit2Phi p k Ω K ζ hζ hζK T hT E e) m).symm.trans
      (congrArg (fun ψ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) →+ Additive Ωˣ =>
        ψ m) hDPhi)
  exact (zetaPowHom_eq_zero_iff _ _ _).symm.trans
    (Iff.of_eq (congrArg (fun z : Additive Ωˣ => z = 0) hpt))

/-- **Naturality of `archSplit2Phi` in the coefficient** (pointwise form): for an equivariant
`f : E → E₂` with transpose `F'`, the identification intertwines `f` with `F'`.  This is the
naturality of `e1aCoeffNat` (`e1aCoeffNat_natural_aux`) together with
`dualEquiv_zpow_symm_natural_apply`. -/
theorem archSplit2Phi_natural_apply (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (E2 : Type) [AddCommGroup E2] [Module (ZMod p) E2] [DistribMulAction (K ≃ₐ[k] K) E2]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E2] [Finite E2]
    (f : E →ₗ[ZMod p] E2) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
    (F' : SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E2 T)) ⟶
      SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
    (hF : ∀ (θ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E2 T)) (e : E) (t : T),
      (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) from F'.hom θ)
        (TensorProduct.tmul (ZMod p) e t) = θ (TensorProduct.tmul (ZMod p) (f e) t))
    (e : E) (m2 : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E2 T)) :
    archSplit2Phi p k Ω K ζ hζ hζK T hT E2 (f e) m2
      = archSplit2Phi p k Ω K ζ hζ hζK T hT E e
          (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) from F'.hom m2) := by
  rw [archSplit2Phi_apply, archSplit2Phi_apply,
    Work.SSGRoute.ExtChain.e1aCoeffNat_natural_aux p k Ω K ζ hζ hζK T hT E E2 f hf F' hF e]
  exact dualEquiv_zpow_symm_natural_apply p (Work.SSGRoute.PT.e1aZetaUnit p Ω ζ hζ)
    (Work.SSGRoute.PT.e1aZetaUnit_isPrimitiveRoot p Ω ζ hζ)
    (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))
    (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E2 T))
    (Rep.Hom.hom F').toAddMonoidHom
    (Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E e) m2

end Work.SSGRoute.ArchSplit2
