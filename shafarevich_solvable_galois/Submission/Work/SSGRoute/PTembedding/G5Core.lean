import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Submission.Work.SSGRoute.PTdualControl.extExact
import Submission.Work.SSGRoute.PTembedding.modRepHom_exists
import Submission.Work.SSGRoute.PTembedding.no_pTorsion_extH_classesK_two
import Submission.Work.SSGRoute.ext_sha1_bridge
import Submission.Work.SSGRoute.local_phi_realization_in
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The assembly of the Tate-Poitou embedding from the two arithmetic inputs E1a and E9

The target of this file is the *last mile* of the `Ext`-core route to the atom
`Work.SSGRoute.tatePoitouEmbedding` (node `G5`): the construction of the natural, injective family

  `Phi_E : Sh^2(k,E) ->_Fp (Sh^1(k, E^v(1)) ->_Fp Fp)`

out of the arithmetic input and nothing else.  The witness is

  `Phi_E(b)(h) = chi (pairK x_b (beta_1 h))`,

where

* `beta : Sh^2(k,E) -> Ext^2_{Gal(K/k)}(E^v(1), K^x)` is the `E1a` map (node `ext_sha2_bridge`);
* `x_b in Ext^1_{Gal(K/k)}(E^v(1), C_K)` is any lift of `beta b` along the connecting map
  `extDelta` of the class formation `0 -> K^x -> I_K -> C_K -> 0` (it exists because the values of
  `beta` are locally trivial, i.e. in `ker extToIdeles = im extDelta`);
* `beta_1 : Sh^1(k,M) -> H^1(Gal(K/k),M)` is the `E1b` descent (node `ext_sha1_bridge`, *proved*),
  whose image is exactly the locally trivial classes;
* `chi : H^2(Gal(K/k),C_K)[p] -> F_p` is the `p`-torsion character (node `pt_char_pTorsion`,
  *proved*), taken with the convention `chi = 0` when `p` does not divide `[K:k]` (there the
  `p`-torsion is trivial, so `chi` is injective in both cases);
* `E9` (node `pt_sha2_core`) supplies the injectivity: a class of `Ext^1(E^v(1),C_K)` pairing to
  zero with every locally trivial `h` comes from the ideles.

## What is new here, and what is not

Everything *below* the two inputs is proved in this file, from the workspace's proved assets:

* `Work.SSGRoute.Sha2Lib.yonedaPair_eq_of_extDelta_eq` (well-definedness of the pairing on `Sh^2`,
  i.e. independence of the lift `x_b`) -- used for the additivity of `Phi_E` in `b` and for the
  naturality square;
* `SSGRoute.PTExt.yonedaPair_extToClasses_eq_zero_of_locTrivial` (orthogonality) -- inside the above;
* `SSGRoute.PTdualControl.exists_extDelta_eq_of_extToIdeles_eq_zero` (exactness of the class
  formation at `Ext^2`) -- used to show that the *filed* form of `E1a` implies the input used here;
* `Work.SSGRoute.ext_sha1_bridge` (`E1b`), `Work.SSGRoute.pt_char_pTorsion` (`chi`), and the
  `Ext`-calculus `Work.SSGRoute.comp_nsmul_aux` / `Work.SSGRoute.nsmul_comp_aux`.

The two inputs are *stated*, not proved: `E1aInput` is the honest form of node `E1a` (see its
docstring) and `E9Input` is node `E9` (`pt_sha2_core`) with its unused hypotheses dropped.

## Status (proved, axiom-clean)

`tatePoitouEmbedding_of_extInputs` is **proved** (`[propext, Classical.choice, Quot.sound]`), as are
`E1aInput_of_E1aFiled`, `yonedaPair_pTorsion` and the elementary helpers.  So the whole of node
`G5` is reduced to the two arithmetic statements:

  `E1aFiled` (`= the conclusion of `Work.SSGRoute.ext_sha2_bridge`)`  **and**  `E9Input`
  (`= `Work.SSGRoute.pt_sha2_core` with its unused `ζ`, `hζ` dropped`),

and the assembly uses *strictly less* than `E1aFiled` states:

* only the **inclusion** `im β ⊆ im(extDelta)` (via the landing clause of `E1aInput`) is used, never
  the converse/image description `= ker extToIdeles` — so the assembly is insensitive to the
  `D_A`-vs-`D_w` doubt about that `↔` clause recorded in `Work.SSGRoute.sha2_dual_control`;
* **no Euler characteristic** is used: the case `p ∤ [K:k]` is absorbed by the convention `χ = 0`
  (there `H²(Gal(K/k),C_K)` has order `[K:k]`, hence no `p`-torsion:
  `Work.SSGRoute.PTembedding.no_pTorsion_extH_classesK_two`), and injectivity still follows from
  `E9` because the pairing values are then automatically zero;
* `φ` is well defined on `Ш²` by `Work.SSGRoute.Sha2Lib.yonedaPair_eq_of_extDelta_eq` (the two
  possible lifts `x_b` differ by `im(extToClasses)`, which pairs to zero with locally trivial
  classes), which is also exactly what makes `Φ` additive in `b` and natural in `E`.

Consequently, once `E1a` and `E9` land, `Work.SSGRoute.tatePoitouEmbedding` follows in one
application of `tatePoitouEmbedding_of_extInputs` composed with `E1aInput_of_E1aFiled`.
-/

open scoped TensorProduct

namespace Work.SSGRoute.G5Core

open CategoryTheory SSGRoute.PTExt

noncomputable section

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-! ## The two arithmetic inputs -/

/-- **The `E1a` input of the `G5` assembly.**  There is a family `beta_E`, natural in the finite
`F_p[Gal(K/k)]`-module `E` and additive, of maps

  `beta_E : Sh^2(k,E) -> Ext^2_{Gal(K/k)}(E^v(1), K^x)`,   `E^v(1) = DualMod p (E (x) T)`,

which is *injective* and whose values lie in the image of the connecting map
`extDelta : Ext^1(E^v(1), C_K) -> Ext^2(E^v(1), K^x)` of the class formation
`0 -> K^x -> I_K -> C_K -> 0` (equivalently: in `ker extToIdeles`).

This is node `E1a` (`Work.SSGRoute.ext_sha2_bridge`) with its image clause weakened to the inclusion
`im beta <= im extDelta = ker extToIdeles` -- which is what the assembly actually consumes.  The
weaker form is the robust one: it is stated without reference to the `D_A`/`D_w` local-condition
comparison that the filed form's `iff` clause depends on. -/
def E1aInput (p : Nat) [Fact p.Prime] (k Omega : Type) [Field k] [NumberField k] [Field Omega]
    [Algebra k Omega] [IsAlgClosure k Omega] (K : IntermediateField k Omega) [FiniteDimensional k K]
    [IsGalois k K] [Fintype (K ≃ₐ[k] K)] (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] : Prop :=
  ∃ β : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      Sha2 p k Omega K E →+
        Abelian.Ext (modRep (K ≃ₐ[k] K) (DualMod p (TensorProduct (ZMod p) E T)))
          (unitsK k K) 2,
    (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E], Function.Injective (β E)) ∧
    (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] (b : Sha2 p k Omega K E),
      ∃ x : Abelian.Ext
            (modRep (K ≃ₐ[k] K) (DualMod p (TensorProduct (ZMod p) E T)))
            (classesK k K) 1,
        extDelta x = β E b) ∧
    (∀ (E₁ : Type) [AddCommGroup E₁] [Module (ZMod p) E₁] [DistribMulAction (K ≃ₐ[k] K) E₁]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₁] [Finite E₁]
        (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
        (f : E₁ →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E₁), f (g • e) = g • f e)
        (F : modRep (K ≃ₐ[k] K) (DualMod p (TensorProduct (ZMod p) E₂ T)) ⟶
          modRep (K ≃ₐ[k] K) (DualMod p (TensorProduct (ZMod p) E₁ T)))
        (hF : ∀ (φ : DualMod p (TensorProduct (ZMod p) E₂ T)) (e : E₁) (t : T),
          (show DualMod p (TensorProduct (ZMod p) E₁ T) from F.hom φ) (e ⊗ₜ[ZMod p] t)
            = φ (f e ⊗ₜ[ZMod p] t))
        (b : Sha2 p k Omega K E₁),
        β E₂ (Sha2Map p k Omega K E₁ E₂ f hf b)
          = (Abelian.Ext.mk₀ F).comp (β E₁ b) (zero_add 2))

/-- The *filed* form of node `E1a` (`Work.SSGRoute.ext_sha2_bridge`): `E1aInput` with the landing
clause `im beta <= im extDelta = ker extToIdeles` replaced by the full image description
`im beta = ker extToIdeles`.  `E1aInput_of_E1aFiled` below shows that this stronger form implies
the input consumed by the assembly; note that the assembly uses only the *inclusion*
(`beta`'s values are locally trivial, hence lie in `im extDelta`), which is the direction that does
not depend on the `D_A`/`D_w` local-condition comparison. -/
def E1aFiled (p : Nat) [Fact p.Prime] (k Omega : Type) [Field k] [NumberField k] [Field Omega]
    [Algebra k Omega] [IsAlgClosure k Omega] (K : IntermediateField k Omega) [FiniteDimensional k K]
    [IsGalois k K] [Fintype (K ≃ₐ[k] K)] (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] : Prop :=
  ∃ β : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      Sha2 p k Omega K E →+
        Abelian.Ext (modRep (K ≃ₐ[k] K) (DualMod p (TensorProduct (ZMod p) E T)))
          (unitsK k K) 2,
    (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E], Function.Injective (β E)) ∧
    (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
        (y : Abelian.Ext
            (modRep (K ≃ₐ[k] K) (DualMod p (TensorProduct (ZMod p) E T)))
            (unitsK k K) 2),
      (∃ b : Sha2 p k Omega K E, β E b = y) ↔ extToIdeles y = 0) ∧
    (∀ (E₁ : Type) [AddCommGroup E₁] [Module (ZMod p) E₁] [DistribMulAction (K ≃ₐ[k] K) E₁]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₁] [Finite E₁]
        (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
        (f : E₁ →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E₁), f (g • e) = g • f e)
        (F : modRep (K ≃ₐ[k] K) (DualMod p (TensorProduct (ZMod p) E₂ T)) ⟶
          modRep (K ≃ₐ[k] K) (DualMod p (TensorProduct (ZMod p) E₁ T)))
        (hF : ∀ (φ : DualMod p (TensorProduct (ZMod p) E₂ T)) (e : E₁) (t : T),
          (show DualMod p (TensorProduct (ZMod p) E₁ T) from F.hom φ) (e ⊗ₜ[ZMod p] t)
            = φ (f e ⊗ₜ[ZMod p] t))
        (b : Sha2 p k Omega K E₁),
        β E₂ (Sha2Map p k Omega K E₁ E₂ f hf b)
          = (Abelian.Ext.mk₀ F).comp (β E₁ b) (zero_add 2))

/-- **The `E9` input of the `G5` assembly** (node `E9`, `Work.SSGRoute.pt_sha2_core`, with its two
unused hypotheses `zeta`, `hzeta` dropped): a class of `Ext^1_{Gal(K/k)}(M, C_K)` whose Yoneda
pairing with every locally trivial `h in H^1(Gal(K/k),M)` vanishes comes from the ideles. -/
def E9Input (p : Nat) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] : Prop :=
  ∀ (M : Rep.{0} Coeff (K ≃ₐ[k] K)) [Finite M], (∀ m : M, p • m = 0) →
    ∀ x : Abelian.Ext M (classesK k K) 1,
      (∀ h : extH M 1, IsLocTrivial h → pairK x h = 0) →
      ∃ z : Abelian.Ext M (idelesK k K) 1, extToClasses z = x

/-! ## Local finiteness instances

`Finite`-ness of the tensor product `E ⊗ T` and of the dual `DualMod p (E ⊗ T)` is needed at every
use of the `E1a`/`E1b` data in the assembly; both are proved in
`Submission/Work/SSGRoute/PTembedding/tatePoitouEmbedding_alt.lean` (`finite_tensor`, `finite_dual`)
and recorded here as local instances. -/

local instance finite_tensor_zmod (p : Nat) [Fact p.Prime] (E T : Type) [AddCommGroup E]
    [Module (ZMod p) E] [Finite E] [AddCommGroup T] [Module (ZMod p) T] [Finite T] :
    Finite (TensorProduct (ZMod p) E T) := finite_tensor (p := p) E T

/-- The `𝔽_p`-dual of a finite module is finite. -/
theorem finite_dual_g5 (p : Nat) [Fact p.Prime] (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [Finite X] : Finite (X →ₗ[ZMod p] ZMod p) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Fintype X := Fintype.ofFinite X
  haveI : Fintype (X → ZMod p) := inferInstance
  exact Finite.of_injective (fun f : X →ₗ[ZMod p] ZMod p => (f : X → ZMod p))
    (fun f g h => LinearMap.ext (congrFun h))

local instance finite_dual_zmod (p : Nat) [Fact p.Prime] (X : Type) [AddCommGroup X]
    [Module (ZMod p) X] [Finite X] : Finite (X →ₗ[ZMod p] ZMod p) := finite_dual_g5 p X

local instance finite_modRep (G : Type) [Group G] {X : Type} [AddCommGroup X]
    [DistribMulAction G X] [Finite X] :
    Finite (SSGRoute.PTExt.modRep G X) := inferInstanceAs (Finite X)

/-! ## Elementary helpers -/

/-- A one-dimensional `F_p`-module is finite. -/
private lemma finite_of_finrank_eq_one (p : Nat) [Fact p.Prime] (T : Type) [AddCommGroup T]
    [Module (ZMod p) T] (h : Module.finrank (ZMod p) T = 1) : Finite T := by
  haveI : Module.Free (ZMod p) T := Module.Free.of_divisionRing (ZMod p) T
  haveI : Module.Finite (ZMod p) T := Module.finite_of_finrank_pos (by rw [h]; norm_num)
  have hfr : Module.finrank (ZMod p) T = Module.finrank (ZMod p) (ZMod p) := by
    rw [h, Module.finrank_self]
  exact Finite.of_injective
    (LinearEquiv.ofFinrankEq T (ZMod p) hfr : T ≃ₗ[ZMod p] ZMod p) (LinearEquiv.injective _)

/-- `Finite T` for a cyclotomic dual `T` of `mu_p`. -/
private lemma finite_of_isCyclotomicDual (p : Nat) [Fact p.Prime] {Γ G T Ω : Type} [Group Γ]
    [Group G] [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T] [Field Ω]
    [MulSemiringAction Γ Ω] (act : Γ →* G) (ζ : Ω)
    (hT : SSGRoute.IsCyclotomicDual p (T := T) act ζ) : Finite T :=
  finite_of_finrank_eq_one p T hT.1

set_option backward.isDefEq.respectTransparency false in
/-- `extDelta` is additive. -/
private lemma extDelta_add' {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] {M : Rep.{0} Coeff (K ≃ₐ[k] K)}
    (x x' : Abelian.Ext M (classesK k K) 1) :
    extDelta (x + x') = extDelta x + extDelta x' := by
  simp only [extDelta]
  rw [Abelian.Ext.add_comp]

set_option backward.isDefEq.respectTransparency false in
/-- **Naturality of `extDelta` in the coefficient module**. -/
private lemma extDelta_mk₀_comp' {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] {M₁ M₂ : Rep.{0} Coeff (K ≃ₐ[k] K)} (F : M₁ ⟶ M₂)
    (x : Abelian.Ext M₂ (classesK k K) 1) :
    extDelta ((Abelian.Ext.mk₀ F).comp x (zero_add 1)) =
      (Abelian.Ext.mk₀ F).comp (extDelta x) (zero_add 2) := by
  have hS := NK.HassePrinciple.ideleShortComplex_shortExact k K
  show ((Abelian.Ext.mk₀ F).comp x (zero_add 1)).comp hS.extClass (rfl : 1 + 1 = 2)
      = (Abelian.Ext.mk₀ F).comp (x.comp hS.extClass (rfl : 1 + 1 = 2)) (zero_add 2)
  rw [Abelian.Ext.comp_assoc]
  omega

/-- **The Yoneda pairing `H¹(G,M) x Ext¹_G(M,C_K) → H²(G,C_K)` is `p`-torsion when `M` is.**  The
value `pairK x h = yonedaPair x h` is `χ`'s argument in the `G5` assembly, so its `p`-torsion is
what makes `χ` applicable; the proof is that `p • h = 0` and the pairing is additive in `h`. -/
theorem yonedaPair_pTorsion (p : ℕ) [Fact p.Prime] {k K : Type} [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {M : Rep.{0} Coeff (K ≃ₐ[k] K)} (hM : ∀ m : M, p • m = 0)
    (x : Abelian.Ext M (classesK k K) 1) (h : extH M 1) :
    p • yonedaPair x h = 0 := by
  rw [yonedaPair, ← Work.SSGRoute.nsmul_comp_aux p h x (rfl : 1 + 1 = 2)]
  rw [show p • h = 0 from Work.SSGRoute.extH_smul_eq_zero_of_pTorsion M hM h]
  exact Abelian.Ext.zero_comp (unitRep (K ≃ₐ[k] K)) 1 x 2 rfl

/-! ## The assembly -/



/-- **The `G5` assembly**: the two arithmetic inputs `E1a` and `E9` produce the Tate-Poitou
embedding `Phi`, injective and natural in the finite `F_p[Gal(K/k)]`-module `E`. -/
theorem tatePoitouEmbedding_of_extInputs
    (p : Nat) [Fact p.Prime] (k Omega : Type) [Field k] [NumberField k] [Field Omega]
    [Algebra k Omega] [IsAlgClosure k Omega] (K : IntermediateField k Omega)
    [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)] (ζ : Omega)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hE1a : E1aInput p k Omega K T) (hE9 : E9Input p k K) :
    ∃ Φ : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
            [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
          Work.SSGRoute.Sha2 p k Omega K E →ₗ[ZMod p]
            (Work.SSGRoute.Sha1 p k Omega K
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)) →ₗ[ZMod p] ZMod p),
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        Function.Injective (Φ E)) ∧
      (∀ (E₁ : Type) [AddCommGroup E₁] [Module (ZMod p) E₁] [DistribMulAction (K ≃ₐ[k] K) E₁]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₁] [Finite E₁]
          (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
          (f : E₁ →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E₁), f (g • e) = g • f e)
          (f' : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T) →ₗ[ZMod p]
                  Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T))
          (hf' : ∀ (g : K ≃ₐ[k] K) (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)),
            f' (g • φ) = g • f' φ)
          (hff' : ∀ (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) (e : E₁) (t : T),
            f' φ (TensorProduct.tmul (ZMod p) e t) = φ (TensorProduct.tmul (ZMod p) (f e) t))
          (b : Work.SSGRoute.Sha2 p k Omega K E₁),
          Φ E₂ (Work.SSGRoute.Sha2Map p k Omega K E₁ E₂ f hf b)
            = (Φ E₁ b).comp
                (Work.SSGRoute.Sha1Map p k Omega K
                  (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T))
                  (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T)) f' hf')) := by
  classical
  obtain ⟨β, hβinj, hβland, hβnat⟩ := hE1a
  obtain ⟨β₁, _hβ₁inj, hβ₁range, hβ₁nat⟩ := ext_sha1_bridge p k Omega K
  haveI : Finite T := finite_of_isCyclotomicDual p (SSGRoute.res k K) ζ hT
  -- the `p`-torsion character `χ` on `H^2(Gal(K/k),C_K)`, with `χ = 0` when `p` does not divide
  -- `[K:k]` (there the `p`-torsion is trivial); `χ` is injective in both cases
  have hchar : ∃ (P : AddSubgroup (extH (classesK k K) 2)) (χ : P →+ ZMod p),
      (∀ v : extH (classesK k K) 2, v ∈ P ↔ p • v = 0) ∧ Function.Injective χ := by
    by_cases hp : p ∣ Module.finrank k K
    · obtain ⟨P, χ, hP, hχbij⟩ := pt_char_pTorsion p k K K hp
      exact ⟨P, χ, hP, hχbij.injective⟩
    · refine ⟨⊥, 0, fun v => ?_, fun a b _ => Subsingleton.elim a b⟩
      constructor
      · intro hv
        rw [AddSubgroup.mem_bot.mp hv, nsmul_zero]
      · exact fun hv => AddSubgroup.mem_bot.mpr (Work.SSGRoute.PTembedding.no_pTorsion_extH_classesK_two p k K hp v hv)
  obtain ⟨P, χ, hP, hχinj⟩ := hchar
  -- the chosen lifts `x_b` of `β b` along `extDelta`
  let xb : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      Sha2 p k Omega K E → Abelian.Ext
        (modRep (K ≃ₐ[k] K) (DualMod p (TensorProduct (ZMod p) E T))) (classesK k K) 1 :=
    fun E _ _ _ _ _ b => Classical.choose (hβland E b)
  have hxb : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
      (b : Sha2 p k Omega K E), extDelta (xb E b) = β E b :=
    fun E _ _ _ _ _ b => Classical.choose_spec (hβland E b)
  -- the pairing value `pairK x (β₁ h)` is `p`-torsion (a specialisation of `yonedaPair_pTorsion`)
  have hptors : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
      (x : Abelian.Ext (modRep (K ≃ₐ[k] K) (DualMod p (TensorProduct (ZMod p) E T)))
        (classesK k K) 1)
      (h : extH (modRep (K ≃ₐ[k] K) (DualMod p (TensorProduct (ZMod p) E T))) 1),
      p • yonedaPair x h = 0 := by
    intro E _ _ _ _ _ x h
    refine yonedaPair_pTorsion p (M := modRep (K ≃ₐ[k] K)
      (DualMod p (TensorProduct (ZMod p) E T))) ?_ x h
    intro m
    haveI : Module (ZMod p) ↑(modRep (K ≃ₐ[k] K)
        (DualMod p (TensorProduct (ZMod p) E T))) :=
      inferInstanceAs (Module (ZMod p) (DualMod p (TensorProduct (ZMod p) E T)))
    rw [← Nat.cast_smul_eq_nsmul (R := ZMod p) p m, ZMod.natCast_self, zero_smul]
  -- local triviality of the values of `β₁`
  have hβ₁loc : forall (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
      (h : Sha1 p k Omega K (DualMod p (TensorProduct (ZMod p) E T))),
      IsLocTrivial (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h) :=
    fun E _ _ _ _ _ h => (hβ₁range (DualMod p (TensorProduct (ZMod p) E T)) _).mp ⟨h, rfl⟩
  -- additivity of the pairing value in `b`
  have hpair_sum : forall (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
      (b₁ b₂ : Sha2 p k Omega K E)
      (h : Sha1 p k Omega K (DualMod p (TensorProduct (ZMod p) E T))),
      yonedaPair (xb E (b₁ + b₂)) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h)
        = yonedaPair (xb E b₁) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h)
          + yonedaPair (xb E b₂) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h) := by
    intro E _ _ _ _ _ b₁ b₂ h
    have hdelta : extDelta (xb E (b₁ + b₂)) = extDelta (xb E b₁ + xb E b₂) := by
      rw [hxb E (b₁ + b₂), extDelta_add', hxb E b₁, hxb E b₂, map_add]
    rw [yonedaPair_eq_of_extDelta_eq (k := k) (K := K) hdelta
      (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h) (hβ₁loc E h)]
    rw [yonedaPair, Abelian.Ext.comp_add, yonedaPair, yonedaPair]
  -- the additive homomorphism `h ↦ χ ⟨pairK (x_b) (β₁ h)⟩`
  let hhom : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
      (b : Sha2 p k Omega K E),
      Sha1 p k Omega K (DualMod p (TensorProduct (ZMod p) E T)) →+ ZMod p := by
    intro E _ _ _ _ _ b
    refine AddMonoidHom.mk' (fun h => χ ⟨yonedaPair (xb E b)
      (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h), (hP _).mpr (hptors E (xb E b) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h))⟩) ?_
    intro h₁ h₂
    have hv : (⟨yonedaPair (xb E b) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) (h₁ + h₂)),
        (hP _).mpr (hptors E (xb E b) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) (h₁ + h₂)))⟩ : P)
        = ⟨yonedaPair (xb E b) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h₁),
            (hP _).mpr (hptors E (xb E b) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h₁))⟩
          + ⟨yonedaPair (xb E b) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h₂),
            (hP _).mpr (hptors E (xb E b) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h₂))⟩ := by
      apply Subtype.ext
      show yonedaPair (xb E b) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) (h₁ + h₂))
        = yonedaPair (xb E b) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h₁)
          + yonedaPair (xb E b) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h₂)
      rw [map_add, yonedaPair, Abelian.Ext.add_comp, yonedaPair, yonedaPair]
    rw [hv]
    exact map_add χ _ _
  let hhom₂ : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      Sha2 p k Omega K E →+
        (Sha1 p k Omega K (DualMod p (TensorProduct (ZMod p) E T)) →ₗ[ZMod p] ZMod p) := by
    intro E _ _ _ _ _
    refine AddMonoidHom.mk' (fun b => AddMonoidHom.toZModLinearMap p (hhom E b)) ?_
    intro b₁ b₂
    apply LinearMap.ext
    intro h
    dsimp only [hhom]
    show χ ⟨yonedaPair (xb E (b₁ + b₂)) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h),
        (hP _).mpr (hptors E (xb E (b₁ + b₂)) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h))⟩
      = χ ⟨yonedaPair (xb E b₁) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h),
          (hP _).mpr (hptors E (xb E b₁) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h))⟩
        + χ ⟨yonedaPair (xb E b₂) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h),
          (hP _).mpr (hptors E (xb E b₂) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h))⟩
    have hv : (⟨yonedaPair (xb E (b₁ + b₂)) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h),
        (hP _).mpr (hptors E (xb E (b₁ + b₂)) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h))⟩ : P)
        = ⟨yonedaPair (xb E b₁) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h),
            (hP _).mpr (hptors E (xb E b₁) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h))⟩
          + ⟨yonedaPair (xb E b₂) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h),
            (hP _).mpr (hptors E (xb E b₂) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h))⟩ := by
      apply Subtype.ext
      show yonedaPair (xb E (b₁ + b₂)) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h)
        = yonedaPair (xb E b₁) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h)
          + yonedaPair (xb E b₂) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h)
      exact hpair_sum E b₁ b₂ h
    rw [hv]
    exact map_add χ _ _
  -- the family `Phi`
  let Phi : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      Sha2 p k Omega K E →ₗ[ZMod p]
        (Sha1 p k Omega K (DualMod p (TensorProduct (ZMod p) E T)) →ₗ[ZMod p] ZMod p) :=
    fun E _ _ _ _ _ => AddMonoidHom.toZModLinearMap p (hhom₂ E)
  have hPhi : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
      (b : Sha2 p k Omega K E) (h : Sha1 p k Omega K (DualMod p (TensorProduct (ZMod p) E T))),
      Phi E b h = χ ⟨yonedaPair (xb E b) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h),
        (hP _).mpr (hptors E (xb E b) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h))⟩ := by
    intro E _ _ _ _ _ b h
    dsimp only [Phi, hhom₂, hhom]
    rfl
  refine ⟨Phi, ?_, ?_⟩
  · intro E _ _ _ _ _ b₁ b₂ hb
    have hker : ∀ b : Sha2 p k Omega K E, Phi E b = 0 → b = 0 := by
      intro b hb
      have hzero : ∀ h : Sha1 p k Omega K (DualMod p (TensorProduct (ZMod p) E T)),
          yonedaPair (xb E b) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h) = 0 := by
        intro h
        have h₁ : Phi E b h = 0 := by rw [hb]; rfl
        rw [hPhi E b h] at h₁
        have h₂ : (⟨yonedaPair (xb E b) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h),
            (hP _).mpr (hptors E (xb E b) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h))⟩ : P) = 0 := by
          apply hχinj
          rw [show χ ⟨yonedaPair (xb E b) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h),
              (hP _).mpr (hptors E (xb E b) (β₁ (DualMod p (TensorProduct (ZMod p) E T)) h))⟩ = 0 from by
            rw [← hPhi E b h]; exact h₁, map_zero]
        exact congrArg Subtype.val h₂
      have hkill : ∀ h : extH (modRep (K ≃ₐ[k] K) (DualMod p (TensorProduct (ZMod p) E T))) 1,
          IsLocTrivial h → pairK (xb E b) h = 0 := by
        intro h hh
        obtain ⟨h₀, hh₀⟩ := (hβ₁range (DualMod p (TensorProduct (ZMod p) E T)) h).mpr hh
        rw [← hh₀]
        exact hzero h₀
      obtain ⟨z, hz⟩ := hE9 (modRep (K ≃ₐ[k] K) (DualMod p (TensorProduct (ZMod p) E T)))
        (fun m => by
          haveI : Module (ZMod p) ↑(modRep (K ≃ₐ[k] K)
              (DualMod p (TensorProduct (ZMod p) E T))) :=
            inferInstanceAs (Module (ZMod p) (DualMod p (TensorProduct (ZMod p) E T)))
          rw [← Nat.cast_smul_eq_nsmul (R := ZMod p) p m, ZMod.natCast_self, zero_smul])
        (xb E b) hkill
      have h0 : β E b = 0 := by
        rw [← hxb E b, ← hz, extDelta_extToClasses]
      exact hβinj E (by rw [h0, map_zero])
    have hsub : Phi E (b₁ - b₂) = 0 := by rw [map_sub, hb, sub_self]
    exact sub_eq_zero.mp (hker (b₁ - b₂) hsub)
  · intro E₁ _ _ _ _ _ E₂ _ _ _ _ _ f hf f' hf' hff' b
    obtain ⟨F, hF⟩ := Work.SSGRoute.PTembedding.modRepHom_exists p (K ≃ₐ[k] K) f' hf'
    have hF'' : ∀ (φ : DualMod p (TensorProduct (ZMod p) E₂ T)) (e : E₁) (t : T),
        (show DualMod p (TensorProduct (ZMod p) E₁ T) from F.hom φ) (e ⊗ₜ[ZMod p] t)
          = φ (f e ⊗ₜ[ZMod p] t) := by
      intro φ e t
      rw [hF φ]
      exact hff' φ e t
    apply LinearMap.ext
    intro h
    rw [hPhi E₂ _ h, LinearMap.comp_apply,
      hPhi E₁ _ (Sha1Map p k Omega K (DualMod p (TensorProduct (ZMod p) E₂ T))
        (DualMod p (TensorProduct (ZMod p) E₁ T)) f' hf' h)]
    -- E1b naturality, as an identity of `P`-elements
    have hnl : β₁ (DualMod p (TensorProduct (ZMod p) E₁ T))
        (Sha1Map p k Omega K (DualMod p (TensorProduct (ZMod p) E₂ T))
          (DualMod p (TensorProduct (ZMod p) E₁ T)) f' hf' h)
        = (β₁ (DualMod p (TensorProduct (ZMod p) E₂ T)) h).comp
          (Abelian.Ext.mk₀ F) (add_zero 1) :=
      hβ₁nat (DualMod p (TensorProduct (ZMod p) E₂ T))
        (DualMod p (TensorProduct (ZMod p) E₁ T)) f' hf' F (fun φ => hF φ) h
    have hsub1 : (⟨yonedaPair (xb E₁ b) (β₁ (DualMod p (TensorProduct (ZMod p) E₁ T))
          (Sha1Map p k Omega K (DualMod p (TensorProduct (ZMod p) E₂ T))
            (DualMod p (TensorProduct (ZMod p) E₁ T)) f' hf' h)),
        (hP _).mpr (hptors E₁ (xb E₁ b) (β₁ (DualMod p (TensorProduct (ZMod p) E₁ T))
          (Sha1Map p k Omega K (DualMod p (TensorProduct (ZMod p) E₂ T))
            (DualMod p (TensorProduct (ZMod p) E₁ T)) f' hf' h)))⟩ : P)
        = ⟨yonedaPair (xb E₁ b) ((β₁ (DualMod p (TensorProduct (ZMod p) E₂ T)) h).comp
            (Abelian.Ext.mk₀ F) (add_zero 1)),
          (hP _).mpr (hptors E₁ (xb E₁ b) ((β₁ (DualMod p (TensorProduct (ZMod p) E₂ T)) h).comp
            (Abelian.Ext.mk₀ F) (add_zero 1)))⟩ := by
      apply Subtype.ext
      rw [hnl]
    rw [hsub1]
    -- the two lifts of `β (f_* b)` have the same `extDelta`
    have hdelta : extDelta (xb E₂ (Sha2Map p k Omega K E₁ E₂ f hf b))
        = extDelta ((Abelian.Ext.mk₀ F).comp (xb E₁ b) (zero_add 1)) := by
      rw [extDelta_mk₀_comp', hxb E₁ b, hxb E₂ (Sha2Map p k Omega K E₁ E₂ f hf b)]
      exact (hβnat E₁ E₂ f hf F hF'' b)
    have hsub2 : (⟨yonedaPair (xb E₂ (Sha2Map p k Omega K E₁ E₂ f hf b))
          (β₁ (DualMod p (TensorProduct (ZMod p) E₂ T)) h),
        (hP _).mpr (hptors E₂ (xb E₂ (Sha2Map p k Omega K E₁ E₂ f hf b)) (β₁ (DualMod p (TensorProduct (ZMod p) E₂ T)) h))⟩ : P)
        = ⟨yonedaPair ((Abelian.Ext.mk₀ F).comp (xb E₁ b) (zero_add 1))
            (β₁ (DualMod p (TensorProduct (ZMod p) E₂ T)) h),
          (hP _).mpr (hptors E₂ ((Abelian.Ext.mk₀ F).comp (xb E₁ b) (zero_add 1))
            (β₁ (DualMod p (TensorProduct (ZMod p) E₂ T)) h))⟩ := by
      apply Subtype.ext
      exact yonedaPair_eq_of_extDelta_eq (k := k) (K := K) hdelta
        (β₁ (DualMod p (TensorProduct (ZMod p) E₂ T)) h) (hβ₁loc E₂ h)
    rw [hsub2]
    -- associativity of the `Ext`-composition
    have hsub3 : (⟨yonedaPair ((Abelian.Ext.mk₀ F).comp (xb E₁ b) (zero_add 1))
          (β₁ (DualMod p (TensorProduct (ZMod p) E₂ T)) h),
        (hP _).mpr (hptors E₂ ((Abelian.Ext.mk₀ F).comp (xb E₁ b) (zero_add 1))
          (β₁ (DualMod p (TensorProduct (ZMod p) E₂ T)) h))⟩ : P)
        = ⟨yonedaPair (xb E₁ b) ((β₁ (DualMod p (TensorProduct (ZMod p) E₂ T)) h).comp
            (Abelian.Ext.mk₀ F) (add_zero 1)),
          (hP _).mpr (hptors E₁ (xb E₁ b) ((β₁ (DualMod p (TensorProduct (ZMod p) E₂ T)) h).comp
            (Abelian.Ext.mk₀ F) (add_zero 1)))⟩ := by
      apply Subtype.ext
      simp only [yonedaPair]
      rw [Abelian.Ext.comp_assoc]
      omega
    rw [hsub3]

end

end Work.SSGRoute.G5Core
