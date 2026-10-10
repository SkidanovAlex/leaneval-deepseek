import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.PTdualControl.charPTorsionLevel
import Submission.Work.SSGRoute.PTdualControl.extExact
import Submission.Work.SSGRoute.PTdualControl.subsingleton_sha2_of_not_dvd_finrank
import Submission.Work.SSGRoute.Sha2Lib.pt_core_assembly
import Submission.Work.SSGRoute.ext_sha1_bridge

/-!
# `G5`: the assembly of `tatePoitouEmbedding` from `E1a` and `E9`

`Work.SSGRoute.PTdualControl.tatePoitouEmbedding_of_E1a_E9` assembles the atom
`Work.SSGRoute.tatePoitouEmbedding` (the injectivity half of Tate--Poitou duality in "embedding"
form, `DESIGN_FIX2.md` §3, node `G5`) from the two remaining arithmetic inputs:

* **`E1a`** (`Work.SSGRoute.ext_sha2_bridge`): a family of injections
  `β₂ : Ш²(k,E) ↪ Ext²_{Gal(K/k)}(E^∨(1), Kˣ)` with image `ker(extToIdeles)`, natural in `E`;
* **`E9`** (`Work.SSGRoute.Sha2Lib.extDelta_eq_zero_of_locTrivial_annihilator`): a class of
  `Ext¹_{Gal(K/k)}(M, C_K)` whose Yoneda pairing with every *locally trivial* element of
  `H¹(Gal(K/k), M)` vanishes lies in the image of `Ext¹_{Gal(K/k)}(M, 𝕀_K)` (`extDelta = 0`).

Everything else is available in the workspace (see the individual lemmas below).  The case
`p ∤ [K:k]` needs no duality at all: `Ш²(k,E) = 0` and `Φ = 0` works.
-/

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory
open scoped TensorProduct

namespace Work.SSGRoute.PTdualControl

open SSGRoute.PTExt


section FastShaInstances
/-! Build-speed: the additive monoid on `Sha1`, stated once. Each occurrence otherwise re-runs the
search through the quotient of the submodule `Z1loc` (several seconds each, mostly a failing
`AddCommGroup ↥(Z1loc …)` attempt). The value is the instance the search finds. -/
variable {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {K : IntermediateField k Ω}
  [Normal k K] {M : Type} [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]

instance (priority := high) instAddCommMonoidSha1Fast : AddCommMonoid (Work.SSGRoute.Sha1 p k Ω K M) :=
  Submodule.Quotient.addCommMonoid _

end FastShaInstances


/-! ## Auxiliary linear algebra: `𝔽_p`-linear maps as `Coeff`-linear and as `Rep`-morphisms -/

section Aux

variable {p : ℕ}

/-- An `𝔽_p`-linear map is automatically `Coeff`-linear, `Coeff = ULift ℤ`: the `ULift ℤ`-action
is the `ℤ`-action, and every additive map commutes with it. -/
def coeffLinear {M N : Type} [AddCommGroup M] [AddCommGroup N] [Module (ZMod p) M]
    [Module (ZMod p) N] (f : M →ₗ[ZMod p] N) : M →ₗ[SSGRoute.PTExt.Coeff] N where
  toFun := f
  map_add' := f.map_add
  map_smul' u m := by
    show f (u.down • m) = u.down • f m
    exact f.toAddMonoidHom.map_zsmul u.down m

@[simp] theorem coeffLinear_apply {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [Module (ZMod p) M] [Module (ZMod p) N]
    (f : M →ₗ[ZMod p] N) (m : M) : coeffLinear f m = f m := rfl

/-- The morphism `modRep G M ⟶ modRep G N` attached to a `G`-equivariant `𝔽_p`-linear map. -/
noncomputable def modRepMap {G : Type} [Group G] {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [Module (ZMod p) M] [Module (ZMod p) N]
    [DistribMulAction G M] [DistribMulAction G N] (f : M →ₗ[ZMod p] N)
    (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) :
    SSGRoute.PTExt.modRep G M ⟶ SSGRoute.PTExt.modRep G N :=
  Rep.ofHom (Representation.IntertwiningMap.mk (coeffLinear f) (fun g => LinearMap.ext (fun m => by
    show f (g • m) = g • f m
    exact hf g m)))

@[simp] theorem modRepMap_hom {G : Type} [Group G] {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [Module (ZMod p) M] [Module (ZMod p) N]
    [DistribMulAction G M] [DistribMulAction G N] (f : M →ₗ[ZMod p] N)
    (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) (m : M) :
    ((modRepMap f hf).hom : M → N) m = f m := rfl

/-- A line over `𝔽_p` is finite. -/
theorem finite_of_finrank_eq_one (p : ℕ) [Fact p.Prime] {T : Type} [AddCommGroup T]
    [Module (ZMod p) T] (h : Module.finrank (ZMod p) T = 1) : Finite T := by
  haveI : Module.Finite (ZMod p) T := Module.finite_of_finrank_pos (by omega)
  exact Module.finite_of_finite (ZMod p)

/-- The `𝔽_p`-dual of `E ⊗ T` is finite when `E` is finite and `T` is a line. -/
theorem finite_dualMod_tensor_of_finrank_eq_one (p : ℕ) [Fact p.Prime] (E T : Type)
    [AddCommGroup E] [Module (ZMod p) E] [Finite E] [AddCommGroup T] [Module (ZMod p) T]
    (h : Module.finrank (ZMod p) T = 1) : Finite (DualMod p (E ⊗[ZMod p] T)) := by
  haveI : Module.Free (ZMod p) T := inferInstance
  haveI : Module.Finite (ZMod p) T := Module.finite_of_finrank_pos (by omega)
  have hfr : Module.finrank (ZMod p) T = Module.finrank (ZMod p) (ZMod p) := by
    rw [h, Module.finrank_self]
  have e : E ⊗[ZMod p] T ≃ₗ[ZMod p] E ⊗[ZMod p] (ZMod p) :=
    TensorProduct.congr (LinearEquiv.refl (ZMod p) E)
      (LinearEquiv.ofFinrankEq T (ZMod p) hfr : T ≃ₗ[ZMod p] ZMod p)
  have e₂ : E ⊗[ZMod p] (ZMod p) ≃ₗ[ZMod p] E := TensorProduct.rid (ZMod p) E
  haveI : Finite (E ⊗[ZMod p] T) :=
    Finite.of_injective ((e.trans e₂ : E ⊗[ZMod p] T ≃ₗ[ZMod p] E) : E ⊗[ZMod p] T → E)
      (LinearEquiv.injective _)
  exact Finite.of_injective (fun f : DualMod p (E ⊗[ZMod p] T) => (f : E ⊗[ZMod p] T → ZMod p))
    DFunLike.coe_injective

end Aux

/-! ## The two arithmetic inputs, as named hypotheses -/

/-- **`E1a`** (`Work.SSGRoute.ext_sha2_bridge`), as an input: the family `β₂` of injections
`Ш²(k,E) ↪ Ext²_{Gal(K/k)}(E^∨(1), Kˣ)` whose image is `ker(extToIdeles)`, natural in `E`. -/
def E1aInput (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) : Prop :=
  ∃ β : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        Work.SSGRoute.Sha2 p k Ω K E →+
          Abelian.Ext (modRep (K ≃ₐ[k] K) (DualMod p (E ⊗[ZMod p] T))) (unitsK k K) 2,
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E], Function.Injective (β E)) ∧
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
          (y : Abelian.Ext (modRep (K ≃ₐ[k] K) (DualMod p (E ⊗[ZMod p] T))) (unitsK k K) 2),
          (∃ b, β E b = y) ↔ extToIdeles y = 0) ∧
      ∀ (E₁ : Type) [AddCommGroup E₁] [Module (ZMod p) E₁] [DistribMulAction (K ≃ₐ[k] K) E₁]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₁] [Finite E₁]
        (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
        (f : E₁ →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E₁), f (g • e) = g • f e)
        (F : modRep (K ≃ₐ[k] K) (DualMod p (E₂ ⊗[ZMod p] T)) ⟶
             modRep (K ≃ₐ[k] K) (DualMod p (E₁ ⊗[ZMod p] T)))
        (hF : ∀ (φ : DualMod p (E₂ ⊗[ZMod p] T)) (e : E₁) (t : T),
          (show DualMod p (E₁ ⊗[ZMod p] T) from F.hom φ) (e ⊗ₜ[ZMod p] t)
            = φ (f e ⊗ₜ[ZMod p] t))
        (b : Work.SSGRoute.Sha2 p k Ω K E₁),
        β E₂ (Work.SSGRoute.Sha2Map p k Ω K E₁ E₂ f hf b)
          = (Abelian.Ext.mk₀ F).comp (β E₁ b) (zero_add 2)

/-- **`E9`** (`Work.SSGRoute.Sha2Lib.extDelta_eq_zero_of_locTrivial_annihilator`), as an input at
the level `K`, guarded by `p ∣ [K:k]` (outside that range it is *false*: the pairing values are
`p`-torsion in the `p`-torsion-free group `H²(Gal(K/k),C_K) ≅ ℤ/[K:k]`).

**WARNING (2026-09-27): this `Prop` is FALSE; do not try to prove it.**  Two independent defects
were found by the two reviewers of the node `Work.SSGRoute.PTdualControl.e9InputProof`:

* the hypothesis `IsLocTrivial h` can be **vacuous**: for the trivial coefficient module
  `M = ℽ_p`, every `h ∈ H¹(Gal(K/k),M)` that dies on every decomposition group is `0`
  (Chebotarev: the Frobenius elements are dense), so the hypothesis reads `pairK x 0 = 0` for every
  `x` and the conclusion would assert `extDelta x = 0` for **all** `x ∈ Ext¹_G(M,C_K)`; for
  `k = ℚ`, `K = ℚ(√2)`, `p = 2`, `M = 𝔽₂` the two sides of `extDelta` both
  have order `2` and `extDelta` is injective, so a nonzero `x` is a counterexample;
* the hypothesis `μ_p ⊆ K` is missing: `p ∣ [K:k]` does not imply `μ_p ⊆ K`
  (e.g. `k = ℚ`, `K = ℚ(ζ₇)⁺`, `p = 3`), and the de-vissage route to `E9`
  runs through `E6Ω` (`Work.SSGRoute.phi1_mono_sylow_in`), whose statement requires
  `ζ : K`, `IsPrimitiveRoot ζ p`.

The all-levels repair (`SSGRoute.PTExt.IsLocTrivialLevel`) does **not** help: by
`Submission/Work/SSGRoute/Sha2Lib/e9_hypothesis_forms_iff.lean` the all-levels hypothesis is
*equivalent* to the level-`K` one.  The correct `E9` is the middle exactness of the Poitou–Tate
sequence in `P¹`-terms (`E9_STATUS.md`: `im(H¹(k,E) → P¹(E)) = ann(loc H¹(k,E'))`),
which is a *different* statement.  Consequently `tatePoitouEmbedding_of_E1a_E9` and
`sha2_dual_control_alt_of_routeA` are **vacuous as reductions** (their `hE9` cannot be discharged);
only route B of `Work.SSGRoute.PTdualControl` is live. -/
def E9Input (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [NumberField k]
    (K : Type) [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] :
    Prop :=
  p ∣ Module.finrank k K →
  ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
    (∀ m : M, p • m = 0) →
    ∀ x : Abelian.Ext.{0} (modRep (K ≃ₐ[k] K) M) (classesK k K) 1,
      (∀ h : extH (modRep (K ≃ₐ[k] K) M) 1, IsLocTrivial (k := k) (K := K) h →
        pairK (k := k) (K := K) x h = 0) →
      extDelta (k := k) (K := K) x = 0

/-! ## Elementary `Ext` bookkeeping -/

section ExtBookkeeping

variable (k : Type) [Field k] [NumberField k]
  (K : Type) [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]

/-- `pairK x ·` is additive. -/
theorem pairK_add {M : Rep.{0} Coeff (K ≃ₐ[k] K)}
    (x : Abelian.Ext.{0} M (classesK k K) 1) (h₁ h₂ : extH M 1) :
    pairK (k := k) (K := K) x (h₁ + h₂)
      = pairK (k := k) (K := K) x h₁ + pairK (k := k) (K := K) x h₂ := by
  simp only [pairK, yonedaPair]
  exact Abelian.Ext.add_comp h₁ h₂ x rfl

/-- `pairK x 0 = 0`. -/
theorem pairK_zero {M : Rep.{0} Coeff (K ≃ₐ[k] K)}
    (x : Abelian.Ext.{0} M (classesK k K) 1) :
    pairK (k := k) (K := K) x (0 : extH M 1) = 0 := by
  simp only [pairK, yonedaPair]
  exact Abelian.Ext.zero_comp _ 1 x 2 rfl

/-- `pairK · h` is additive. -/
theorem pairK_add_left {M : Rep.{0} Coeff (K ≃ₐ[k] K)}
    (x x' : Abelian.Ext.{0} M (classesK k K) 1) (h : extH M 1) :
    pairK (k := k) (K := K) (x + x') h
      = pairK (k := k) (K := K) x h + pairK (k := k) (K := K) x' h := by
  simp only [pairK, yonedaPair]
  exact Abelian.Ext.comp_add h x x' rfl

/-- `pairK 0 h = 0`. -/
theorem zero_pairK {M : Rep.{0} Coeff (K ≃ₐ[k] K)} (h : extH M 1) :
    pairK (k := k) (K := K) (0 : Abelian.Ext.{0} M (classesK k K) 1) h = 0 := by
  simp only [pairK, yonedaPair]
  exact Abelian.Ext.comp_zero h (classesK k K) 1 2 rfl

/-- `extDelta` is additive. -/
theorem extDelta_add {M : Rep.{0} Coeff (K ≃ₐ[k] K)}
    (x x' : Abelian.Ext.{0} M (classesK k K) 1) :
    extDelta (k := k) (K := K) (x + x')
      = extDelta (k := k) (K := K) x + extDelta (k := k) (K := K) x' := by
  simp only [extDelta]
  exact Abelian.Ext.add_comp x x' _ rfl

/-- `extDelta 0 = 0`. -/
theorem extDelta_zero {M : Rep.{0} Coeff (K ≃ₐ[k] K)} :
    extDelta (k := k) (K := K) (0 : Abelian.Ext.{0} M (classesK k K) 1) = 0 := by
  simp only [extDelta]
  exact Abelian.Ext.zero_comp _ 1 _ 2 rfl

/-- `extDelta` commutes with precomposition by `mk₀ F`. -/
theorem extDelta_comp_mk₀ {M N : Rep.{0} Coeff (K ≃ₐ[k] K)} (F : M ⟶ N)
    (x : Abelian.Ext.{0} N (classesK k K) 1) :
    extDelta (k := k) (K := K) ((Abelian.Ext.mk₀ F).comp x (zero_add 1))
      = (Abelian.Ext.mk₀ F).comp (extDelta (k := k) (K := K) x) (zero_add 2) := by
  have h := Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ F) x
    ((NK.HassePrinciple.ideleShortComplex_shortExact k K).extClass)
    (zero_add 1) (rfl : 1 + 1 = 2) (show 0 + 1 + 1 = 2 from rfl)
  simpa only [extDelta] using h

end ExtBookkeeping

/-! ## The `p ∤ [K:k]` case -/

section NotDvd

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [Fintype (K ≃ₐ[k] K)] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]

include ζ hζ hζK in
/-- **The `p ∤ [K:k]` case of `G5`**: `Ш²(k,E) = 0`, so the zero family works. -/
theorem exists_Phi_of_not_dvd
    (hp : ¬ p ∣ Module.finrank k K) :
    ∃ Φ : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
            [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
          Sha2 p k Ω K E →ₗ[ZMod p]
            (Sha1 p k Ω K (DualMod p (E ⊗[ZMod p] T)) →ₗ[ZMod p] ZMod p),
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        Function.Injective (Φ E)) ∧
      (∀ (E₁ : Type) [AddCommGroup E₁] [Module (ZMod p) E₁] [DistribMulAction (K ≃ₐ[k] K) E₁]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₁] [Finite E₁]
          (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
          (f : E₁ →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E₁), f (g • e) = g • f e)
          (f' : DualMod p (E₂ ⊗[ZMod p] T) →ₗ[ZMod p] DualMod p (E₁ ⊗[ZMod p] T))
          (hf' : ∀ (g : K ≃ₐ[k] K) (φ : DualMod p (E₂ ⊗[ZMod p] T)), f' (g • φ) = g • f' φ)
          (hff' : ∀ (φ : DualMod p (E₂ ⊗[ZMod p] T)) (e : E₁) (t : T),
            f' φ (e ⊗ₜ[ZMod p] t) = φ (f e ⊗ₜ[ZMod p] t))
          (b : Sha2 p k Ω K E₁),
          Φ E₂ (Sha2Map p k Ω K E₁ E₂ f hf b)
            = (Φ E₁ b).comp
                (Sha1Map p k Ω K (DualMod p (E₂ ⊗[ZMod p] T))
                  (DualMod p (E₁ ⊗[ZMod p] T)) f' hf')) := by
  refine ⟨fun E _ _ _ _ _ => 0, ?_, ?_⟩
  · intro E _ _ _ _ _
    have hsub : Subsingleton (Sha2 p k Ω K E) :=
      subsingleton_sha2_of_not_dvd_finrank p k Ω K ζ hζ hζK E hp
    intro b₁ b₂ _
    exact hsub.elim _ _
  · intro E₁ _ _ _ _ _ E₂ _ _ _ _ _ f hf f' hf' hff' b
    simp

end NotDvd

/-! ## The `p ∣ [K:k]` case -/

section Dvd

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [Fintype (K ≃ₐ[k] K)] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)

/-- **The `p ∣ [K:k]` case of `G5`**, from the inputs `E1a` and `E9`.

The pairing value `Φ E b a = χ ⟨pairK x_b (β_{E1b} a), ·⟩` is well defined because two choices of
`x_b` (a preimage of `β₂ E b` under `extDelta`) differ by an element of `im(extToClasses)`, which
pairs to `0` with every locally trivial class.  Injectivity is `E9`; naturality is `E1a` + `E1b` +
associativity of `Ext.comp`. -/
theorem exists_Phi_of_dvd
    (hE1a : E1aInput p k Ω K ζ hζ hζK T hT)
    (hE9 : E9Input p k ↥K)
    (hp : p ∣ Module.finrank k K) :
    ∃ Φ : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
            [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
          Sha2 p k Ω K E →ₗ[ZMod p]
            (Sha1 p k Ω K (DualMod p (E ⊗[ZMod p] T)) →ₗ[ZMod p] ZMod p),
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        Function.Injective (Φ E)) ∧
      (∀ (E₁ : Type) [AddCommGroup E₁] [Module (ZMod p) E₁] [DistribMulAction (K ≃ₐ[k] K) E₁]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₁] [Finite E₁]
          (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
          (f : E₁ →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E₁), f (g • e) = g • f e)
          (f' : DualMod p (E₂ ⊗[ZMod p] T) →ₗ[ZMod p] DualMod p (E₁ ⊗[ZMod p] T))
          (hf' : ∀ (g : K ≃ₐ[k] K) (φ : DualMod p (E₂ ⊗[ZMod p] T)), f' (g • φ) = g • f' φ)
          (hff' : ∀ (φ : DualMod p (E₂ ⊗[ZMod p] T)) (e : E₁) (t : T),
            f' φ (e ⊗ₜ[ZMod p] t) = φ (f e ⊗ₜ[ZMod p] t))
          (b : Sha2 p k Ω K E₁),
          Φ E₂ (Sha2Map p k Ω K E₁ E₂ f hf b)
            = (Φ E₁ b).comp
                (Sha1Map p k Ω K (DualMod p (E₂ ⊗[ZMod p] T))
                  (DualMod p (E₁ ⊗[ZMod p] T)) f' hf')) := by
  classical
  -- finiteness of the dual of `E ⊗ T`: needed to apply `β₁`
  haveI hfin : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      Finite (DualMod p (E ⊗[ZMod p] T)) :=
    fun E _ _ _ _ _ => finite_dualMod_tensor_of_finrank_eq_one p E T hT.1
  -- `E1b`: `Ш¹(k,M) ↪ H¹(Gal(K/k),M)` with range the locally trivial classes
  obtain ⟨β₁, hβ₁inj, hβ₁range, hβ₁nat⟩ := ext_sha1_bridge p k Ω K
  -- `E1a`: `Ш²(k,E) ↪ Ext²_G(E^∨(1),Kˣ)` with image `ker(extToIdeles)`
  obtain ⟨β₂, hβ₂inj, hβ₂im, hβ₂nat⟩ := hE1a
  -- the `p`-torsion character `χ` at the level `K`
  obtain ⟨P, χ, hPmem, hχbij⟩ := char_pTorsion_level_of p k Ω K hp
  -- a choice of a preimage of `β₂ E b` under the connecting map `extDelta`
  let xB : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      Sha2 p k Ω K E →
        Abelian.Ext (modRep (K ≃ₐ[k] K) (DualMod p (E ⊗[ZMod p] T))) (classesK k ↥K) 1 :=
    fun E _ _ _ _ _ b =>
      Classical.choose (exists_extDelta_eq_of_extToIdeles_eq_zero (k := k) (K := ↥K) (r := 1)
        (M := modRep (K ≃ₐ[k] K) (DualMod p (E ⊗[ZMod p] T))) (β₂ E b)
        ((hβ₂im E (β₂ E b)).mp ⟨b, rfl⟩))
  have hxB : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
      (b : Sha2 p k Ω K E),
      extDelta (k := k) (K := ↥K) (xB E b) = β₂ E b := by
    intro E _ _ _ _ _ b
    exact Classical.choose_spec (exists_extDelta_eq_of_extToIdeles_eq_zero (k := k) (K := ↥K)
      (r := 1) (M := modRep (K ≃ₐ[k] K) (DualMod p (E ⊗[ZMod p] T))) (β₂ E b)
      ((hβ₂im E (β₂ E b)).mp ⟨b, rfl⟩))
  -- the coefficients `DualMod p (E ⊗ T)` are `p`-torsion
  have hpM : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      ∀ m : DualMod p (E ⊗[ZMod p] T), p • m = 0 := by
    intro E _ _ _ _ _ m
    rw [← Nat.cast_smul_eq_nsmul (ZMod p) p m, ZMod.natCast_self, zero_smul]
  -- `β₁`'s values are locally trivial
  have hβ₁loc : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
      (a : Sha1 p k Ω K (DualMod p (E ⊗[ZMod p] T))),
      IsLocTrivial (k := k) (K := ↥K) (β₁ (DualMod p (E ⊗[ZMod p] T)) a) := by
    intro E _ _ _ _ _ a
    exact (hβ₁range (DualMod p (E ⊗[ZMod p] T)) (β₁ (DualMod p (E ⊗[ZMod p] T)) a)).mp
      ⟨a, rfl⟩
  -- the pairing value of a preimage depends on `β₂ E b` only (well-definedness of the pairing)
  have hchoice : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
      (x x' : Abelian.Ext (modRep (K ≃ₐ[k] K) (DualMod p (E ⊗[ZMod p] T))) (classesK k ↥K) 1)
      (hxx' : extDelta (k := k) (K := ↥K) x = extDelta (k := k) (K := ↥K) x')
      (a : Sha1 p k Ω K (DualMod p (E ⊗[ZMod p] T))),
      pairK (k := k) (K := ↥K) x (β₁ (DualMod p (E ⊗[ZMod p] T)) a)
        = pairK (k := k) (K := ↥K) x' (β₁ (DualMod p (E ⊗[ZMod p] T)) a) := by
    intro E _ _ _ _ _ x x' hxx' a
    have h := yonedaPair_eq_of_extDelta_eq k ↥K hxx'
      (β₁ (DualMod p (E ⊗[ZMod p] T)) a) (hβ₁loc E a)
    simpa only [pairK] using h
  -- membership in the `p`-torsion subgroup
  have hmem : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
      (x : Abelian.Ext (modRep (K ≃ₐ[k] K) (DualMod p (E ⊗[ZMod p] T))) (classesK k ↥K) 1)
      (a : Sha1 p k Ω K (DualMod p (E ⊗[ZMod p] T))),
      pairK (k := k) (K := ↥K) x (β₁ (DualMod p (E ⊗[ZMod p] T)) a) ∈ P := by
    intro E _ _ _ _ _ x a
    exact (hPmem _).mpr (nsmul_pairK p k ↥K (hpM E) x (β₁ (DualMod p (E ⊗[ZMod p] T)) a))
  -- the additive map `a ↦ χ ⟨pairK x_b (β₁ a), ·⟩`
  let Ψ : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
      (b : Sha2 p k Ω K E), Sha1 p k Ω K (DualMod p (E ⊗[ZMod p] T)) →+ ZMod p :=
    fun E _ _ _ _ _ b =>
      { toFun := fun a => χ ⟨pairK (k := k) (K := ↥K) (xB E b)
            (β₁ (DualMod p (E ⊗[ZMod p] T)) a), hmem E (xB E b) a⟩
        map_zero' := by
          have h0 : pairK (k := k) (K := ↥K) (xB E b)
              (β₁ (DualMod p (E ⊗[ZMod p] T)) 0) = 0 := by
            rw [map_zero]
            exact pairK_zero k ↥K (xB E b)
          have : (⟨pairK (k := k) (K := ↥K) (xB E b) (β₁ (DualMod p (E ⊗[ZMod p] T)) 0),
              hmem E (xB E b) 0⟩ : P) = 0 := Subtype.ext h0
          rw [this, map_zero]
        map_add' := fun a₁ a₂ => by
          have hadd : pairK (k := k) (K := ↥K) (xB E b)
              (β₁ (DualMod p (E ⊗[ZMod p] T)) (a₁ + a₂))
              = pairK (k := k) (K := ↥K) (xB E b) (β₁ (DualMod p (E ⊗[ZMod p] T)) a₁)
                + pairK (k := k) (K := ↥K) (xB E b) (β₁ (DualMod p (E ⊗[ZMod p] T)) a₂) := by
            rw [map_add]
            exact pairK_add k ↥K (xB E b) _ _
          have hsub : (⟨pairK (k := k) (K := ↥K) (xB E b)
                (β₁ (DualMod p (E ⊗[ZMod p] T)) (a₁ + a₂)), hmem E (xB E b) (a₁ + a₂)⟩ : P)
              = ⟨pairK (k := k) (K := ↥K) (xB E b) (β₁ (DualMod p (E ⊗[ZMod p] T)) a₁),
                  hmem E (xB E b) a₁⟩
                + ⟨pairK (k := k) (K := ↥K) (xB E b) (β₁ (DualMod p (E ⊗[ZMod p] T)) a₂),
                  hmem E (xB E b) a₂⟩ := Subtype.ext hadd
          rw [hsub, map_add] }
  have hΨeq : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
      (b : Sha2 p k Ω K E) (a : Sha1 p k Ω K (DualMod p (E ⊗[ZMod p] T))),
      Ψ E b a = χ ⟨pairK (k := k) (K := ↥K) (xB E b)
        (β₁ (DualMod p (E ⊗[ZMod p] T)) a), hmem E (xB E b) a⟩ := fun E _ _ _ _ _ b a => rfl
  -- `b ↦ Ψ E b`
  let Φam : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      Sha2 p k Ω K E →+ (Sha1 p k Ω K (DualMod p (E ⊗[ZMod p] T)) →ₗ[ZMod p] ZMod p) :=
    fun E _ _ _ _ _ =>
      { toFun := fun b => (Ψ E b).toZModLinearMap p
        map_zero' := by
          -- `extDelta (xB E 0) = 0 = extDelta 0`
          refine LinearMap.ext (fun a => ?_)
          simp only [AddMonoidHom.coe_toZModLinearMap, LinearMap.zero_apply]
          have hx : extDelta (k := k) (K := ↥K) (xB E 0)
              = extDelta (k := k) (K := ↥K)
                  (0 : Abelian.Ext (modRep (K ≃ₐ[k] K) (DualMod p (E ⊗[ZMod p] T)))
                    (classesK k ↥K) 1) := by
            rw [hxB E 0, map_zero, extDelta_zero k ↥K]
          have hpt := hchoice E (xB E 0) 0 hx a
          have hsub : (⟨pairK (k := k) (K := ↥K) (xB E 0)
              (β₁ (DualMod p (E ⊗[ZMod p] T)) a), hmem E (xB E 0) a⟩ : P) = 0 := by
            refine Subtype.ext ?_
            show pairK (k := k) (K := ↥K) (xB E 0) (β₁ (DualMod p (E ⊗[ZMod p] T)) a) = 0
            rw [hpt, zero_pairK k ↥K]
          rw [hΨeq E 0 a, hsub]
          exact map_zero χ
        map_add' := fun b₁ b₂ => by
          -- `xB E (b₁+b₂)` and `xB E b₁ + xB E b₂` pair alike
          refine LinearMap.ext (fun a => ?_)
          simp only [AddMonoidHom.coe_toZModLinearMap, LinearMap.add_apply]
          have hx : extDelta (k := k) (K := ↥K) (xB E (b₁ + b₂))
              = extDelta (k := k) (K := ↥K) (xB E b₁ + xB E b₂) := by
            rw [hxB E (b₁ + b₂), map_add, extDelta_add k ↥K (xB E b₁) (xB E b₂), hxB E b₁,
              hxB E b₂]
          have hpt := hchoice E (xB E (b₁ + b₂)) (xB E b₁ + xB E b₂) hx a
          have hsub : (⟨pairK (k := k) (K := ↥K) (xB E (b₁ + b₂))
                (β₁ (DualMod p (E ⊗[ZMod p] T)) a), hmem E (xB E (b₁ + b₂)) a⟩ : P)
              = ⟨pairK (k := k) (K := ↥K) (xB E b₁) (β₁ (DualMod p (E ⊗[ZMod p] T)) a),
                  hmem E (xB E b₁) a⟩
                + ⟨pairK (k := k) (K := ↥K) (xB E b₂) (β₁ (DualMod p (E ⊗[ZMod p] T)) a),
                  hmem E (xB E b₂) a⟩ := by
            refine Subtype.ext ?_
            show pairK (k := k) (K := ↥K) (xB E (b₁ + b₂))
                (β₁ (DualMod p (E ⊗[ZMod p] T)) a) = _
            rw [hpt, pairK_add_left k ↥K]
            rfl
          rw [hΨeq E (b₁ + b₂) a, hΨeq E b₁ a, hΨeq E b₂ a, hsub, map_add] }
  have hΦameq : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
      (b : Sha2 p k Ω K E) (a : Sha1 p k Ω K (DualMod p (E ⊗[ZMod p] T))),
      Φam E b a = χ ⟨pairK (k := k) (K := ↥K) (xB E b)
        (β₁ (DualMod p (E ⊗[ZMod p] T)) a), hmem E (xB E b) a⟩ :=
    fun E _ _ _ _ _ b a => hΨeq E b a
  refine ⟨fun E => (Φam E).toZModLinearMap p, ?_, ?_⟩
  · -- injectivity, from `E9`
    intro E _ _ _ _ _
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro b hb
    rw [LinearMap.mem_ker] at hb
    have hzero : ∀ a : Sha1 p k Ω K (DualMod p (E ⊗[ZMod p] T)),
        pairK (k := k) (K := ↥K) (xB E b) (β₁ (DualMod p (E ⊗[ZMod p] T)) a) = 0 := by
      intro a
      have h : χ (⟨pairK (k := k) (K := ↥K) (xB E b)
          (β₁ (DualMod p (E ⊗[ZMod p] T)) a), hmem E (xB E b) a⟩ : P) = 0 := by
        have hb' : Φam E b = 0 := hb
        rw [← hΦameq E b a, hb']
        rfl
      have h3 : (⟨pairK (k := k) (K := ↥K) (xB E b)
          (β₁ (DualMod p (E ⊗[ZMod p] T)) a), hmem E (xB E b) a⟩ : P) = 0 :=
        hχbij.injective (by rw [h, map_zero])
      exact congrArg Subtype.val h3
    have hx : ∀ h : extH (modRep (K ≃ₐ[k] K) (DualMod p (E ⊗[ZMod p] T))) 1,
        IsLocTrivial (k := k) (K := ↥K) h → pairK (k := k) (K := ↥K) (xB E b) h = 0 := by
      intro h hh
      obtain ⟨a, rfl⟩ := (hβ₁range (DualMod p (E ⊗[ZMod p] T)) h).mpr hh
      exact hzero a
    have hdel : extDelta (k := k) (K := ↥K) (xB E b) = 0 :=
      hE9 hp (DualMod p (E ⊗[ZMod p] T)) (hpM E) (xB E b) hx
    have hb2 : β₂ E b = 0 := by rw [← hxB E b]; exact hdel
    have hb0 : b = 0 := (hβ₂inj E) (by rw [hb2, map_zero])
    simpa using hb0
  · -- naturality, from `E1a` + `E1b` + associativity of `Ext.comp`
    intro E₁ _ _ _ _ _ E₂ _ _ _ _ _ f hf f' hf' hff' b
    let F : modRep (K ≃ₐ[k] K) (DualMod p (E₂ ⊗[ZMod p] T)) ⟶
            modRep (K ≃ₐ[k] K) (DualMod p (E₁ ⊗[ZMod p] T)) := modRepMap f' hf'
    have hF₁ : ∀ m : DualMod p (E₂ ⊗[ZMod p] T), F.hom m = f' m := fun m => rfl
    have hF₂ : ∀ (φ : DualMod p (E₂ ⊗[ZMod p] T)) (e : E₁) (t : T),
        (show DualMod p (E₁ ⊗[ZMod p] T) from F.hom φ) (e ⊗ₜ[ZMod p] t)
          = φ (f e ⊗ₜ[ZMod p] t) := by
      intro φ e t
      rw [modRepMap_hom]
      exact hff' φ e t
    refine LinearMap.ext (fun a => ?_)
    have hβnat := hβ₁nat (DualMod p (E₂ ⊗[ZMod p] T)) (DualMod p (E₁ ⊗[ZMod p] T))
      f' hf' F hF₁ a
    have hassoc : pairK (k := k) (K := ↥K) (xB E₁ b)
        ((β₁ (DualMod p (E₂ ⊗[ZMod p] T)) a).comp (Abelian.Ext.mk₀ F) (add_zero 1))
        = pairK (k := k) (K := ↥K)
            ((Abelian.Ext.mk₀ F).comp (xB E₁ b) (zero_add 1))
            (β₁ (DualMod p (E₂ ⊗[ZMod p] T)) a) := by
      simp only [pairK, yonedaPair]
      exact Abelian.Ext.comp_assoc (β₁ (DualMod p (E₂ ⊗[ZMod p] T)) a)
        (Abelian.Ext.mk₀ F) (xB E₁ b) (add_zero 1) (zero_add 1)
        (show 1 + 0 + 1 = 2 from rfl)
    have hdel : extDelta (k := k) (K := ↥K)
        ((Abelian.Ext.mk₀ F).comp (xB E₁ b) (zero_add 1))
        = extDelta (k := k) (K := ↥K) (xB E₂ (Sha2Map p k Ω K E₁ E₂ f hf b)) := by
      rw [extDelta_comp_mk₀ k ↥K F (xB E₁ b), hxB E₁ b,
        hxB E₂ (Sha2Map p k Ω K E₁ E₂ f hf b), hβ₂nat E₁ E₂ f hf F hF₂ b]
    have hpair : pairK (k := k) (K := ↥K)
        ((Abelian.Ext.mk₀ F).comp (xB E₁ b) (zero_add 1))
        (β₁ (DualMod p (E₂ ⊗[ZMod p] T)) a)
        = pairK (k := k) (K := ↥K) (xB E₂ (Sha2Map p k Ω K E₁ E₂ f hf b))
            (β₁ (DualMod p (E₂ ⊗[ZMod p] T)) a) := by
      have h := yonedaPair_eq_of_extDelta_eq k ↥K hdel
        (β₁ (DualMod p (E₂ ⊗[ZMod p] T)) a) (hβ₁loc E₂ a)
      simpa only [pairK] using h
    show χ (⟨pairK (k := k) (K := ↥K) (xB E₂ (Sha2Map p k Ω K E₁ E₂ f hf b))
        (β₁ (DualMod p (E₂ ⊗[ZMod p] T)) a),
        hmem E₂ (xB E₂ (Sha2Map p k Ω K E₁ E₂ f hf b)) a⟩ : P)
      = χ (⟨pairK (k := k) (K := ↥K) (xB E₁ b)
          (β₁ (DualMod p (E₁ ⊗[ZMod p] T))
            (Sha1Map p k Ω K (DualMod p (E₂ ⊗[ZMod p] T))
              (DualMod p (E₁ ⊗[ZMod p] T)) f' hf' a)),
          hmem E₁ (xB E₁ b) (Sha1Map p k Ω K (DualMod p (E₂ ⊗[ZMod p] T))
              (DualMod p (E₁ ⊗[ZMod p] T)) f' hf' a)⟩ : P)
    have hfin_eq : (⟨pairK (k := k) (K := ↥K) (xB E₁ b)
          (β₁ (DualMod p (E₁ ⊗[ZMod p] T))
            (Sha1Map p k Ω K (DualMod p (E₂ ⊗[ZMod p] T))
              (DualMod p (E₁ ⊗[ZMod p] T)) f' hf' a)),
          hmem E₁ (xB E₁ b) (Sha1Map p k Ω K (DualMod p (E₂ ⊗[ZMod p] T))
              (DualMod p (E₁ ⊗[ZMod p] T)) f' hf' a)⟩ : P)
        = ⟨pairK (k := k) (K := ↥K) (xB E₂ (Sha2Map p k Ω K E₁ E₂ f hf b))
            (β₁ (DualMod p (E₂ ⊗[ZMod p] T)) a),
          hmem E₂ (xB E₂ (Sha2Map p k Ω K E₁ E₂ f hf b)) a⟩ := by
      refine Subtype.ext ?_
      show pairK (k := k) (K := ↥K) (xB E₁ b)
          (β₁ (DualMod p (E₁ ⊗[ZMod p] T))
            (Sha1Map p k Ω K (DualMod p (E₂ ⊗[ZMod p] T))
              (DualMod p (E₁ ⊗[ZMod p] T)) f' hf' a))
        = pairK (k := k) (K := ↥K) (xB E₂ (Sha2Map p k Ω K E₁ E₂ f hf b))
            (β₁ (DualMod p (E₂ ⊗[ZMod p] T)) a)
      rw [hβnat, hassoc, hpair]
    rw [hfin_eq]

end Dvd

/-! ## `G5` from `E1a` and `E9` -/

section G5

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [Fintype (K ≃ₐ[k] K)] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)

/-- **The atom `Work.SSGRoute.tatePoitouEmbedding` (`G5`) from the two arithmetic inputs `E1a`
and `E9`.**  This is exactly the statement of `Work.SSGRoute.tatePoitouEmbedding`, so once `E1a`
and `E9` land the atom is the two-line application below.

**WARNING (2026-09-27): `E9Input` is FALSE** (see the warning on `E9Input` above), so this
reduction is *vacuous*: `hE9 : E9Input p k ↥K` cannot be discharged in the degenerate cases
(`ℽ_p`-coefficients, or `μ_p ⊆ K` false).  Use route B
(`tatePoitouEmbedding_of_poitouTate_and_card`) instead. -/
theorem tatePoitouEmbedding_of_E1a_E9
    (hE1a : E1aInput p k Ω K ζ hζ hζK T hT)
    (hE9 : E9Input p k ↥K) :
    ∃ Φ : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
            [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
          Sha2 p k Ω K E →ₗ[ZMod p]
            (Sha1 p k Ω K (DualMod p (E ⊗[ZMod p] T)) →ₗ[ZMod p] ZMod p),
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        Function.Injective (Φ E)) ∧
      (∀ (E₁ : Type) [AddCommGroup E₁] [Module (ZMod p) E₁] [DistribMulAction (K ≃ₐ[k] K) E₁]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₁] [Finite E₁]
          (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
          (f : E₁ →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E₁), f (g • e) = g • f e)
          (f' : DualMod p (E₂ ⊗[ZMod p] T) →ₗ[ZMod p] DualMod p (E₁ ⊗[ZMod p] T))
          (hf' : ∀ (g : K ≃ₐ[k] K) (φ : DualMod p (E₂ ⊗[ZMod p] T)), f' (g • φ) = g • f' φ)
          (hff' : ∀ (φ : DualMod p (E₂ ⊗[ZMod p] T)) (e : E₁) (t : T),
            f' φ (e ⊗ₜ[ZMod p] t) = φ (f e ⊗ₜ[ZMod p] t))
          (b : Sha2 p k Ω K E₁),
          Φ E₂ (Sha2Map p k Ω K E₁ E₂ f hf b)
            = (Φ E₁ b).comp
                (Sha1Map p k Ω K (DualMod p (E₂ ⊗[ZMod p] T))
                  (DualMod p (E₁ ⊗[ZMod p] T)) f' hf')) := by
  by_cases hp : p ∣ Module.finrank k K
  · exact exists_Phi_of_dvd (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ)
      (hζK := hζK) (T := T) (hT := hT) (hE1a := hE1a) (hE9 := hE9) (hp := hp)
  · exact exists_Phi_of_not_dvd (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ)
      (hζK := hζK) (T := T) (hp := hp)

end G5

end Work.SSGRoute.PTdualControl
