import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Submission.Work.SSGRoute.ExtChain.FreeCover
import Submission.Work.SSGRoute.PT.e1a_coeff_iso_natural
import Submission.Work.SSGRoute.PT.e1a_shift
import Submission.Work.SSGRoute.PT.pt_extSegment_exact
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The canonical `Ext`-side chain of E1a, at the level `Γ = Gal(Ω/k)`

For the node `Work.SSGRoute.ext_sha2_bridge` (E1a) the `Ext`-side dictionary has to be a *single*
construction, uniform in the coefficient `E` (the naturality clause of the target compares the
dictionaries of `E₁` and `E₂`).  Every earlier statement of the workspace obtains the free cover of
`E' = DualMod p (E ⊗ T)` by `Classical.choose`, which makes such a comparison impossible.

This module builds the chain from the *canonical* cover `freeCover` of `ExtChain/FreeCover.lean`:

`Ext²_G(E', Kˣ) --(syzygy shift)⁻¹--> Ext¹_G(R, Kˣ) --(E1c)--> H¹(Γ, Hom_ℤ(R, Ωˣ))`
`  --δ--> H²(Γ, Hom_ℤ(E', Ωˣ)) --(coefficient iso)--> H²(Γ, E)`

with `R = kernel (freeCover E')` and `G = Gal(K/k)`.

* `homCoindFreeT` — a `@[reducible]` wrapper for the free coefficient
  `Hom_ℤ(ℤ[G]^ι, Ωˣ)` of the middle term of the dualised resolution, with its two instances
  (instance search for the cohomology quotients of the `Rep.free`-based coefficient diverges, cf.
  `PT/e1a_chain.lean`).
* `e1aSyzMap`, `e1aSyzMap_bijective`, `e1aSyzShift` — the *explicit* syzygy shift
  `x ↦ x.comp (extClass)` for the canonical cover, with its bijectivity (so that the equivalence is
  the canonical one, not a `Classical.choose`d witness of `Nonempty`).
* `e1aE1c` — the `E1c` dictionary `Ext¹_G(R, Kˣ) ≃+ H¹(Γ, Hom_ℤ(R, Ωˣ))`.
* `e1aSES`, `e1aDelta` — the dualised canonical resolution and its connecting map
  `δ = S.deltaH2`, whose kernel is the range of `mapH1 S.pi`.
* `e1aChainHom` — the assembled `Hom`-side chain `Ext²_G(E', Kˣ) →+ H²(Γ, Hom_ℤ(E', Ωˣ))`, and
  `e1aChainHom_injective`.
-/

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 10000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute.ExtChain

noncomputable section

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [NumberField K]

/- The syzygy of the canonical cover of a finite representation is a finitely generated
`ℤ`-module; registered as a local instance so that `e1aE1c` can be applied to it. -/
attribute [local instance] Work.SSGRoute.freeCoverSES_finite

/-! ## The wrapper for the free coefficient -/

/-- `Hom_ℤ(ℤ[G]^ι, Ωˣ)`, wrapped in a `@[reducible] def` so that instance search for the
cohomology quotients `H¹`, `H²` of this coefficient terminates on the head symbol `homCoindFreeT`
(cf. `homCoindFree` of `PT/e1a_chain.lean`). -/
@[reducible] def homCoindFreeT (k : Type) [Field k] [CharZero k] (Ω : Type) [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ι : Type) : Type :=
  Work.SSGRoute.homCoind k Ω K (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι)

noncomputable instance instAddCommGroupHomCoindFreeT (k : Type) [Field k] [CharZero k]
    (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (ι : Type) : AddCommGroup (homCoindFreeT k Ω K ι) :=
  Work.SSGRoute.homCoind.instAddCommGroup _

noncomputable instance instDistribMulActionHomCoindFreeT (k : Type) [Field k] [CharZero k]
    (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (ι : Type) :
    DistribMulAction (Ω ≃ₐ[k] Ω) (homCoindFreeT k Ω K ι) :=
  Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv _

/-! ## The `E1c` dictionary and the explicit syzygy shift -/

/-- **The `E1c` dictionary**: for a `ℤ`-finitely-generated `G`-module `R`,
`Ext¹_G(R, Kˣ) ≃+ H¹(Γ, Hom_ℤ(R, Ωˣ))`. -/
noncomputable def e1aE1c (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V] :
    Abelian.Ext.{0} R (unitsK k K) 1 ≃+
      Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R) :=
  Classical.choice (Work.SSGRoute.PT.ext_one_homCoind_iso k Ω K R)

/-- **The syzygy shift map, explicitly**: `x ↦ x.comp (S.extClass)`.  For a short exact sequence
`0 → X₁ → X₂ → X₃ → 0` with `X₂` projective and `1 ≤ n`, this is a bijection
`Extⁿ(X₁,Y) → Ext^{n+1}(X₃,Y)` (the proof of `ext_shift_of_projective_presentation`, made explicit
so that the map — and hence its naturality — is available). -/
theorem extClass_precomp_bijective {C : Type*} [Category C] [Abelian C] [HasExt C]
    (S : ShortComplex C) (hS : S.ShortExact) [Projective S.X₂]
    (Y : C) (n : ℕ) (hn1 : 1 ≤ n) :
    Function.Bijective (hS.extClass.precomp Y (Nat.one_add n)) := by
  haveI hsub : Subsingleton (Abelian.Ext S.X₂ Y n) := by
    have h := Abelian.Ext.subsingleton_of_projective S.X₂ Y (n - 1)
    rwa [Nat.sub_add_cancel hn1] at h
  haveI hsub' : Subsingleton (Abelian.Ext S.X₂ Y (n + 1)) :=
    Abelian.Ext.subsingleton_of_projective S.X₂ Y n
  have hker : ∀ z : Abelian.Ext S.X₁ Y n,
      hS.extClass.precomp Y (Nat.one_add n) z = 0 → z = 0 := by
    intro z hz
    obtain ⟨x₂, hx₂⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS Y z (Nat.one_add n) hz
    have h0 : (Abelian.Ext.mk₀ S.f).comp (0 : Abelian.Ext S.X₂ Y n) (zero_add n) = 0 :=
      Abelian.Ext.comp_zero (Abelian.Ext.mk₀ S.f) Y n n (zero_add n)
    have hx2' : (Abelian.Ext.mk₀ S.f).comp x₂ (zero_add n) = 0 := by
      rw [Subsingleton.elim x₂ 0]; exact h0
    rw [hx2'] at hx₂
    exact hx₂.symm
  refine ⟨?_, ?_⟩
  · intro x y hxy
    exact sub_eq_zero.mp (hker (x - y) (by rw [map_sub, hxy, sub_self]))
  · intro y
    have hy : (Abelian.Ext.mk₀ S.g).comp y (zero_add (n + 1)) = 0 := Subsingleton.elim _ _
    obtain ⟨x, hx⟩ := Abelian.Ext.contravariant_sequence_exact₃ hS Y y hy (Nat.one_add n)
    exact ⟨x, hx⟩

/-- **The canonical syzygy shift**: `Ext¹_G(R, Kˣ) ≃+ Ext²_G(E', Kˣ)` for the canonical syzygy
`R = kernel (freeCover E')`.  It is Mathlib's connecting map `S.extClass` of the canonical
presentation, so it is compatible with morphisms of short complexes
(`Work.SSGRoute.PT.e1aShiftEquiv_natural`). -/
noncomputable def e1aSyzShift (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) :
    Abelian.Ext.{0} (Limits.kernel (freeCover N)) (unitsK k K) 1 ≃+
      Abelian.Ext.{0} N (unitsK k K) 2 :=
  Work.SSGRoute.PT.e1aShiftEquiv (freeCoverSES N) (freeCoverSES_shortExact N)
    (unitsK k K) 1 (le_refl 1)

/-- The syzygy shift as an additive map (the same function as `e1aSyzShift`, packaged so that
its computation rule stays cheap to unfold). -/
noncomputable def e1aSyzMap (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) :
    Abelian.Ext.{0} (Limits.kernel (freeCover N)) (unitsK k K) 1 →+
      Abelian.Ext.{0} N (unitsK k K) 2 :=
  AddMonoidHom.mk' (fun x => e1aSyzShift (k := k) (K := K) N x)
    (fun a b => map_add (e1aSyzShift (k := k) (K := K) N) a b)

/-- **Naturality of the canonical syzygy shift in the first variable.**  For `F : N₂ ⟶ N₁`, the
comparison of the canonical presentations (`freeMapKernel F`, `freeMap F`, `F`) makes the shift
maps commute:
`e1aSyzMap N₂ ((mk₀ (freeMapKernel F)).comp z) = (mk₀ F).comp (e1aSyzMap N₁ z)`. -/
theorem syzShift_natural (N₁ N₂ : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (F : N₂ ⟶ N₁)
    (z : Abelian.Ext.{0} (Limits.kernel (freeCover N₁)) (unitsK k K) 1) :
    e1aSyzMap (k := k) (Ω := Ω) (K := K) N₂
        ((Abelian.Ext.mk₀ (Work.SSGRoute.freeMapKernel F)).comp z (zero_add 1)) =
      (Abelian.Ext.mk₀ F).comp
        (e1aSyzMap (k := k) (Ω := Ω) (K := K) N₁ z) (zero_add 2) := by
  haveI : CategoryTheory.Projective (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) N₁.V) :=
    Rep.free_projective (k := SSGRoute.PTExt.Coeff) (G := K ≃ₐ[k] K) (α := N₁.V)
  haveI : CategoryTheory.Projective (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) N₂.V) :=
    Rep.free_projective (k := SSGRoute.PTExt.Coeff) (G := K ≃ₐ[k] K) (α := N₂.V)
  show Work.SSGRoute.PT.e1aShiftEquiv (freeCoverSES N₂) (freeCoverSES_shortExact N₂)
        (unitsK k K) 1 (le_refl 1)
        ((Abelian.Ext.mk₀ (Work.SSGRoute.freeMapKernel F)).comp z (zero_add 1)) =
      (Abelian.Ext.mk₀ F).comp
        (Work.SSGRoute.PT.e1aShiftEquiv (freeCoverSES N₁) (freeCoverSES_shortExact N₁)
          (unitsK k K) 1 (le_refl 1) z) (zero_add 2)
  exact Work.SSGRoute.PT.e1aShiftEquiv_natural
    (freeCoverSES_shortExact N₂) (freeCoverSES_shortExact N₁)
    (ShortComplex.homMk (Work.SSGRoute.freeMapKernel F) (Work.SSGRoute.freeMap F) F
      (Work.SSGRoute.freeMapKernel_ι F) (Work.SSGRoute.freeMap_freeCover F))
    (unitsK k K) 1 (le_refl 1) z

/-! ## The dualised canonical resolution and its connecting map -/

/-- **The dualised resolution of the canonical cover** `0 → R → F → E' → 0`: applying `Hom_ℤ(-,Ωˣ)`
(exact because `Ωˣ` is divisible) gives
`0 → Hom(E',Ωˣ) → Hom(F,Ωˣ) → Hom(R,Ωˣ) → 0`.  The middle coefficient is written with the
wrapper `homCoindFreeT` so that its cohomology quotients are well-behaved. -/
noncomputable def e1aSES (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V] :
    Work.AbsoluteKummer.ShortExactSeq (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.homCoind k Ω K N)
      (homCoindFreeT k Ω K N.V)
      (Work.SSGRoute.homCoind k Ω K (Limits.kernel (freeCover N))) :=
  Classical.choose (Work.SSGRoute.PT.homCoind_SES (k := k) (Ω := Ω) (K := K) (ι := N.V)
    (freeCover N) (freeCover_surjective N))

/-- **The connecting map `δ` of the dualised canonical resolution**,
`δ : H¹(Γ, Hom_ℤ(R,Ωˣ)) →+ H²(Γ, Hom_ℤ(E',Ωˣ))`.  It is `S.deltaH2`, i.e. *the* connecting map of
the short exact sequence `S` (not a `Classical.choose`d witness). -/
noncomputable def e1aDelta (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V] :
    Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω)
        (Work.SSGRoute.homCoind k Ω K (Limits.kernel (freeCover N))) →+
      Work.AbsoluteKummer.H2 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K N) :=
  (e1aSES N).deltaH2

/-- The kernel of `e1aDelta` is the range of `mapH1 S.pi`, i.e. `H¹(Γ, Hom_ℤ(F,Ωˣ))` (Shapiro +
Hilbert 90). -/
theorem e1aDelta_ker_eq_range_mapH1 (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V] :
    (e1aDelta (k := k) (Ω := Ω) (K := K) N).ker =
      (Work.AbsoluteKummer.mapH1 (e1aSES N).pi (e1aSES N).pi_equivariant).range :=
  (Work.AbsoluteKummer.SES.range_mapH1_eq_ker_deltaH2 (e1aSES N)).symm

/-- `e1aDelta` is injective: its kernel is the range of `mapH1 S.pi`, whose source is
`H¹(Γ, Hom_ℤ(F,Ωˣ)) = 0` (Shapiro + Hilbert 90). -/
theorem e1aDelta_injective (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V] :
    Function.Injective (e1aDelta (k := k) (Ω := Ω) (K := K) N) := by
  haveI hsub : Subsingleton
      (Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (homCoindFreeT k Ω K N.V)) :=
    Work.SSGRoute.homCoind_H1_free_conj_v2 (k := k) (Ω := Ω) (K := K) (ι := N.V)
  intro x y hxy
  have hmem : x - y ∈ (e1aDelta (k := k) (Ω := Ω) (K := K) N).ker := by
    rw [AddMonoidHom.mem_ker, map_sub, hxy, sub_self]
  rw [e1aDelta_ker_eq_range_mapH1] at hmem
  obtain ⟨z, hz⟩ := hmem
  have hz0 : z = 0 := Subsingleton.elim z 0
  rw [hz0, map_zero] at hz
  exact sub_eq_zero.mp hz.symm

/-! ## The assembled `Hom`-side chain -/

/-- **The `Hom`-side chain** `Ext²_G(E', Kˣ) →+ H²(Γ, Hom_ℤ(E', Ωˣ))`, the composite of the
canonical syzygy shift, the `E1c` dictionary and the connecting map `δ`. -/
noncomputable def e1aChainHom (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V] :
    Abelian.Ext.{0} N (unitsK k K) 2 →+
      Work.AbsoluteKummer.H2 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K N) := by
  exact (e1aDelta (k := k) (Ω := Ω) (K := K) N).comp
    ((e1aE1c (k := k) (Ω := Ω) (K := K) (Limits.kernel (freeCover N))).toAddMonoidHom.comp
      (e1aSyzShift (k := k) (K := K) N).symm.toAddMonoidHom)

theorem e1aChainHom_apply (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V]
    (x : Abelian.Ext.{0} N (unitsK k K) 2) :
    e1aChainHom (k := k) (Ω := Ω) (K := K) N x =
      e1aDelta (k := k) (Ω := Ω) (K := K) N
        (e1aE1c (k := k) (Ω := Ω) (K := K) (Limits.kernel (freeCover N))
          ((e1aSyzShift (k := k) (K := K) N).symm x)) := rfl

/-- The `Hom`-side chain is injective (all three factors are). -/
theorem e1aChainHom_injective (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V] :
    Function.Injective (e1aChainHom (k := k) (Ω := Ω) (K := K) N) := by
  intro x y hxy
  rw [e1aChainHom_apply, e1aChainHom_apply] at hxy
  have h1 := e1aDelta_injective (k := k) (Ω := Ω) (K := K) N hxy
  have h2 := (e1aE1c (k := k) (Ω := Ω) (K := K)
    (Limits.kernel (freeCover N))).injective h1
  exact (e1aSyzShift (k := k) (K := K) N).symm.injective h2


end

end Work.SSGRoute.ExtChain

/-! ## The coefficient identification and the full chain

This part is written with fully explicit binder lists (no section variables), so that the argument
order of every declaration is the one written down. -/

namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 10000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

/-- The coefficient identification `E ≃+ Hom_ℤ(E',Ωˣ)` (`E' = DualMod p (E ⊗ T)`), chosen *once*
from the natural family of `PT/e1a_coeff_iso_natural`. -/
noncomputable def e1aCoeffNat (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) :
    ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      E ≃+ Work.SSGRoute.homCoind k Ω K
        (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) :=
  Classical.choose (Work.SSGRoute.PT.e1a_coeff_iso_natural p k Ω K ζ hζ hζK T hT)

/-- The equivariance of `e1aCoeffNat`. -/
theorem e1aCoeffNat_equivariant (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (σ : Ω ≃ₐ[k] Ω) (e : E) :
    e1aCoeffNat p k Ω K ζ hζ hζK T hT E ((SSGRoute.res k K σ) • e)
      = σ • e1aCoeffNat p k Ω K ζ hζ hζK T hT E e :=
  (Classical.choose_spec
    (Work.SSGRoute.PT.e1a_coeff_iso_natural p k Ω K ζ hζ hζK T hT)).1 E σ e

/-- The equivariance of the *inverse* of `e1aCoeffNat`, in elementwise form (the action of
`Γ` on `E` is the pullback along `res k K`, so the statement is phrased with `(res k K σ) • ·`). -/
theorem e1aCoeffNat_symm_equivariant (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ K) (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (σ : Ω ≃ₐ[k] Ω)
    (n : Work.SSGRoute.homCoind k Ω K
      (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))) :
    (e1aCoeffNat p k Ω K ζ hζ hζK T hT E).symm (σ • n)
      = (SSGRoute.res k K σ) • (e1aCoeffNat p k Ω K ζ hζ hζK T hT E).symm n := by
  apply (e1aCoeffNat p k Ω K ζ hζ hζK T hT E).injective
  rw [AddEquiv.apply_symm_apply]
  rw [e1aCoeffNat_equivariant p k Ω K ζ hζ hζK T hT E σ
        ((e1aCoeffNat p k Ω K ζ hζ hζK T hT E).symm n)]
  rw [AddEquiv.apply_symm_apply]

/-- `T` is finite (it is a line over `𝔽_p`). -/
theorem e1aFiniteT (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharZero k] (Ω : Type) [Field Ω]
    [Algebra k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] (ζ : Ω)
    (T : Type) [AddCommGroup T]
    [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) : Finite T := by
  haveI : Module.Finite (ZMod p) T :=
    Module.finite_of_finrank_pos (by rw [hT.1]; norm_num)
  let u : T ≃ₗ[ZMod p] ZMod p := LinearEquiv.ofFinrankEq (R := ZMod p) T (ZMod p)
    (by rw [hT.1, Module.finrank_self])
  exact Finite.of_injective u u.injective

/-- **The coefficient map on `H²`**: `H²(Γ, Hom_ℤ(E',Ωˣ)) →+ H²(Γ,E)`, `mapH2` of the inverse of
the canonical coefficient identification. -/
noncomputable def e1aCoeffH2 (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] :
    Work.AbsoluteKummer.H2 (Ω ≃ₐ[k] Ω)
        (Work.SSGRoute.homCoind k Ω K
          (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))) →+
      @Work.AbsoluteKummer.H2 (Ω ≃ₐ[k] Ω) E _ _ _
        (DistribMulAction.compHom E (SSGRoute.res k K)) := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  exact Work.AbsoluteKummer.mapH2
    (e1aCoeffNat p k Ω K ζ hζ hζK T hT E).symm.toAddMonoidHom
    (fun σ n => e1aCoeffNat_symm_equivariant p k Ω K ζ hζ hζK T hT E σ n)

/-- `e1aCoeffH2` is injective: it is `mapH2` of an isomorphism. -/
theorem e1aCoeffH2_injective (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] :
    Function.Injective (e1aCoeffH2 p k Ω K ζ hζ hζK T hT E) := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  have hφ' : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω)
      ((e1aCoeffNat p k Ω K ζ hζ hζK T hT E).symm.toAddMonoidHom) :=
    fun σ n => e1aCoeffNat_symm_equivariant p k Ω K ζ hζ hζK T hT E σ n
  have hφ : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω)
      ((e1aCoeffNat p k Ω K ζ hζ hζK T hT E).toAddMonoidHom) :=
    fun σ e => e1aCoeffNat_equivariant p k Ω K ζ hζ hζK T hT E σ e
  exact Work.SSGRoute.sha2_coeff.mapH2_injective_of_addEquiv
    (φ := (e1aCoeffNat p k Ω K ζ hζ hζK T hT E).symm) hφ' hφ

/-- **The full canonical chain** `Ext²_G(E', Kˣ) →+ H²(Γ,E)`, `E' = DualMod p (E ⊗ T)`: the
`Hom`-side chain composed with the coefficient identification. -/
noncomputable def e1aChain (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] :
    Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
        (SSGRoute.PTExt.unitsK k K) 2 →+
      @Work.AbsoluteKummer.H2 (Ω ≃ₐ[k] Ω) E _ _ _
        (DistribMulAction.compHom E (SSGRoute.res k K)) := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  haveI : Finite T := e1aFiniteT p k Ω K ζ T hT
  haveI : Finite (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))).V :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  exact (e1aCoeffH2 p k Ω K ζ hζ hζK T hT E).comp
    (e1aChainHom (k := k) (Ω := Ω) (K := K)
      (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))

/-- The full chain is injective. -/
theorem e1aChain_injective (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] :
    Function.Injective (e1aChain p k Ω K ζ hζ hζK T hT E) := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  haveI : Finite T := e1aFiniteT p k Ω K ζ T hT
  haveI : Finite (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))).V :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  exact (e1aCoeffH2_injective p k Ω K ζ hζ hζK T hT E).comp
    (e1aChainHom_injective (k := k) (Ω := Ω) (K := K)
      (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))

end

end Work.SSGRoute.ExtChain
