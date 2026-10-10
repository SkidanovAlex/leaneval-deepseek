import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Submission.Work.SSGRoute.ExtChain.ChainGamma
import Submission.Work.SSGRoute.PT.e1a_coverSES
import Submission.Work.SSGRoute.PT.e1a_deltaH1_natural
import Submission.Work.SSGRoute.PT.e1a_toCoindH0_natural
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# E1a: the naturality squares of the `E1c` dictionary

The dictionary `Ext¹_G(X,Kˣ) ≅ H¹(Γ, Hom_ℤ(X,Ωˣ))` of `Work.SSGRoute.PT.ext_one_homCoind_iso` is
proved by resolving `X` by a `Classical.choose`d free cover; the naturality clause of
`Work.SSGRoute.PT.e1a_ext_sha2_bridge` needs the *canonical* presentation `freeCoverSES X`, and
every map in the proof must be natural in `X`.  This file records those squares:

* `e1aE1c_step_ext` — the Ext-side map `ΦE = (freeCoverSES X).extClass.precomp (unitsK k K) …`
  (from the degree-zero case `extClass_precomp_natural_zero` of the `extClass` naturality);
* `e1aE1c_step_coeff` — the coefficient identification `Ext⁰_G(M,Kˣ) ≅ H⁰(Γ, Hom_ℤ(M,Ωˣ))` given by
  `Abelian.Ext.addEquiv₀` followed by the *canonical* `Work.SSGRoute.toCoindH0`
  (from `toCoindH0_natural`);
* `precompAddHom_comp` — precomposition by a composite, used to compare the canonical resolutions.

The δ-side square (naturality of the connecting map of the canonical dualised resolution) is
`e1a_deltaH1_natural` together with the commuting squares of the comparison morphisms; it is
assembled in the file that constructs the dictionary.
-/

open CategoryTheory SSGRoute.PTExt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.style.haveILetI false

namespace Work.SSGRoute.PT

noncomputable section

section Steps

variable {G : Type} [Group G] [Fintype G]

/-- **The Ext-side square of `E1c`**: the connecting map `ΦE = extClass.precomp` of the canonical
presentation is natural. -/
theorem e1aE1c_step_ext (Y : Rep.{0} SSGRoute.PTExt.Coeff G)
    (X₁ X₂ : Rep.{0} SSGRoute.PTExt.Coeff G) (h : X₁ ⟶ X₂)
    (x : CategoryTheory.Abelian.Ext (Work.SSGRoute.freeCoverSES X₂).X₁ Y 0) :
    ((Work.SSGRoute.freeCoverSES_shortExact X₁).extClass.precomp Y (by norm_num : 1 + 0 = 1))
        ((CategoryTheory.Abelian.Ext.mk₀ (Work.SSGRoute.freeMapKernel h)).comp x (zero_add 0)) =
      (CategoryTheory.Abelian.Ext.mk₀ h).comp
        (((Work.SSGRoute.freeCoverSES_shortExact X₂).extClass.precomp Y
          (by norm_num : 1 + 0 = 1)) x) (zero_add 1) :=
  extClass_precomp_natural_zero (Work.SSGRoute.freeCoverSES_shortExact X₁)
    (Work.SSGRoute.freeCoverSES_shortExact X₂) (Work.SSGRoute.freeCoverSESMap h) Y x

end Steps

section CoeffStep

variable {k : Type} [Field k] [CharZero k] [NumberField k]
variable {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField K]

/-- Precomposition by a composite: `precompAddHom (g ∘ f) = precompAddHom f ∘ precompAddHom g`. -/
theorem precompAddHom_comp {A B C D : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup D] (f : A →+ B) (g : B →+ C) :
    (Work.SSGRoute.precompAddHom (g.comp f) : (C →+ D) →+ (A →+ D)) =
      (Work.SSGRoute.precompAddHom f).comp (Work.SSGRoute.precompAddHom g) := by
  ext h x
  rfl

/-- **The coefficient square of `E1c`**, in the canonical form: the identification
`Ext⁰_G(M,Kˣ) ≅ H⁰(Γ, Hom_ℤ(M,Ωˣ))` given by `Abelian.Ext.addEquiv₀` followed by the canonical
`toCoindH0` is natural in the first variable. -/
theorem e1aE1c_step_coeff (M N : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) (u : M ⟶ N)
    (h : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.precompAddHom (Rep.Hom.hom u).toAddMonoidHom))
    (x : CategoryTheory.Abelian.Ext N (SSGRoute.PTExt.unitsK k K) 0) :
    Work.SSGRoute.toCoindH0 M
        (Abelian.Ext.addEquiv₀
          ((Abelian.Ext.mk₀ u).precomp (SSGRoute.PTExt.unitsK k K)
            (by norm_num : 0 + 0 = 0) x)) =
      Work.GroupCohomology.mapH0 (Ω ≃ₐ[k] Ω)
        (Work.SSGRoute.precompAddHom (Rep.Hom.hom u).toAddMonoidHom) h
        (Work.SSGRoute.toCoindH0 N (Abelian.Ext.addEquiv₀ x)) := by
  rw [show x = Abelian.Ext.mk₀ (Abelian.Ext.addEquiv₀ x) from
    (Abelian.Ext.mk₀_addEquiv₀_apply x).symm]
  rw [ext_precomp_mk₀, ext_addEquiv₀_mk₀_ehb, ext_addEquiv₀_mk₀_ehb]
  exact Work.SSGRoute.PT.toCoindH0_natural k Ω K M N u h (Abelian.Ext.addEquiv₀ x)

/-- The conjugation action of `Γ` on `Hom_ℤ(M,Ωˣ)` is compatible with precomposition: for a
morphism `u : M ⟶ N` of `Gal(K/k)`-modules, `precompAddHom u` is `Γ`-equivariant. -/
theorem precompAddHom_isEquivariant {M N : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)} (u : M ⟶ N) :
    Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.precompAddHom (Rep.Hom.hom u).toAddMonoidHom :
        Work.SSGRoute.homCoind k Ω K N →+ Work.SSGRoute.homCoind k Ω K M) := by
  intro σ ψ
  apply AddMonoidHom.ext
  intro v
  rw [Work.SSGRoute.precompAddHom_apply, AddMonoidHom.comp_apply]
  simp only [Work.SSGRoute.homCoind.smul_apply]
  rw [Work.SSGRoute.precompAddHom_apply, AddMonoidHom.comp_apply]
  congr 1
  exact congrArg ψ (Rep.hom_comm_apply u ((SSGRoute.res k K) σ)⁻¹ v).symm

/-- The `iota` of the canonical dualised resolution `ExtChain.e1aSES` is the precomposition by the
canonical cover. -/
theorem e1aSES_iota (X : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite X.V] :
    (Work.SSGRoute.ExtChain.e1aSES (k := k) (Ω := Ω) (K := K) X).iota =
      Work.SSGRoute.precompAddHom
        (Rep.Hom.hom (Work.SSGRoute.freeCover X)).toAddMonoidHom :=
  (Classical.choose_spec (Work.SSGRoute.PT.homCoind_SES (k := k) (Ω := Ω) (K := K)
    (ι := X.V) (Work.SSGRoute.freeCover X)
    (Work.SSGRoute.freeCover_surjective X))).1

/-- The `pi` of the canonical dualised resolution `ExtChain.e1aSES` is the precomposition by the
kernel inclusion. -/
theorem e1aSES_pi (X : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite X.V] :
    (Work.SSGRoute.ExtChain.e1aSES (k := k) (Ω := Ω) (K := K) X).pi =
      Work.SSGRoute.precompAddHom
        (Rep.Hom.hom (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover X))).toAddMonoidHom :=
  (Classical.choose_spec (Work.SSGRoute.PT.homCoind_SES (k := k) (Ω := Ω) (K := K)
    (ι := X.V) (Work.SSGRoute.freeCover X)
    (Work.SSGRoute.freeCover_surjective X))).2

/-- **The δ-side square of `E1c`**: the connecting map of the canonical dualised resolution is
natural in the first variable. -/
theorem e1aE1c_step_delta (X₁ X₂ : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite X₁.V]
    [Finite X₂.V] (h : X₁ ⟶ X₂)
    (y : Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.homCoind k Ω K (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover X₂)))) :
    (Work.SSGRoute.ExtChain.e1aSES (k := k) (Ω := Ω) (K := K) X₁).delta
        (Work.GroupCohomology.mapH0 (Ω ≃ₐ[k] Ω)
          (Work.SSGRoute.precompAddHom
            (Rep.Hom.hom (Work.SSGRoute.freeMapKernel h)).toAddMonoidHom)
          (precompAddHom_isEquivariant (k := k) (Ω := Ω) (K := K) (Work.SSGRoute.freeMapKernel h))
          y) =
      Work.AbsoluteKummer.mapH1
        (Work.SSGRoute.precompAddHom (Rep.Hom.hom h).toAddMonoidHom)
        (precompAddHom_isEquivariant (k := k) (Ω := Ω) (K := K) h)
        ((Work.SSGRoute.ExtChain.e1aSES (k := k) (Ω := Ω) (K := K) X₂).delta y) := by
  refine e1a_deltaH1_natural
    (Work.SSGRoute.ExtChain.e1aSES (k := k) (Ω := Ω) (K := K) X₂)
    (Work.SSGRoute.ExtChain.e1aSES (k := k) (Ω := Ω) (K := K) X₁)
    (Work.SSGRoute.precompAddHom (Rep.Hom.hom h).toAddMonoidHom)
    (Work.SSGRoute.precompAddHom (Rep.Hom.hom (Work.SSGRoute.freeMap h)).toAddMonoidHom)
    (Work.SSGRoute.precompAddHom
      (Rep.Hom.hom (Work.SSGRoute.freeMapKernel h)).toAddMonoidHom)
    (precompAddHom_isEquivariant (k := k) (Ω := Ω) (K := K) h)
    (precompAddHom_isEquivariant (k := k) (Ω := Ω) (K := K) (Work.SSGRoute.freeMap h))
    (precompAddHom_isEquivariant (k := k) (Ω := Ω) (K := K) (Work.SSGRoute.freeMapKernel h))
    ?_ ?_ y
  · -- the left square, from `freeMap_freeCover`
    intro m
    rw [e1aSES_iota X₂, e1aSES_iota X₁]
    simp only [Work.SSGRoute.precompAddHom_apply, AddMonoidHom.comp_apply]
    apply AddMonoidHom.ext
    intro v
    exact congrArg m (congrArg (fun (φ : (Work.SSGRoute.freeCoverSES X₁).X₂ ⟶ X₂) =>
      (Rep.Hom.hom φ) v) (Work.SSGRoute.freeMap_freeCover h))
  · -- the right square, from `freeMapKernel_ι`
    intro n
    rw [e1aSES_pi X₂, e1aSES_pi X₁]
    simp only [Work.SSGRoute.precompAddHom_apply, AddMonoidHom.comp_apply]
    apply AddMonoidHom.ext
    intro v
    exact congrArg n (congrArg (fun (φ : (Work.SSGRoute.freeCoverSES X₁).X₁ ⟶
      (Work.SSGRoute.freeCoverSES X₂).X₂) => (Rep.Hom.hom φ) v)
      (Work.SSGRoute.freeMapKernel_ι h))

end CoeffStep

end

end Work.SSGRoute.PT
