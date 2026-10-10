import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.PT.archLevelPair_decomposition
import Submission.Work.SSGRoute.PT.levelTransport_injective_of_components
import Submission.Work.SSGRoute.PT.localUnitsMap_injective
import Submission.Work.SSGRoute.PT.localUnitsMap_invariants
import Submission.Work.SSGRoute.PT.localUnitsMap_retraction_of_ne_bot
import Submission.Work.SSGRoute.PT.pushClass_transport_vanishing
import Submission.Work.SSGRoute.PT.vfShared
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module
set_option backward.isDefEq.respectTransparency false

/-- Composing with `mk₀` of an isomorphism of coefficient modules is injective: `u ≫ mk₀ θ = 0`
forces `u = 0`.  (Local copy of `Work.SSGRoute.E7bFin.ext_eq_zero_of_comp_mk₀_iso`.) -/
lemma ext_eq_zero_of_comp_mk₀_iso' {G : Type} [Group G] {M M' X : Rep.{0} Coeff G} {n : ℕ}
    (θ : M ≅ M') (u : CategoryTheory.Abelian.Ext.{0} X M n)
    (h : u.comp (CategoryTheory.Abelian.Ext.mk₀ θ.hom) (add_zero n) = 0) : u = 0 := by
  have h2 : (u.comp (CategoryTheory.Abelian.Ext.mk₀ θ.hom) (add_zero n)).comp
      (CategoryTheory.Abelian.Ext.mk₀ θ.inv) (add_zero n) = 0 := by rw [h]; simp
  simpa only [CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero,
    CategoryTheory.Abelian.Ext.mk₀_comp_mk₀, θ.hom_inv_id,
    CategoryTheory.Abelian.Ext.comp_mk₀_id] using h2

/-- Composing with `mk₀ ι` is injective as soon as `ι` has a retraction `ρ` (`ι ≫ ρ = 𝟙`). -/
lemma comp_mk₀_injective_of_retraction {G : Type} [Group G] (X : Rep.{0} Coeff G)
    {A B : Rep.{0} Coeff G}
    (ι : A ⟶ B) (ρ : B ⟶ A) (hρι : ι ≫ ρ = 𝟙 A) :
    ∀ u : CategoryTheory.Abelian.Ext X A 1,
      u.comp (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1) = 0 → u = 0 := by
  intro u hu
  have h2 : (u.comp (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1)).comp
      (CategoryTheory.Abelian.Ext.mk₀ ρ) (add_zero 1) = 0 := by rw [hu]; simp
  have h3 : u.comp (CategoryTheory.Abelian.Ext.mk₀ (𝟙 A)) (add_zero 1) = 0 := by
    rwa [CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero,
      CategoryTheory.Abelian.Ext.mk₀_comp_mk₀, hρι] at h2
  simpa only [CategoryTheory.Abelian.Ext.comp_mk₀_id] using h3

/-- **The level transport is injective when the group map is an isomorphism and the coefficient map
has a retraction.**  For `f : H →* G` bijective and `ρ : B ⟶ Rep.res f A` with `ι ≫ ρ = 𝟙`, the map
`x ↦ (extRes f x) ∘ mk₀ ι` on `Ext¹_G(X, A)` is injective. -/
theorem levelTransport_injective_of_iso {G H : Type} [Group G] [Group H] (f : H →* G)
    (hf : Function.Bijective f) {X A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H}
    (ι : Rep.res f A ⟶ B) (ρ : B ⟶ Rep.res f A) (hρι : ι ≫ ρ = 𝟙 (Rep.res f A)) :
    Function.Injective (fun x : CategoryTheory.Abelian.Ext X A 1 =>
      (SSGRoute.PTExt.extRes f x).comp (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1)) := by
  have hpost := comp_mk₀_injective_of_retraction (Rep.res f X) ι ρ hρι
  let e : H ≃* G := { Equiv.ofBijective f hf with map_mul' := f.map_mul }
  have he : e.toMonoidHom = f := rfl
  have hinj := Work.SSGRoute.extRes_injective_of_mulEquiv e X A 1
  rw [he] at hinj
  intro x y hxy
  have hxy' : (SSGRoute.PTExt.extRes f x).comp (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1)
      = (SSGRoute.PTExt.extRes f y).comp (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1) := hxy
  have hz : SSGRoute.PTExt.extRes f x - SSGRoute.PTExt.extRes f y = 0 := by
    apply hpost
    rw [sub_eq_add_neg, CategoryTheory.Abelian.Ext.add_comp,
      CategoryTheory.Abelian.Ext.neg_comp, hxy', add_neg_cancel]
  rw [sub_eq_zero] at hz
  exact hinj hz
/-- **In the case `D_w ≠ ⊥` the restriction map `D_u → D_w` is bijective.**  (Both groups have order
`2`: `D_w` because `w` is then complex and ramified, `D_u` because it surjects onto `D_w` and has
order at most `2`.) -/
lemma decompKRestrict_bijective_of_ne_bot {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] {K L : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] [FiniteDimensional k L] [IsGalois k L] [Algebra ↥K ↥L]
    [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (w : NK.GlobalCFT.Place ↥K)
    (hw : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u w)
    (hD : decompK (k := k) w ≠ ⊥) :
    Function.Bijective (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu) := by
  have hw2 : Nat.card ↥(decompK (k := k) w) = 2 :=
    Work.SSGRoute.PT.natCard_decompK_eq_two_of_ne_bot (k := k) w hw hD
  have hle : Nat.card ↥(decompK (k := k) u) ≤ 2 :=
    Work.SSGRoute.PT.natCard_stabilizer_le_two_of_liesOver (k := k) (K := ↥K) (L := ↥L) w hw u hu
  let f : ↥(decompK (k := k) u) →* ↥(decompK (k := k) w) :=
    Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu
  have hsurj : Function.Surjective f :=
    Work.SSGRoute.decompK_restrict_surjective k ↥K w ↥L u hu f
      (fun σ => Work.SSGRoute.decompKRestrict_coe k ↥K ↥L w u hu σ)
  have hge : Nat.card ↥(decompK (k := k) w) ≤ Nat.card ↥(decompK (k := k) u) :=
    Nat.card_le_card_of_surjective f hsurj
  have hcard : Nat.card ↥(decompK (k := k) u) = Nat.card ↥(decompK (k := k) w) := by
    have h1 : Nat.card ↥(decompK (k := k) u) ≤ Nat.card ↥(decompK (k := k) w) := by
      rw [hw2]; exact hle
    exact le_antisymm h1 hge
  refine ⟨?_, hsurj⟩
  have hsplit : Nat.card ↥(decompK (k := k) u)
      = Nat.card ↥(f.range) * Nat.card ↥(f.ker) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (f.ker)]
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have hrange : Nat.card ↥(f.range) = 2 := by
    rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, hw2]
  have hker : Nat.card ↥(f.ker) = 1 := by
    rw [hcard, hrange] at hsplit
    omega
  have hbot : f.ker = ⊥ := by
    rw [← Subgroup.card_eq_one]
    exact hker
  exact (MonoidHom.ker_eq_bot_iff f).mp hbot

/-! ## The transport as an additive map -/

/-- **The level transport** `Ext¹_G(X, A) → Ext¹_H(res f X, B)`,
`x ↦ (extRes f x) ∘ mk₀ ι`.  This is the map appearing in the target statement (with `H = D_u`,
`G = D_w`, `f = decompKRestrict`, `ι = localUnitsMap`). -/
noncomputable def levelTransport {G H : Type} [Group G] [Group H] (f : H →* G)
    {X A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B)
    (x : CategoryTheory.Abelian.Ext X A 1) :
    CategoryTheory.Abelian.Ext (Rep.res f X) B 1 :=
  (SSGRoute.PTExt.extRes f x).comp (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1)

@[simp] lemma levelTransport_apply {G H : Type} [Group G] [Group H] (f : H →* G)
    {X A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B)
    (x : CategoryTheory.Abelian.Ext X A 1) :
    levelTransport f ι x
      = (SSGRoute.PTExt.extRes f x).comp (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1) := rfl

lemma levelTransport_add {G H : Type} [Group G] [Group H] (f : H →* G)
    {X A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B)
    (x y : CategoryTheory.Abelian.Ext X A 1) :
    levelTransport f ι (x + y) = levelTransport f ι x + levelTransport f ι y := by
  simp only [levelTransport_apply, Work.SSGRoute.extRes_add, CategoryTheory.Abelian.Ext.add_comp]

set_option backward.isDefEq.respectTransparency false in
/-- **The transport of a `pushClass` is a `pushClass`** (the `mapExactFunctor` computation). -/
lemma extRes_pushClass_comp' {G H : Type} [Group G] [Group H] (p : ℕ) [Fact p.Prime]
    (f : H →* G) {A : Rep Coeff G} {B : Rep Coeff H} (ι : Rep.res f A ⟶ B)
    (φ : unitRep G ⟶ A) :
    (SSGRoute.PTExt.extRes f (Work.SSGRoute.pushClass_lde p A φ)).comp
      (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1)
      = Work.SSGRoute.pushClass_lde p B ((Rep.resFunctor f).map φ ≫ ι) := by
  have hext : ((SSGRoute.Phi1.coeffSES_shortExact G p).extClass).mapExactFunctor
      (Rep.resFunctor f) = (SSGRoute.Phi1.coeffSES_shortExact H p).extClass := by
    rw [CategoryTheory.Abelian.Ext.mapExactFunctor_extClass]
  simp only [Work.SSGRoute.pushClass_lde, SSGRoute.PTExt.extRes,
    CategoryTheory.Abelian.Ext.mapExactFunctor_comp,
    CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀, hext,
    CategoryTheory.Abelian.Ext.mk₀_comp_mk₀,
    CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero,
    CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero]

lemma levelTransport_zero {G H : Type} [Group G] [Group H] (f : H →* G)
    {X A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B) :
    levelTransport f ι (0 : CategoryTheory.Abelian.Ext X A 1) = 0 := by
  simp only [levelTransport_apply, Work.SSGRoute.extRes_zero,
    CategoryTheory.Abelian.Ext.zero_comp]

/-- The transport is additive, packaged as an `AddMonoidHom`. -/
noncomputable def levelTransportHom {G H : Type} [Group G] [Group H] (f : H →* G)
    (X : Rep.{0} Coeff G) {A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B) :
    CategoryTheory.Abelian.Ext X A 1 →+ CategoryTheory.Abelian.Ext (Rep.res f X) B 1 where
  toFun := levelTransport f ι
  map_zero' := levelTransport_zero f ι
  map_add' := levelTransport_add f ι

/-! ## The `𝔽_p` case -/

/-- **Abstraction of the `𝔽_p`-node of the real-under-complex case (uniform in `p`).**

`f : H →* G` is surjective, `ι : res f A ⟶ B` is injective, `B` has no `H¹` (Hilbert 90 for the
local units), and every `H`-fixed point of `B` is in the image of `ι` (the "invariants of the level
`L` local units are the level-`K` local units" input `globalCFT_localFixed_infinite`).  Then the
transport `Ext¹_G(𝔽_p, A) → Ext¹_H(𝔽_p, B)` is injective.

Route: `x = pushClass_lde p A φ` (`pushClass_surjective`, using `hA`); push forward along `ι` and
use `pushClass_lde_eq_zero_iff_factors` at `H`: if the image vanishes then `ι(φ 1) = p · b` with
`b ∈ B^H`, `hinv` writes `b = ι a`, and `hι` gives `φ 1 = p · a`, so `x = 0`. -/
theorem levelTransport_fp_injective {G H : Type} [Group G] [Group H] (p : ℕ) [Fact p.Prime]
    (f : H →* G) (hf : Function.Surjective f) {A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H}
    (ι : Rep.res f A ⟶ B)
    (hA : Subsingleton (SSGRoute.PTExt.extH A 1))
    (hι : Function.Injective (fun a => ι.hom a))
    (hinv : ∀ b : B.V, (∀ h : H, B.ρ h b = b) → ∃ a : A.V, ι.hom a = b) :
    Function.Injective (fun x : CategoryTheory.Abelian.Ext
        (Rep.trivial Coeff G (ZMod p)) A 1 => levelTransport f ι x) := by
  have hfp : ∀ x : CategoryTheory.Abelian.Ext (Rep.trivial Coeff G (ZMod p)) A 1,
      levelTransport f ι x = 0 → x = 0 := by
    intro x hx
    obtain ⟨φ, rfl⟩ := Work.SSGRoute.pushClass_surjective p A hA x
    exact Work.SSGRoute.PT.pushClass_transport_vanishing p f hf ι hι hinv φ hx
  intro x y hxy
  rw [← sub_eq_zero]
  refine hfp (x - y) ?_
  have hneg : levelTransport f ι (-y) = -levelTransport f ι y := by
    have h2 : levelTransport f ι (y + (-y)) = levelTransport f ι y + levelTransport f ι (-y) :=
      levelTransport_add f ι y (-y)
    rw [add_neg_cancel, levelTransport_zero] at h2
    exact eq_neg_of_add_eq_zero_right h2.symm
  have hsub : levelTransport f ι (x - y) = levelTransport f ι x - levelTransport f ι y := by
    rw [sub_eq_add_neg, levelTransport_add, hneg, sub_eq_add_neg]
  have hxyeq : levelTransport f ι x = levelTransport f ι y := hxy
  rw [hsub, hxyeq, sub_self]

/-- **The non-trivial-`D_w`-action case of the target.**  If the `D_w`-action on `V` is not
trivial then `decompK w ≠ ⊥`, so the restriction `D_u → D_w` is bijective and the local units map
has a retraction; `levelTransport_injective_of_iso` then gives injectivity. -/
theorem archLevelPair_injective_of_nontrivial (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K L : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [FiniteDimensional k L] [IsGalois k L] [NumberField ↥L]
    [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (V : Type) [AddCommGroup V] [Module (ZMod p) V] [DistribMulAction (↥K ≃ₐ[k] ↥K) V]
    [SMulCommClass (↥K ≃ₐ[k] ↥K) (ZMod p) V] [Finite V]
    (w : NK.GlobalCFT.Place ↥K)
    (hw : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u w)
    (hnt : ∃ (σ : ↥K ≃ₐ[k] ↥K), σ ∈ decompK (k := k) w ∧ ∃ v : V, σ • v ≠ v) :
    Function.Injective (fun x : CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) V))
        (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) w) 1 =>
      (SSGRoute.PTExt.extRes (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu) x).comp
        (CategoryTheory.Abelian.Ext.mk₀ (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu)) (add_zero 1)) := by
  have hD : decompK (k := k) w ≠ ⊥ := by
    intro h
    obtain ⟨σ, hσ, v, hv⟩ := hnt
    rw [h, Subgroup.mem_bot] at hσ
    exact hv (by rw [hσ]; exact one_smul _ v)
  have hbij := decompKRestrict_bijective_of_ne_bot (k := k) (K := K) (L := L) w hw u hu hD
  obtain ⟨ρ, hρ⟩ := Work.SSGRoute.PT.localUnitsMap_retraction_of_ne_bot
    (k := k) (K := K) (L := L) w hw u hu hD
  have hmain := levelTransport_injective_of_iso (G := ↥(decompK (k := k) w))
    (H := ↥(decompK (k := k) u))
    (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu) hbij
    (X := Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
      (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) V))
    (A := SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) w)
    (B := NK.HassePrinciple.localUnitsRep k ↥L u)
    (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu) ρ hρ
  simpa only [levelTransport_apply] using hmain

/-- **The trivial-`D_w`-action case of the target**, parameterised by the three local inputs
(the decomposition data `he`/`pr`, injectivity of `localUnitsMap`, and the invariants statement):
the déclvissage `levelTransport_injective_of_components` reduces the transport on `X` to the `𝔽_p`
case `levelTransport_fp_injective`. -/
theorem archLevelPair_injective_of_trivial (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K L : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [FiniteDimensional k L] [IsGalois k L] [NumberField ↥L]
    [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (V : Type) [AddCommGroup V] [Module (ZMod p) V] [DistribMulAction (↥K ≃ₐ[k] ↥K) V]
    [SMulCommClass (↥K ≃ₐ[k] ↥K) (ZMod p) V] [Finite V]
    (w : NK.GlobalCFT.Place ↥K)
    (hw : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u w)
    (htriv : ∀ (σ : ↥K ≃ₐ[k] ↥K), σ ∈ SSGRoute.PTExt.decompK (k := k) w → ∀ v : V, σ • v = v)
    (n : ℕ)
    (he : Fin n → (Rep.trivial Coeff ↥(SSGRoute.PTExt.decompK (k := k) w) (ZMod p) ⟶
        Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) V)))
    (pr : Fin n → (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
        (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) V) ⟶
        Rep.trivial Coeff ↥(SSGRoute.PTExt.decompK (k := k) w) (ZMod p)))
    (hsum : (∑ i : Fin n, pr i ≫ he i)
        = 𝟙 (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) V)))
    (hι : Function.Injective (fun a => (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu).hom a))
    (hinv : ∀ b : (NK.HassePrinciple.localUnitsRep k ↥L u).V,
      (∀ σ : ↥(SSGRoute.PTExt.decompK (k := k) u),
        (NK.HassePrinciple.localUnitsRep k ↥L u).ρ σ b = b) →
      ∃ a : (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) w).V,
        (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu).hom a = b) :
    Function.Injective (fun x : CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) V))
        (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) w) 1 =>
      (SSGRoute.PTExt.extRes (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu) x).comp
        (CategoryTheory.Abelian.Ext.mk₀ (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu)) (add_zero 1)) := by
  have hsurj : Function.Surjective (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu) :=
    Work.SSGRoute.decompK_restrict_surjective k ↥K w ↥L u hu _
      (fun σ => Work.SSGRoute.decompKRestrict_coe k ↥K ↥L w u hu σ)
  have hfp := levelTransport_fp_injective (G := ↥(SSGRoute.PTExt.decompK (k := k) w))
    (H := ↥(SSGRoute.PTExt.decompK (k := k) u)) p
    (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu) hsurj
    (A := SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) w)
    (B := NK.HassePrinciple.localUnitsRep k ↥L u)
    (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu)
    (Work.SSGRoute.hilbert90_localUnits_extH k ↥K w) hι hinv
  have hcomp := Work.SSGRoute.PT.levelTransport_injective_of_components
    (f := Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
    (A := SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) w)
    (B := NK.HassePrinciple.localUnitsRep k ↥L u)
    (ι := Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu)
    (P := Rep.trivial Coeff ↥(SSGRoute.PTExt.decompK (k := k) w) (ZMod p))
    (X := Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
      (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) V))
    he pr hsum hfp
  exact hcomp

/-- The archimedean level transport is injective (input for G1⁺ clause (4) at involutions).  Let
`w` be an infinite place of `K` and `u | w` a place of a level `L ≥ K`.  Then the map
`Ext¹_{D_w}(V, K_wˣ) → Ext¹_{D_u}(V, L_uˣ)`, `x ↦ (extRes (D_u → D_w) x) ∘ mk₀ (K_wˣ → L_uˣ)`, is
injective for every finite `ZMod p`-module `V`.  This is the map inside `levelPair`, so the level-`L`
involution pairing inherits the perfectness of `archYoneda_perfect` at `u`.

Route, by the three cases of `u | w`.
* `w` complex: `u` is complex, `D_u → D_w` is an isomorphism (both are trivial or both have order 2,
  and the map is onto because `D_w` is the image of a decomposition group above it), and
  `K_w = ℂ → L_u = ℂ` is an isomorphism of topological fields.  So the map is an isomorphism.
* `w` and `u` real: `D_u = D_w = ⊥`, and `ℝ → ℝ` is an isomorphism.
* `w` real, `u` complex: `D_w = ⊥`, `D_u = ⟨c⟩ ≅ ℤ/2` acting on `ℂˣ` by conjugation, and `D_u` acts
  trivially on `V`.  Both sides are additive in `V` and `V ≅ (ℤ/p)ⁿ`, so reduce to `V = ℤ/p`.
  * Odd `p`: `Ext¹_ℤ(ℤ/p, ℝˣ) = ℝˣ/ℝˣᵖ = 0`.
  * `p = 2`: the source is `ℝˣ/ℝˣ² = {±1}`.  The class of `−1` adjoins `m` with `2m = −1`; its image
    splits only if some `z ∈ ℂˣ` has `(zm)² = 1` (so `z = ±i`) and `zm` is conjugation-invariant
    (so `z` is real).  No such `z` exists, so the image is non-zero. -/
theorem archLevelPair_injective (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K L : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [FiniteDimensional k L] [IsGalois k L] [NumberField ↥L]
    [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (V : Type) [AddCommGroup V] [Module (ZMod p) V] [DistribMulAction (↥K ≃ₐ[k] ↥K) V]
    [SMulCommClass (↥K ≃ₐ[k] ↥K) (ZMod p) V] [Finite V]
    (w : NK.GlobalCFT.Place ↥K)
    (hw : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u w) :
    Function.Injective (fun x : CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) V))
        (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) w) 1 =>
      (SSGRoute.PTExt.extRes (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu) x).comp
        (CategoryTheory.Abelian.Ext.mk₀ (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu)) (add_zero 1)) := by
  by_cases hnt : ∃ (σ : ↥K ≃ₐ[k] ↥K), σ ∈ SSGRoute.PTExt.decompK (k := k) w ∧ ∃ v : V, σ • v ≠ v
  · -- the `D_w`-action on `V` is not trivial: `D_w ≅ D_u` and the local units map is an iso
    exact archLevelPair_injective_of_nontrivial p k Ω K L V w hw u hu hnt
  · -- the `D_w`-action on `V` is trivial: dévissage to `𝔽_p`
    have htriv : ∀ (σ : ↥K ≃ₐ[k] ↥K), σ ∈ SSGRoute.PTExt.decompK (k := k) w →
        ∀ v : V, σ • v = v := by
      intro σ hσ v
      by_contra hv
      exact hnt ⟨σ, hσ, v, hv⟩
    obtain ⟨n, he, pr, hsum⟩ :=
      Work.SSGRoute.PT.archLevelPair_decomposition p k Ω K L V w hw u hu htriv
    exact archLevelPair_injective_of_trivial p k Ω K L V w hw u hu htriv n he pr hsum
      (Work.SSGRoute.PT.localUnitsMap_injective (k := k) (K := K) (L := L) w hw u hu)
      (Work.SSGRoute.PT.localUnitsMap_invariants (k := k) (K := K) (L := L) w hw u hu)

end Work.SSGRoute.PT
