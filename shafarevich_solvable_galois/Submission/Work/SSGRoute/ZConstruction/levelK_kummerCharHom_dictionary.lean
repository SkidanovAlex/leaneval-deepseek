import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.LocallyConstant.Basic
import Submission.Work.SSGRoute.ZConstruction.kummerCharZMod_fixingSubgroup_mul_pow
import Submission.Work.SSGRoute.localKummerReciprocity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local Kummer dictionary in `MonoidHom` form

The global Kummer character `Work.SSGRoute.kummerCharZMod` of `β ∈ Kˣ` is a `ZMod p`-valued
function on `Gal(Ω/↥K)`.  Because it is *additive in the automorphism* (`kummerIdx_mul_apply`) it is
a group homomorphism, and because it is *additive in `β`* and *kills `p`-th powers*
(`kummerCharZMod_fixingSubgroup_mul_pow`) that homomorphism depends multiplicatively on `β`.

This file packages the character, at a *finite place* `A`, as

`kummerCharHom ... A β : ↥(decomp (k := ↥K) A) →* Multiplicative (ZMod p)`

together with

* `kummerCharHom_mul` : `β ↦ kummerCharHom ... A β` is a group homomorphism `Kˣ →* ...`;
* `kummerCharHom_pow` : it kills `p`-th powers;
* `kummerCharHom_eq_one_iff` : **the local Kummer dictionary** -- the character is trivial if and
  only if `β` is a local `p`-th power at the prime of `K` below `A`
  (`NK.UchidaKummer.localPowClass`), i.e. this is the inverse direction of
  `Work.SSGRoute.local_kummer_dictionary` transported to the homomorphism form.

Together these say that the Kummer map `Kˣ ⧸ (Kˣ)^p → ↥(lcHoms p (decomp A))` is well defined and
injective; surjectivity is the weak-approximation/Kummer count (`ZSplit.levelK_localKummer`,
`PTembedding.lcHoms_localUnits`).  This is the `lcHoms`-valued form of the level-`K` local Kummer
isomorphism, which the product formula for the level-`K` local Tate pairing consumes.
-/

open scoped Pointwise IntermediateField

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  {ζ : ↥K} {hζ : IsPrimitiveRoot ζ p} {A : ValuationSubring Ω}

/-- The Kummer character of `β` is additive in `β` at every automorphism. -/
theorem kummerCharZMod_add (β β' : Kˣ) (σ : Ω ≃ₐ[↥K] Ω) :
    kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ (β * β') σ =
      kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ β σ +
        kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ β' σ := by
  rw [kummerCharZMod_apply, kummerCharZMod_apply, kummerCharZMod_apply]
  have hcd : (kummerSqrtUnitZMod (Ω := Ω) p β * kummerSqrtUnitZMod (Ω := Ω) p β') ^ p =
      Units.map (algebraMap ↥K Ω) (β * β') := by
    rw [mul_pow, kummerSqrtUnitZMod_pow, kummerSqrtUnitZMod_pow, ← map_mul]
  rw [kummerIdx_congr p hζ (β * β') (kummerSqrtUnitZMod_pow (Ω := Ω) p (β * β')) hcd σ,
    kummerIdx_mul p hζ β β' (kummerSqrtUnitZMod (Ω := Ω) p β) (kummerSqrtUnitZMod (Ω := Ω) p β')
      (kummerSqrtUnitZMod_pow (Ω := Ω) p β) (kummerSqrtUnitZMod_pow (Ω := Ω) p β') hcd σ]

/-- **The Kummer character of `β` as a monoid homomorphism on the local group `decomp A`.** -/
noncomputable def kummerCharHom (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (A : ValuationSubring Ω) (β : Kˣ) :
    ↥(SSGRoute.decomp (k := ↥K) A) →* Multiplicative (ZMod p) where
  toFun g := Multiplicative.ofAdd (kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ β (g : Ω ≃ₐ[↥K] Ω))
  map_one' := by
    show Multiplicative.ofAdd
      (kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ β (1 : Ω ≃ₐ[↥K] Ω)) = 1
    rw [kummerCharZMod_apply,
      kummerIdx_one p hζ β (kummerSqrtUnitZMod (Ω := Ω) p β) (kummerSqrtUnitZMod_pow (Ω := Ω) p β)]
    exact ofAdd_zero
  map_mul' g h := by
    have hcoe : ((g * h : ↥(SSGRoute.decomp (k := ↥K) A)) : Ω ≃ₐ[↥K] Ω) =
        (g : Ω ≃ₐ[↥K] Ω) * (h : Ω ≃ₐ[↥K] Ω) := rfl
    show Multiplicative.ofAdd (kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ β
        ((g * h : ↥(SSGRoute.decomp (k := ↥K) A)) : Ω ≃ₐ[↥K] Ω)) =
      Multiplicative.ofAdd (kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ β (g : Ω ≃ₐ[↥K] Ω)) *
        Multiplicative.ofAdd (kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ β (h : Ω ≃ₐ[↥K] Ω))
    rw [hcoe, kummerCharZMod_apply, kummerCharZMod_apply, kummerCharZMod_apply,
      kummerIdx_mul_apply p hζ β (kummerSqrtUnitZMod (Ω := Ω) p β)
        (kummerSqrtUnitZMod_pow (Ω := Ω) p β) (g : Ω ≃ₐ[↥K] Ω) (h : Ω ≃ₐ[↥K] Ω),
      ofAdd_add]

/-- **The Kummer map `β ↦ χ_β` is a group homomorphism `Kˣ →* (decomp A →* 𝔽_p)`.** -/
theorem kummerCharHom_mul (β β' : Kˣ) :
    kummerCharHom p k Ω K ζ hζ A (β * β') =
      kummerCharHom p k Ω K ζ hζ A β * kummerCharHom p k Ω K ζ hζ A β' := by
  ext g
  show Multiplicative.ofAdd
      (kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ (β * β') (g : Ω ≃ₐ[↥K] Ω)) =
    Multiplicative.ofAdd (kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ β (g : Ω ≃ₐ[↥K] Ω)) *
      Multiplicative.ofAdd (kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ β' (g : Ω ≃ₐ[↥K] Ω))
  rw [← ofAdd_add]
  exact congrArg Multiplicative.ofAdd (kummerCharZMod_add β β' (g : Ω ≃ₐ[↥K] Ω))

/-- **The Kummer character kills `p`-th powers.** -/
theorem kummerCharHom_pow (β : Kˣ) :
    kummerCharHom p k Ω K ζ hζ A (β ^ p) = 1 := by
  ext g
  show Multiplicative.ofAdd
    (kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ (β ^ p) (g : Ω ≃ₐ[↥K] Ω)) = 1
  rw [kummerCharZMod_apply,
    kummerIdx_eq_zero_of_mem_pow p hζ (β ^ p) β rfl
      (kummerSqrtUnitZMod (Ω := Ω) p (β ^ p)) (kummerSqrtUnitZMod_pow (Ω := Ω) p (β ^ p))
      (g : Ω ≃ₐ[↥K] Ω)]
  exact ofAdd_zero

/-- **The local Kummer dictionary in homomorphism form.**  The Kummer character of `β` is trivial
on the local group `decomp A` if and only if `β` is a local `p`-th power at the prime `𝔭` of `K`
below `A`. -/
theorem kummerCharHom_eq_one_iff (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (β : Kˣ) :
    kummerCharHom p k Ω K ζ hζ A β = 1 ↔
      NK.UchidaKummer.localPowClass ↥K p 𝔭 β = 1 := by
  have hiff : (kummerCharHom p k Ω K ζ hζ A β = 1) ↔
      (∀ σ : Ω ≃ₐ[↥K] Ω, σ ∈ SSGRoute.decomp (k := ↥K) A →
        kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ β σ = 0) := by
    constructor
    · intro h σ hσ
      have h1 : (kummerCharHom p k Ω K ζ hζ A β) ⟨σ, hσ⟩ = 1 := by rw [h]; rfl
      have h2 : Multiplicative.ofAdd
          (kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ β σ) = 1 := h1
      exact (ofAdd_eq_one).mp h2
    · intro h
      ext g
      have h1 : kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ β (g : Ω ≃ₐ[↥K] Ω) = 0 := h _ g.2
      show Multiplicative.ofAdd
        (kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ β (g : Ω ≃ₐ[↥K] Ω)) = 1
      rw [h1]
      exact ofAdd_zero
  exact hiff.trans (local_kummer_dictionary p K ζ hζ A hA 𝔭 h𝔭 β)

/-- **Local constancy of the Kummer character.**  `χ_β` is constant on the cosets of the fixing
subgroup of the Kummer field `K(β^{1/p})`, and that fixing subgroup is open (the Kummer field is
finite over `↥K`); hence `χ_β` is locally constant, i.e. `χ_β` lies in
`Work.SSGRoute.lcHoms p ↥(decomp A)`. -/
theorem kummerCharHom_isLocallyConstant (hA : SSGRoute.IsFinPlace k A) (β : Kˣ) :
    IsLocallyConstant (kummerCharHom p k Ω K ζ hζ A β) := by
  classical
  haveI hnumK : NumberField ↥K :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField K
  haveI hsep : IsSepClosure ↥K Ω := by
    haveI : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
    exact IsSepClosure.of_isAlgClosure_of_perfectField ↥K Ω
  -- the Kummer field of `β`, and the vanishing of its character on its fixing subgroup
  set N : IntermediateField ↥K Ω := NK.LocalAnabelian.kummerField (K' := Ω) p β with hNdef
  have hα : ((kummerSqrtUnitZMod (Ω := Ω) p β : Ω)) ^ p = algebraMap ↥K Ω (β : ↥K) :=
    kummerSqrtZMod_pow (Ω := Ω) p β
  have hmem : (kummerSqrtUnitZMod (Ω := Ω) p β : Ω) ∈ N := by
    rw [hNdef]
    exact NK.LocalAnabelian.mem_kummerField_of_pow_eq (K' := Ω) hα
  have hvan : ∀ σ : Ω ≃ₐ[↥K] Ω, σ ∈ N.fixingSubgroup →
      kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ β σ = 0 := by
    intro σ hσ
    have hfix : (σ : Ω → Ω) ((kummerSqrtUnitZMod (Ω := Ω) p β : Ω)) =
        (kummerSqrtUnitZMod (Ω := Ω) p β : Ω) :=
      (IntermediateField.mem_fixingSubgroup_iff N σ).mp hσ _ hmem
    exact kummerIdx_eq_zero_of_apply_eq p hζ β (kummerSqrtUnitZMod (Ω := Ω) p β)
      (kummerSqrtUnitZMod_pow (Ω := Ω) p β) σ hfix
  haveI hfdN : FiniteDimensional ↥K N :=
    NK.GlobalCFTdeep.SecondInequality.finiteDimensional_kummerField (p := p) Fact.out hζ β
  have hNopen : IsOpen ((N.fixingSubgroup : Subgroup (Ω ≃ₐ[↥K] Ω)) : Set (Ω ≃ₐ[↥K] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen N
  -- the open subgroup of `↥(decomp A)` on which `χ_β` is trivial
  set U : Subgroup ↥(SSGRoute.decomp (k := ↥K) A) :=
    (N.fixingSubgroup).comap (SSGRoute.decomp (k := ↥K) A).subtype with hUdef
  have hUcoe : (U : Set ↥(SSGRoute.decomp (k := ↥K) A)) =
      Subtype.val ⁻¹' (N.fixingSubgroup : Set (Ω ≃ₐ[↥K] Ω)) := Subgroup.coe_comap _ _
  have hUopen : IsOpen ((U : Set ↥(SSGRoute.decomp (k := ↥K) A))) := by
    rw [hUcoe]
    exact hNopen.preimage continuous_subtype_val
  have hUtriv : ∀ u : ↥(SSGRoute.decomp (k := ↥K) A), u ∈ U →
      kummerCharHom p k Ω K ζ hζ A β u = 1 := by
    intro u hu
    have h1 : kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ β (u : Ω ≃ₐ[↥K] Ω) = 0 := hvan _ hu
    show Multiplicative.ofAdd
      (kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ β (u : Ω ≃ₐ[↥K] Ω)) = 1
    rw [h1]
    exact ofAdd_zero
  -- `x * U` is an open neighbourhood of `x` on which the character is constant
  rw [IsLocallyConstant.iff_eventually_eq (kummerCharHom p k Ω K ζ hζ A β)]
  intro x
  have hxmem : x ∈ ({x} : Set ↥(SSGRoute.decomp (k := ↥K) A)) * (U : Set _) :=
    ⟨x, rfl, 1, U.one_mem, by simp⟩
  have hnbhd : ({x} : Set ↥(SSGRoute.decomp (k := ↥K) A)) * (U : Set _) ∈ nhds x :=
    (hUopen.mul_left (s := {x})).mem_nhds hxmem
  refine Filter.mem_of_superset hnbhd ?_
  · rintro x' hx'
    obtain ⟨a, ha, u, hu, hau⟩ := Set.mem_mul.mp hx'
    have hax : a = x := Set.mem_singleton_iff.mp ha
    change (kummerCharHom p k Ω K ζ hζ A β) x' =
      (kummerCharHom p k Ω K ζ hζ A β) x
    rw [← hau, hax, map_mul, hUtriv u hu, mul_one]

/-- **The Kummer map lands in `lcHoms`.**  Packaged form of
`kummerCharHom_isLocallyConstant`: `β ↦ χ_β` is a map `Kˣ → ↥(lcHoms p ↥(decomp A))`, which by
`kummerCharHom_mul` / `kummerCharHom_pow` / `kummerCharHom_eq_one_iff` is additive in `β`, kills
`p`-th powers, and has kernel exactly the local `p`-th powers.  Surjectivity (the remaining half of
the level-`K` local Kummer isomorphism) is the weak-approximation/Kummer count. -/
theorem kummerCharHom_mem_lcHoms (hA : SSGRoute.IsFinPlace k A) (β : Kˣ) :
    kummerCharHom p k Ω K ζ hζ A β ∈
      Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A) :=
  kummerCharHom_isLocallyConstant hA β

end Work.SSGRoute.ZConstruction
