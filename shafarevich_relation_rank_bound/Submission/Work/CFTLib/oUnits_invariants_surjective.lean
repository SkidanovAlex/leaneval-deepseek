import Mathlib
import Submission.Work.CFTLib.RelShafReps
import Submission.Work.CFT.IdeleClassGroup.tateCohomology_zero_iso
import Submission.Work.CFT.IdeleClassGroup.TateBasic

/-!
# Surjectivity of `𝒪_Fˣ` onto the Galois invariants of `𝒪_Kˣ`

For a finite Galois extension `K/F` of number fields, the `Gal(K/F)`-invariants of the
unit group `𝒪_Kˣ` are exactly the units of `𝒪_F`, embedded via the natural map
`𝒪_F → 𝒪_K`.  The present file proves the (weaker) surjectivity statement needed for the
Shafarevich relation-rank bound: there is a surjective additive homomorphism

`Additive 𝒪_Fˣ →+ ↥(invariants (oUnitsRep F K))`.

The proof proceeds by exhibiting the natural inclusion `𝒪_Fˣ →* 𝒪_Kˣ` (whose image
consists of invariants), and then showing that every Galois-fixed unit `w : 𝒪_Kˣ` comes
from `𝒪_Fˣ`.  The latter is the classical argument: the underlying element of `K` is
fixed by all `F`-automorphisms, hence lies in `F` (`IsGalois.mem_range_algebraMap_iff_fixed`),
and being integral over `ℤ` it lies in `𝒪_F`; the same applies to `w⁻¹`.
-/

open scoped Classical
open NumberField

noncomputable section

namespace Work.CFTLib

/-! ## Elementary lemmas about the Galois action on `𝒪_Kˣ` -/

/-- The action of `Gal(K/F)` on the unit idèles/units `𝒪_Kˣ` in terms of `ofMul`. -/
lemma oUnitsRep_rho_ofMul {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] (g : K ≃ₐ[F] K) (u : (𝓞 K)ˣ) :
    (oUnitsRep F K).ρ g (Additive.ofMul u) = Additive.ofMul (g • u) :=
  Rep.ofDistribMulAction_ρ_apply_apply (k := ℤ) (G := K ≃ₐ[F] K)
    (A := Additive ((𝓞 K)ˣ)) g (Additive.ofMul u)

/-- The underlying ring element of `g • u`. -/
lemma oUnitsRep_smul_val {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] (g : K ≃ₐ[F] K) (u : (𝓞 K)ˣ) :
    (g • u).val = (mapAlgEquivMonoidHom F K g) u.val := rfl

/-- The action of `Gal(K/F)` on `𝓞 K` restricts to the algebra automorphism on `K`. -/
lemma mapAlgEquivMonoidHom_coe {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] (g : K ≃ₐ[F] K) (x : 𝓞 K) :
    (((mapAlgEquivMonoidHom F K g) x : 𝓞 K) : K) = g (x : K) := rfl

/-- The natural ring homomorphism `𝓞 F → 𝓞 K` is injective. -/
lemma ringOfIntegers_algebraMap_injective {F K : Type} [Field F] [NumberField F] [Field K]
    [NumberField K] [Algebra F K] :
    Function.Injective (algebraMap (𝓞 F) (𝓞 K)) := by
  intro x y h
  have h' : algebraMap F K (x : F) = algebraMap F K (y : F) := by
    have h2 := congrArg (fun t : 𝓞 K => (t : K)) h
    rw [show ∀ t : 𝓞 F,
      ((algebraMap (𝓞 F) (𝓞 K) t : 𝓞 K) : K) = algebraMap F K (t : F)
      from fun t => rfl] at h2
    exact h2
  exact RingOfIntegers.coe_injective (FaithfulSMul.algebraMap_injective F K h')

/-- **Key lifting lemma.** A unit `w : 𝒪_Kˣ` fixed by all of `Gal(K/F)` is the image of an
element `z : 𝒪_F` under the natural map `𝒪_F → 𝒪_K`. -/
lemma exists_ringOfIntegers_of_fixed {F K : Type} [Field F] [NumberField F] [Field K]
    [NumberField K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    (w : (𝓞 K)ˣ) (hfix : ∀ g : K ≃ₐ[F] K, g • w = w) :
    ∃ z : 𝓞 F, algebraMap (𝓞 F) (𝓞 K) z = w.val := by
  have hfixed : ∀ g : K ≃ₐ[F] K,
      g ((w.val : 𝓞 K) : K) = ((w.val : 𝓞 K) : K) := by
    intro g
    have h := congrArg (fun z : (𝓞 K)ˣ => (z.val : K)) (hfix g)
    rw [oUnitsRep_smul_val, mapAlgEquivMonoidHom_coe] at h
    exact h
  obtain ⟨a, ha⟩ :=
    (IsGalois.mem_range_algebraMap_iff_fixed ((w.val : 𝓞 K) : K)).mpr hfixed
  have hint : IsIntegral ℤ a := by
    have h2 : IsIntegral ℤ (algebraMap F K a) := by rw [ha]; exact w.val.2
    exact (isIntegral_algebraMap_iff (A := F) (B := K)).mp h2
  refine ⟨⟨a, hint⟩, ?_⟩
  apply RingOfIntegers.coe_injective
  show ((algebraMap (𝓞 F) (𝓞 K) ⟨a, hint⟩ : 𝓞 K) : K) = ((w.val : 𝓞 K) : K)
  rw [show ((algebraMap (𝓞 F) (𝓞 K) ⟨a, hint⟩ : 𝓞 K) : K)
        = algebraMap F K ((⟨a, hint⟩ : 𝓞 F) : F) from rfl,
      show ((⟨a, hint⟩ : 𝓞 F) : F) = a from rfl, ha]

/-! ## The natural additive map -/

/-- The natural map `Additive 𝒪_Fˣ →+ Additive 𝒪_Kˣ` induced by the inclusion `𝒪_F → 𝒪_K`. -/
def oUnitsInclAdd (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] :
    Additive ((𝓞 F)ˣ) →+ Additive ((𝓞 K)ˣ) :=
  (Units.map (algebraMap (𝓞 F) (𝓞 K))).toAdditive

lemma oUnitsInclAdd_apply {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] (x : Additive ((𝓞 F)ˣ)) :
    oUnitsInclAdd F K x
      = Additive.ofMul ((Units.map (algebraMap (𝓞 F) (𝓞 K))) x.toMul) := rfl

/-! ## The main theorem -/

theorem oUnits_invariants_surjective {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] [FiniteDimensional F K] [IsGalois F K] :
    ∃ f : Additive (NumberField.RingOfIntegers F)ˣ →+
        ↥(Work.CFT.IdeleClassGroup.invariants (Work.CFTLib.oUnitsRep F K)),
      Function.Surjective f := by
  have hmem : ∀ x : Additive ((𝓞 F)ˣ),
      oUnitsInclAdd F K x ∈ Work.CFT.IdeleClassGroup.invariants (oUnitsRep F K) := by
    intro x
    rw [oUnitsInclAdd_apply]
    change ∀ g : K ≃ₐ[F] K,
      (oUnitsRep F K).ρ g
        (Additive.ofMul ((Units.map (algebraMap (𝓞 F) (𝓞 K))) x.toMul)) = _
    intro g
    rw [oUnitsRep_rho_ofMul]
    congr 1
    apply Units.ext
    show ((mapAlgEquivMonoidHom F K g)
        ((Units.map (algebraMap (𝓞 F) (𝓞 K))) x.toMul).val : 𝓞 K) = _
    rw [show ((Units.map (algebraMap (𝓞 F) (𝓞 K))) x.toMul).val
        = algebraMap (𝓞 F) (𝓞 K) x.toMul.val from rfl]
    exact AlgEquiv.commutes (mapAlgEquivMonoidHom F K g) x.toMul.val
  refine ⟨AddMonoidHom.codRestrict (oUnitsInclAdd F K)
      (Work.CFT.IdeleClassGroup.invariants (oUnitsRep F K)) hmem, ?_⟩
  intro y
  set w : (𝓞 K)ˣ := y.1.toMul with hw
  have hy1 : y.1 = Additive.ofMul w := ofMul_toMul y.1
  have hfix : ∀ g : K ≃ₐ[F] K, g • w = w := by
    intro g
    have hρ : (oUnitsRep F K).ρ g (Additive.ofMul w) = Additive.ofMul w := by
      have h := y.2 g
      rw [show y.1 = Additive.ofMul w from hy1] at h
      exact h
    have h2 : Additive.ofMul (g • w) = Additive.ofMul w :=
      (oUnitsRep_rho_ofMul g w).symm.trans hρ
    exact Additive.ofMul.injective h2
  obtain ⟨z, hz⟩ := exists_ringOfIntegers_of_fixed w hfix
  have hfix_inv : ∀ g : K ≃ₐ[F] K, g • w⁻¹ = w⁻¹ := by
    intro g
    have h1 : (g • w) * (g • w⁻¹) = 1 := by
      rw [← smul_mul', mul_inv_cancel, smul_one]
    rw [hfix g] at h1
    exact eq_inv_of_mul_eq_one_right h1
  obtain ⟨b, hb⟩ := exists_ringOfIntegers_of_fixed w⁻¹ hfix_inv
  have hzb : z * b = 1 := by
    apply ringOfIntegers_algebraMap_injective (F := F) (K := K)
    rw [map_mul, hz, hb, map_one]
    exact Units.mul_inv w
  have hbz : b * z = 1 := by
    apply ringOfIntegers_algebraMap_injective (F := F) (K := K)
    rw [map_mul, hb, hz, map_one]
    exact Units.inv_mul w
  let u : (𝓞 F)ˣ := Units.mk z b hzb hbz
  have hinc : (Units.map (algebraMap (𝓞 F) (𝓞 K))) u = w := by
    apply Units.ext
    change (algebraMap (𝓞 F) (𝓞 K)) u.val = w.val
    rw [show u.val = z from rfl, hz]
  refine ⟨Additive.ofMul u, ?_⟩
  apply Subtype.ext
  show Additive.ofMul ((Units.map (algebraMap (𝓞 F) (𝓞 K))) u) = y.1
  rw [hinc, ← hy1]

end Work.CFTLib
