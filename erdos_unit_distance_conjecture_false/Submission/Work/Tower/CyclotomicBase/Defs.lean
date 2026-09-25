import Mathlib
import Submission.Work.Tower.Defs
import Submission.Work.Tower.CyclotomicCubic
import Submission.Work.Tower.CubicDiscriminant

/-!
# The cyclotomic base of the tower (paper Proposition 3.2): setup

Let `r : Fin ℓ → ℕ` be a family of pairwise distinct primes `≡ 1 (mod 3)`, and let
`D = ∏ i, r i`.  This file sets up the ambient cyclotomic field `ℚ(ζ_D)`, the product of the
`ℓ` cubic characters `χᵢ` of conductor `rᵢ`, the field `M` cut out by all of them (so that
`Gal(M/ℚ) ≅ (ℤ/3)^ℓ`), and the field `F` cut out by the product character `χ₁⋯χ_ℓ`.

## Main definitions

* `Work.Tower.CyclotomicBase.D r`: the product of the primes.
* `Work.Tower.CyclotomicBase.Cyc r`: the field `ℚ(ζ_D)`.
* `Work.Tower.CyclotomicBase.cubeChar p hp hp3`: the cubic character `(ℤ/p)ˣ → ℤ/3` whose kernel
  is the subgroup of cubes.
* `Work.Tower.CyclotomicBase.coordChar r hr hr3 i`: its `i`-th CRT component on `(ℤ/D)ˣ`.
* `Work.Tower.CyclotomicBase.galMap`: the resulting map `Gal(ℚ(ζ_D)/ℚ) → (ℤ/3)^ℓ`.
* `Work.Tower.CyclotomicBase.Mfield`: the field `M` cut out by `galMap`.
* `Work.Tower.CyclotomicBase.Lfield i`: the cubic subfield `Lᵢ` cut out by `χᵢ`.
* `Work.Tower.CyclotomicBase.sumHom`: the sum-of-coordinates map `(ℤ/3)^ℓ → ℤ/3`.
* `Work.Tower.CyclotomicBase.Ffield`: the cubic field `F` cut out by `sumHom ∘ galMap`.
-/

set_option linter.style.haveILetI false
set_option autoImplicit false

open NumberField
open scoped Classical nonZeroDivisors

namespace Work.Tower.CyclotomicBase

variable {ℓ : ℕ}

/-! ## The product of the primes and the ambient cyclotomic field -/

/-- `D r = ∏ᵢ rᵢ`, the product of the (pairwise distinct) primes `rᵢ`. -/
def D (r : Fin ℓ → ℕ) : ℕ := ∏ i, r i

lemma D_def (r : Fin ℓ → ℕ) : D r = ∏ i, r i := rfl

lemma D_pos (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i)) : 0 < D r :=
  Finset.prod_pos fun i _ => (hr i).pos

lemma D_ne_zero (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i)) : D r ≠ 0 :=
  (D_pos r hr).ne'

lemma neZero_D (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i)) : NeZero (D r) :=
  ⟨D_ne_zero r hr⟩

/-- The `i`-th prime divides the product `D r`. -/
lemma r_dvd_D (r : Fin ℓ → ℕ) (i : Fin ℓ) : r i ∣ D r :=
  Finset.dvd_prod_of_mem r (Finset.mem_univ i)

/-- The ambient field `ℚ(ζ_D)`. -/
abbrev Cyc (r : Fin ℓ → ℕ) : Type := CyclotomicField (D r) ℚ

/-- `ℚ(ζ_D)` is the `D`-th cyclotomic field of `ℚ`. -/
lemma isCyclotomicExtension_cyc (r : Fin ℓ → ℕ) [NeZero (D r)] :
    IsCyclotomicExtension {(D r : ℕ)} ℚ (Cyc r) := by
  haveI : NeZero ((D r : ℚ)) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne (D r))⟩
  exact CyclotomicField.isCyclotomicExtension (D r) ℚ

/-- The canonical isomorphism `Gal(ℚ(ζ_D)/ℚ) ≃* (ℤ/D)ˣ`. -/
noncomputable def galEquiv (r : Fin ℓ → ℕ) [NeZero (D r)] :
    Gal(Cyc r/ℚ) ≃* (ZMod (D r))ˣ := by
  haveI := isCyclotomicExtension_cyc r
  exact IsCyclotomicExtension.Rat.galEquivZMod (D r) (Cyc r)

/-! ## The cubic character of `(ℤ/p)ˣ` -/

/-- The subgroup of cubes of `(ℤ/p)ˣ`. -/
def cubes (p : ℕ) : Subgroup (ZMod p)ˣ := (powMonoidHom 3).range

lemma cubes_eq_range (p : ℕ) : cubes p = (powMonoidHom 3).range := rfl

/-- For a prime `p ≡ 1 (mod 3)`, the cubes have index `3` in `(ℤ/p)ˣ`. -/
lemma cubes_index (p : ℕ) (hp : Nat.Prime p) (hp3 : p % 3 = 1) : (cubes p).index = 3 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime hp
  rw [cubes_eq_range, IsCyclic.index_powMonoidHom_range, Nat.card_eq_fintype_card, ZMod.card_units p]
  exact Nat.gcd_eq_right (by simpa [hp3] using Nat.dvd_sub_mod (n := 3) p)

lemma cubes_card_quot (p : ℕ) (hp : Nat.Prime p) (hp3 : p % 3 = 1) :
    Nat.card ((ZMod p)ˣ ⧸ cubes p) = 3 := by
  rw [← Subgroup.index_eq_card, cubes_index p hp hp3]

/-- An arbitrary isomorphism of the (cyclic) quotient `(ℤ/p)ˣ/cubes` of order `3` with `ℤ/3`. -/
noncomputable def cubesQuotEquiv (p : ℕ) (hp : Nat.Prime p) (hp3 : p % 3 = 1) :
    (ZMod p)ˣ ⧸ cubes p ≃* Multiplicative (ZMod 3) :=
  mulEquivOfPrimeCardEq (cubes_card_quot p hp hp3) (by simp [Nat.card_eq_fintype_card])

/-- For a prime `p ≡ 1 (mod 3)`, a surjective homomorphism `(ℤ/p)ˣ →* ℤ/3` whose kernel is the
subgroup of cubes of `(ℤ/p)ˣ`.  It is defined as the quotient map onto `(ℤ/p)ˣ/C` followed by the
chosen isomorphism of the (cyclic) group of order `3` with `ℤ/3`. -/
noncomputable def cubeChar (p : ℕ) (hp : Nat.Prime p) (hp3 : p % 3 = 1) :
    (ZMod p)ˣ →* Multiplicative (ZMod 3) :=
  (cubesQuotEquiv p hp hp3).toMonoidHom.comp (QuotientGroup.mk' (cubes p))

lemma cubeChar_ker (p : ℕ) (hp : Nat.Prime p) (hp3 : p % 3 = 1) :
    (cubeChar p hp hp3).ker = cubes p := by
  rw [cubeChar, MonoidHom.ker_comp_of_injective _ _ (cubesQuotEquiv p hp hp3).injective,
    QuotientGroup.ker_mk']

lemma cubeChar_ker' (p : ℕ) (hp : Nat.Prime p) (hp3 : p % 3 = 1) :
    (cubeChar p hp hp3).ker = (powMonoidHom 3).range := by
  rw [cubeChar_ker, cubes_eq_range]

lemma cubeChar_surjective (p : ℕ) (hp : Nat.Prime p) (hp3 : p % 3 = 1) :
    Function.Surjective (cubeChar p hp hp3) := by
  rw [cubeChar]
  exact (cubesQuotEquiv p hp hp3).surjective.comp (QuotientGroup.mk'_surjective (cubes p))

/-! ## The coordinate characters on `(ℤ/D)ˣ` -/

/-- The `i`-th coordinate of the CRT decomposition `(ℤ/D)ˣ → (ℤ/rᵢ)ˣ`, followed by the cubic
character. -/
noncomputable def coordChar (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i)) (hr3 : ∀ i, r i % 3 = 1)
    (i : Fin ℓ) : (ZMod (D r))ˣ →* Multiplicative (ZMod 3) :=
  (cubeChar (r i) (hr i) (hr3 i)).comp (ZMod.unitsMap (r_dvd_D r i))

lemma coordChar_surjective (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i)) (hr3 : ∀ i, r i % 3 = 1)
    [NeZero (D r)] (i : Fin ℓ) : Function.Surjective (coordChar r hr hr3 i) := by
  intro a
  obtain ⟨b, hb⟩ := cubeChar_surjective (r i) (hr i) (hr3 i) a
  obtain ⟨c, hc⟩ := ZMod.unitsMap_surjective (r_dvd_D r i) b
  exact ⟨c, by rw [coordChar, MonoidHom.comp_apply, hc]; exact hb⟩

/-- The product of the `ℓ` coordinate characters, `(ℤ/D)ˣ → (ℤ/3)^ℓ`. -/
noncomputable def piChar (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i)) (hr3 : ∀ i, r i % 3 = 1) :
    (ZMod (D r))ˣ →* (Fin ℓ → Multiplicative (ZMod 3)) where
  toFun u i := coordChar r hr hr3 i u
  map_one' := by funext i; simp
  map_mul' u v := by funext i; simp

lemma piChar_apply (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i)) (hr3 : ∀ i, r i % 3 = 1)
    (u : (ZMod (D r))ˣ) (i : Fin ℓ) :
    piChar r hr hr3 u i = coordChar r hr hr3 i u := rfl

lemma piChar_ker (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i)) (hr3 : ∀ i, r i % 3 = 1) :
    (piChar r hr hr3).ker = ⨅ i, (coordChar r hr hr3 i).ker := by
  ext u
  rw [MonoidHom.mem_ker, Subgroup.mem_iInf]
  constructor
  · intro h i
    show coordChar r hr hr3 i u = 1
    exact congrFun h i
  · intro h; funext i; exact h i

/-! ## The Galois group of `ℚ(ζ_D)` -/

/-- The map `Gal(ℚ(ζ_D)/ℚ) → (ℤ/3)^ℓ` given by the `ℓ` cubic characters of conductor `rᵢ`. -/
noncomputable def galMap (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i)) (hr3 : ∀ i, r i % 3 = 1)
    [NeZero (D r)] : Gal(Cyc r/ℚ) →* (Fin ℓ → Multiplicative (ZMod 3)) :=
  (piChar r hr hr3).comp (galEquiv r).toMonoidHom

/-- The `i`-th coordinate of `galMap`. -/
noncomputable def galCoord (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i)) (hr3 : ∀ i, r i % 3 = 1)
    [NeZero (D r)] (i : Fin ℓ) : Gal(Cyc r/ℚ) →* Multiplicative (ZMod 3) :=
  (coordChar r hr hr3 i).comp (galEquiv r).toMonoidHom

lemma galMap_apply (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i)) (hr3 : ∀ i, r i % 3 = 1)
    [NeZero (D r)] (σ : Gal(Cyc r/ℚ)) (i : Fin ℓ) :
    galMap r hr hr3 σ i = galCoord r hr hr3 i σ := rfl

/-- The cubic subfield `Lᵢ ⊆ ℚ(ζ_D)` cut out by the character `χᵢ`. -/
noncomputable def Lfield (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i)) (hr3 : ∀ i, r i % 3 = 1)
    [NeZero (D r)] (i : Fin ℓ) : IntermediateField ℚ (Cyc r) :=
  IntermediateField.fixedField (galCoord r hr hr3 i).ker

/-- The field `M ⊆ ℚ(ζ_D)` cut out by all the `ℓ` characters `χᵢ` simultaneously. -/
noncomputable def Mfield (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i)) (hr3 : ∀ i, r i % 3 = 1)
    [NeZero (D r)] : IntermediateField ℚ (Cyc r) :=
  IntermediateField.fixedField (galMap r hr hr3).ker

/-! ## The inertia subgroup and inertia field of the prime `rᵢ` -/

lemma div_r_dvd_D (r : Fin ℓ → ℕ) (i : Fin ℓ) : D r / r i ∣ D r :=
  ⟨r i, (Nat.div_mul_cancel (r_dvd_D r i)).symm⟩

/-- The subgroup of `(ℤ/D)ˣ` of units congruent to `1` modulo `D / rᵢ`: this is the inertia
subgroup of the rational prime `rᵢ` in `Gal(ℚ(ζ_D)/ℚ)`. -/
def inertiaSub (r : Fin ℓ → ℕ) (i : Fin ℓ) : Subgroup (ZMod (D r))ˣ :=
  (ZMod.unitsMap (div_r_dvd_D r i)).ker

/-- The subfield of `ℚ(ζ_D)` fixed by the inertia subgroup of `rᵢ`: the inertia field of `rᵢ`,
which is `ℚ(ζ_{D/rᵢ})`. -/
noncomputable def Zfield (r : Fin ℓ → ℕ) [NeZero (D r)] (i : Fin ℓ) :
    IntermediateField ℚ (Cyc r) :=
  IntermediateField.fixedField ((inertiaSub r i).comap (galEquiv r).toMonoidHom)

lemma fixingSubgroup_Zfield (r : Fin ℓ → ℕ) [NeZero (D r)] (i : Fin ℓ) :
    (Zfield r i).fixingSubgroup = (inertiaSub r i).comap (galEquiv r).toMonoidHom :=
  IntermediateField.fixingSubgroup_fixedField _

lemma isGalois_Zfield (r : Fin ℓ → ℕ) [NeZero (D r)] (i : Fin ℓ) : IsGalois ℚ ↥(Zfield r i) := by
  haveI := isCyclotomicExtension_cyc r
  haveI hG : IsGalois ℚ (Cyc r) := IsCyclotomicExtension.isGalois {D r} ℚ (Cyc r)
  haveI := IsCyclotomicExtension.isAbelianGalois {D r} ℚ (Cyc r)
  exact IsGalois.of_fixedField_normal_subgroup _


/-! ## The sum-of-coordinates character and the field `F` -/

/-- The sum of the coordinates in `(ℤ/3)^ℓ`, written multiplicatively. -/
noncomputable def sumHom (ℓ : ℕ) : (Fin ℓ → Multiplicative (ZMod 3)) →* Multiplicative (ZMod 3)
    where
  toFun a := ∏ i, a i
  map_one' := by simp
  map_mul' a b := by simp [Finset.prod_mul_distrib]

lemma sumHom_apply (ℓ : ℕ) (a : Fin ℓ → Multiplicative (ZMod 3)) :
    sumHom ℓ a = ∏ i, a i := rfl

lemma sumHom_surjective {ℓ : ℕ} (hℓ : 0 < ℓ) : Function.Surjective (sumHom ℓ) := by
  intro a
  refine ⟨fun i => if i = ⟨0, hℓ⟩ then a else 1, ?_⟩
  rw [sumHom_apply, Finset.prod_eq_single ⟨0, hℓ⟩]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The cubic subfield `F ⊆ ℚ(ζ_D)` cut out by the product character `χ₁⋯χ_ℓ`. -/
noncomputable def Ffield (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i)) (hr3 : ∀ i, r i % 3 = 1)
    [NeZero (D r)] : IntermediateField ℚ (Cyc r) :=
  IntermediateField.fixedField ((sumHom ℓ).comp (galMap r hr hr3)).ker

end Work.Tower.CyclotomicBase
