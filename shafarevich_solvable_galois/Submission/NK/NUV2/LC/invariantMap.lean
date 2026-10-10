import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.Basic
import Submission.NK.LocalArtin.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local invariant map at a finite abelian level

This is the first piece of the **local invariant map** `inv_v : Br(F_v) → ℚ/ℤ` that the labelled
Hasse principle (`NK.NUV2.LC.HasseTwo`) and Hilbert reciprocity `Σ_v inv_v = 0` need.

## Conventions

The invariant takes values in `(1/n)ℤ/ℤ` (`n = [L : F]`, the local degree), which for the
*multiplicative* source `Fˣ` is the additive group `ZMod n` written multiplicatively, i.e.
`Multiplicative (ZMod n)`: the classical "`inv(x) = 0`" is `inv x = 1`.

## What is here

For a field `F` with Galois extension `F'` (in the application `F = κ` a `p`-adic field,
`F' = κ̄`), the corrected local reciprocity datum `NK.LocalCFT.ArtinReciprocity F F'` gives, at
every finite abelian level `L ≤ F^{ab}`, the reciprocity isomorphism

  `R.artinLevelMulEquiv L hcomm : Fˣ ⧸ N_{L/F} Lˣ ≃* Gal(L/F)`.

An **invariant map** at the level `L` is the composite of this with a fixed isomorphism
`Gal(L/F) ≃* Multiplicative (ZMod n)`; in the classical theory the latter is *canonical*, because
the fundamental class of `L/F` normalises it (`inv(π) = 1/n` for a uniformiser `π`).  This file
isolates the part of the theory that needs **no** normalisation:

* `localInvariant` — the composite `Fˣ →* Multiplicative (ZMod n)`;
* `localInvariant_ker` — its kernel is exactly the norm group `N_{L/F} Lˣ`;
* `localInvariant_surjective`;
* `localInvariantQuotientMulEquiv` — the induced isomorphism `Fˣ ⧸ N_{L/F} Lˣ ≃* Multiplicative (ZMod n)`;
* `localInvariant_eq_one_iff` — the invariant is trivial exactly on the norms (the property that
  Hilbert reciprocity consumes);
* **`localInvariant_two_heq`** — the **`2`-torsion case is canonical**: `Multiplicative (ZMod 2)`
  has a unique non-identity element, so any two normalisations `Gal(L/F) ≃* Multiplicative (ZMod 2)`
  agree and the invariant map is *independent of all choices*.  This is the case (`p = 2`) in which
  Neukirch's argument and the `p = 2` labelled Hasse principle consume the invariant map.

## What is *not* here (the road ahead)

* the *canonical* normalisation in general (via the local fundamental class — the workspace has the
  existence statement
  `Commons.NumberTheory.NumberField.Completion.exists_addOrderOf_eq_finrank_groupCohomology_two_units_adicCompletion`);
* the *functoriality* of `inv_v` (base change and the norm/transfer compatibility in towers);
* the *global* product formula `Σ_v inv_v = 0` (Hilbert reciprocity).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Classical

namespace NK.NUV2.LC

open NK.LocalCFT

variable {F : Type*} {F' : Type*} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']

/-- **The local invariant map at a finite abelian level, relative to a normalisation
`e : Gal(L/F) ≃* Multiplicative (ZMod n)`.**

It is the Artin map `Fˣ →* Gal(L/F)` followed by `e`.  In the classical theory `e` is canonical,
coming from the local fundamental class; see `localInvariant_two_heq` for the case `n = 2`, where
canonicity is automatic. -/
noncomputable def localInvariant (R : NK.LocalArtin.ReciprocityMap F F')
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L] (n : ℕ)
    (e : (L ≃ₐ[F] L) ≃* Multiplicative (ZMod n)) : Fˣ →* Multiplicative (ZMod n) :=
  e.toMonoidHom.comp ((levelRestrict L).comp R.artin)

/-- The invariant map is the Artin map followed by the normalisation. -/
theorem localInvariant_apply (R : NK.LocalArtin.ReciprocityMap F F')
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L] (n : ℕ)
    (e : (L ≃ₐ[F] L) ≃* Multiplicative (ZMod n)) (x : Fˣ) :
    localInvariant R L n e x = e ((levelRestrict L) (R.artin x)) := rfl

/-- **The kernel of the invariant map is the norm group** (the level reciprocity law). -/
theorem localInvariant_ker (R : NK.LocalArtin.ReciprocityMap F F')
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L] (hcomm : ∀ σ τ : L ≃ₐ[F] L, σ * τ = τ * σ)
    (n : ℕ) (e : (L ≃ₐ[F] L) ≃* Multiplicative (ZMod n)) :
    MonoidHom.ker (localInvariant R L n e) = NK.LocalReciprocity.normGroup F ↥L := by
  have h := (R.isLevelIso L hcomm).2
  ext x
  rw [MonoidHom.mem_ker, localInvariant_apply, e.map_eq_one_iff,
    show NK.LocalReciprocity.normGroup F ↥L = NK.LocalArtin.normGroup F ↥L from rfl,
    ← h, MonoidHom.mem_ker]
  exact Iff.rfl

/-- **The invariant map is surjective** (the Artin map at the level is surjective, and the
normalisation is an isomorphism). -/
theorem localInvariant_surjective (R : NK.LocalArtin.ReciprocityMap F F')
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L] (hcomm : ∀ σ τ : L ≃ₐ[F] L, σ * τ = τ * σ)
    (n : ℕ) (e : (L ≃ₐ[F] L) ≃* Multiplicative (ZMod n)) :
    Function.Surjective (localInvariant R L n e) :=
  e.surjective.comp (fun g => by
    obtain ⟨x, hx⟩ := (R.isLevelIso L hcomm).1 (g : (↥L ≃ₐ[F] ↥L))
    exact ⟨x, hx⟩)

/-- **The invariant map induces the isomorphism `Fˣ ⧸ N_{L/F} Lˣ ≃* Multiplicative (ZMod n)`.**

This is the form in which the local invariant is used: it identifies the local Brauer group
`Br(L/F) ≃ Fˣ ⧸ N_{L/F} Lˣ` with `(1/n)ℤ/ℤ`. -/
noncomputable def localInvariantQuotientMulEquiv (R : NK.LocalArtin.ReciprocityMap F F')
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L] (hcomm : ∀ σ τ : L ≃ₐ[F] L, σ * τ = τ * σ)
    (n : ℕ) (e : (L ≃ₐ[F] L) ≃* Multiplicative (ZMod n)) :
    (Fˣ ⧸ NK.LocalReciprocity.normGroup F ↥L) ≃* Multiplicative (ZMod n) :=
  (R.artinLevelMulEquiv L hcomm).trans e

/-- The quotient isomorphism is the map induced on the quotient by the invariant map. -/
theorem localInvariantQuotientMulEquiv_mk (R : NK.LocalArtin.ReciprocityMap F F')
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L] (hcomm : ∀ σ τ : L ≃ₐ[F] L, σ * τ = τ * σ)
    (n : ℕ) (e : (L ≃ₐ[F] L) ≃* Multiplicative (ZMod n)) (x : Fˣ) :
    localInvariantQuotientMulEquiv R L hcomm n e (QuotientGroup.mk x) =
      localInvariant R L n e x := by
  rw [localInvariantQuotientMulEquiv, localInvariant, MulEquiv.trans_apply]
  congr 1

/-- **The invariant of an element is trivial exactly when the element is a norm** — the defining
property of the local invariant map (and the form consumed by Hilbert reciprocity). -/
theorem localInvariant_eq_one_iff (R : NK.LocalArtin.ReciprocityMap F F')
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L] (hcomm : ∀ σ τ : L ≃ₐ[F] L, σ * τ = τ * σ)
    (n : ℕ) (e : (L ≃ₐ[F] L) ≃* Multiplicative (ZMod n)) (x : Fˣ) :
    localInvariant R L n e x = 1 ↔ x ∈ NK.LocalReciprocity.normGroup F ↥L := by
  rw [← localInvariant_ker R L hcomm n e]
  exact MonoidHom.mem_ker

/-! ## Canonicity in the `2`-torsion case

For `n = 2` the normalisation is unique: `Multiplicative (ZMod 2)` has exactly one non-identity
element, so any two isomorphisms `Gal(L/F) ≃* Multiplicative (ZMod 2)` agree.  Hence the
`2`-torsion invariant map is canonical and `localInvariant` may be used with an arbitrary such
isomorphism. -/

/-- In `ZMod 2`, `1` is the unique non-zero element. -/
theorem zmod_two_eq_one_of_ne_zero : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide

/-- In `Multiplicative (ZMod 2)`, `ofAdd 1` is the unique non-identity element. -/
theorem mul_two_eq_ofAdd_one_of_ne_one (y : Multiplicative (ZMod 2)) (hy : y ≠ 1) :
    y = Multiplicative.ofAdd 1 := by
  have hne : Multiplicative.toAdd y ≠ 0 := by
    intro h0
    refine hy ?_
    have hyy : y = Multiplicative.ofAdd (Multiplicative.toAdd y) := rfl
    rw [hyy, h0]
    rfl
  have h : Multiplicative.toAdd y = 1 := zmod_two_eq_one_of_ne_zero _ hne
  rw [← h]
  rfl

/-- **Canonicity of the `2`-torsion invariant map**: two arbitrary normalisations of the same level
give the *same* invariant map.  Consequently the local invariant at a quadratic level is a
canonical invariant of the level, with no choice involved. -/
theorem localInvariant_two_heq (R : NK.LocalArtin.ReciprocityMap F F')
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L]
    (e₁ e₂ : (L ≃ₐ[F] L) ≃* Multiplicative (ZMod 2)) :
    localInvariant R L 2 e₁ = localInvariant R L 2 e₂ := by
  have h : e₁ = e₂ := by
    ext g
    by_cases hg : g = 1
    · subst hg
      simp
    · have h1 : e₁ g ≠ 1 := fun h0 => hg (e₁.injective (by rw [h0, map_one]))
      have h2 : e₂ g ≠ 1 := fun h0 => hg (e₂.injective (by rw [h0, map_one]))
      rw [mul_two_eq_ofAdd_one_of_ne_one _ h1, mul_two_eq_ofAdd_one_of_ne_one _ h2]
  rw [h]

end NK.NUV2.LC
