import Submission.NK.NUV2.LC.invariantMap
import Submission.NK.GlobalCFT.Place
import Submission.NK.GlobalCFT.Idele

/-!
# The `2`-torsion local invariant and Hilbert reciprocity at `p = 2`

This is the second piece of the invariant-map chapter (see `NOTES_invariantMap.md`): the
**`p = 2` global product formula** — Hilbert reciprocity in the only case the Neukirch–Uchida
route consumes, where it is *canonical* (no normalisation, no fundamental class, no invariant map
in the classical sense).

## The local symbol

For a field `F` with Galois extension `F'` and a **quadratic** abelian level `L ≤ F^ab`
(`Nat.card (L ≃ₐ[F] L) = 2`), the invariant map `localInvariant R L 2 e` is *independent of the
normalisation* `e` (`localInvariant_two_heq`), so it is a canonical invariant of the level:

  `localInvariantTwo R L e : Fˣ →* Multiplicative (ZMod 2)`,

the classical "(·, L/F)" -symbol: `x ↦ 1` iff `x` is a norm from `L`, `x ↦ -1` otherwise
(`localInvariantTwo_eq_one_iff`).  Basic properties proved here: independence of `e`, the norm
criterion, and the vanishing on squares (`localInvariantTwo_sq`), i.e. the classical bilinearity
`(a²,b) = 1` which makes the symbol a `2`-torsion pairing.

## The global statement

`NK.NUV2.LC.IsLocalNorm K L x v` says that `x ∈ Kˣ` is a norm from `L ⊗ K_v` at the place `v`
of `K`; `NK.NUV2.LC.HilbertReciprocityTwo` is the classical product formula for quadratic
extensions of number fields:

  **for a quadratic `L/K` and `x ∈ Kˣ`, the set of places `v` of `K` at which `x` is not a local
  norm is finite and has even cardinality.**

(Equivalently `∏_v (x, L/K)_v = 1`: each bad place contributes `-1`, so the product is `1` exactly
when the number of bad places is even.)  The corollaries recorded below are the forms in which the
statement is consumed: the bad set is never a *singleton* (`HilbertReciprocityTwo.not_singleton`),
i.e. **"a single place of local-norm failure is no failure at all"** — Milne, *CFT*, VIII.2
Example 2.2(ii).

## The road (the sub-pieces to be delegated)

The classical proof of `HilbertReciprocityTwo` proceeds by four independent steps:

1. **multiplicativity**: `(a₁a₂, b)_v = (a₁,b)_v (a₂,b)_v` and `(a,b₁b₂)_v = (a,b₁)_v (a,b₂)_v`;
2. **the tower/norm formula**: `(N_{K_v(√b)/K_v} y, b)_v = 1` and the general base-change rule,
   from the norm/Verlagerung square `NK.LocalArtin.Transfer.exists_normTransfer`;
3. **the reduction to rational symbols**: express a general symbol as a product of symbols of
   rational elements (via the tower formula and multiplicativity);
4. **quadratic reciprocity over `ℚ`**: `∏_v (a,b)_v = 1` for `a b ∈ ℚˣ` (Gauss's reciprocity law
   plus the supplementary laws, i.e. the classical table of Hilbert symbols over `ℚ_p`).

Steps 1 and 2 are local and independent of the global set-up; 3 and 4 are global but only over
`ℚ`.  None of them depends on the general class-formation machinery.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField

open NK.GlobalCFT
open NumberField IsDedekindDomain

namespace NK.NUV2.LC

variable {F : Type*} {F' : Type*} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']

/-! ## The canonical `2`-torsion local invariant -/

/-- **The canonical `2`-torsion local invariant at a quadratic abelian level**: the invariant map
`Fˣ →* Multiplicative (ZMod 2)` of a quadratic level `L ≤ F^ab`.  It is independent of the
normalisation `e` (`localInvariantTwo_congr`), so `e` is a dummy argument. -/
noncomputable def localInvariantTwo (R : NK.LocalArtin.ReciprocityMap F F')
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L]
    (e : (L ≃ₐ[F] L) ≃* Multiplicative (ZMod 2)) : Fˣ →* Multiplicative (ZMod 2) :=
  localInvariant R L 2 e

/-- **The `2`-torsion local invariant is independent of the normalisation.** -/
theorem localInvariantTwo_congr (R : NK.LocalArtin.ReciprocityMap F F')
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L]
    (e₁ e₂ : (L ≃ₐ[F] L) ≃* Multiplicative (ZMod 2)) :
    localInvariantTwo R L e₁ = localInvariantTwo R L e₂ :=
  localInvariant_two_heq R L e₁ e₂

/-- **The norm criterion**: the `2`-torsion local invariant is trivial exactly on the norms. -/
theorem localInvariantTwo_eq_one_iff (R : NK.LocalArtin.ReciprocityMap F F')
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L] (hcomm : ∀ σ τ : L ≃ₐ[F] L, σ * τ = τ * σ)
    (e : (L ≃ₐ[F] L) ≃* Multiplicative (ZMod 2)) (x : Fˣ) :
    localInvariantTwo R L e x = 1 ↔ x ∈ NK.LocalReciprocity.normGroup F ↥L :=
  localInvariant_eq_one_iff R L hcomm 2 e x

/-- In `Multiplicative (ZMod 2)` every element has order dividing `2`. -/
theorem mul_self_eq_one_two : ∀ y : Multiplicative (ZMod 2), y * y = 1 := by decide

/-- **The local invariant is a `2`-torsion pairing in its first variable**: squares have trivial
invariant.  Classically `(a², b) = 1`, the form of bilinearity that Hilbert reciprocity uses. -/
theorem localInvariantTwo_sq (R : NK.LocalArtin.ReciprocityMap F F')
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L]
    (e : (L ≃ₐ[F] L) ≃* Multiplicative (ZMod 2)) (x : Fˣ) :
    localInvariantTwo R L e (x * x) = 1 := by
  rw [map_mul]
  exact mul_self_eq_one_two _

/-! ## The local-norm condition at a place of a number field -/

/-- The canonical map `Kˣ →* K_vˣ` to the completion at a place. -/
noncomputable def localIncl (K : Type*) [Field K] [NumberField K]
    (v : NK.GlobalCFT.Place K) : Kˣ →* (NK.GlobalCFT.Place.localField K v)ˣ :=
  Units.map (algebraMap K (NK.GlobalCFT.Place.localField K v)).toMonoidHom

/-- **`x` is a local norm at the place `v`**: the image of `x` in `K_vˣ` lies in the image of the
local norm `N_{L_w/K_v} : L_wˣ →* K_vˣ` for a place `w` of `L` above `v`. -/
noncomputable def IsLocalNorm (K : Type*) [Field K] [NumberField K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (x : Kˣ) (v : NK.GlobalCFT.Place K) : Prop :=
  match v with
  | Sum.inl w => ∃ (w' : InfinitePlace L) (h : w'.LiesOver w),
      localIncl K (NK.GlobalCFT.Place.ofInfinite w) x ∈
        (NK.GlobalCFT.Place.localNormInfinite (K := K) (L := L) w' w).range
  | Sum.inr Q => ∃ (q : HeightOneSpectrum (𝓞 L)) (h : q.asIdeal.LiesOver Q.asIdeal),
      localIncl K (NK.GlobalCFT.Place.ofFinite Q) x ∈
        (NK.GlobalCFT.Place.localNormFinite (K := K) (L := L) q Q h).range

/-! ## Hilbert reciprocity at `p = 2` -/

/-- **Hilbert reciprocity for quadratic extensions of number fields** (the `p = 2` product formula):
for a quadratic `L/K` and `x ∈ Kˣ`, the set of places of `K` at which `x` is not a local norm is
finite with even cardinality.

Equivalently `∏_v (x, L_w/K_v)_v = 1`: with the canonical `2`-torsion invariant of
`localInvariantTwo`, a bad place contributes `-1` and a good place contributes `1`.

The classical proof has four independent steps — multiplicativity, the tower/norm formula, the
reduction to rational symbols, and quadratic reciprocity over `ℚ`; see the module docstring. -/
def HilbertReciprocityTwo : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L], Nat.card (L ≃ₐ[K] L) = 2 →
    ∀ x : Kˣ, ∃ s : Finset (NK.GlobalCFT.Place K),
      (∀ v, v ∈ s ↔ ¬ IsLocalNorm K L x v) ∧ Even s.card

namespace HilbertReciprocityTwo

/-- **"One place of local-norm failure is no failure at all"**: for a quadratic `L/K` and `x ∈ Kˣ`,
if `x` is a local norm at every place except possibly one, then it is a local norm at every place.

This is the form in which the statement enters the Hasse principle
(Milne, *CFT*, VIII.2 Example 2.2(ii)). -/
theorem eq_empty_of_subset_singleton (h : HilbertReciprocityTwo)
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (h2 : Nat.card (L ≃ₐ[K] L) = 2) (x : Kˣ)
    (v₀ : NK.GlobalCFT.Place K)
    (hv : ∀ v, v ≠ v₀ → IsLocalNorm K L x v) :
    ∀ v, IsLocalNorm K L x v := by
  classical
  obtain ⟨s, hs, heven⟩ := h K L h2 x
  have hsub : ∀ v ∈ s, v = v₀ := by
    intro v hv'
    by_contra hne
    exact (hs v).mp hv' (hv v hne)
  rcases Finset.eq_empty_or_nonempty s with hse | ⟨v, hv'⟩
  · intro v
    by_contra hbad
    exact Finset.notMem_empty v (hse ▸ (hs v).mpr hbad)
  · exfalso
    have hcard : s.card = 1 := by
      refine le_antisymm (Finset.card_le_one.mpr fun a ha b hb => by rw [hsub a ha, hsub b hb])
        (Finset.card_pos.mpr ⟨v, hv'⟩)
    rw [hcard] at heven
    norm_num at heven

end HilbertReciprocityTwo

end NK.NUV2.LC
