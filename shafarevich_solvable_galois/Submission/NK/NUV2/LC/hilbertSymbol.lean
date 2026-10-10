import Mathlib.Computability.Language
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Complex.Polynomial.Basic
import Submission.NK.NUV2.LC.invariantMap
import Submission.NK.NUV2.LC.quadraticLevel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Hilbert symbol at `p = 2`

For a field `F` with Galois extension `F'`, an element `b ∈ Fˣ`, a square root `y ∈ F'` of `b`, and a
reciprocity datum `R : NK.LocalArtin.ReciprocityMap F F'` (in the application `F = κ` a `p`-adic
field and `R` produced from `hKC`), this file defines the classical **Hilbert symbol** `(a,b)` at
`p = 2`:

  `(a,b) = 1`  iff  `a` is a norm from `F(√b)`,

i.e. the value of the local invariant map `inv_{F(√b)/F}` on `a`.  Because the values lie in
`Multiplicative (ZMod 2)`, the symbol is *canonical*: the normalisation of the local invariant map is
vacuous at `p = 2` (`NK.NUV2.LC.localInvariant_two_heq`), so no choice of a normalising isomorphism
into `Mul (ZMod 2)` is needed — the *only* information is whether the Artin image is trivial.  This
also disposes of the degenerate case in which `b` is a square (where `F(√b) = F` and no such
isomorphism exists at all).

## Contents

* `quadLevel_card_le_two` — the Galois group of `F(√b)` has at most two elements;
* `quadLevelRestrict` — the Artin map to the quadratic level;
* `hilbertSymbolAt R y b hy a` — the symbol for a given square root `y`;
* `hilbertSymbolAt_apply`, `hilbertSymbolAt_eq_one_iff` — unfolding and the norm criterion
  `(a,b) = 1 ↔ a ∈ N_{F(√b)/F}F(√b)ˣ`;
* `hilbertSymbolAt_mul` — multiplicativity in the first variable (formal, from the reciprocity law);
* `hilbertSymbolAt_self_mul_left` — `(a²,b) = 1`;
* `sqroot`, `sqroot_mul_self`, `hilbertSymbol` — the canonical square root in a separable closure
  and the resulting canonical symbol.

The genuinely arithmetic statements — symmetry `(a,b) = (b,a)`, multiplicativity in the *second*
variable, and the independence of the symbol from the chosen square root — are delegated.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped Classical

namespace NK.NUV2.LC

section Symbol

variable {F : Type*} {F' : Type*} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']
variable [NeZero (2 : F)]

/-- The Galois group of the quadratic level `F(√b)` has at most two elements. -/
theorem quadLevel_card_le_two (y : F') (b : F) (hy : y * y = algebraMap F F' b) :
    Nat.card (↥(quadLevel y b hy) ≃ₐ[F] ↥(quadLevel y b hy)) ≤ 2 := by
  haveI := quadLevel_finiteDimensional y b hy
  haveI := quadLevel_normal y b hy
  haveI : IsGalois F ↥(quadLevel y b hy) :=
    IsGalois.mk (to_isSeparable := inferInstance) (to_normal := quadLevel_normal y b hy)
  rw [IsGalois.card_aut_eq_finrank F ↥(quadLevel y b hy)]
  exact quadLevel_finrank_le_two y b hy

/-- **The Artin map to the quadratic level `F(√b)`**, `Gal(F^{ab}/F) →* Gal(F(√b)/F)`. -/
noncomputable def quadLevelRestrict (y : F') (b : F) (hy : y * y = algebraMap F F' b) :
    NK.LocalCFT.AbGal F F' →* (↥(quadLevel y b hy) ≃ₐ[F] ↥(quadLevel y b hy)) :=
  haveI := quadLevel_normal y b hy
  NK.LocalCFT.levelRestrict (quadLevel y b hy)

/-- **The Hilbert symbol `(a,b)` at `p = 2`**, for a given square root `y` of `b`: the value of the
local invariant map `inv_{F(√b)/F}` on `a`, written multiplicatively in `Mul (ZMod 2)`. -/
noncomputable def hilbertSymbolAt (R : NK.LocalArtin.ReciprocityMap F F') (y : F') (b : F)
    (hy : y * y = algebraMap F F' b) (a : Fˣ) : Multiplicative (ZMod 2) :=
  if quadLevelRestrict y b hy (R.artin a) = 1 then 1 else Multiplicative.ofAdd 1

/-- Unfolding lemma for the Hilbert symbol. -/
theorem hilbertSymbolAt_apply (R : NK.LocalArtin.ReciprocityMap F F') (y : F') (b : F)
    (hy : y * y = algebraMap F F' b) (a : Fˣ) :
    hilbertSymbolAt R y b hy a =
      (if quadLevelRestrict y b hy (R.artin a) = 1 then 1
        else Multiplicative.ofAdd (1 : ZMod 2)) := rfl

/-- The non-trivial element of `Mul (ZMod 2)`. -/
theorem ofAdd_one_ne_one_zmod_two : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide

/-- Every element of `Mul (ZMod 2)` is an involution. -/
theorem mul_self_eq_one_zmod_two (u : Multiplicative (ZMod 2)) : u * u = 1 := by
  fin_cases u <;> decide

/-- **The norm criterion**: `(a,b) = 1` exactly when `a` is a norm from `F(√b)`.  This is the
defining property of the local invariant map, and it is what the product formula consumes. -/
theorem hilbertSymbolAt_eq_one_iff (R : NK.LocalArtin.ReciprocityMap F F') (y : F') (b : F)
    (hy : y * y = algebraMap F F' b) (a : Fˣ) :
    hilbertSymbolAt R y b hy a = 1 ↔
      a ∈ NK.LocalReciprocity.normGroup F ↥(quadLevel y b hy) := by
  haveI : FiniteDimensional F ↥(quadLevel y b hy) := quadLevel_finiteDimensional y b hy
  haveI : Normal F ↥(quadLevel y b hy) := quadLevel_normal y b hy
  have hker := (R.isLevelIso (quadLevel y b hy) (quadLevel_commutative y b hy)).2
  have hker' : MonoidHom.ker ((quadLevelRestrict y b hy).comp R.artin) =
      NK.LocalReciprocity.normGroup F ↥(quadLevel y b hy) := hker
  rw [hilbertSymbolAt_apply]
  by_cases h : quadLevelRestrict y b hy (R.artin a) = 1
  · rw [if_pos h]
    exact ⟨fun _ => by rw [← hker', MonoidHom.mem_ker]; exact h, fun _ => rfl⟩
  · rw [if_neg h]
    refine ⟨fun hh => absurd hh ofAdd_one_ne_one_zmod_two, fun hh => absurd ?_ h⟩
    have h1 : ((quadLevelRestrict y b hy).comp R.artin) a = 1 := by
      rw [← MonoidHom.mem_ker, hker']
      exact hh
    simpa using h1

/-- **Multiplicativity in the first variable.**  The first variable enters through the Artin map, so
this is a formal consequence of the reciprocity law: the symbol is a character in `a`. -/
theorem hilbertSymbolAt_mul (R : NK.LocalArtin.ReciprocityMap F F') (y : F') (b : F)
    (hy : y * y = algebraMap F F' b) (a a' : Fˣ) :
    hilbertSymbolAt R y b hy (a * a') =
      hilbertSymbolAt R y b hy a * hilbertSymbolAt R y b hy a' := by
  haveI : Finite (↥(quadLevel y b hy) ≃ₐ[F] ↥(quadLevel y b hy)) := by
    haveI := quadLevel_finiteDimensional y b hy
    infer_instance
  have hcard := quadLevel_card_le_two y b hy
  have hmul : quadLevelRestrict y b hy (R.artin (a * a')) =
      quadLevelRestrict y b hy (R.artin a) * quadLevelRestrict y b hy (R.artin a') := by
    rw [map_mul, map_mul]
  rw [hilbertSymbolAt_apply, hilbertSymbolAt_apply, hilbertSymbolAt_apply]
  by_cases ha : quadLevelRestrict y b hy (R.artin a) = 1
  · by_cases ha' : quadLevelRestrict y b hy (R.artin a') = 1
    · have hA : quadLevelRestrict y b hy (R.artin (a * a')) = 1 := by
        rw [hmul, ha, ha', one_mul]
      rw [if_pos hA, if_pos ha, if_pos ha']
      simp
    · have hA : quadLevelRestrict y b hy (R.artin (a * a')) ≠ 1 := by
        rw [hmul, ha, one_mul]; exact ha'
      rw [if_neg hA, if_pos ha, if_neg ha']
      simp
  · by_cases ha' : quadLevelRestrict y b hy (R.artin a') = 1
    · have hA : quadLevelRestrict y b hy (R.artin (a * a')) ≠ 1 := by
        rw [hmul, ha', mul_one]; exact ha
      rw [if_neg hA, if_neg ha, if_pos ha']
      simp
    · have heq : quadLevelRestrict y b hy (R.artin a) =
          quadLevelRestrict y b hy (R.artin a') := eq_of_ne_one_of_card_le_two hcard ha ha'
      have hsq : quadLevelRestrict y b hy (R.artin a) *
          quadLevelRestrict y b hy (R.artin a) = 1 :=
        mul_self_eq_one_of_card_le_two hcard _
      have hA : quadLevelRestrict y b hy (R.artin (a * a')) = 1 := by
        rw [hmul, ← heq]; exact hsq
      rw [if_pos hA, if_neg ha, if_neg ha', mul_self_eq_one_zmod_two]

/-- `(a², b) = 1`: a square is always a norm. -/
theorem hilbertSymbolAt_self_mul_left (R : NK.LocalArtin.ReciprocityMap F F') (y : F') (b : F)
    (hy : y * y = algebraMap F F' b) (a : Fˣ) :
    hilbertSymbolAt R y b hy (a * a) = 1 := by
  rw [hilbertSymbolAt_mul, mul_self_eq_one_zmod_two]

end Symbol

section Canonical

variable {F : Type*} {F' : Type*} [Field F] [Field F'] [Algebra F F'] [IsSepClosure F F']
variable [NeZero (2 : F)]

/-- A square root of `b` exists in the separable closure. -/
theorem exists_sqroot (b : Fˣ) : ∃ y : F', y * y = algebraMap F F' b := by
  haveI h2 : NeZero (2 : F') := by
    refine ⟨fun h => (NeZero.ne (2 : F)) ?_⟩
    have hmap : algebraMap F F' (2 : F) = 0 := by
      rw [show algebraMap F F' (2 : F) = (2 : F') from map_ofNat _ 2, h]
    exact (algebraMap F F').injective (hmap.trans (map_zero _).symm)
  haveI : IsSepClosed F' := IsSepClosure.sep_closed F
  obtain ⟨z, hz⟩ := IsSepClosed.exists_eq_mul_self (algebraMap F F' (b : F))
  exact ⟨z, hz.symm⟩

/-- A chosen square root of `b` in the separable closure. -/
noncomputable def sqroot (b : Fˣ) : F' := Classical.choose (exists_sqroot b)

/-- The defining property of the chosen square root. -/
theorem sqroot_mul_self (b : Fˣ) : sqroot b * sqroot b = algebraMap F F' b :=
  Classical.choose_spec (exists_sqroot b)

/-- **The canonical Hilbert symbol at `p = 2`**, with the square root chosen in the separable
closure. -/
noncomputable def hilbertSymbol (R : NK.LocalArtin.ReciprocityMap F F') (a b : Fˣ) :
    Multiplicative (ZMod 2) :=
  hilbertSymbolAt R (sqroot b) (b : F) (sqroot_mul_self b) a

end Canonical

section Real

/-- **`ℂ` is a separable closure of `ℝ`** (it is separably closed, and `ℝ → ℂ` is separable since
`ℝ` has characteristic `0`).  Bound as a theorem rather than a global instance; use
`attribute [local instance] NK.NUV2.LC.isSepClosure_real_complex` where needed. -/
theorem isSepClosure_real_complex : IsSepClosure ℝ ℂ :=
  ⟨inferInstance, inferInstance⟩

end Real

end NK.NUV2.LC
