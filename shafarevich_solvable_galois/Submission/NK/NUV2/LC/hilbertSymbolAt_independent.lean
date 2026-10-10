import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.NUV2.LC.hilbertSymbol
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Independence of the Hilbert symbol at `p = 2` from the chosen square root

`NK.NUV2.LC.hilbertSymbolAt R y b hy a` is the Hilbert symbol `(a,b) = inv_{F(√b)/F}(a)` at
`p = 2`, computed from a *chosen* square root `y` of `b` inside the Galois extension `F'/F`:

  `hilbertSymbolAt R y b hy a = 1`  iff  the Artin image `R.artin a` acts trivially on `F(√b)`.

The symbol is a priori a function of the pair `(b, y)`, not of `b` alone.  This file proves that it
is in fact independent of the choice of `y`, so that the canonical symbol
`NK.NUV2.LC.hilbertSymbol` (with the square root chosen in a separable closure) is well defined —
this is the missing piece needed to state the *two-variable* Hilbert symbol `(a,b)` at `p = 2`.

## The mathematics

If `y` and `y'` are both square roots of `b` in `F'`, then `y'² = y²`, i.e. `(y' - y)(y' + y) = 0`,
so in the field `F'` we have `y' = y` or `y' = -y`.  (No hypothesis on `2` is needed: the two roots
are simply `±y`.)  Passing to the maximal abelian subextension `F^{ab} = maxAbelianSubext F F'`,
which contains both roots (`mem_maxAbelianSubext_of_sq`), the intermediate fields `F(y)` and
`F(y')` agree:

* `y' = y` is immediate;
* `y' = -y`: `-y ∈ F(y)` and `-(-y) = y ∈ F(-y)`, so the adjoins coincide
  (`adjoin_singleton_neg`).

Since `levelRestrict L σ = 1 ↔ ∀ x ∈ L, σ x = x`, the restriction of `R.artin a` to the level
`F(√b)` is trivial regardless of which square root is used, and the value of the symbol follows
(it is a function of that condition alone).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped Classical

namespace NK.NUV2.LC

section General

/-- **In a field, two elements with the same square are equal or opposite.** -/
theorem eq_or_eq_neg_of_mul_self_eq {K : Type*} [Field K] {x y : K} (h : y * y = x * x) :
    y = x ∨ y = -x := by
  have h' : (y - x) * (y + x) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h1 | h2
  · exact Or.inl (sub_eq_zero.mp h1)
  · exact Or.inr (by rw [add_eq_zero_iff_eq_neg] at h2; exact h2)

/-- **Adjoining `x` and adjoining `-x` give the same field.** -/
theorem adjoin_singleton_neg {K L : Type*} [Field K] [Field L] [Algebra K L] (x : L) :
    IntermediateField.adjoin K ({x} : Set L) = IntermediateField.adjoin K ({-x} : Set L) := by
  have h1 : x ∈ (IntermediateField.adjoin K ({-x} : Set L)) := by
    have h := neg_mem (IntermediateField.subset_adjoin K ({-x} : Set L) (Set.mem_singleton (-x)))
    simpa using h
  have h2 : -x ∈ (IntermediateField.adjoin K ({x} : Set L)) :=
    neg_mem (IntermediateField.subset_adjoin K ({x} : Set L) (Set.mem_singleton x))
  exact le_antisymm (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr h1))
    (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr h2))

end General

section QuadLevel

variable {F : Type*} {F' : Type*} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']
variable [NeZero (2 : F)]

/-- The quadratic level `F(√b)` is the `F`-adjoin of the chosen square root, by definition. -/
theorem quadLevel_eq_adjoin (y : F') (b : F) (hy : y * y = algebraMap F F' b) :
    quadLevel y b hy = IntermediateField.adjoin F
      ({⟨y, mem_maxAbelianSubext_of_sq y b hy⟩} :
        Set (NK.LocalReciprocity.maxAbelianSubext F F')) := rfl

/-- **The quadratic level `F(√b)` is independent of the chosen square root.** -/
theorem quadLevel_eq_of_mul_self_eq (y y' : F') (b : F)
    (hy : y * y = algebraMap F F' b) (hy' : y' * y' = algebraMap F F' b) :
    quadLevel y b hy = quadLevel y' b hy' := by
  -- both roots satisfy `Y * Y = Y' * Y'` in `F^{ab}`
  have hmul : (⟨y, mem_maxAbelianSubext_of_sq y b hy⟩ :
        NK.LocalReciprocity.maxAbelianSubext F F') *
      ⟨y, mem_maxAbelianSubext_of_sq y b hy⟩ =
      ⟨y', mem_maxAbelianSubext_of_sq y' b hy'⟩ * ⟨y', mem_maxAbelianSubext_of_sq y' b hy'⟩ := by
    rw [quadLevel_coe_mul_self y b hy, quadLevel_coe_mul_self y' b hy']
  rw [quadLevel_eq_adjoin y b hy, quadLevel_eq_adjoin y' b hy']
  rcases eq_or_eq_neg_of_mul_self_eq hmul with h | h
  · -- `√b = √b'`: the two adjoins are literally equal
    rw [h]
  · -- `√b = -√b'`: the two adjoins agree because `x` and `-x` generate the same field
    have hY : (⟨y', mem_maxAbelianSubext_of_sq y' b hy'⟩ :
        NK.LocalReciprocity.maxAbelianSubext F F') =
        -⟨y, mem_maxAbelianSubext_of_sq y b hy⟩ := by rw [h]; simp
    rw [hY]
    exact adjoin_singleton_neg (K := F) _

/-- **Restriction to a level depends only on the level.**  For two normal levels `L`, `L'` of
`F^{ab}` with the same underlying set, `levelRestrict L σ` is trivial if and only if
`levelRestrict L' σ` is.  (The `Normal F L` instances are explicit arguments, since they are not
canonical: `L` is an arbitrary level of the maximal abelian subextension.) -/
theorem levelRestrict_eq_one_congr
    {L L' : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F')}
    [Normal F L] [Normal F L'] (hL : L = L') (σ : NK.LocalCFT.AbGal F F') :
    NK.LocalCFT.levelRestrict L σ = 1 ↔ NK.LocalCFT.levelRestrict L' σ = 1 := by
  subst hL
  exact Iff.rfl

/-- **The restriction to the quadratic level `F(√b)` is trivial independently of the square root
used to define it.** -/
theorem quadLevelRestrict_eq_one_congr {y y' : F'} {b : F}
    (hy : y * y = algebraMap F F' b) (hy' : y' * y' = algebraMap F F' b)
    (hL : quadLevel y b hy = quadLevel y' b hy') (σ : NK.LocalCFT.AbGal F F') :
    quadLevelRestrict y b hy σ = 1 ↔ quadLevelRestrict y' b hy' σ = 1 := by
  haveI h1 : Normal F ↥(quadLevel y b hy) := quadLevel_normal y b hy
  haveI h2 : Normal F ↥(quadLevel y' b hy') := quadLevel_normal y' b hy'
  have key := levelRestrict_eq_one_congr (L := quadLevel y b hy) (L' := quadLevel y' b hy') hL σ
  show (@NK.LocalCFT.levelRestrict F F' _ _ _ _ (quadLevel y b hy)
        (quadLevel_normal y b hy) σ = 1) ↔
      (@NK.LocalCFT.levelRestrict F F' _ _ _ _ (quadLevel y' b hy')
        (quadLevel_normal y' b hy') σ = 1)
  exact key

end QuadLevel

/-- **The Hilbert symbol `(a,b)` at `p = 2` does not depend on the square root of `b` used to
define it.** -/
theorem hilbertSymbolAt_independent {F F' : Type*} [Field F] [Field F'] [Algebra F F']
    [IsGalois F F'] [NeZero (2 : F)] (R : NK.LocalArtin.ReciprocityMap F F')
    {y y' : F'} {b : F} (hy : y * y = algebraMap F F' b)
    (hy' : y' * y' = algebraMap F F' b) (a : Fˣ) :
    NK.NUV2.LC.hilbertSymbolAt R y b hy a = NK.NUV2.LC.hilbertSymbolAt R y' b hy' a := by
  have hL : quadLevel y b hy = quadLevel y' b hy' := quadLevel_eq_of_mul_self_eq y y' b hy hy'
  have hiff : quadLevelRestrict y b hy (R.artin a) = 1 ↔
      quadLevelRestrict y' b hy' (R.artin a) = 1 :=
    quadLevelRestrict_eq_one_congr hy hy' hL (R.artin a)
  rw [hilbertSymbolAt_apply, hilbertSymbolAt_apply, hiff]

end NK.NUV2.LC
