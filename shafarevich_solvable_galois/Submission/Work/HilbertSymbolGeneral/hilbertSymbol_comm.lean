import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.HilbertSymbolGeneral.exists_eq_add_mul_quadGen
import Submission.Work.HilbertSymbolGeneral.exists_sq_sub_mul_sq_comm
import Submission.Work.HilbertSymbolGeneral.quadLevel_finrank_eq_two_of_notMem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Symmetry of the canonical `2`-adic Hilbert symbol

This file proves `Work.HilbertSymbolGeneral.hilbertSymbol_comm`: for a field `F` with a separable
closure `F'` and a local reciprocity datum `R`, the canonical Hilbert symbol
`(a,b) = NK.NUV2.LC.hilbertSymbol R a b` is symmetric.

The route is the classical one.  By the norm criterion
(`NK.NUV2.LC.hilbertSymbol_eq_one_iff_normGroup`), `(a,b) = 1` says that `a` is a norm from
`F(√b)`; for the quadratic level `F(√b)` this is the same as saying that `a` is represented by the
norm form `X ^ 2 - b * Y ^ 2`:

  `a ∈ N_{F(√b)/F} F(√b)ˣ ↔ ∃ u v : F, u ^ 2 - b * v ^ 2 = a`

(`mem_normGroup_quadLevel_iff`, proved here with the help of `quadGen` from `Gens.lean` and the
quadratic-norm formula `NK.NUV2.QuadFaithful.norm_algebraMap_add_mul`).  The two solvability
statements `∃ u v, u ^ 2 - b * v ^ 2 = a` and `∃ u v, u ^ 2 - a * v ^ 2 = b` are interchanged by
`u ↦ u / v`, `v ↦ 1 / v` (and trivially when `a` or `b` is a square), so `(a,b) = 1 ↔ (b,a) = 1`;
as both values lie in the two-element group `Multiplicative (ZMod 2)`, equality of the "`= 1`"
predicates gives `(a,b) = (b,a)`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open scoped Classical

namespace Work.HilbertSymbolGeneral

/-- **The norm group of the trivial intermediate field is everything**: the norm of `F` over itself
is the identity. -/
theorem normGroup_bot_eq_top {F E : Type*} [Field F] [Field E] [Algebra F E] :
    NK.LocalReciprocity.normGroup F ↥(⊥ : IntermediateField F E) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro x
  rw [NK.LocalReciprocity.mem_normGroup_iff]
  refine ⟨Units.mk0 (algebraMap F ↥(⊥ : IntermediateField F E) (x : F)) ?_, ?_⟩
  · intro h
    exact Units.ne_zero x
      ((algebraMap F ↥(⊥ : IntermediateField F E)).injective (by rw [h, map_zero]))
  · rw [Units.val_mk0, Algebra.norm_algebraMap, IntermediateField.finrank_bot, pow_one]

section Aux

variable {F : Type*} {F' : Type*} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']
variable [NeZero (2 : F)]

/-- **The quadratic level is trivial when the square root is a base-field element.** -/
theorem quadLevel_eq_bot_of_mem_range (y : F') (b : F) (hy : y * y = algebraMap F F' b)
    (hx : y ∈ Set.range (algebraMap F F')) : NK.NUV2.LC.quadLevel y b hy = ⊥ := by
  obtain ⟨s, hs⟩ := hx
  refine bot_unique ?_
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro z hz
  rw [Set.mem_singleton_iff] at hz
  rw [hz]
  exact IntermediateField.mem_bot.mpr ⟨s, by
    apply Subtype.ext
    simpa using hs⟩

/-- **An explicit representation of a unit by the norm form when the coefficient is a square**:
for `b = s * s` with `s ≠ 0`, the unit `a` is represented by `X ^ 2 - b * Y ^ 2`, namely by
`X = (a + 1) / 2`, `Y = (a - 1) / (2 * s)`. -/
theorem exists_sq_sub_mul_sq_of_sq (a : Fˣ) {b s : F} (hss : s * s = b) (hs : s ≠ 0) :
    ∃ u v : F, u ^ 2 - b * v ^ 2 = (a : F) := by
  have h2 : (2 : F) ≠ 0 := NeZero.ne 2
  refine ⟨((a : F) + 1) / 2, ((a : F) - 1) / (2 * s), ?_⟩
  rw [← hss]
  field_simp
  ring

end Aux

section Main

variable {F : Type*} {F' : Type*} [Field F] [Field F'] [Algebra F F'] [IsSepClosure F F']
variable [NeZero (2 : F)]

/-- **The norm group of the quadratic level `F(√b)`.**  For `b ≠ 0` and any square root `y` of `b`,
a unit `a` is a norm from `F(√b)` if and only if it is represented by the norm form
`u ^ 2 - b * v ^ 2`. -/
theorem mem_normGroup_quadLevel_iff (y : F') (b : F) (hb : b ≠ 0)
    (hy : y * y = algebraMap F F' b) (a : Fˣ) :
    a ∈ NK.LocalReciprocity.normGroup F ↥(NK.NUV2.LC.quadLevel y b hy) ↔
      ∃ u v : F, u ^ 2 - b * v ^ 2 = (a : F) := by
  by_cases hx : y ∈ Set.range (algebraMap F F')
  · -- `b` is a square in `F`: the level is trivial and every unit is a norm
    obtain ⟨s, hs⟩ := hx
    have hss : s * s = b := (algebraMap F F').injective (by simp only [map_mul, hs, hy])
    have hs0 : s ≠ 0 := fun h => hb (by rw [← hss, h, mul_zero])
    have hbot : NK.NUV2.LC.quadLevel y b hy = ⊥ := quadLevel_eq_bot_of_mem_range y b hy ⟨s, hs⟩
    constructor
    · intro _
      exact exists_sq_sub_mul_sq_of_sq a hss hs0
    · intro _
      rw [hbot, normGroup_bot_eq_top]
      trivial
  · -- `y` is not a base-field element: `F(√b)` is quadratic with basis `1, quadGen`
    haveI : FiniteDimensional F ↥(NK.NUV2.LC.quadLevel y b hy) :=
      NK.NUV2.LC.quadLevel_finiteDimensional y b hy
    haveI : Normal F ↥(NK.NUV2.LC.quadLevel y b hy) := NK.NUV2.LC.quadLevel_normal y b hy
    haveI : IsGalois F ↥(NK.NUV2.LC.quadLevel y b hy) :=
      IsGalois.mk (to_isSeparable := inferInstance)
        (to_normal := NK.NUV2.LC.quadLevel_normal y b hy)
    have hdim : Module.finrank F ↥(NK.NUV2.LC.quadLevel y b hy) = 2 :=
      quadLevel_finrank_eq_two_of_notMem y b hy hx
    have hgen_not : quadGen y b hy ∉
        Set.range (algebraMap F ↥(NK.NUV2.LC.quadLevel y b hy)) :=
      quadGen_notMem_range y b hy hx
    have hgen_sq : (quadGen y b hy) ^ 2 =
        algebraMap F ↥(NK.NUV2.LC.quadLevel y b hy) b := by
      rw [pow_two]
      exact quadGen_mul_self y b hy
    have hnorm : ∀ u v : F, Algebra.norm F
        (algebraMap F ↥(NK.NUV2.LC.quadLevel y b hy) u +
          algebraMap F ↥(NK.NUV2.LC.quadLevel y b hy) v * quadGen y b hy) =
        u ^ 2 - b * v ^ 2 :=
      fun u v => NK.NUV2.QuadFaithful.norm_algebraMap_add_mul hdim hgen_not hgen_sq u v
    constructor
    · intro ha
      obtain ⟨w, hw⟩ := (NK.LocalReciprocity.mem_normGroup_iff a).mp ha
      obtain ⟨u, v, huv⟩ := exists_eq_add_mul_quadGen y b hy hx (w : ↥(NK.NUV2.LC.quadLevel y b hy))
      refine ⟨u, v, ?_⟩
      have h1 : Algebra.norm F (w : ↥(NK.NUV2.LC.quadLevel y b hy)) = u ^ 2 - b * v ^ 2 := by
        rw [huv]
        exact hnorm u v
      rw [← hw, h1]
    · rintro ⟨u, v, huv⟩
      have hwne : algebraMap F ↥(NK.NUV2.LC.quadLevel y b hy) u +
          algebraMap F ↥(NK.NUV2.LC.quadLevel y b hy) v * quadGen y b hy ≠ 0 := by
        intro hW
        have h1 : Algebra.norm F (algebraMap F ↥(NK.NUV2.LC.quadLevel y b hy) u +
            algebraMap F ↥(NK.NUV2.LC.quadLevel y b hy) v * quadGen y b hy) = 0 := by
          rw [hW]
          exact Algebra.norm_zero
        rw [hnorm u v] at h1
        exact Units.ne_zero a (by rw [← huv, h1])
      rw [NK.LocalReciprocity.mem_normGroup_iff]
      refine ⟨Units.mk0 _ hwne, ?_⟩
      rw [Units.val_mk0, hnorm u v, huv]

end Main

section Sym

variable {F : Type*} {F' : Type*} [Field F] [Field F'] [Algebra F F'] [IsSepClosure F F']
variable [NeZero (2 : F)]

/-- In the two-element group `Multiplicative (ZMod 2)`, two elements whose "`= 1`" predicates are
equivalent are equal. -/
theorem eq_of_eq_one_iff_eq_one {x y : Multiplicative (ZMod 2)} (h : x = 1 ↔ y = 1) : x = y := by
  have key : ∀ z : Multiplicative (ZMod 2), z ≠ 1 → z = Multiplicative.ofAdd (1 : ZMod 2) := by
    decide
  by_cases hx : x = 1
  · rw [hx, h.mp hx]
  · rw [key x hx, key y fun hy => hx (h.mpr hy)]

/-- The value `(a,b) = 1` is exactly the representability of `a` by the norm form `X² - b Y²`. -/
theorem hilbertSymbol_eq_one_iff_form (R : NK.LocalArtin.ReciprocityMap F F') (a b : Fˣ) :
    NK.NUV2.LC.hilbertSymbol R a b = 1 ↔
      ∃ u v : F, u ^ 2 - (b : F) * v ^ 2 = (a : F) := by
  rw [NK.NUV2.LC.hilbertSymbol_eq_one_iff_normGroup]
  constructor
  · rintro ⟨y, hy, hm⟩
    exact (mem_normGroup_quadLevel_iff y (b : F) (Units.ne_zero b) hy a).mp hm
  · rintro ⟨u, v, huv⟩
    exact ⟨NK.NUV2.LC.sqroot b, NK.NUV2.LC.sqroot_mul_self b,
      (mem_normGroup_quadLevel_iff _ (b : F) (Units.ne_zero b) _ a).mpr ⟨u, v, huv⟩⟩

end Sym

/-- **Symmetry of the canonical `2`-adic Hilbert symbol.**

For a field `F` with separable closure `F'` and a local reciprocity datum `R`
(`NK.LocalArtin.ReciprocityMap F F'`), the canonical Hilbert symbol
`(a,b) = NK.NUV2.LC.hilbertSymbol R a b` — the value of the local invariant map `inv_{F(√b)/F}`
on `a`, which is normalised canonically at `2` because all values lie in `Multiplicative (ZMod 2)`
— is symmetric: `(a,b) = (b,a)`. -/
theorem hilbertSymbol_comm {F : Type*} {F' : Type*} [Field F] [Field F'] [Algebra F F']
    [IsSepClosure F F'] [NeZero (2 : F)] (R : NK.LocalArtin.ReciprocityMap F F') (a b : Fˣ) :
    NK.NUV2.LC.hilbertSymbol R a b = NK.NUV2.LC.hilbertSymbol R b a := by
  refine eq_of_eq_one_iff_eq_one ?_
  rw [hilbertSymbol_eq_one_iff_form R a b, hilbertSymbol_eq_one_iff_form R b a]
  exact exists_sq_sub_mul_sq_comm a b

end Work.HilbertSymbolGeneral
