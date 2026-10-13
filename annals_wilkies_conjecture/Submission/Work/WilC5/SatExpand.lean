/-
  WilC5 — the gadget for expanding a structure along an injection of constant sets.

  Given an `L[[C]]`-structure `N` and an injection `inc : C → C'`, we build an `L[[C']]`-structure
  on the same carrier whose `L`-part agrees with `N`'s and whose constants are interpreted by a
  prescribed function `w : C' → N` on the new constants and by `N`'s values on the old ones.
  This is what turns a model of the specification at a lower level into a model of the
  specification at a higher level (the new constants are interpreted as witnesses).

  The `IsExpansionOn` statement and the realization lemmas for this expansion are delegated to
  `Submission/Work/WilC5/SatExpansion.lean` (`Work.WilC5.SatExpand_model`).
-/
import Mathlib
import Submission.Work.WilC5.SatSetup

open FirstOrder Language
open scoped FirstOrder

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilC5

/-- The value of an `L[[C]]`-constant in a structure. -/
noncomputable def SatConVal (L : FirstOrder.Language.{0, 0}) (C : Type) (N : Type)
    [(L[[C]]).Structure N] (c : C) : N :=
  @Structure.funMap (L[[C]]) N inferInstance 0 (Sum.inr c) default

/-- The interpretation function for the constants of `L[[C']]` in the expansion of an
`L[[C]]`-structure along `inc : C → C'`; the constants outside the range of `inc` get the
prescribed values `w`. -/
noncomputable def SatExpVal (L : FirstOrder.Language.{0, 0}) (C C' : Type) (inc : C → C')
    (hinc : Function.Injective inc) (N : Type) [(L[[C]]).Structure N] (w : C' → N) : C' → N :=
  fun c' => if h : ∃ c, inc c = c' then SatConVal L C N h.choose else w c'

theorem SatExpVal_inc (L : FirstOrder.Language.{0, 0}) (C C' : Type) (inc : C → C')
    (hinc : Function.Injective inc) (N : Type) [(L[[C]]).Structure N] (w : C' → N) (c : C) :
    SatExpVal L C C' inc hinc N w (inc c) = SatConVal L C N c := by
  have h₀ : ∃ c', inc c' = inc c := ⟨c, rfl⟩
  rw [SatExpVal, dif_pos h₀]
  exact congrArg (SatConVal L C N) (hinc h₀.choose_spec)

theorem SatExpVal_notMem (L : FirstOrder.Language.{0, 0}) (C C' : Type) (inc : C → C')
    (hinc : Function.Injective inc) (N : Type) [(L[[C]]).Structure N] (w : C' → N) (c' : C')
    (h : ∀ c, inc c ≠ c') : SatExpVal L C C' inc hinc N w c' = w c' := by
  rw [SatExpVal, dite_eq_right]
  rintro ⟨c, hc⟩
  exact h c hc

/-- The `L`-reduct of an `L[[C]]`-structure. -/
@[instance_reducible]
noncomputable def SatLeftStruct (L : FirstOrder.Language.{0, 0}) (C : Type) (N : Type)
    [(L[[C]]).Structure N] : L.Structure N where
  funMap := fun {n} f xs => @Structure.funMap (L[[C]]) N inferInstance n (Sum.inl f) xs
  RelMap := fun {n} R xs => @Structure.RelMap (L[[C]]) N inferInstance n (Sum.inl R) xs

/-- The expansion of an `L[[C]]`-structure `N` to the language `L[[C']]` along an injection
`inc : C → C'`, with prescribed values `w` for the new constants. -/
@[instance_reducible]
noncomputable def SatExpansion (L : FirstOrder.Language.{0, 0}) (C C' : Type) (inc : C → C')
    (hinc : Function.Injective inc) (N : Type) [(L[[C]]).Structure N] (w : C' → N) :
    (L[[C']]).Structure N :=
  letI : L.Structure N := SatLeftStruct L C N
  letI : (constantsOn C').Structure N := constantsOn.structure (SatExpVal L C C' inc hinc N w)
  sumStructure L (constantsOn C') N

@[simp]
theorem SatExpansion_const (L : FirstOrder.Language.{0, 0}) (C C' : Type) (inc : C → C')
    (hinc : Function.Injective inc) (N : Type) [(L[[C]]).Structure N] (w : C' → N) {β : Type}
    (c' : C') (ρ : β → N) :
    @Term.realize (L[[C']]) N (SatExpansion L C C' inc hinc N w) β ρ
      (Constants.term (Sum.inr c') : (L[[C']]).Term β) =
    SatExpVal L C C' inc hinc N w c' := rfl

/-- The old constants keep their values in the expansion. -/
@[simp]
theorem SatExpansion_old (L : FirstOrder.Language.{0, 0}) (C C' : Type) (inc : C → C')
    (hinc : Function.Injective inc) (N : Type) [(L[[C]]).Structure N] (w : C' → N) {β : Type}
    (c : C) (ρ : β → N) :
    @Term.realize (L[[C']]) N (SatExpansion L C C' inc hinc N w) β ρ
      (Constants.term (Sum.inr (inc c)) : (L[[C']]).Term β) =
    SatConVal L C N c := by
  rw [SatExpansion_const, SatExpVal_inc]

end Work.WilC5
