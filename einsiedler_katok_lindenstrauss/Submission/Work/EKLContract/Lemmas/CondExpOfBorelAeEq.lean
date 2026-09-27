import Mathlib

/-!
# Conditional expectation against a σ-algebra that agrees `ν`-a.e. with the ambient one

## Why this file contains two statements

The statement requested under the name `CondExpOfBorelAeEq` is

```
(𝔪 : MeasurableSpace α) (hle : 𝔪 ≤ mα) (ν : MeasureTheory.Measure α) [IsFiniteMeasure ν]
(f : α → ℝ) (hfm : Measurable f) (hfbdd : ∃ C, ∀ y, |f y| ≤ C)
(h : ∀ B, MeasurableSet B → ∃ S, @MeasurableSet α 𝔪 S ∧ ν (symmDiff B S) = 0) :
  ∀ᵐ x ∂ν, condExp 𝔪 ν f x = f x
```

where `mα` is the *ambient* `MeasurableSpace α` instance.  The σ-algebra arguments of
`Measurable f`, `MeasurableSet B` and `Measure α` are all implicit there, and **Lean's typeclass
search resolves such implicit instance arguments by searching the local context of the
declaration itself**, which contains the bound variable `𝔪 : MeasurableSpace α` — itself a local
hypothesis of class type.  That hypothesis is captured (this is the hazard diagnosed and worked
around in `Submission/Work/EKLContract/Defs.lean`, in the `NOTE` on `IsLeafwise.condexp`).  So the
statement above, *as elaborated*, is the statement about the measurable space `𝔪`:

```
ν : Measure[𝔪] α,  hfm : Measurable[𝔪] f,  h : ∀ B, MeasurableSet[𝔪] B → ...
```

i.e. `ν` is a measure on `𝔪`, `f` is `𝔪`-measurable, `hle : 𝔪 ≤ mα` is unused, and `h` is
satisfied by `S = B`.  That statement is true and is proved below, but it is **not** the intended
content.  The intended content is the statement in which the ambient σ-algebra is `mα`: `ν` is a
measure on `mα`, `f` is `mα`-measurable, and `h` says that every `mα`-measurable set is `ν`-a.e.
equal to an `𝔪`-measurable set — this is what
`Work.EKLContract.Lemmas.BorelAeEqOfAtoms` produces for a *Borel* measure `ν`, and it is what is
needed e.g. to discharge the `condexp` field of `IsLeafwise`.  It is recorded, with every
σ-algebra written explicitly, as `CondExpOfBorelAeEq_intended` below.  **If you are looking for a
lemma about a Borel measure `ν`, use `CondExpOfBorelAeEq_intended`.**

Both statements are the same clause, `CondExpOfBorelAeEq` being the specialisation `mα := 𝔪`
(and its proof below is literally that instantiation).

## The argument

`f` is integrable (it is bounded and `ν` is finite), and `condExp 𝔪 ν f` is integrable, so by the
uniqueness of the conditional expectation
(`Integrable.ae_eq_of_forall_setIntegral_eq`) it suffices to compare the integrals over every
measurable set of finite measure.  For such a set `B` the hypothesis gives an `𝔪`-measurable `S`
with `ν (B ∆ S) = 0`, and then

  `∫_B condExp = ∫_S condExp = ∫_S f = ∫_B f`,

by `setIntegral_congr_set` (the sets agree `ν`-a.e.) and `setIntegral_condExp` (the defining
property of the conditional expectation over an `𝔪`-measurable set).
-/

namespace Work.EKLContract.Lemmas

/-- **The intended statement**, with every `MeasurableSpace` argument made explicit: `ν` is a
measure on the ambient σ-algebra `mα`, the function `f` is `mα`-measurable and bounded, and every
`mα`-measurable set is `ν`-almost everywhere equal to an `𝔪`-measurable set.  Then `f` is its own
conditional expectation with respect to the sub-σ-algebra `𝔪`. -/
theorem CondExpOfBorelAeEq_intended {α : Type*} [mα : MeasurableSpace α]
    (𝔪 : MeasurableSpace α) (hle : 𝔪 ≤ mα) (ν : @MeasureTheory.Measure α mα)
    [MeasureTheory.IsFiniteMeasure ν] (f : α → ℝ) (hfm : @Measurable α ℝ mα Real.measurableSpace f)
    (hfbdd : ∃ C, ∀ y, |f y| ≤ C)
    (h : ∀ B : Set α, @MeasurableSet α mα B →
      ∃ S : Set α, @MeasurableSet α 𝔪 S ∧ ν (symmDiff B S) = 0) :
    ∀ᵐ x ∂ν, @MeasureTheory.condExp α ℝ 𝔪 mα _ _ ν f x = f x := by
  obtain ⟨C, hC⟩ := hfbdd
  have hfi : MeasureTheory.Integrable f ν :=
    MeasureTheory.Integrable.of_bound hfm.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => by simpa using hC x)
  refine MeasureTheory.Integrable.ae_eq_of_forall_setIntegral_eq
    (MeasureTheory.condExp 𝔪 ν f) f MeasureTheory.integrable_condExp hfi ?_
  intro s hs _
  obtain ⟨S, hS𝔪, hSν⟩ := h s hs
  have hse : s =ᵐ[ν] S := MeasureTheory.measure_symmDiff_eq_zero_iff.mp hSν
  have h1 : ∫ x in s, MeasureTheory.condExp 𝔪 ν f x ∂ν
      = ∫ x in S, MeasureTheory.condExp 𝔪 ν f x ∂ν :=
    MeasureTheory.setIntegral_congr_set hse
  have h2 : ∫ x in S, MeasureTheory.condExp 𝔪 ν f x ∂ν = ∫ x in S, f x ∂ν :=
    MeasureTheory.setIntegral_condExp hle hfi hS𝔪
  have h3 : ∫ x in S, f x ∂ν = ∫ x in s, f x ∂ν :=
    (MeasureTheory.setIntegral_congr_set hse).symm
  exact h1.trans (h2.trans h3)

-- The statement below is frozen and has `hle : 𝔪 ≤ mα` as a hypothesis which is unused (the
-- ambient σ-algebra captured by its implicit instance arguments is `𝔪` itself, see the module
-- docstring).  Silence the corresponding linter, which would otherwise fire on this one binder.
set_option linter.unusedVariables false in
/-- **As requested.**  See the module docstring: on elaboration the ambient `MeasurableSpace α`
instance of this declaration is the bound variable `𝔪`, so here `ν` is a measure on `𝔪`, `f` is
`𝔪`-measurable, `h` ranges over `𝔪`-measurable sets and `hle` is unused (it is kept because the
statement is frozen).  This statement is the specialisation `mα := 𝔪` of
`CondExpOfBorelAeEq_intended` above, which is also how it is proved. -/
theorem CondExpOfBorelAeEq {α : Type*} [mα : MeasurableSpace α]
    (𝔪 : MeasurableSpace α) (hle : 𝔪 ≤ mα) (ν : MeasureTheory.Measure α)
    [MeasureTheory.IsFiniteMeasure ν] (f : α → ℝ) (hfm : Measurable f) (hfbdd : ∃ C, ∀ y, |f y| ≤ C)
    (h : ∀ B : Set α, MeasurableSet B → ∃ S : Set α, @MeasurableSet α 𝔪 S ∧ ν (symmDiff B S) = 0) :
    ∀ᵐ x ∂ν, MeasureTheory.condExp 𝔪 ν f x = f x := by
  -- the ambient σ-algebra of this declaration is `𝔪`, so this is
  -- `CondExpOfBorelAeEq_intended` specialised to `mα := 𝔪`
  exact CondExpOfBorelAeEq_intended 𝔪 le_rfl ν f hfm hfbdd h

end Work.EKLContract.Lemmas
