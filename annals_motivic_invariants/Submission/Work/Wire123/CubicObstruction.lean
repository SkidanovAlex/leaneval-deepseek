import Submission.Work.Wire123.CohomologicalObstruction

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.Wire123.CubicObstruction` — the old `G₂` cubic interface was refutable, and the repaired one

**The finding.**  The first version of `Work.G2.CubicInput` (`G2/Defs.lean`, still quoted below as
`legacyCubicInput`) asserted the well-definedness of the cubic self-intersection as a clause about a
**fieldless** class `Work.G2.CubicSelfIntersection 𝕜 X n`: since a class with no fields is inhabited
at every `n`, that clause reduced to `n = m` for arbitrary `n, m : ℤ`, hence to `0 = 1`.  The type
was therefore **empty** (`not_legacyCubicInput`), and every reduction taking it as a hypothesis —
`Work.CY3Stab.theorem_1_2_3_of_G2`, `Work.G2.not_gen_of_G2_infiniteField`,
`Work.G2.CY3DatumZ.toCY3Input` — was uninstantiable *whatever* geometry was built
(`not_usable_G2_reduction`).

**The repair (landed in `G2/Defs.lean`).**  `Work.G2.CubicInput 𝕜` now *supplies the function*
`cubic : (X) → [Variety 𝕜 X] → ℤ` together with `cubic_iso` (invariance under `IsoOver`), and the
two computed values `14`, `42` are hypotheses about that function at the centres of a model (they
were fields `Work.G2.CY3DatumZ.cubic_Z`, `cubic_Z'` of that model, and have since been **deleted**
in the authorised repair: see `Verdict.lean` and `NOTES.md` §12).  The
statements of `not_isoOver_of_cubic`, `CY3DatumZ.notIso`, `toCY3Input`, `toCY3Link` and of
`Work.CY3Stab.theorem_1_2_3_of_G2` are **unchanged**; only the two proofs inside `G2/` changed.

**The repaired interface is inhabited and can carry the two values**:

* `Work.Wire123.nonempty_cubicInput` — the constant-`0` function inhabits it (so it cannot be
  refuted by inhabitance, unlike the legacy one);
* `Work.Wire123.exists_cubicInput_values` — with `𝔸⁰` and `𝔸¹` (non-isomorphic over `𝕜`, and
  stably birational: `Work.Wire123.not_isoOver_affineSpace_zero_one`), there is a `CubicInput` whose
  values there are `14` and `42`.  So the *hypothesis pair* `(C, values)` that `lem-nSBG2` consumes
  is consistent — as it must be, since the paper's `G₂` model realises it with the dual numbers
  computing `14 ≠ 42`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.Wire123

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-! ## 1. The legacy interface, and its refutation -/

/-- The **legacy** predicate of `G2/Defs.lean`: a class with no fields. -/
class legacyCubicSelfIntersection (𝕜 : Type) [Field 𝕜] (X : Scheme.{0}) [Variety 𝕜 X]
    (n : ℤ) : Prop

/-- The **legacy** `Work.G2.CubicInput`: the interface in which the well-definedness of `c₁(M|_X)³`
was asserted about the fieldless predicate above. -/
structure legacyCubicInput (𝕜 : Type) [Field 𝕜] : Prop where
  unique : ∀ (X : Scheme.{0}) [Variety 𝕜 X] {n m : ℤ},
    legacyCubicSelfIntersection 𝕜 X n → legacyCubicSelfIntersection 𝕜 X m → n = m
  eq_of_isoOver : ∀ {X Y : Scheme.{0}} [Variety 𝕜 X] [Variety 𝕜 Y],
    Work.CY3.IsoOver 𝕜 X Y → ∀ {n : ℤ},
    legacyCubicSelfIntersection 𝕜 X n → legacyCubicSelfIntersection 𝕜 Y n

/-- `legacyCubicSelfIntersection` is inhabited at every value of `n`: it has no fields. -/
theorem legacyCubicSelfIntersection_holds (X : Scheme.{0}) [Variety 𝕜 X] (n : ℤ) :
    legacyCubicSelfIntersection 𝕜 X n := ⟨⟩

/-- **The legacy interface is refutable** (the finding of the first round of this area): its
`unique` clause, applied to the affine line at the values `0` and `1`, gives `0 = 1`. -/
theorem not_legacyCubicInput : ¬ legacyCubicInput 𝕜 := fun C =>
  (by norm_num : (0 : ℤ) ≠ 1)
    (C.unique (X := Work.CY3.Affine 𝕜 1) (n := 0) (m := 1) ⟨⟩ ⟨⟩)

/-- Consequently the legacy type is empty — nothing taking it can ever be applied. -/
theorem not_nonempty_legacyCubicInput : ¬ Nonempty (legacyCubicInput 𝕜) :=
  fun ⟨C⟩ => not_legacyCubicInput C

/-- **Both `G₂`-level reductions of the challenge are unusable with the legacy interface**: the
passage from the `ℤ`-model to the CY3 chapter's input (`Work.G2.CY3DatumZ.toCY3Input`) and the
challenge-level reductions (`Work.G2.not_gen_of_G2_infiniteField`,
`Work.CY3Stab.theorem_1_2_3_of_G2`) all take `(C : CubicInput 𝕜)`, an argument of an empty type in
the legacy interface.  (With the repaired interface they are usable: see §2 and
`Work.Wire123.not_gen_of_G2_of_cubicInput`.) -/
theorem not_usable_G2_reduction : ¬ ∃ C : legacyCubicInput 𝕜, True :=
  fun ⟨C, _⟩ => not_legacyCubicInput C

/-! ## 2. The repaired interface is inhabited and can carry the two values -/

/-- **The repaired `Work.G2.CubicInput 𝕜` is inhabited** (the constant-`0` function): unlike the
legacy interface it cannot be refuted by inhabitance. -/
theorem nonempty_cubicInput : Nonempty (Work.G2.CubicInput 𝕜) :=
  ⟨{ cubic := fun X _ => 0
     cubic_iso := fun _ => rfl }⟩

/-- **The repaired interface can carry the two values at a non-isomorphic pair**: on `𝔸⁰`, `𝔸¹`
(non-isomorphic over `𝕜` by `Work.Wire123.not_isoOver_affineSpace_zero_one`) there is a
`Work.G2.CubicInput` whose cubic self-intersections are `14` and `42`.  So the hypothesis pair that
`lem-nSBG2` consumes is *consistent*: the repaired input is exactly the data the paper's model
provides. -/
theorem exists_cubicInput_values :
    ∃ (C : Work.G2.CubicInput 𝕜) (X Y : Scheme.{0}) (_ : Variety 𝕜 X) (_ : Variety 𝕜 Y),
      C.cubic X = 14 ∧ C.cubic Y = 42 ∧ ¬ Work.CY3.IsoOver 𝕜 X Y := by
  classical
  -- the function is constant on the isomorphism class of each of the two test varieties
  let f : (X : Scheme.{0}) → [Variety 𝕜 X] → ℤ := fun X _ =>
    if Nonempty (Work.CY3.IsoOver 𝕜 X (A0 𝕜)) then
      (if Nonempty (Work.CY3.IsoOver 𝕜 X (A1 𝕜)) then 0 else 14)
    else
      (if Nonempty (Work.CY3.IsoOver 𝕜 X (A1 𝕜)) then 42 else 0)
  have hf : ∀ {X Y : Scheme.{0}} [Variety 𝕜 X] [Variety 𝕜 Y],
      Work.CY3.IsoOver 𝕜 X Y → f X = f Y := by
    intro X Y _ _ h
    have h₀ : Nonempty (Work.CY3.IsoOver 𝕜 X (A0 𝕜)) ↔
        Nonempty (Work.CY3.IsoOver 𝕜 Y (A0 𝕜)) :=
      ⟨fun ⟨e⟩ => ⟨Work.CY3.IsoOver.trans (Work.CY3.IsoOver.symm h) e⟩,
        fun ⟨e⟩ => ⟨Work.CY3.IsoOver.trans h e⟩⟩
    have h₁ : Nonempty (Work.CY3.IsoOver 𝕜 X (A1 𝕜)) ↔
        Nonempty (Work.CY3.IsoOver 𝕜 Y (A1 𝕜)) :=
      ⟨fun ⟨e⟩ => ⟨Work.CY3.IsoOver.trans (Work.CY3.IsoOver.symm h) e⟩,
        fun ⟨e⟩ => ⟨Work.CY3.IsoOver.trans h e⟩⟩
    simp only [f, h₀, h₁]
  have hA0 : f (A0 𝕜) = 14 := by
    have h1 : Nonempty (Work.CY3.IsoOver 𝕜 (A0 𝕜) (A0 𝕜)) :=
      ⟨Work.CY3.IsoOver.refl 𝕜 (A0 𝕜)⟩
    have h2 : ¬ Nonempty (Work.CY3.IsoOver 𝕜 (A0 𝕜) (A1 𝕜)) :=
      fun h => not_isoOver_affineSpace_zero_one 𝕜 h.some
    dsimp only [f]
    rw [if_pos h1, if_neg h2]
  have hA1 : f (A1 𝕜) = 42 := by
    have h1 : ¬ Nonempty (Work.CY3.IsoOver 𝕜 (A1 𝕜) (A0 𝕜)) :=
      fun h => not_isoOver_affineSpace_zero_one 𝕜 (Work.CY3.IsoOver.symm h.some)
    have h2 : Nonempty (Work.CY3.IsoOver 𝕜 (A1 𝕜) (A1 𝕜)) :=
      ⟨Work.CY3.IsoOver.refl 𝕜 (A1 𝕜)⟩
    dsimp only [f]
    rw [if_neg h1, if_pos h2]
  exact ⟨⟨f, hf⟩, A0 𝕜, A1 𝕜, inferInstance, inferInstance, hA0, hA1,
    not_isoOver_affineSpace_zero_one 𝕜⟩

end

end Work.Wire123
