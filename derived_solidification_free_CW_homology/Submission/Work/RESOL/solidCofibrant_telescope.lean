import Mathlib
import Submission.Work.RESOL.Basic
import Submission.Work.RESOL.B5Telescope

/-!
AREA RESOL — the mapping telescope of a sequence of solid-cofibrant complexes is
solid-cofibrant (the last ingredient of B5, `RESOL/DESIGN.md` §3).

The telescope of `X` along `i` is `telescope X i = mappingCone (𝟙 (∐ X) - telescopeShift X i)`
(`RESOL/B5Telescope.lean`).  It is the third object of the distinguished triangle of a morphism
`∐ X ⟶ ∐ X` in `K(LightCondAb)` (`CochainComplex.mappingCone.triangleh`), so the closure
properties of `CofibrantClosure` give the result in three steps:

* `hC.sigma` applied to the family `X` gives `SolidCofibrant (∐ X)`.  The hypothesis `hX` is
  stated for all shifts, so in particular for the zero shift; the shift-`0` functor is
  isomorphic to the identity (`CategoryTheory.shiftFunctorZero`), and `hC.iso` transports the
  statement back along that isomorphism.
* `hC.shift` upgrades this to all shifts of `∐ X`, which is what the cone axiom needs.
* `hC.cone` applied to the distinguished triangle of `𝟙 (∐ X) - telescopeShift X i` gives
  `SolidCofibrantH` of its third object, which *is* `hq (telescope X i)` by definition.
-/

open CategoryTheory Limits

namespace Work.RESOL

/-- The `m`-th term `X m` of a sequence whose every shift is solid-cofibrant is solid-cofibrant:
the zero shift is isomorphic to the identity, and solid-cofibrancy is invariant under isomorphism
in `K(LightCondAb)` (`CofibrantClosure.iso`). -/
theorem solidCofibrant_of_shifts (hC : Work.RESOL.CofibrantClosure) (X : ℕ → Work.RESOL.Cpx)
    (hX : ∀ (m : ℕ) (n : ℤ),
      Submission.Blueprint.SolidCofibrant ((CategoryTheory.shiftFunctor Work.RESOL.Cpx n).obj (X m)))
    (m : ℕ) : Submission.Blueprint.SolidCofibrant (X m) :=
  hC.iso ((HomotopyCategory.quotient LightCondAb (ComplexShape.up ℤ)).mapIso
    ((CategoryTheory.shiftFunctorZero Work.RESOL.Cpx ℤ).app (X m))) (hX m 0)

theorem solidCofibrant_telescope (hC : Work.RESOL.CofibrantClosure) (X : ℕ → Work.RESOL.Cpx)
    [CategoryTheory.Limits.HasCoproduct X]
    (i : ∀ m : ℕ, X m ⟶ X (m + 1))
    (hX : ∀ (m : ℕ) (n : ℤ),
      Submission.Blueprint.SolidCofibrant ((CategoryTheory.shiftFunctor Work.RESOL.Cpx n).obj (X m))) :
    Submission.Blueprint.SolidCofibrant (Work.RESOL.telescope X i) := by
  -- the coproduct `∐ X` is solid-cofibrant
  have hsig : Submission.Blueprint.SolidCofibrant (∐ X) :=
    hC.sigma ℕ X (fun m => solidCofibrant_of_shifts hC X hX m)
  have h1 : Work.RESOL.SolidCofibrantH (Submission.Blueprint.hq (∐ X)) := hsig
  -- the telescope is the third object of the distinguished triangle of `1 - shift`
  exact hC.cone (CochainComplex.mappingCone.triangleh (𝟙 (∐ X) - Work.RESOL.telescopeShift X i))
    (HomotopyCategory.mappingCone_triangleh_distinguished _)
    (fun n => hC.shift n _ h1) (fun n => hC.shift n _ h1)

end Work.RESOL
