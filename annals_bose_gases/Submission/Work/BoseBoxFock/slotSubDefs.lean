import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.sectorSliceDefs
import Submission.Work.BoseDict.Defs3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.slotSubDefs` — the `↥S`-indexed slot operators of the BF3c decoupling

`Work.BoseDict.boxSlotOf e w v j` is the slot-`j` (`j : Fin d`) operator of the one-body rank-one
form `|η_w⟩⟨η_v|`, and `boxSlotSum e T = Σ_{j : Fin d} Σ_{l l'} T_{l'l} • boxSlotOf e l l' j`
is its slot sum.  The BF3c fibre selection
(`FINDING_BF3c_selection_s8.md` §1, `FINDING_BF3c_realcomplex_RESOLUTION.md` §3.2) needs the same
operators *restricted to the `S`-slots* of a sector state, acting on the slice
`Work.BoseBoxFock.sectorSlice e S Φ y`, whose variables are `↥S → Ω`.

This module therefore carries the two definitions of that restriction
(`slotOfSub`, `slotSumSub`, arbitrary index type), which differ from the `BoseDict` ones only in
the index type of the slot.  The decoupling identity itself is the delegated lemma
`Work.BoseBoxFock.slotSum_sectorPointwise`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The slot-`j` operator of the rank-one one-body form `|η_w⟩⟨η_v|`, for an arbitrary index
type of slots (the `Fin d` version is `Work.BoseDict.boxSlotOf`). -/
noncomputable def slotOfSub {m : ℕ} (e : Fin m → Ω → ℂ) (w v : Fin m → ℝ)
    {ι : Type*} [DecidableEq ι] (j : ι) (Θ : (ι → Ω) → ℂ) : (ι → Ω) → ℂ :=
  fun x => Work.BoseDict.etaOf e w (x j) *
    ∫ z : Ω, (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) * Θ (Function.update x j z)

/-- The `S`-slot part of `Work.BoseDict.boxSlotSum e T`, acting on `↥S`-indexed functions:
`Σ_{j : ↥S} Σ_{l l'} T_{l'l} • slotOfSub e l l' j`. -/
noncomputable def slotSumSub {m n : ℕ} (e : Fin m → Ω → ℂ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (S : Finset (Fin n))
    (Θ : ({i // i ∈ S} → Ω) → ℂ) : ({i // i ∈ S} → Ω) → ℂ :=
  ∑ j : {i // i ∈ S}, ∑ l : Fin m, ∑ l' : Fin m,
    T (Work.BoseB4.evec m l') l
      • slotOfSub e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ

end Work.BoseBoxFock
