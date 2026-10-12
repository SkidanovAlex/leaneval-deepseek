import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseDict.Defs2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseDict.Defs3` — the first-quantised slot sum of a one-body operator

`Work.BoseB4.dGamma m T = Σ_{ij} (T e_j)_i · a_i† a_j` is the second quantisation of a
one-particle operator `T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)` (FS `lem:2ndQuand`).  Under the
dictionary, `dGamma m T` must become the **first-quantised** sum `Σ_j (T^♯)_j` where
`T^♯ = Σ_{ll'} T_{ll'} |η_{e_l}⟩⟨η_{e_{l'}}|` acts on `L²(Sp)`.  The slot-`j` action of the
rank-one piece `|η_w⟩⟨η_v|` is `Work.BoseDict.boxSlotOf e w v j`, so

    boxSlotSum e T Θ := Σ_j Σ_l Σ_{l'} (T (evec l'))_l • boxSlotOf e (evec l) (evec l') j Θ

is the first-quantised form of `T` on `Xn d → ℂ`, matching the corpus's `slotFormB`
(`Work.BoseKinLoc.Defs`) shape.  The dictionary identity is

    boxRealise e d (dGamma m T Ψ) = boxSlotSum e T (boxRealise e d Ψ)

for `Ψ` of degree `d` (`Work.BoseDict.boxRealise_dGamma`).
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The **first-quantised slot sum** of a one-body operator `T` on `Xn d → ℂ`:
`Σ_{j} Σ_{l,l'} (T e_{l'})_l • boxSlotOf e (evec l) (evec l') j Θ`. -/
noncomputable def boxSlotSum {m d : ℕ} (e : Fin m → Sp → ℂ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (Θ : Xn d → ℂ) : Xn d → ℂ :=
  ∑ j : Fin d, ∑ l : Fin m, ∑ l' : Fin m,
    T (Work.BoseB4.evec m l') l • boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ

end Work.BoseDict
