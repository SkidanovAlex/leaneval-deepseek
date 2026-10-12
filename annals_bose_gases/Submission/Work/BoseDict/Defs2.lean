import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseDict.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseDict.Defs2` — the general (superposition) box ladder operators

`Defs.lean` has the *mode-wise* box annihilation `boxAnn e l`.  The model's rows of
`H2ndF` use the superposed operators `annOf m w = Σ_l w_l ann m l` (and `creOf m w`),
so the dictionary needs the same superposition on the box side:

* `boxAnnOf e w d : (Xn (d+1) → ℂ) → (Xn d → ℂ)`, `(boxAnnOf e w d Θ)(y) =
  √(d+1) ∫_z conj(η_w z) Θ(z,y)`, `η_w = Σ_l w_l e_l`;
* `boxCreOf e w d : (Xn d → ℂ) → (Xn (d+1) → ℂ)`, the **symmetrised** creation
  `(boxCreOf e w d Θ)(x) = (1/√(d+1)) Σ_{j : Fin (d+1)} η_w(x_j) Θ(x ∖ j)`,
  where `x ∖ j := fun i => x (Fin.succAbove j i)`.  The symmetrisation is forced by
  the intertwining with the model's `cre`: at `d = 1` with `Ψ = x^{e_{l'}}`,
  `boxRealise e 2 (cre m l Ψ) = (1/√2)(e_l(x_0)e_{l'}(x_1) + e_{l'}(x_0)e_l(x_1))`,
  which is the *symmetrised* product, not `e_l(x_0)·e_{l'}(x_1)`;
* `boxCre e l d` — the mode-wise creation (`w = Pi.single l 1`);
* `boxSlotOf e w v j Θ`, the `j`-th slot of the first-quantised rank-one operator
  `|η_w⟩⟨η_v|`: `(boxSlotOf e w v j Θ)(x) = η_w(x_j) ∫_z conj(η_v z) Θ(x[j ↦ z])`, with
  `x[j ↦ z] = Function.update x j z`.  This is the shape in which the corpus writes the
  box's rows (`Work.BoseKinLoc.slotFormB`), so the identity
  `boxCreOf ∘ boxAnnOf = Σ_j boxSlotOf` (for symmetric `Θ`) is the
  "second quantisation = first quantisation" step of the dictionary.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The physical one-particle function with coordinate vector `w`: `η_w = Σ_l w_l e_l`. -/
noncomputable def etaOf {m : ℕ} (e : Fin m → Sp → ℂ) (w : Fin m → ℝ) : Sp → ℂ :=
  fun z => ∑ l : Fin m, (w l : ℂ) * e l z

/-- The box annihilation of the superposition `η_w`: `(d+1)`-particle functions to
`d`-particle functions, `(boxAnnOf e w d Θ)(y) = √(d+1) ∫_z conj(η_w z) Θ(z,y)`. -/
noncomputable def boxAnnOf {m : ℕ} (e : Fin m → Sp → ℂ) (w : Fin m → ℝ) (d : ℕ)
    (Θ : Xn (d + 1) → ℂ) : Xn d → ℂ :=
  fun y => (Real.sqrt ((d : ℝ) + 1) : ℂ) *
    ∫ z : Sp, (starRingEnd ℂ) (etaOf e w z) * Θ (Fin.cons z y)

/-- The box creation of the superposition `η_w`, **symmetrised**:
`(boxCreOf e w d Θ)(x) = (1/√(d+1)) Σ_{j : Fin (d+1)} η_w(x_j) Θ(x ∖ j)`. -/
noncomputable def boxCreOf {m : ℕ} (e : Fin m → Sp → ℂ) (w : Fin m → ℝ) (d : ℕ)
    (Θ : Xn d → ℂ) : Xn (d + 1) → ℂ :=
  fun x => (1 / (Real.sqrt ((d : ℝ) + 1) : ℂ)) *
    ∑ j : Fin (d + 1),
      etaOf e w (x j) * Θ (fun i : Fin d => x (Fin.succAbove j i))

/-- The box creation of the single mode `e l`. -/
noncomputable def boxCre {m : ℕ} (e : Fin m → Sp → ℂ) (l : Fin m) (d : ℕ)
    (Θ : Xn d → ℂ) : Xn (d + 1) → ℂ :=
  boxCreOf e (Pi.single l (1 : ℝ)) d Θ

/-- The `j`-th slot of the first-quantised rank-one operator `|η_w⟩⟨η_v|`:
`(boxSlotOf e w v j Θ)(x) = η_w(x_j) ∫_z conj(η_v z) Θ(x[j ↦ z])`. -/
noncomputable def boxSlotOf {m d : ℕ} (e : Fin m → Sp → ℂ) (w v : Fin m → ℝ) (j : Fin d)
    (Θ : Xn d → ℂ) : Xn d → ℂ :=
  fun x => etaOf e w (x j) *
    ∫ z : Sp, (starRingEnd ℂ) (etaOf e v z) * Θ (Function.update x j z)

end Work.BoseDict
