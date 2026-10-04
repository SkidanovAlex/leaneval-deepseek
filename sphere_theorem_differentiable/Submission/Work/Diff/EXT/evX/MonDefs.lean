import Mathlib
import Submission.Work.Diff.EXT.evX.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The monomial of a binary word

`Work.Diff.EXT.evX.Monε g n ε e` is the packed monomial of the word `ε : Fin n → Bool` at level `n`:
the contraction of `rmSym (∇^a Rm) (∇^b Rm)` (with `a = cntT n ε`, `b = cntF n ε`) in the frame field
`e` with the tuple, where the `r`-th derivative slot of the first (resp. second) factor is the tuple
position `map₁ n ε r` (resp. `map₂ n ε r`) and the four `reactionMap`-slots sit at `sPos n t`.
-/

set_option linter.unusedSectionVars false

namespace Work.Diff.EXT.evX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The packed monomial of the word `ε` at level `n`. -/
noncomputable def Monε (g : Submission.Diff.SMet I M) (n : ℕ) (ε : Fin n → Bool)
    (e : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M)) :
    (Fin (4 + n) → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ :=
  Work.Diff.EXT.MonoD (I := I) (M := M) g (4 + n) (cntT n ε) (cntF n ε) (map₁ n ε) (map₂ n ε)
    (sPos n) e

end Work.Diff.EXT.evX
