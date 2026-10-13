import Mathlib
import Submission.Work.WilkiesH.Count.Interface
import Submission.Work.WilkiesH.Count.Defs
import Submission.Work.WilkiesH.Count.step
import Submission.Work.WilkiesH.Count.CountBoundDim_zero
import Submission.Work.WilkiesH.Count.countBoundDim_of_cube
import Submission.Work.WilkiesH.Count.chartCover_of_interp
import Submission.Work.WilkiesH.Strat.Defs

/-!
# Area H (counting) — the dimension induction assembled

`countBoundDim_all_of` is the final assembly of the counting induction of BNZ §6: given

* `hcd : S.SharpCD` — the sharp cell decomposition of the structure (only used for the base
  case of the induction, `CountBoundDim_zero`, and for the stratification input),
* `hG : ∀ F n, AlgLemma S F n` — BNZ's algebraic lemma (area G, a hypothesis of the area
  theorem),
* `hinterp : ∀ F n, InterpPerChart S F n` — the interpolation step (BNZ Prop. 6.1, area (I)),
* `hstr : StratInput S` — the stratification input (BNZ §2.3, area (B)),

the dimension-indexed counting statement `CountBoundDim S F n μ` holds for all `F, n, μ`.

The chain is

```
ChartCover          (from InterpPerChart + AlgLemma, `chartCover_of_interp`)
  + StratInput      (the stratification input)
  ↓ `countBoundDimCube_step`                     (dimension induction)
CountBoundDimCube
  ↓ `countBoundDim_of_cube`                      (normalisation)
CountBoundDim
  ↓ `countBound_of_countBoundDim`  (at `μ = n`)  (vacuous `DimLE X n`)
CountBound
```

and the base case of the induction is `CountBoundDim_zero`.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH.Count

open WilkiesDesign WilkiesConjecture

/-- **The dimension induction of BNZ §6.**  The cube-restricted counting statement holds for
every format `F`, ambient dimension `n` and dimension bound `μ`. -/
theorem countBoundDimCube_all_of {S : SOMin} (hcd : S.SharpCD)
    (hG : ∀ F n : ℕ, AlgLemma S F n) (hstr : StratInput S)
    (hinterp : ∀ F n : ℕ, InterpPerChart S F n) :
    ∀ F n μ : ℕ, CountBoundDimCube S F n μ := by
  intro F n μ
  induction μ generalizing F n with
  | zero => exact countBoundDimCube_of_countBoundDim (CountBoundDim_zero S hcd F n)
  | succ k ih =>
      refine countBoundDimCube_step hstr (fun F' => ?_) (chartCover_of_interp (hG F n) (hinterp F n))
      simpa using ih F' n

/-- **The dimension-indexed counting statement**, for all `F, n, μ`. -/
theorem countBoundDim_all_of {S : SOMin} (hcd : S.SharpCD)
    (hG : ∀ F n : ℕ, AlgLemma S F n) (hstr : StratInput S)
    (hinterp : ∀ F n : ℕ, InterpPerChart S F n) :
    ∀ F n μ : ℕ, CountBoundDim S F n μ := by
  have h := countBoundDimCube_all_of hcd hG hstr hinterp
  exact fun F n μ => countBoundDim_of_cube (fun F' => h F' n μ)

/-- **Area H's counting theorem, from the area's two inputs.**  This is the statement the
lead's hole `WilkiesDesign.H_count` demands, modulo (i) the interpolation step
`InterpPerChart` (BNZ Prop. 6.1) and (ii) the stratification input `StratInput` (BNZ §2.3),
both of which are area H's own content. -/
theorem countBound_of_inputs {S : SOMin} (hcd : S.SharpCD)
    (hG : ∀ F n : ℕ, AlgLemma S F n) (hstr : StratInput S)
    (hinterp : ∀ F n : ℕ, InterpPerChart S F n) (F n : ℕ) : CountBound S F n :=
  countBound_of_countBoundDim S F n (countBoundDim_all_of hcd hG hstr hinterp F n n)

end Work.WilkiesH.Count
