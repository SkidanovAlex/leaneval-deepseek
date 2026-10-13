import Mathlib
import Submission.Work.WilG4c.Hyps
import Submission.Work.WilG1.Basic
import Submission.Work.WilG2.Tnorm
import Submission.Work.WilG2.CompBound
import Submission.Work.WilG3.Defs
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4b.Basic
import Submission.Work.WilG4a.F1AffineW
import Submission.Work.WilG4c.StepLipAux
import Submission.Work.WilG4c.StepLipR0
import Submission.Work.WilG4c.StepLipHighOuter
import Submission.Work.WilG4c.StepLipHighPsiCond

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- **BNZ §5.3 — reduction to `1`-Lipschitz families.**  From `FLem` for families that have
unit `y`-derivatives and are `1`-Lipschitz on the cube (`Work.WilkG4c.PYLip`), deduce `FLem`
for families that merely have unit `y`-derivatives (`Work.WilkG4c.PY`).

Plan (BNZ §5.3).  For each `i` let
`S_i := {(l,x,y) : |(F_i)_x(l,x,y)| ≥ ½ sup_{y'} |(F_i)_x(l,x,y')|}`;
`hbdd : BddDxHyp S` (BNZ Lemma 5.6, area G4b's hole `CG.G4_bdd_dx`) shows the sup is finite
for all `x` outside a finite set, and `hder` makes `S_i` `Ω`-bounded.  Definable choice
(`hchoice : ChoiceHyp S`, area G1's hole `CG.G1_choice`) gives `Γ_i ⊆ S_i` meeting each fibre
`(l,x)` once; `Γ_i` is the graph of `γ_i : Λ × I_x → I^n` with `Ω`-bounded coordinates.
Applying `h1 q : Work.WilG4a.F1AffineW S q` (the corrected `n = 1` corollary, BNZ Cor 5.5) to the tuple consisting of
`x`, the coordinates `γ_{i,j}` and `F_i ∘ (x,γ_i)` shows `|(F_i)_x| = O_n(1)` on `Γ_i`, hence
everywhere (that is where the paper's `1 ≥ |(F_{i,η})_t|` comes from).  With `y`-Lipschitzness
this makes each `F_i` `O_n(1)`-Lipschitz off finitely many hyperplanes `x = x_j`; a cell
decomposition `hcd` of `Λ × I_x` compatible with the projections of the (definable)
discontinuity loci splits each `F_i` into pieces on which it is `O_n(1)`-Lipschitz in `x`,
each handled either by `ih q` (when the `x`-interval degenerates to a point, the family is a
dimension-`n` family over the parameter space with `x` appended) or by rescaling `x` linearly
back to `(0,1)` (which only improves the Lipschitz constant) plus one further subdivision into
a *constant* number `C` of pieces, so that the Lipschitz constant becomes `1` while the
`y`-derivatives stay `≤ 1`; `hP1` then applies to each piece.

Beware λ-uniformity: every chart of the final `Finset` must satisfy the `C^r` norm and
cube-membership conditions for *every* `l ∈ Λ`; the clean way is to apply `hP1` to each
pullback family with the *whole* parameter set and take the `Finset` union of the resulting
chart families (counts add; format/degree are unchanged), rather than defining charts
piecewise in the parameter space. -/
theorem StepLip (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (n p : ℕ) (hn : 1 ≤ n)
    (h1 : ∀ q, Work.WilG4a.F1AffineW S q) (ih : ∀ q, FLem S q n) (hchoice : Work.WilkG4c.ChoiceHyp S)
    (hbdd : Work.WilkG4c.BddDxHyp S)
    (hP1 : Work.WilkG4c.FLemP S p (n + 1) (Work.WilkG4c.PYLip p n)) :
    Work.WilkG4c.FLemP S p (n + 1) (Work.WilkG4c.PY p n) :=
  -- `FLemP` is the conjunction of its `r = 0` and `r ≥ 1` slices
  -- (`Work.WilkG4c.FLemP_of_zero_of_high`):
  --
  -- * `Work.WilkG4c.StepLipR0` is the `r = 0` slice (`StepLipR0.lean`);
  -- * the `r ≥ 1` slice is the outer assembly `Work.WilkG4c.FLemPHigh_of_Psi`
  --   (`StepLipHighOuter.lean`) fed with the per-chart step
  --   `Work.WilG4c.StepLipHighPsiCond` (`StepLipHighPsiCond.lean`), i.e. BNZ §5.3 proper:
  --   `YbCharts` + the parameter-clamp globalisation + the per-`ψ` cell decomposition of
  --   `ℝ^{q+1}`, the good/pin/section dispatch, the covers and the counts.
  Work.WilkG4c.FLemP_of_zero_of_high
    (Work.WilG4c.StepLipR0 S hcd hder n p hn h1 ih hchoice hbdd hP1)
    (Work.WilkG4c.FLemPHigh_of_Psi S hcd hder n p hn h1 ih hchoice hbdd hP1
      (fun q hP1q hind =>
        Work.WilG4c.StepLipHighPsiCond S hcd hder n q hn h1 ih hchoice hbdd hP1q hind))

end Work.WilG4c
