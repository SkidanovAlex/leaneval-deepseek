/-
# `E4R3/N4C/rows/HonDecay` — the `z = ∞` decay of the honest context

`Work.FTS.StrongEps.E4R3.N4C.decayAll_of_classC` (proved in the parent directory) shows that the
class `ClassC α g` — which carries the integration-by-parts boundary vanishing `BdryTraces α 6 g`
and the angular normalisation `normTh g = g` — already forces

  `Work.Spaces.DecayAll 4 g`

i.e. the per-angle decay at `z → ∞` of the plain partials `∂_z^j ∂_θ^i g` (`i + j ≤ 4`) and of
the mixed `D`-derivatives `D_z^b D_θ^a g` (`a + b ≤ 4`).  This is exactly the hypothesis of the
transport clauses `N4ExtraH.t1`–`t4` (whence every `IP`-bound row of the honest §8 table).

This module exposes the three projections of that decay which the row proofs consume.
Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.Hon
import Submission.Work.FTS.StrongEps.E4R3.N4C.decayAll_of_classC

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The `z = ∞` decay of the profile and of its `D`-derivatives of order `≤ 4`. -/
theorem CtxT.hdecay {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.Spaces.DecayAll 4 g := decayAll_of_classC h.hα h.hg h.hco

/-- The decay of the plain `z`-partials of order `≤ 4`, in the form consumed by the rows. -/
theorem CtxT.hdecayInZ {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg)
    {j i : ℕ} (hji : i + j ≤ 4) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Filter.Tendsto (fun z => Work.Spaces.pzIter j (Work.Spaces.pthIter i g) z θ)
      Filter.atTop (nhds 0) := h.hdecay.1 j i hji θ hθ

/-- The decay of the mixed `D`-derivatives of order `≤ 4`. -/
theorem CtxT.hdecayMixed {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg)
    {a b : ℕ} (hab : a + b ≤ 4) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Filter.Tendsto (fun z => Work.Spaces.mixed b a g z θ) Filter.atTop (nhds 0) :=
  h.hdecay.2 a b hab θ hθ

/-- The decay of the `D_θ`-slot, as used by the radial-moment rows. -/
theorem CtxT.hdecayDth {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    ∀ θ ∈ Work.Spaces.Iθ,
      Filter.Tendsto (fun z => Work.Spaces.Dth g z θ) Filter.atTop (nhds 0) :=
  fun θ hθ => by
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
      using h.hdecayMixed (a := 1) (b := 0) (by norm_num) hθ

end Work.FTS.StrongEps.E4R3.N4C
