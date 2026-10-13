import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.affine_comb_graph_mem
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex
import Submission.Work.WilG4a.affine_chart_graph_mem

namespace Work.WilG4a

/-- **The affine-chart lemma** (BNZ §5.1, `n = 1` base case).

If the graphs of `α` and `β` are `Ω`-definable with format `F` and degree `D`, then so is
the graph of the one-parameter family `(l, t) ↦ α l + β l * t`, with a format depending only
on `F` and `p` and a degree bounded by a polynomial in `D`.

This is the identity of `WilkiesDesign.graphOf` with `Work.WilG4a.graphFam`; following the
statement literally we phrase it on the `graphOf` side of the two inputs and the `graphFam`
side of the output.  The construction (two substitution atoms, a degree-`2` hypersurface and
a projection) is carried out in `affine_chart_graph_mem`. -/
theorem affineChart_graph_mem (S : WilkiesDesign.SOMin) (p : ℕ) (F : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D r : ℕ) {α β : (Fin p → ℝ) → ℝ},
      WilkiesDesign.graphOf α ∈ S.Ω F D (p + 1) →
      WilkiesDesign.graphOf β ∈ S.Ω F D (p + 1) →
      Work.WilG4a.graphFam (fun l (t : ℝ) => α l + β l * t) ∈
        S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1 + 1) :=
  affine_chart_graph_mem S p F

end Work.WilG4a
