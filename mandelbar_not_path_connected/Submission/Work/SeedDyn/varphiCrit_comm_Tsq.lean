import Mathlib
import Submission.Work.SeedDyn.Defs
import Submission.Work.Bottcher.CritBottcherExists

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedDyn

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- The holomorphic second iterate `Tsq c = (T_c)^2` is the two-fold iterate of `T_c`,
`z ↦ (z² + c̄)² + c`: applying `T_c`, i.e. `z ↦ z̄² + c`, twice conjugates the inner square back
and reproduces `Tsq c` exactly.  Hence the Böttcher functional equation of `T_c` can be applied
twice to `Tsq c`. -/
theorem Tsq_eq_Tantibar_comp (c : ℂ) :
    Work.Landing.Tsq c = Tantibar c ∘ Tantibar c := by
  funext z
  simp [Work.Landing.Tsq, Work.Landing.Tantibar_apply]

/-- **The Böttcher equation for the holomorphic second return map.**
For `c ∈ M*` and `z` in the escaping set of `T_c`, the canonical critical Böttcher coordinate
sends the holomorphic second iterate `Tsq c = (T_c)^2` to the fourth power:
`φ (Tsq c z) = (φ z)^4`.

This is the iteration of the antiholomorphic Böttcher equation `φ (T_c w) = conj (φ w)^2`:
applying it twice and using `conj (conj ζ) = ζ` turns the two conjugations into the identity, so
the exponent doubles to `4`.  Both `z` and `T_c z` lie in the critical domain because for
`c ∈ M*` that domain *is* the escaping set (`Work.SeedDyn.critDomain_eq_escapingSet`) and it is
`T_c`-invariant (`Work.ParamRays.Tantibar_mem_critDomain`). -/
theorem varphiCrit_comm_Tsq {c : ℂ} (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) {z : ℂ}
    (hz : z ∈ Work.SeedDyn.esc c) :
    Work.Bottcher.varphiCrit c (Work.Landing.Tsq c z) = Work.Bottcher.varphiCrit c z ^ 4 := by
  have hcd : Work.ParamRays.critDomain c = Work.SeedDyn.esc c :=
    Work.SeedDyn.critDomain_eq_escapingSet hc
  have hz' : z ∈ Work.ParamRays.critDomain c := by
    rw [hcd]; exact hz
  have hT : Tantibar c z ∈ Work.ParamRays.critDomain c :=
    Work.ParamRays.Tantibar_mem_critDomain hz'
  have hTsq : Work.Landing.Tsq c z = Tantibar c (Tantibar c z) :=
    congrFun (Tsq_eq_Tantibar_comp c) z
  rw [hTsq, Work.Bottcher.varphiCrit_comm_Tantibar hT,
    Work.Bottcher.varphiCrit_comm_Tantibar hz']
  simp only [map_pow, starRingEnd_apply, star_star]
  ring

end Work.SeedDyn
