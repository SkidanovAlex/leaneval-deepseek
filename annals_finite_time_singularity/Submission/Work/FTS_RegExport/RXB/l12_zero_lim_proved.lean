import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.StrongEps.L12_tendsto_of_dominated
import Submission.Work.FTS.StrongEps.SupPort.classC_sup_le
import Submission.Work.FTS_RegExport.RXB.l12_aux
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.FTS_RegExport.RXB.l12dens_weighted_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXB

/-- **RX-B**: the zero mode of `L₁₂` passes to the limit along the class-C approximants of
`Work.FTS.FinalV2.LimApprox` (the `τ ↦ slice g τ` family is the pointwise limit of profiles
which are `C^∞` on the open quadrant and uniformly `ℋ⁴`-bounded, each carrying `L₁₂(·)(0) = 0`
as part of the class data).

The proof is the assembly lemma `Work.FTS_RegExport.RXB.l12_zero_lim_of_bounds` fed with the two
analytic inputs of the directory:

* `sup_bound_all_alpha` — the interior `L^∞`–`ℋ⁴` trade-off `f² ≤ C|f|²_{ℋ⁴}` for every `α > 0`
  (used for the angular dominated convergence of the density);
* `l12dens_weighted_bound` — the weighted bound `|L₁₂dens f s| ≤ C(√s/(1+s)²)|f|_{ℋ⁴}`, which
  turns the uniform `ℋ⁴`-bound of the approximants into an `L¹(ds)` majorant. -/
theorem l12_zero_lim_proved {αG C₀ : ℝ} (hα : 0 < αG) {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hA : Work.FTS.FinalV2.LimApprox αG C₀ Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ → Work.Construction.L12 (Work.FTS.Galerkin.slice g τ) 0 = 0 :=
  l12_zero_lim_of_bounds hα
    (fun α hα => sup_bound_all_alpha hα)
    (fun α hα => l12dens_weighted_bound hα)
    hA

end Work.FTS_RegExport.RXB
