/-
# `Work.FTS.PhiStar.FlatW_psiSeries` — the `R`-term flat estimate of the `PhiStar` node

**Target** (unchanged, the statement the `PhiStar` chapter consumes, see `FlatWAux/NOTES.md`):

`∃ C > 0, ∀ α ψ, 0 < α → α ≤ 1/5 → AngModel α ψ →
   FlatW 7 (fun z θ => (z+1)/z · (psiSeries α (RemSource α ψ) z θ / sin 2θ)) (C α²)`.

`FlatW 7 f K` asks for two families of bounds,
`|(z+1)^k ∂_z^k f z θ| ≤ K` (`k ≤ 7`) and `|(z+1)^k ∂_z^k (D_θ^i(∂_θ f)) z θ| ≤ K` (`k+i+1 ≤ 7`).
They are `Fam1Bound` and `Fam2Bound`; the assembly below takes the maximum of the two constants
(all of which are independent of `α` and `ψ` — this is the point of the `U`-suffixed siblings).

The route (see `FlatWAux/NOTES.md` for the full map):
`RemSource α ψ = α²·(𝒜φ)(z)·ψ(θ)` is separable, so `psiSeries α (RemSource α ψ)` is an explicit
`m`-series; `ModeZDeriv` differentiates it termwise in `z`, the radial expansion
`radGreen α m c = Σ_{j<J} α^j (𝒜^j c)/λ_m^{j+1} + (α^J/λ_m^J)·radGreen α m (𝒜^J c)` splits each
mode into the resummed leading part (`Wt`, bounded by `AngBoundU`) and an absolutely summable
remainder; `Fam1Bound`/`Fam2Bound` do the bookkeeping, `Fam2DiffId` supplying the θ-differentiated
form of the split.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.Fam1Bound
import Submission.Work.FTS.PhiStar.FlatWAux.Fam2Bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false

theorem FlatW_psiSeries : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (ψ : ℝ → ℝ), 0 < α → α ≤ 1 / 5 →
    Work.FTS.PhiStar.AngModel α ψ →
    Work.FTS.VocabO2.FlatW 7
      (fun z θ => (z + 1) / z
        * (Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z θ
           / Work.Construction.s2 θ)) (C * α ^ 2) := by
  obtain ⟨C1, hC10, hF1⟩ := Work.FTS.PhiStar.FlatWAux.Fam1Bound
  obtain ⟨C2, hC20, hF2⟩ := Work.FTS.PhiStar.FlatWAux.Fam2Bound
  refine ⟨max C1 C2 + 1, by positivity, ?_⟩
  intro α ψ hα hα5 hang z θ hz hθ0 hθ2
  have hα2 : (0 : ℝ) ≤ α ^ 2 := pow_nonneg (le_of_lt hα) 2
  refine ⟨fun k hk => ?_, fun k i hki => ?_⟩
  · refine le_trans (hF1 α ψ hα hα5 hang z θ hz hθ0 hθ2 k hk) ?_
    exact mul_le_mul_of_nonneg_right (by linarith [le_max_left C1 C2]) hα2
  · refine le_trans (hF2 α ψ hα hα5 hang z θ hz hθ0 hθ2 k i hki) ?_
    exact mul_le_mul_of_nonneg_right (by linarith [le_max_right C1 C2]) hα2

end Work.FTS.PhiStar
