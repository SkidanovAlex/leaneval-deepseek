import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Continuity of the composition (Nemytskii) operator on `L²(Conf N)`

For a `1`-Lipschitz function `ψ : ℝ → ℝ` with `ψ 0 = 0`, composition with `ψ`
descends to a continuous (indeed `1`-Lipschitz) map on `L²(Conf N)`, the
Mathlib construction `LipschitzWith.compLp`.  Consequently, if a sequence
`u n : L²(Conf N)` converges to `v`, then the `L²`-elements represented by
`ψ ∘ u n` converge to the one represented by `ψ ∘ v`.

The two `MemLp` hypotheses record square-integrability of the composed
functions; they are used only to give the `MemLp.toLp` elements named in the
statement, which are then identified with `hψ.compLp hψ0 (u n)` and
`hψ.compLp hψ0 v` by almost-everywhere equality.
-/

namespace Work.BoseSym.Trunc

open MeasureTheory Filter
open scoped Topology ENNReal

theorem tendsto_toLp_comp {N : ℕ} {ψ : ℝ → ℝ} (hψ0 : ψ 0 = 0) (hψ : LipschitzWith 1 ψ)
    {u : ℕ → Work.BoseSym.L2 N} {v : Work.BoseSym.L2 N}
    (h : Filter.Tendsto u Filter.atTop (nhds v))
    (hmem : ∀ n, MeasureTheory.MemLp (fun x => ψ ((u n : Work.BoseSym.Conf N → ℝ) x)) 2
      (Work.BoseSym.volC N))
    (hmemv : MeasureTheory.MemLp (fun x => ψ ((v : Work.BoseSym.Conf N → ℝ) x)) 2
      (Work.BoseSym.volC N)) :
    Filter.Tendsto
      (fun n => (MeasureTheory.MemLp.toLp (fun x => ψ ((u n : Work.BoseSym.Conf N → ℝ) x))
        (hmem n) : Work.BoseSym.L2 N))
      Filter.atTop
      (nhds (MeasureTheory.MemLp.toLp (fun x => ψ ((v : Work.BoseSym.Conf N → ℝ) x)) hmemv)) := by
  -- The composition operator `ψ ∘ ·` on `L²` is continuous.
  have hcont : Continuous (hψ.compLp hψ0 : Work.BoseSym.L2 N → Work.BoseSym.L2 N) :=
    hψ.continuous_compLp hψ0
  have hkey : Filter.Tendsto (fun n => hψ.compLp hψ0 (u n)) Filter.atTop
      (nhds (hψ.compLp hψ0 v)) :=
    (hcont.tendsto v).comp h
  -- The `toLp` elements of the statement agree a.e. with `hψ.compLp hψ0`.
  have hseq : ∀ n,
      (MeasureTheory.MemLp.toLp (fun x => ψ ((u n : Work.BoseSym.Conf N → ℝ) x))
        (hmem n) : Work.BoseSym.L2 N) = hψ.compLp hψ0 (u n) := by
    intro n
    apply MeasureTheory.Lp.ext
    filter_upwards [MeasureTheory.MemLp.coeFn_toLp (hmem n),
      hψ.coeFn_compLp hψ0 (u n)] with x h1 h2
    rw [h1, h2]
    rfl
  have hlim :
      (MeasureTheory.MemLp.toLp (fun x => ψ ((v : Work.BoseSym.Conf N → ℝ) x))
        hmemv : Work.BoseSym.L2 N) = hψ.compLp hψ0 v := by
    apply MeasureTheory.Lp.ext
    filter_upwards [MeasureTheory.MemLp.coeFn_toLp hmemv, hψ.coeFn_compLp hψ0 v] with x h1 h2
    rw [h1, h2]
    rfl
  simpa only [hseq, hlim] using hkey

end Work.BoseSym.Trunc
