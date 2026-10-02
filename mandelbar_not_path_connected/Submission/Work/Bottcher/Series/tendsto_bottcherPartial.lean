import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.Series

/-- The partial products `z * exp (Σ_{n<N} t_n)` of the Böttcher product formula
converge to the Böttcher coordinate `bottcher c z = z * exp (Σ' n, t_n)` as soon
as the series `Σ_n t_n` of logarithms is summable: the partial sums converge to
the sum, `exp` is continuous, and multiplication by `z` is continuous. -/
theorem tendsto_bottcherPartial (c z : ℂ)
    (h : Summable (fun n : ℕ => Work.Bottcher.bottcherTerm c n z)) :
    Filter.Tendsto (fun N : ℕ => Work.Bottcher.bottcherPartial c N z) Filter.atTop
      (nhds (Work.Bottcher.bottcher c z)) := by
  unfold Work.Bottcher.bottcherPartial Work.Bottcher.bottcher
  have h1 : Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, Work.Bottcher.bottcherTerm c n z)
      Filter.atTop (nhds (∑' n, Work.Bottcher.bottcherTerm c n z)) :=
    h.hasSum.tendsto_sum_nat
  exact Filter.Tendsto.const_mul z ((Complex.continuous_exp.tendsto _).comp h1)

end Work.Bottcher.Series
