import Mathlib

namespace Work.Analysis.Deriv

open Filter
open scoped Topology

/-- If `F` has derivative `F'` at `s`, and there is a sequence `t` tending to `s` with
`t n ≠ s` and `F (t n) = F s` for all `n`, then `F' = 0`.

Indeed the difference quotients `(F (t n) - F s) / (t n - s)` are identically zero and
converge to `F'` by the definition of the derivative. -/
theorem hasDerivAt_eq_zero_of_tendsto {F : ℝ → ℝ} {F' s : ℝ} {t : ℕ → ℝ}
    (h : HasDerivAt F F' s) (ht : Filter.Tendsto t Filter.atTop (nhds s)) (htne : ∀ n, t n ≠ s)
    (heq : ∀ n, F (t n) = F s) : F' = 0 := by
  have hmem : ∀ᶠ n in atTop, t n ∈ ({s}ᶜ : Set ℝ) :=
    Filter.Eventually.of_forall (fun n => by simpa using htne n)
  have ht' : Tendsto t atTop (𝓝[≠] s) := tendsto_nhdsWithin_iff.mpr ⟨ht, hmem⟩
  have hcomp : Tendsto (fun n => slope F s (t n)) atTop (𝓝 F') := h.tendsto_slope.comp ht'
  have hzero : (fun n => slope F s (t n)) = fun _ => (0 : ℝ) := by
    funext n
    simp [slope, heq n]
  have hconst : Tendsto (fun n => slope F s (t n)) atTop (𝓝 0) := by
    rw [hzero]; exact tendsto_const_nhds
  exact tendsto_nhds_unique hcomp hconst

end Work.Analysis.Deriv
