import Mathlib
import Submission.Work.Diff.Alg.PA.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Alg.PA

open Finset Submission.Diff.Alg

/-!
# Elementary consequences of `IsPinchedAlg`

`IsPinchedAlg δ R` says `δ · K(σ') ≤ K(σ)` for all planes `σ, σ'`. Two immediate consequences:

* if `δ < 1`, then taking `σ' = σ` gives `(δ - 1) K(σ) ≤ 0`, hence `0 ≤ K(σ)`;
* if the inequality holds with `δ = 1 - 1/(k+1)` for every `k`, letting `k → ∞` gives
  `K(σ') ≤ K(σ)` **and** (swapping the roles) `K(σ) ≤ K(σ')`, so all sectional curvatures
  coincide.
-/

/-- `IsPinchedAlg δ R` with `δ < 1` forces every sectional curvature to be nonnegative:
apply the pinching inequality to the same plane twice. -/
theorem pinch_nonneg_of_lt_one {n : ℕ} {δ : ℝ} {R : Curv4 n} (h : IsPinchedAlg δ R)
    (hδ : δ < 1) : ∀ u v : Fin n → ℝ, IsONPair u v → 0 ≤ secK R u v := by
  intro u v huv
  have h1 := h u v u v huv huv
  nlinarith [h1, hδ]

/-- If `(1 - 1/(k+1)) * A ≤ B` for every `k : ℕ`, then `A ≤ B`: let `k → ∞` (the factor tends
to `1`). -/
theorem le_of_pinched {A B : ℝ} (h : ∀ k : ℕ, (1 - 1 / ((k : ℝ) + 1)) * A ≤ B) : A ≤ B := by
  have hlim : Filter.Tendsto (fun k : ℕ => (1 - 1 / ((k : ℝ) + 1)) * A) Filter.atTop
      (nhds (1 * A)) := by
    have h1 : Filter.Tendsto (fun k : ℕ => (1 : ℝ) - 1 / ((k : ℝ) + 1)) Filter.atTop
        (nhds (1 - 0)) :=
      Filter.Tendsto.sub tendsto_const_nhds tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using h1.mul tendsto_const_nhds
  have := le_of_tendsto hlim (Filter.Eventually.of_forall h)
  simpa using this

theorem pinch_basic (n : ℕ) :
    (∀ (δ : ℝ) (R : Curv4 n), IsPinchedAlg δ R → δ < 1 →
      ∀ u v : Fin n → ℝ, IsONPair u v → 0 ≤ secK R u v) ∧
    (∀ R : Curv4 n, (∀ k : ℕ, IsPinchedAlg (1 - 1 / ((k : ℝ) + 1)) R) →
      ∀ u v u' v' : Fin n → ℝ, IsONPair u v → IsONPair u' v' →
        secK R u v = secK R u' v') := by
  constructor
  · intro δ R hpinch hδ
    exact pinch_nonneg_of_lt_one hpinch hδ
  · intro R hR u v u' v' hu hu'
    exact le_antisymm (le_of_pinched (fun k => hR k u' v' u v hu' hu))
      (le_of_pinched (fun k => hR k u v u' v' hu hu'))

end Work.Diff.Alg.PA
