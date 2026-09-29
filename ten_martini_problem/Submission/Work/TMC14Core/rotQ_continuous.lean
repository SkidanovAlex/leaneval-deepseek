import Mathlib
import Submission.Work.TMC14Core.RatRot

open Filter Topology Metric

namespace Work.TMC14Core

/-- `rotQ` is the locally uniform limit of the continuous functions
`E ↦ qIter p q lam E x m / m`, with rate `1/m` (`rotQ_rate`); hence continuous. -/
theorem rotQ_continuous (p : ℤ) (q : ℕ) (lam x : ℝ) (hq : 1 ≤ q) :
    Continuous (fun E : ℝ => Work.TMC14Core.rotQ p q lam E x) := by
  have hcont : ∀ m : ℕ, Continuous (fun E : ℝ => qIter p q lam E x m / (m : ℝ)) :=
    fun m => (qIter_continuous_E p q lam x m).div_const _
  have hunif : TendstoUniformly
      (fun m : ℕ => fun E : ℝ => qIter p q lam E x m / (m : ℝ))
      (fun E : ℝ => rotQ p q lam E x) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have h1 : Tendsto (fun m : ℕ => (1:ℝ) / (m:ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 1
    have hlt : ∀ᶠ m : ℕ in atTop, (1:ℝ)/(m:ℝ) < ε :=
      h1.eventually_lt tendsto_const_nhds hε
    filter_upwards [hlt, eventually_ge_atTop 1] with m hmε hm1
    intro E
    rw [Real.dist_eq]
    calc |rotQ p q lam E x - qIter p q lam E x m / (m:ℝ)|
        ≤ 1 / (m:ℝ) := rotQ_rate p q lam E x hq hm1
      _ < ε := hmε
  exact TendstoUniformly.continuous hunif (Eventually.of_forall hcont).frequently

end Work.TMC14Core
