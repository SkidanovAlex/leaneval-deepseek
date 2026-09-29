import Mathlib
import Submission.Work.Holonomy3.cleared_defs
import Submission.Work.Holonomy3.finsupp_prod_hasSum
import Submission.Work.Holonomy3.embedVarC_prod_coeff

namespace Work.Holonomy3

open scoped BigOperators

theorem hasSum_prod_embedVarC {d : ℕ} (σ : Fin d → PowerSeries ℂ) (A : Fin d → ℂ) (z : Fin d → ℂ)
    (h : ∀ s, HasSum (fun n : ℕ => PowerSeries.coeff n (σ s) * z s ^ n) (A s)) :
    HasSum (fun n : Fin d →₀ ℕ =>
        (∏ s, Work.Holonomy3.embedVarC s (σ s)).coeff n * ∏ s, z s ^ (n s))
      (∏ s, A s) := by
  have key := finsupp_prod_hasSum (fun s j => PowerSeries.coeff j (σ s)) z
    (fun s => (h s).summable.norm)
  have hval : (∏ s : Fin d, ∑' j : ℕ, PowerSeries.coeff j (σ s) * z s ^ j) = ∏ s, A s :=
    Finset.prod_congr rfl fun s _ => (h s).tsum_eq
  rw [hval] at key
  simpa [embedVarC_prod_coeff] using key

end Work.Holonomy3
