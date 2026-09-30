import ChallengeDeps
import Submission.Helpers
import Submission.Work.BW.Main

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex

namespace Submission

theorem bakerWustholz_linearForms_logs {n : ℕ} (hn : 0 < n)
    {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ)
    (α : Fin n → K) (hα : ∀ i, α i ≠ 0)
    (b : Fin n → ℤ) {B : ℕ} (hB : 2 ≤ B) (hbB : ∀ i, (b i).natAbs ≤ B)
    (hΛ_ne_zero : (∑ i, (b i : ℂ) * Complex.log (φ (α i))) ≠ 0) :
    Real.log ‖∑ i, (b i : ℂ) * Complex.log (φ (α i))‖
      ≥ -(BakerWustholz.C n (Module.finrank ℚ K)
          * max (Real.log B) (1 / (Module.finrank ℚ K : ℝ))
          * ∏ i, BakerWustholz.modifiedHeight φ (α i)) :=
  Work.BW.bw_holds φ n α hα b B hB hbB hΛ_ne_zero

end Submission
