import Mathlib
import Submission.Work.WilE7.auxiliary.piRangeTopOfRank

namespace Work.WilE9G.Mult

theorem surjective_pi_of_rank_eq_card {m n : ℕ} (cs : Fin m → Fin n → ℝ)
    (hr : (Matrix.of cs).rank = m) :
    Function.Surjective (ContinuousLinearMap.pi (fun a : Fin m =>
      (∑ j : Fin n, cs a j • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)))) := by
  have h := Work.WilE7.auxiliary.piRangeTopOfRank cs hr
  exact LinearMap.range_eq_top.mp h

end Work.WilE9G.Mult
