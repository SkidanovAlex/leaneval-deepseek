import Mathlib
import Submission.Work.WilE3.API.RemDefs
import Submission.Work.WilE3.API.Rem.eTayBasic
import Submission.Work.WilE3.API.Rem.hasFDerivAt_eTayMon
import Submission.Work.WilE3.API.Rem.sum_b_smul_eTayGrad

namespace Work.WilE3.API.Rem

open Classical Topology

theorem fderiv_eTay {k : ℕ} (y : Fin k → ℝ) (S : Finset (Fin k → ℕ)) (b : (Fin k → ℕ) → ℝ) (x : Fin k → ℝ) :
    HasFDerivAt (fun z => Work.WilE3.API.eTay y S b z)
      ((∑ i : Fin k, (∑ m ∈ S.filter (fun m => 0 < m i), Work.WilE3.API.eDTay y b i m x) •
        (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i)) : (Fin k → ℝ) →L[ℝ] ℝ) x := by
  have h := HasFDerivAt.fun_sum (u := S)
    (A := fun m (z : Fin k → ℝ) => b m * Work.WilE3.API.eTayMon y m z)
    (A' := fun m => b m • Work.WilE3.API.eTayGrad y m x)
    (fun m _ => (hasFDerivAt_eTayMon y x m).const_mul (b m))
  simpa only [Work.WilE3.API.eTay_eq_sum_mon, Work.WilE3.API.eDTay_eq, sum_b_smul_eTayGrad]
    using h

end Work.WilE3.API.Rem
