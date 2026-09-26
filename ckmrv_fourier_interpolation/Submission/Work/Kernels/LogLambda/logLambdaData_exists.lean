/-
# Existence of the logarithm data `(𝓛, 𝓛_S)` of CKMRV

The pair `(𝓛, 𝓛_S)` of CKMRV (Cohn--Kumar--Miller--Radchenko--Viazovska, Ann. of Math. 196
(2022), Section 2.1.5) is realised by

  `𝓛(z) = Lfun z`  (the normalised logarithm of `λ = θ₁₀⁴/θ₀₀⁴`, equal to the explicit branch
  `LU(z) = πiz + 4log2 + 4log(θ₂(z/2,z)/2) - 4log θ₀₀(z)` on `{im z > 1/2}`),

  `𝓛_S(z) = Lfun(-z⁻¹)`.

The transformation laws `𝓛|₀T = 𝓛 - 𝓛_S + πi`, `𝓛_S|₀T = -𝓛_S`, `𝓛|₀S = 𝓛_S`, `𝓛_S|₀S = 𝓛` are
proved in `LogLaws`, and the moderate growth of `𝓛` in `LogGrowth`.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.LogLambda.LogAssembly
import Submission.Work.Kernels.LogLambda.LogGrowth.Lfun_growth
import Submission.Work.Kernels.LogLambda.LogGrowth.Lfun_re_bound
import Submission.Work.Kernels.LogLambda.LogGrowth.Lfun_sub_pi_I_bound

namespace Work.Kernels.LogLambda

theorem logLambdaData_exists : Nonempty Work.Kernels.LogLambdaData := by
  refine logLambdaData_of ?_
  refine Lfun_growth_of_bounds ?_ ?_
  · exact LogGrowth.Lfun_re_bound
  · obtain ⟨C, hC, hb⟩ := LogGrowth.Lfun_sub_pi_I_bound
    exact ⟨C, hC, fun z hz h1 => by simpa only [PsiC, linC] using hb z hz h1⟩

end Work.Kernels.LogLambda
