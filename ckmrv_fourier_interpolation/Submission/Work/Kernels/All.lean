/-
# The CKMRV kernels chapter: entry point

Import this module to obtain the whole area developed under `Submission/Work/Kernels/`:

* `Work.Kernels.ModerateGrowth` : the class `𝒫` of holomorphic functions of moderate growth,
  its closure properties and the equivalence of the three forms of the growth bound.
* `Work.Kernels.SlashDefs`, `Work.Kernels.Slash` : the slash action of `SL(2,ℤ)`, the factor
  of automorphy `jFun`, and Lemma "HCmoderategrowthPslashed" (`𝒫` is slash-stable).
* `Work.Kernels.Classical` and the modules under `ClassicalFacts/` : the classical modular
  forms `E₂, E₄, E₆, Δ`, the `j`-invariant, Jacobi's theta functions, and their membership
  in `𝒫`.
* `Work.Kernels.GroupAlgebra` : the group algebra `R = ℂ[SL(2,ℤ)]`, its action on `ℍ → ℂ`
  by slash operators, the right ideals `𝓘, 𝓘_±, 𝓘̃_±`, and the spaces `Ann_k(J, 𝒫)`.
* `Work.Kernels.Kernels` : the explicit kernels `K_±^{(d)}`, `K^{(d)}`, `K̂^{(d)}` of
  Theorem 4.9 for `d = 8, 24`.
* `Work.Kernels.E2Laws`, `Work.Kernels.PhiAnnihilation`, `Work.Kernels.KernelEquations` :
  the transformation laws of `E₂`, the annihilation of the basis functions
  `φ_{-2}, φ_0, φ_2` by `(T-I)²` and `S+I`, and the product rules for those conditions.
* `Work.Kernels.Theorem31` : the hypotheses of Theorem 3.1 (`SatisfiesThm31`), the resulting
  existence statement `Thm31Conclusion`, and the contour-integral construction of `F`, `F̃`.
-/
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.Kernels.SlashDefs
import Submission.Work.Kernels.SlashBounds.jFun_bound_upper
import Submission.Work.Kernels.SlashBounds.jFun_bound_inv
import Submission.Work.Kernels.SlashBounds.jFun_rpow_bound
import Submission.Work.Kernels.SlashBounds.nFun_bound
import Submission.Work.Kernels.Slash
import Submission.Work.Kernels.Classical
import Submission.Work.Kernels.ClassicalFacts.E2Fun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.E4Fun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.E6Fun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.DeltaFun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.theta00Fun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.theta01Fun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.theta10Fun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.DeltaFun_basic
import Submission.Work.Kernels.GroupAlgebra
import Submission.Work.Kernels.AlgebraFacts.slash_smul
import Submission.Work.Kernels.AlgebraFacts.slash_mul
import Submission.Work.Kernels.AlgebraFacts.InP_slash_R
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.E2Laws
import Submission.Work.Kernels.PhiAnnihilation
import Submission.Work.Kernels.KernelEquations
import Submission.Work.Kernels.Theorem31
-- NOTE: `KernelFacts.fk_slash` and `KernelFacts.KPlusCoeff_vadd_one` declare helper names
-- (`fk_neg_two`, ..., `KPlusCoeff_vadd_one`) that clash with `KernelFacts.KPlus_S_add` and
-- `KernelFacts.KPlus_T2` respectively.  Those two files are therefore imported individually by
-- a caller who wants them; each is individually correct.
import Submission.Work.Kernels.KernelFacts.KPlusCoeff_slash_S
import Submission.Work.Kernels.KernelFacts.KPlus_T2
import Submission.Work.Kernels.KernelFacts.KPlus_S_add
import Submission.Work.Kernels.KernelFacts.psi2_T2
import Submission.Work.Kernels.KernelFacts.psi4_T2
import Submission.Work.Kernels.KernelFacts.psi2_Sopm
import Submission.Work.Kernels.KernelFacts.psi4_Sopm
import Submission.Work.Kernels.KernelFacts.KMinus_T2
import Submission.Work.Kernels.KernelFacts.KMinus_Sopm
import Submission.Work.Kernels.KernelSlash
import Submission.Work.Kernels.KMinusSlash
import Submission.Work.Kernels.KernelGrowth
import Submission.Work.Kernels.LogLambda.logLambdaData_exists
import Submission.Work.Kernels.TildeOps
import Submission.Work.Kernels.TildeFacts.KPlus_z_tildeA
import Submission.Work.Kernels.TildeFacts.KPlus_z_tildeB
import Submission.Work.Kernels.TildeFacts.KMinus_z_tildeA
import Submission.Work.Kernels.TildeFacts.KMinus_z_tildeB
import Submission.Work.Kernels.Section5
import Submission.Work.Kernels.Section5Facts.kernelTransform_slash_S
import Submission.Work.Kernels.Section5Facts.Ftgen_T2
import Submission.Work.Kernels.Section5Facts.Fgen_third
import Submission.Work.Kernels.Section5Pack
import Submission.Work.Kernels.ClearLink.UpsilonPlusClear_eq_smul
import Submission.Work.Kernels.ClearLink.UpsilonMinusClear_eq_smul
import Submission.Work.Kernels.ClearLink.KPlusClear_eq_smul
import Submission.Work.Kernels.ClearLink.KMinusClear_eq_smul
import Submission.Work.Kernels.LogLambdaInstance
