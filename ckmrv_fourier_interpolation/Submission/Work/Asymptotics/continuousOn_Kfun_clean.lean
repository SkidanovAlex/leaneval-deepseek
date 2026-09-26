/-
# Joint continuity of the kernel `Kfun` off the coincidence divisor

The CKMRV kernel `K^{(d)}(τ,z)` is meromorphic on `ℍ × ℍ` with poles exactly on the coincidence
set `j τ = j z`; in the formalisation (`Work.Kernels.Kfun`) it is a total function, and it is
*continuous* wherever `j τ ≠ j z`.  This is the analytic ingredient needed in order to bound
`K(τ,z)` on compact subsets of the clean set, and hence to differentiate contour integrals of
`K` under the integral sign.

The proof does not unfold the explicit matrix formula of `Work.Kernels.Kfun` (whose entries
involve `(j τ - j z)⁻¹`, so that continuity would require a case analysis).  Instead it uses
the master identity of `Work.Asymptotics.KfunAuxDefs`,

  `K^{(d)}(τ,z) · (j τ - j z) = AfunFun ℓ d τ z`   (`j τ ≠ j z`),

together with the *joint* continuity of the cleared function `AfunFun`
(`Work.Asymptotics.continuous_AfunFun`): off the divisor, `Kfun` is `AfunFun` divided by the
non-vanishing continuous function `j τ - j z`.
-/
import Mathlib
import Submission.Work.Asymptotics.continuationDefs
import Submission.Work.Asymptotics.differentiableAt_Kfun_tau
import Submission.Work.Asymptotics.KfunAuxDefs
import Submission.Work.Asymptotics.continuous_AfunFun

noncomputable section

open UpperHalfPlane Filter Topology
open scoped Topology

namespace Work.Asymptotics

open Work.Kernels

/-- The `j`-invariant is continuous on `ℍ`. -/
lemma continuous_jInvariantFun' : Continuous (fun τ : UpperHalfPlane => jInvariantFun τ) := by
  have h4 : Continuous (fun τ : UpperHalfPlane => E4Fun τ) :=
    (ModularForm.holo' ModularForm.E₄).continuous
  have hΔ : Continuous (fun τ : UpperHalfPlane => DeltaFun τ) :=
    (CuspForm.holo' CuspForm.discriminant).continuous
  have h : (fun τ : UpperHalfPlane => jInvariantFun τ)
      = fun τ : UpperHalfPlane => E4Fun τ ^ 3 / DeltaFun τ := rfl
  rw [h]
  exact (h4.pow 3).div hΔ (fun τ => ClassicalFacts.DeltaFun_ne_zero τ)

/-- The coincidence difference `(τ,z) ↦ j τ - j z` is continuous on `ℍ × ℍ`. -/
lemma continuous_jInvariantFun_sub' :
    Continuous (fun p : UpperHalfPlane × UpperHalfPlane =>
      jInvariantFun p.1 - jInvariantFun p.2) :=
  (continuous_jInvariantFun'.comp continuous_fst).sub
    (continuous_jInvariantFun'.comp continuous_snd)

/-- **Joint continuity of the kernel off the divisor.**  On the clean set
`{p : ℍ × ℍ | j p.1 ≠ j p.2}` the kernel `K^{(d)}` agrees with the continuous function
`AfunFun ℓ d p.1 p.2 / (j p.1 - j p.2)`. -/
theorem continuousOn_Kfun_clean (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ContinuousOn (fun p : UpperHalfPlane × UpperHalfPlane => Kfun ℓ d p.1 p.2)
      {p : UpperHalfPlane × UpperHalfPlane |
        jInvariantFun p.1 ≠ jInvariantFun p.2} := by
  have hdiv : ContinuousOn (fun p : UpperHalfPlane × UpperHalfPlane =>
      AfunFun ℓ d p.1 p.2 / (jInvariantFun p.1 - jInvariantFun p.2))
      {p : UpperHalfPlane × UpperHalfPlane |
        jInvariantFun p.1 ≠ jInvariantFun p.2} :=
    ((continuous_AfunFun ℓ d).continuousOn).div
      continuous_jInvariantFun_sub'.continuousOn
      (fun p hp => sub_ne_zero.mpr hp)
  refine hdiv.congr (fun p hp => ?_)
  rw [eq_div_iff (sub_ne_zero.mpr hp)]
  exact Kfun_mul_slope_eq_AfunFun ℓ d hd p.1 p.2 hp

/-- The clean set of the kernel is open, so `continuousOn_Kfun_clean` gives continuity at every
point of it. -/
theorem continuousAt_Kfun_of_clean {ℓ : Work.Kernels.LogLambdaData} {d : ℕ} (hd : d = 8 ∨ d = 24)
    {p : UpperHalfPlane × UpperHalfPlane}
    (hp : jInvariantFun p.1 ≠ jInvariantFun p.2) :
    ContinuousAt (fun q : UpperHalfPlane × UpperHalfPlane => Kfun ℓ d q.1 q.2) p := by
  have hclosed : IsClosed {q : UpperHalfPlane × UpperHalfPlane |
      jInvariantFun q.1 = jInvariantFun q.2} :=
    isClosed_eq (continuous_jInvariantFun'.comp continuous_fst)
      (continuous_jInvariantFun'.comp continuous_snd)
  have hmem : {q : UpperHalfPlane × UpperHalfPlane |
      jInvariantFun q.1 ≠ jInvariantFun q.2} ∈ 𝓝 p :=
    hclosed.isOpen_compl.mem_nhds hp
  exact (continuousOn_Kfun_clean ℓ d hd).continuousAt hmem

end Work.Asymptotics
