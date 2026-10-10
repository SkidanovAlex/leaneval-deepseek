import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicCompletion_algEquiv_tensor_tmul
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.trace_pi_apply
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped TensorProduct
open IsDedekindDomain

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

noncomputable section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **The local–global trace identity.**  For a number field `K` and a rational prime `p` with
`Q₀ = (p)` in `𝓞 ℚ`, the global trace of `z ∈ K` is the sum of the local traces of its images in
the completions `K_Q`, `Q | Q₀`. -/
theorem sum_trace_adicCompletion_eq_trace {K : Type*} [Field K] [NumberField K]
    (Q0 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    [Fintype {Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
      Q.asIdeal.LiesOver Q0.asIdeal}] (z : K) :
    letI : ∀ Q : {Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
        Q.asIdeal.LiesOver Q0.asIdeal},
        Algebra (Q0.adicCompletion ℚ) (Q.1.adicCompletion K) :=
      fun Q => RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q0 Q.1 Q.2)
    (∑ Q : {Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
        Q.asIdeal.LiesOver Q0.asIdeal},
      Algebra.trace (Q0.adicCompletion ℚ) (Q.1.adicCompletion K)
        (algebraMap K (Q.1.adicCompletion K) z))
      = algebraMap ℚ (Q0.adicCompletion ℚ) (Algebra.trace ℚ K z) := by
  classical
  let F := Q0.adicCompletion ℚ
  let ι := {Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
      Q.asIdeal.LiesOver Q0.asIdeal}
  letI : ∀ Q : ι, Algebra F (Q.1.adicCompletion K) :=
    fun Q => RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q0 Q.1 Q.2)
  haveI : ∀ Q : ι, Module.Finite F (Q.1.adicCompletion K) :=
    fun Q => Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q0 Q.1 Q.2
  haveI : ∀ Q : ι, Module.Free F (Q.1.adicCompletion K) := fun Q => inferInstance
  obtain ⟨e, he⟩ := adicCompletion_algEquiv_tensor_tmul (K := K) Q0
  have h1 := trace_tensorProduct_tmul (K := K) (F := F) z (1 : F)
  have h2 := Algebra.trace_eq_of_algEquiv e (TensorProduct.mk ℚ K F z 1)
  have h3 := trace_pi_apply (R := F) (ι := ι) (fun Q : ι => Q.1.adicCompletion K)
    (e (TensorProduct.mk ℚ K F z 1))
  have hsum : (∑ Q : ι, Algebra.trace F (Q.1.adicCompletion K)
        (algebraMap K (Q.1.adicCompletion K) z))
      = ∑ Q : ι, Algebra.trace F (Q.1.adicCompletion K)
          ((e (TensorProduct.mk ℚ K F z 1)) Q) := by
    refine Finset.sum_congr rfl fun Q _ => ?_
    rw [he z]
  rw [hsum, ← h3, h2]
  exact h1.trans (one_mul _)

end

end Work.SSGRoute.TatePoitouRoute.FinitenessHM
