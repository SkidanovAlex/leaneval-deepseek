import Mathlib
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.NumberTheory.NumberField.Completion.ef_le_finrank_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.sumFinrank_adicCompletion_le_finrank
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField BigOperators

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField.Completion

open Commons.RingTheory.Henselian

theorem sumFinrank_completions_eq_finrank
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    let e : Q.asIdeal.primesOver (NumberField.RingOfIntegers L) →
        IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) :=
      fun qq => IsDedekindDomain.HeightOneSpectrum.mk qq.1 qq.2.1
        (Ideal.ne_bot_of_mem_primesOver (A := NumberField.RingOfIntegers K)
          (B := NumberField.RingOfIntegers L) Q.ne_bot qq.2)
    (∑ qq : Q.asIdeal.primesOver (NumberField.RingOfIntegers L),
        @Module.finrank (Q.adicCompletion K) ((e qq).adicCompletion L) _ _
          (RingHom.toAlgebra (adicCompletionMap Q (e qq) qq.2.2)).toModule) =
      Module.finrank K L := by
  classical
  intro e
  let P := Q.asIdeal.primesOver (𝓞 L)
  let d (qq : P) : ℕ :=
    @Module.finrank (Q.adicCompletion K) ((e qq).adicCompletion L) _ _
      (RingHom.toAlgebra (adicCompletionMap Q (e qq) qq.2.2)).toModule
  let ef (qq : P) : ℕ := qq.1.ramificationIdx (𝓞 K) * qq.1.inertiaDeg (𝓞 K)
  -- global fundamental identity: ∑_{q | Q} e(q)·f(q) = [L : K]
  have hfin : Module.finrank (𝓞 K) (𝓞 L) = Module.finrank K L := by
    exact (IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L).symm
  have hsum_ef : (∑ qq : P, ef qq) = Module.finrank K L := by
    rw [← hfin]
    dsimp [ef]
    exact Ideal.sum_ramification_inertia_eq_finrank (R := 𝓞 K) (S := 𝓞 L) (p := Q.asIdeal)
  -- termwise lower bound e·f ≤ [L_q : K_Q]
  have hge : ∀ qq : P, ef qq ≤ d qq := by
    intro qq
    have hsp : (e qq).asIdeal = qq.1 := rfl
    simpa [ef, d, e, hsp] using (ef_le_finrank_adicCompletion (K := K) (L := L) Q (e qq) qq.2.2)
  -- upper bound of the sum of local degrees
  have hsum_le : (∑ qq : P, d qq) ≤ Module.finrank K L := by
    simpa [d, e] using (sumFinrank_adicCompletion_le_finrank (K := K) (L := L) Q)
  -- sandwich
  have hsum_ge : Module.finrank K L ≤ (∑ qq : P, d qq) := by
    calc
      Module.finrank K L = (∑ qq : P, ef qq) := hsum_ef.symm
      _ ≤ (∑ qq : P, d qq) := Finset.sum_le_sum (fun qq _ => hge qq)
  have hsum_eq : (∑ qq : P, d qq) = Module.finrank K L := le_antisymm hsum_le hsum_ge
  -- restate in the let-e form of the statement
  calc
    (∑ qq : P, @Module.finrank (Q.adicCompletion K) ((e qq).adicCompletion L) _ _
          (RingHom.toAlgebra (adicCompletionMap Q (e qq) qq.2.2)).toModule)
        = ∑ qq : P, d qq := rfl
    _ = Module.finrank K L := hsum_eq

end Commons.NumberTheory.NumberField.Completion
