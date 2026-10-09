import Mathlib
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.NumberTheory.NumberField.Completion.ef_le_finrank_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.sumFinrank_adicCompletion_le_finrank
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField

noncomputable section

namespace Commons.NumberTheory.NumberField.Completion

/-- **The local fundamental identity for adic completions of number fields.**

Let `L / K` be an extension of number fields, `Q` a height-one prime of `𝓞 K` and `q` a
height-one prime of `𝓞 L` lying over `Q`.  The degree `[L_q : K_Q]` of the extension of
`q`-adic and `Q`-adic completions equals the product of the ramification index `e` and the
inertia degree `f` of `q` over `Q`:

`e · f = [L_q : K_Q]`,

where the module structure on `L_q = q.adicCompletion L` over `K_Q = Q.adicCompletion K` is the
one induced by the continuous algebra map
`Commons.RingTheory.Henselian.adicCompletionMap Q q hq`.

*Proof.*  By the *global* fundamental identity (`Ideal.sum_ramification_inertia_eq_finrank`)
the sum over all primes `qq` of `𝓞 L` lying over `Q` of `e(qq)·f(qq)` equals `[L : K]`;
its local avatar (`sumFinrank_adicCompletion_le_finrank`) bounds the sum of the local degrees
`∑_qq [L_qq : K_Q]` by `[L : K]`, while each local degree dominates `e(qq)·f(qq)`
(`ef_le_finrank_adicCompletion`).  Hence both sums are equal, and every inequality is an
equality; the claim for the given prime `q` follows. -/
theorem finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg_aux
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
        q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) =
      @Module.finrank (Q.adicCompletion K) (q.adicCompletion L) _ _
        (RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)).toModule := by
  classical
  let R := NumberField.RingOfIntegers K
  let S := NumberField.RingOfIntegers L
  let e : Q.asIdeal.primesOver S → IsDedekindDomain.HeightOneSpectrum S :=
    fun qq => IsDedekindDomain.HeightOneSpectrum.mk qq.1 qq.2.1
      (Ideal.ne_bot_of_mem_primesOver (A := R) (B := S) Q.ne_bot qq.2)
  let n : Q.asIdeal.primesOver S → ℕ := fun qq =>
    @Module.finrank (Q.adicCompletion K) ((e qq).adicCompletion L) _ _
      (RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q (e qq) qq.2.2)).toModule
  let ef : Q.asIdeal.primesOver S → ℕ := fun qq =>
    (e qq).asIdeal.ramificationIdx R * (e qq).asIdeal.inertiaDeg R
  -- the sum over primes `qq | Q` of the local degrees is at most the global degree `[L : K]`
  have hsumN_le : (∑ qq : Q.asIdeal.primesOver S, n qq) ≤ Module.finrank K L := by
    simpa [n] using (sumFinrank_adicCompletion_le_finrank (K := K) (L := L) Q)
  -- the global fundamental identity: `∑_{qq | Q} e(qq)·f(qq) = [L : K]`
  have hfin : Module.finrank R S = Module.finrank K L := by
    simpa [R, S] using (IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L).symm
  have hsumEF : (∑ qq : Q.asIdeal.primesOver S, ef qq) = Module.finrank K L := by
    rw [← hfin]
    have hsum0 : (∑ qq : Q.asIdeal.primesOver S,
        qq.1.ramificationIdx R * qq.1.inertiaDeg R) = Module.finrank R S := by
      exact Ideal.sum_ramification_inertia_eq_finrank (R := R) (S := S) (p := Q.asIdeal)
    have hcongr : (∑ qq : Q.asIdeal.primesOver S, ef qq) =
        (∑ qq : Q.asIdeal.primesOver S, qq.1.ramificationIdx R * qq.1.inertiaDeg R) := by
      apply Finset.sum_congr rfl
      intro qq _
      simp [ef, e]
    rw [hcongr, hsum0]
  -- the lower bound `e(qq)·f(qq) ≤ [L_qq : K_Q]` for every prime `qq | Q`
  have hge : ∀ qq : Q.asIdeal.primesOver S, ef qq ≤ n qq := by
    intro qq
    simpa [ef, n, e] using
      (ef_le_finrank_adicCompletion (K := K) (L := L) Q (e qq) qq.2.2)
  -- hence `∑ ef ≤ ∑ n`, and with both global bounds the sum of local degrees equals `[L : K]`
  have hsumEF_le_sumN : (∑ qq : Q.asIdeal.primesOver S, ef qq) ≤
      (∑ qq : Q.asIdeal.primesOver S, n qq) := by
    exact Finset.sum_le_sum (fun qq _ => hge qq)
  have hsumN_eq : (∑ qq : Q.asIdeal.primesOver S, n qq) = Module.finrank K L := by
    exact le_antisymm hsumN_le (by rw [← hsumEF]; exact hsumEF_le_sumN)
  -- since both sums agree, all inequalities are equalities
  let qq0 : Q.asIdeal.primesOver S := ⟨q.asIdeal, ⟨q.isPrime, hq⟩⟩
  have hne : n qq0 = ef qq0 := by
    by_contra h
    have hlt : ef qq0 < n qq0 := lt_of_le_of_ne (hge qq0) (by
      intro hEQ
      exact h hEQ.symm)
    have hsumlt : (∑ qq : Q.asIdeal.primesOver S, ef qq) <
        (∑ qq : Q.asIdeal.primesOver S, n qq) := by
      exact Finset.sum_lt_sum (fun qq _ => hge qq) ⟨qq0, Finset.mem_univ qq0, hlt⟩
    rw [hsumEF, hsumN_eq] at hsumlt
    exact (lt_irrefl (Module.finrank K L)) hsumlt
  -- restate in terms of `q` and `Q`
  have hef : ef qq0 = q.asIdeal.ramificationIdx R * q.asIdeal.inertiaDeg R := by
    simp [ef, e, qq0]
  have hfinrank : n qq0 =
      @Module.finrank (Q.adicCompletion K) (q.adicCompletion L) _ _
        (RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)).toModule := by
    dsimp [n, e, qq0]
  rw [← hef, ← hfinrank]
  exact hne.symm

end Commons.NumberTheory.NumberField.Completion
