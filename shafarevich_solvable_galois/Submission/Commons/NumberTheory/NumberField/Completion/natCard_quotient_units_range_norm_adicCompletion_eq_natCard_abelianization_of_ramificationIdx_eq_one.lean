import Mathlib
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.NumberTheory.NumberField.Completion.exists_mulEquiv_artinMap_of_ramificationIdx_eq_one
import Submission.Commons.NumberTheory.NumberField.Completion.isCyclic_algEquiv_adicCompletion_of_ramificationIdx_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField.Completion

theorem natCard_quotient_units_range_norm_adicCompletion_eq_natCard_abelianization_of_ramificationIdx_eq_one
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (h1 : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    Nat.card ((Q.adicCompletion K)ˣ ⧸
        MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) :
          q.adicCompletion L →* Q.adicCompletion K))) =
      Nat.card (Abelianization
        (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  obtain ⟨Φ, hΦsurj, hΦker⟩ :=
    exists_mulEquiv_artinMap_of_ramificationIdx_eq_one Q q hq h1
  have hrange : MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) :
        q.adicCompletion L →* Q.adicCompletion K)) = Φ.ker := by
    ext x
    rw [MonoidHom.mem_range, MonoidHom.mem_ker]
    constructor
    · rintro ⟨y, hy⟩
      have h2 : Φ (Units.map (Algebra.norm (Q.adicCompletion K) :
          q.adicCompletion L →* Q.adicCompletion K) y) = 1 :=
        (hΦker _).mpr ⟨y, rfl⟩
      rwa [hy] at h2
    · intro hx
      obtain ⟨y, hy⟩ := (hΦker x).mp hx
      exact ⟨y, Units.ext (by simpa using hy)⟩
  rw [hrange]
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective Φ hΦsurj).toEquiv]
  haveI hcyc : IsCyclic (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
    isCyclic_algEquiv_adicCompletion_of_ramificationIdx_eq_one Q q hq h1
  letI : CommGroup (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
    IsCyclic.commGroup
  exact Nat.card_congr (Abelianization.equivOfComm).toEquiv

end Commons.NumberTheory.NumberField.Completion
