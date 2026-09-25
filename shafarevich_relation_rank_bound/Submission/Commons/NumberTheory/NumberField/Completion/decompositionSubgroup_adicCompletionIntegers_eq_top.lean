import Mathlib
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.NumberTheory.NumberField.Completion.isIntegralClosure_adicCompletionIntegers_extension

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField.Completion

open IsDedekindDomain
open scoped Pointwise

/-- The decomposition subgroup of the ring of integers of a `q`-adic completion, acting on the
completion via the canonical algebra structure over the `Q`-adic completion, is everything:
every `Q.adicCompletion K`-algebra automorphism of `q.adicCompletion L` preserves
`q.adicCompletionIntegers L`.

The reason is that `q.adicCompletionIntegers L` is the integral closure of
`Q.adicCompletionIntegers K` in `q.adicCompletion L`
(`isIntegralClosure_adicCompletionIntegers_extension`), a purely algebraic characterization, so
it is preserved by every `Q.adicCompletion K`-algebra automorphism (which is in particular a
`Q.adicCompletionIntegers K`-algebra automorphism). -/
theorem decompositionSubgroup_adicCompletionIntegers_eq_top {K L : Type*} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    (q.adicCompletionIntegers L).decompositionSubgroup (Q.adicCompletion K) = ⊤ := by
  classical
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletion L) :=
    RingHom.toAlgebra ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
      (Q.adicCompletionIntegers K).subtype)
  haveI hIC : IsIntegralClosure (q.adicCompletionIntegers L) (Q.adicCompletionIntegers K)
      (q.adicCompletion L) :=
    isIntegralClosure_adicCompletionIntegers_extension Q q hq
  -- `q.adicCompletionIntegers L` is exactly the set of elements integral over
  -- `Q.adicCompletionIntegers K`.
  have hiff : ∀ z : q.adicCompletion L,
      z ∈ q.adicCompletionIntegers L ↔ IsIntegral (Q.adicCompletionIntegers K) z := by
    intro z
    constructor
    · intro hz
      exact (IsIntegralClosure.isIntegral_iff (A := q.adicCompletionIntegers L)
        (R := Q.adicCompletionIntegers K) (B := q.adicCompletion L)).mpr ⟨⟨z, hz⟩, rfl⟩
    · intro hz
      obtain ⟨w, hw⟩ := (IsIntegralClosure.isIntegral_iff (A := q.adicCompletionIntegers L)
        (R := Q.adicCompletionIntegers K) (B := q.adicCompletion L)).mp hz
      rw [ValuationSubring.algebraMap_apply] at hw
      exact hw ▸ w.2
  rw [Subgroup.eq_top_iff']
  intro σ
  show σ ∈ MulAction.stabilizer (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
    (q.adicCompletionIntegers L)
  rw [MulAction.mem_stabilizer_iff]
  -- `σ`, being a `Q.adicCompletion K`-algebra automorphism, is also an algebra automorphism
  -- over the subring `Q.adicCompletionIntegers K`, hence preserves integrality.
  let σ' : q.adicCompletion L →ₐ[Q.adicCompletionIntegers K] q.adicCompletion L :=
    { σ.toAlgHom.toRingHom with
      commutes' := fun r => by
        show σ (algebraMap (Q.adicCompletionIntegers K) (q.adicCompletion L) r) =
          algebraMap (Q.adicCompletionIntegers K) (q.adicCompletion L) r
        exact σ.commutes (r : Q.adicCompletion K) }
  have hσ' : ∀ z : q.adicCompletion L,
      IsIntegral (Q.adicCompletionIntegers K) (σ z) ↔
        IsIntegral (Q.adicCompletionIntegers K) z :=
    fun z => isIntegral_algHom_iff σ' σ'.injective (x := z)
  apply SetLike.ext
  intro x
  rw [ValuationSubring.mem_smul_pointwise_iff_exists, hiff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hσ' y).mpr ((hiff y).mp hy)
  · intro hx
    refine ⟨σ.symm x, ?_, ?_⟩
    · refine (hiff (σ.symm x)).mpr ((hσ' (σ.symm x)).mp ?_)
      rw [σ.apply_symm_apply]
      exact hx
    · rw [AlgEquiv.smul_def, σ.apply_symm_apply]

end Commons.NumberTheory.NumberField.Completion
