import Mathlib
import Submission.Work.SSGRoute.Sha2Lib.exists_unramified_inert_cyclic_level
import Submission.NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely
import Submission.Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
import Submission.Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime
import Submission.Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top
import Submission.Work.SSGRoute.ZDataMup.localNormSubgroup_eq_top_of_isSplitIn
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Sha2Lib

/-- **The splitting of the primes in `Ss` in the level `M`.**

Let `ψ : G_k → 𝔽_p^×` be a (continuous) character with `M = ` the fixed field of `ker ψ` (so that
`M/k` is the cyclic level attached to `ψ`), and let `Ss` be a finite set of primes of `k` such that
the decomposition group of *every* place of `Ω` above each `𝔭 ∈ Ss` is contained in `ker ψ`
(hypothesis `hsplit`).  Then every `𝔭 ∈ Ss` splits completely in `M/k`: for every prime `𝔮` of
`M` above `𝔭`, the ramification index and the inertia degree of `𝔮` over `k` are both `1`. -/
theorem level_char_split_at_places
    (p : ℕ) [Fact p.Prime]
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (M : IntermediateField k Ω) [FiniteDimensional k M] [IsGalois k M] [NumberField ↥M]
    (ψ : (Ω ≃ₐ[k] Ω) →* Multiplicative (ZMod p))
    (hfix : M.fixingSubgroup = ψ.ker)
    (Ss : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)))
    (hsplit : ∀ 𝔭 ∈ Ss, ∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
      A.comap (algebraMap k Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭 →
      ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k A → ψ σ = 1) :
    ∀ 𝔭 ∈ Ss, ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥M),
      𝔮.asIdeal.LiesOver 𝔭.asIdeal →
        𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 ∧
        𝔮.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) = 1 := by
  intro 𝔭 h𝔭 𝔮 h𝔮
  -- A place `A` of `Ω` above `𝔭` (places of an algebraic closure restrict to every prime).
  obtain ⟨A, hA⟩ :=
    Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime
      (K := k) (K' := Ω) 𝔭
  have hAfin : SSGRoute.IsFinPlace k A := by
    show A.comap (algebraMap k Ω) ≠ ⊤
    rw [hA]
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top (K := k) 𝔭
  -- The decomposition group of `A` is contained in `ker ψ =` the fixing subgroup of `M`.
  have hle : SSGRoute.decomp k A ≤ M.fixingSubgroup := by
    intro σ hσ
    rw [hfix]
    exact MonoidHom.mem_ker.mpr (hsplit 𝔭 h𝔭 A hAfin hA σ hσ)
  -- Hence `𝔭` splits completely in `M/k` (its invariant ramification index and inertia degree
  -- are `1`), and then so does every prime of `M` above `𝔭`.
  have hncard : (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers ↥M)).ncard =
      Module.finrank k ↥M :=
    (NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely (K := k) (K' := Ω) (N := M)
      𝔭 A hA).mp hle
  have hIn := (Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
    (K := k) (L := ↥M) 𝔭).mp hncard
  exact ⟨Work.SSGRoute.ZDataMup.ramificationIdx_eq_one_of_ramificationIdxIn_eq_one
            (K := k) (L := ↥M) 𝔭 hIn.1 𝔮 h𝔮,
         Work.SSGRoute.ZDataMup.inertiaDeg_eq_one_of_inertiaDegIn_eq_one
            (K := k) (L := ↥M) 𝔭 hIn.2 𝔮 h𝔮⟩

end Work.SSGRoute.Sha2Lib
