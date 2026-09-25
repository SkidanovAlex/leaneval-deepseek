import Mathlib
import Submission.NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime
import Submission.NK.LocalInputs.Instantiation
import Submission.NK.Mine.ResidueCharAutomatic
import Submission.Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists

namespace NK.GlobalCFTdeep.SecondInequality

/-- `CharP` is transported along a ring isomorphism. -/
private theorem charP_of_ringEquiv {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    [Nontrivial R] [Nontrivial S] (e : R ≃+* S) {p : ℕ} (hp : p.Prime) (h : CharP R p) :
    CharP S p := by
  rw [CharP.charP_iff_prime_eq_zero hp] at h ⊢
  rw [← map_natCast (e : R →+* S) p, h, map_zero]

/-- **The residue characteristic of the completion at a finite prime, from the rational prime.**

If the rational prime `p` lies in the prime ideal `𝔮`, then the residue field of the completion
`K_𝔮` has characteristic `p`.  (The residue field of `𝒪_{K_𝔮}` is `𝓞 K / 𝔮`.) -/
private theorem charP_residueField_of_mem_natCast {K : Type} [Field K] [NumberField K]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ}
    (hp : p.Prime) (hmem : (p : NumberField.RingOfIntegers K) ∈ 𝔮.asIdeal) :
    CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K)) p := by
  have hquot : CharP (NumberField.RingOfIntegers K ⧸ 𝔮.asIdeal) p := by
    rw [CharP.charP_iff_prime_eq_zero hp]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  obtain ⟨e⟩ := Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists 𝔮
  exact charP_of_ringEquiv e.symm hp hquot

theorem localIndex_finite_mem {K : Type} [Field K] [NumberField K]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ} (hp : p.Prime)
    (hmem : (p : NumberField.RingOfIntegers K) ∈ 𝔮.asIdeal)
    (hζ : ∃ ζ : 𝔮.adicCompletion K, IsPrimitiveRoot ζ p) :
    Nat.card ((𝔮.adicCompletion K)ˣ ⧸
      (powMonoidHom p : (𝔮.adicCompletion K)ˣ →* (𝔮.adicCompletion K)ˣ).range)
      = p ^ (NK.LocalInputs.localDegree K 𝔮 + 2) := by
  have hchar := charP_residueField_of_mem_natCast 𝔮 hp hmem
  have hcard := NK.LocalInputs.natCard_KummerGroup_adicCompletion_eq_pow 𝔮
    (NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime 𝔮 hp hchar)
  rw [NK.LocalInputs.zetaIndicator_eq_one_iff p (𝔮.adicCompletion K) |>.mpr hζ] at hcard
  change Nat.card (NK.LocalAnabelian.KummerGroup p (𝔮.adicCompletion K)) =
    p ^ (NK.LocalInputs.localDegree K 𝔮 + 2)
  rw [hcard]

end NK.GlobalCFTdeep.SecondInequality
