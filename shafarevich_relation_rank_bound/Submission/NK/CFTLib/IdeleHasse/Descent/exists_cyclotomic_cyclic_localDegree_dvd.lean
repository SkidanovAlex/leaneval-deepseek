import Mathlib
import Submission.NK.CFTLib.IdeleHasse.localNormSubgroup
import Submission.Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.NK.CFTLib.IdeleHasse.Descent.exists_prime_dvd_orderOf
import Submission.NK.CFTLib.IdeleHasse.Descent.dvd_localDegree_of_isPrimitiveRoot

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace NK.CFTLib.IdeleHasse.Descent

open NumberField IsDedekindDomain Polynomial

/-- **The arithmetic input: a cyclic cyclotomic extension with prescribed local degree.**

For a number field `K` (with separable closure `K'`), a finite place `Q` of `K` and `N > 0` there
is `m > 0` and a cyclotomic intermediate field `M = K(ζ_m) ⊆ K'` which is cyclic over `K` and such
that the local degree `e(w|Q)·f(w|Q)` at every place `w` of `M` above `Q` is divisible by `N`.

Construction: `M = K(ζ_q)` for a prime `q ∤ NQ` with `N ∣ ord_q(NQ)` (e.g. `q` a prime divisor of
`Φ_{Nk}(NQ)` with `q ∤ Nk`); then `Gal(K(ζ_q)/K) ↪ (ℤ/q)ˣ` is cyclic and the extension is
unramified at `Q` with inertia degree `ord_q(NQ)`. -/
theorem exists_cyclotomic_cyclic_localDegree_dvd
    {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (N : ℕ) (hN : 0 < N) :
    ∃ (m : ℕ) (_ : 0 < m) (M : IntermediateField K K'),
      IsCyclotomicExtension {m} K ↥M ∧
      IsCyclic (↥M ≃ₐ[K] ↥M) ∧
      (∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥M), w.asIdeal.LiesOver Q.asIdeal →
        N ∣ w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K)) := by
  -- the separable closure is separably closed, hence contains a primitive `q`-th root of unity
  haveI hsc : IsSepClosed K' := IsSepClosure.sep_closed (k := K) (K := K')
  haveI hsep : Algebra.IsSeparable K K' := IsSepClosure.separable
  haveI hcz : CharZero K' := by
    haveI : CharZero K := NumberField.to_charZero
    exact charZero_of_injective_algebraMap (RingHom.injective (algebraMap K K'))
  haveI hi : Algebra.IsIntegral K K' := ⟨fun x => Algebra.IsSeparable.isIntegral K x⟩
  -- the residue field of `K` at `Q`, a finite field of cardinality `n ≥ 2`
  haveI hmQ : Q.asIdeal.IsMaximal := inferInstance
  haveI hfQ : Finite (𝓞 K ⧸ Q.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum Q
  haveI : Fintype (𝓞 K ⧸ Q.asIdeal) := Fintype.ofFinite _
  haveI : Field (𝓞 K ⧸ Q.asIdeal) := Ideal.Quotient.field Q.asIdeal
  have hn1 : 1 < Nat.card (𝓞 K ⧸ Q.asIdeal) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  -- the prime `q`
  obtain ⟨q, hq, hqndvd, hNord⟩ :=
    exists_prime_dvd_orderOf (Nat.card (𝓞 K ⧸ Q.asIdeal)) N hn1 hN
  haveI hneq0 : NeZero q := ⟨hq.ne_zero⟩
  haveI : NeZero (q : K') := ⟨by exact_mod_cast hq.ne_zero⟩
  -- a primitive `q`-th root of unity in `K'`
  have hdeg : (cyclotomic q K').degree ≠ 0 := by
    rw [degree_cyclotomic, Nat.totient_prime hq]
    exact_mod_cast Nat.sub_ne_zero_of_lt hq.one_lt
  obtain ⟨ζ, hζ⟩ := IsSepClosed.exists_root (cyclotomic q K') hdeg (separable_cyclotomic q K')
  have hζp : IsPrimitiveRoot ζ q := isRoot_cyclotomic_iff.mp hζ
  -- the cyclotomic intermediate field `M = K(ζ)`
  set M : IntermediateField K K' := IntermediateField.adjoin K ({ζ} : Set K') with hMdef
  haveI hcycM : IsCyclotomicExtension ({q} : Set ℕ) K M :=
    hζp.intermediateField_adjoin_isCyclotomicExtension K
  haveI hfd : FiniteDimensional K M := IsCyclotomicExtension.finiteDimensional {q} K M
  haveI hNF : NumberField M :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField M
  -- `Gal(M/K)` injects into the cyclic group `(ℤ/q)ˣ`
  have hcyc : IsCyclic (M ≃ₐ[K] M) := by
    haveI : IsCyclic (ZMod q)ˣ := by
      rw [ZMod.isCyclic_units_iff]
      rcases eq_or_ne q 2 with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          ⟨q, 1, hq, hq.odd_of_ne_two h, le_refl 1, Or.inl (pow_one q).symm⟩)))
    obtain ⟨ζ', hζ'⟩ := hcycM.exists_isPrimitiveRoot (Set.mem_singleton q) hq.ne_zero
    exact isCyclic_of_injective (IsPrimitiveRoot.autToPow K hζ') (hζ'.autToPow_injective K)
  refine ⟨q, hq.pos, M, hcycM, hcyc, ?_⟩
  -- the local degree at every place above `Q`
  intro w hw
  obtain ⟨ζ', hζ'⟩ := hcycM.exists_isPrimitiveRoot (Set.mem_singleton q) hq.ne_zero
  have hint : IsIntegral ℤ ζ' := hζ'.isIntegral hq.pos
  let ζ'' : 𝓞 M := ⟨ζ', hint⟩
  have hζ'' : IsPrimitiveRoot (ζ'' : M) q := hζ'
  exact dvd_localDegree_of_isPrimitiveRoot Q w hw hq hqndvd hNord ζ'' hζ''

end NK.CFTLib.IdeleHasse.Descent
