import Mathlib
import Submission.Work.ShafarevichKoch.SupportedTower

/-!
# `Work.ShafarevichKoch.kSupported_isPGroup_and_unramified`

The maximal pro-`2` extension `k_∅ = kSupported F 2 ∅` of a number field `F` unramified at *every*
finite prime has pro-`2` Galois group and trivial relative different at each of its finite Galois
levels.  Concretely: for every finite dimensional Galois subextension `L ≤ k_∅`,

* `IsPGroup 2 (L ≃ₐ[F] L)` -- `L` is a finite quotient of a pro-`2` group;
* `differentIdeal (𝓞 F) (𝓞 ↥L) = ⊤` -- `L/F` is unramified at every finite prime.

Both statements are consequences of the fact that `k_∅` is the supremum of the finite Galois
subextensions of `AlgebraicClosure F` which are pro-`2` and whose relative different is supported
on the *empty* set of rational primes (`Submission.NumberField.SupportedPField F 2 ∅`), together
with the two transfer theorems for such a supremum:

* `Commons.FieldTheory.Galois.isPGroup_aut_of_le_iSup_finite_galois_pGroup` (the Galois group of a
  finite Galois subextension of a compositum of `p`-group extensions is a `p`-group);
* `Commons.NumberTheory.NumberField.differentIdeal_supp_le_iSup_finset` (the support of the
  relative different is inherited by finite Galois subextensions), with `S = ∅`.

Since the only `∅`-supported prime divisors are the divisors of the unit ideal, the support
condition for `S = ∅` says exactly that the relative different is `⊤`
(`Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_forall_not_dvd`).  The two statements
are transported back from `AlgebraicClosure F` to `L` along the `F`-algebra isomorphism
`↥L ≃ₐ[F] ↥(L.map k_∅ ≤ Ω)` (`Submission.NumberField.differentIdeal_supp_of_algEquiv`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

theorem kSupported_isPGroup_and_unramified (F : Type) [Field F] [NumberField F]
    (L : IntermediateField F ↥(kSupported F 2 (∅ : Finset ℕ))) [NumberField ↥L]
    (hfd : FiniteDimensional F L) (hgal : IsGalois F L) :
    IsPGroup 2 (L ≃ₐ[F] L) ∧
      differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥L) = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hfdL : FiniteDimensional F ↥L := hfd
  haveI hgalL : IsGalois F ↥L := hgal
  -- the family of finite Galois pro-`2` `∅`-supported subextensions whose supremum is `k_∅`
  let f : Submission.NumberField.SupportedPField F 2 (∅ : Finset ℕ) →
      IntermediateField F (AlgebraicClosure F) := fun i => i.L
  have hfd_f : ∀ i, FiniteDimensional F ↥(f i) := fun i => i.hfd
  have hgal_f : ∀ i, IsGalois F ↥(f i) := fun i => i.hgal
  have hnum_f : ∀ i, NumberField ↥(f i) := fun i => i.hnum
  have hpg_f : ∀ i, IsPGroup 2 (↥(f i) ≃ₐ[F] ↥(f i)) := fun i => i.hpg
  have hsupp_f : ∀ i, ∀ (P : Ideal (𝓞 ↥(f i))), P.IsPrime → P ≠ ⊥ →
      P ∣ differentIdeal (𝓞 F) (𝓞 ↥(f i)) →
        ∃ q ∈ (∅ : Finset ℕ), P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := fun i => i.hsupp
  haveI hfd_fI : ∀ i, FiniteDimensional F ↥(f i) := hfd_f
  haveI hgal_fI : ∀ i, IsGalois F ↥(f i) := hgal_f
  haveI hnum_fI : ∀ i, NumberField ↥(f i) := hnum_f
  -- transport `L` into the algebraic closure of `F`
  let Ω := AlgebraicClosure F
  let K : IntermediateField F Ω := kSupported F 2 (∅ : Finset ℕ)
  let vK : ↥K →ₐ[F] Ω := IntermediateField.val K
  let vL : ↥L →ₐ[F] ↥K := IntermediateField.val L
  let eL : ↥L →ₐ[F] Ω := vK.comp vL
  let L' : IntermediateField F Ω := eL.fieldRange
  let eeqL : ↥L ≃ₐ[F] ↥L' := AlgEquiv.ofInjectiveField eL
  haveI hfdL' : FiniteDimensional F ↥L' := eeqL.toLinearEquiv.finiteDimensional
  haveI hgalL' : IsGalois F ↥L' := IsGalois.of_algEquiv eeqL
  haveI hnumL' : NumberField ↥L' := NumberField.of_module_finite F ↥L'
  have hL'K : L' ≤ ⨆ i, f i := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    change ((vL y : ↥K) : Ω) ∈ ⨆ i, f i
    exact (vL y).2
  -- the Galois group of `L` is a `2`-group: transfer along `↥L ≃ₐ[F] ↥L'`
  have hpgL' : IsPGroup 2 (↥L' ≃ₐ[F] ↥L') :=
    Commons.FieldTheory.Galois.isPGroup_aut_of_le_iSup_finite_galois_pGroup
      (F := F) (K := Ω) (p := 2) (f := f) hfd_f hgal_f hpg_f hL'K
  have hpgL : IsPGroup 2 (↥L ≃ₐ[F] ↥L) := hpgL'.of_equiv (AlgEquiv.autCongr eeqL).symm
  -- the relative different of `L'` is supported on the empty set of rational primes
  have hsuppL' : ∀ (P : Ideal (𝓞 ↥L')), P.IsPrime → P ≠ ⊥ →
      P ∣ differentIdeal (𝓞 F) (𝓞 ↥L') →
        ∃ q ∈ (∅ : Finset ℕ), P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) :=
    Commons.NumberTheory.NumberField.differentIdeal_supp_le_iSup_finset (F := F) (∅ : Finset ℕ)
      hfd_f hgal_f hsupp_f hL'K
  -- transport the support condition back to `L`
  have hsuppL : ∀ (P : Ideal (𝓞 ↥L)), P.IsPrime → P ≠ ⊥ →
      P ∣ differentIdeal (𝓞 F) (𝓞 ↥L) →
        ∃ q ∈ (∅ : Finset ℕ), P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) :=
    Submission.NumberField.differentIdeal_supp_of_algEquiv (F := F) (∅ : Finset ℕ) eeqL.symm
      hsuppL'
  -- an empty support condition forces the relative different to be the unit ideal
  have hdiffL : differentIdeal (𝓞 F) (𝓞 ↥L) = ⊤ := by
    refine Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_forall_not_dvd
      (E := F) (K := ↥L) ?_
    intro Q hQ
    by_cases hQbot : Q = ⊥
    · intro hdvd
      subst hQbot
      obtain ⟨c, hc⟩ := hdvd
      exact differentIdeal_ne_bot (by rw [hc]; simp)
    · intro hdvd
      exact absurd (hsuppL Q hQ hQbot hdvd) (by simp)
  exact ⟨hpgL, hdiffL⟩

end Work.ShafarevichKoch
