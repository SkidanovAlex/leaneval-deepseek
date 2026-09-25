import Mathlib
import Submission.Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow
import Submission.Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing
import Submission.Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists
import Submission.Commons.NumberTheory.NumberField.Completion.mem_ker_units_residue_adicCompletion_iff
import Submission.Commons.NumberTheory.NumberField.Completion.surjective_units_residue_adicCompletion

open scoped NumberField

set_option linter.style.haveILetI false

namespace NK.Reconstruct

/-- Auxiliary group-theoretic lemma: if `g : G →* P` is surjective and its kernel contains the
kernel of a surjective `f : G →* H`, then `g` factors through `f`, so `Nat.card P ∣ Nat.card H`. -/
theorem card_dvd_of_surjective_ker_le {G H P : Type*} [Group G] [Group H] [Group P]
    (f : G →* H) (hf : Function.Surjective f) (g : G →* P) (hg : Function.Surjective g)
    (h : f.ker ≤ g.ker) : Nat.card P ∣ Nat.card H := by
  let ψ : H →* P := MonoidHom.liftOfSurjective f hf ⟨g, h⟩
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := hg y
    exact ⟨f x, by simp [ψ]⟩
  exact Subgroup.card_dvd_of_surjective ψ hψ

/-- Auxiliary: if a natural number `n` has nonzero image in the residue field
`𝓞 K ⧸ Q`, then `n` is a unit of the `Q`-adic integers `𝓞_{K_Q}`.  This is the form in which
`p ≠ ℓ` enters: `ℓ` is nonzero in the residue field of characteristic `p`. -/
theorem isUnit_natCast_adicCompletionIntegers {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {n : ℕ}
    (hn : (n : NumberField.RingOfIntegers K ⧸ Q.asIdeal) ≠ 0) :
    IsUnit ((n : ℕ) : Q.adicCompletionIntegers K) := by
  classical
  obtain ⟨e₀⟩ :=
    Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists (K := K) Q
  let e : IsLocalRing.ResidueField (Q.adicCompletionIntegers K) ≃+*
      (NumberField.RingOfIntegers K ⧸ Q.asIdeal) := e₀
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
  intro h0
  apply hn
  have h2 : e (IsLocalRing.residue (Q.adicCompletionIntegers K)
      ((n : ℕ) : Q.adicCompletionIntegers K)) = (n : NumberField.RingOfIntegers K ⧸ Q.asIdeal) := by
    have hres : IsLocalRing.residue (Q.adicCompletionIntegers K) ((n : ℕ) : Q.adicCompletionIntegers K)
        = ((n : ℕ) : IsLocalRing.ResidueField (Q.adicCompletionIntegers K)) :=
      map_natCast (IsLocalRing.residue (Q.adicCompletionIntegers K)) n
    rw [hres]
    exact map_natCast e n
  have h1 : e (IsLocalRing.residue (Q.adicCompletionIntegers K)
      ((n : ℕ) : Q.adicCompletionIntegers K)) = 0 := by
    rw [h0, map_zero]
  rwa [h2] at h1

/-- **Every finite `ℓ`-group quotient of the units of a `p`-adic field has order dividing `q - 1`.**

Let `K` be a number field, `Q` a finite prime of `K` whose residue field has characteristic `p`,
and `ℓ ≠ p` a prime.  Then for every finite group `P` all of whose elements have `ℓ`-power order,
and every surjective homomorphism `φ : (𝓞_{K_Q})ˣ →* P` from the units of the ring of integers of
the `Q`-adic completion of `K`, the order of `P` divides `q - 1`, where `q` is the cardinality of
`𝓞 K ⧸ Q`.

Proof sketch (add the commons imports you need; the useful ones are
`Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow`,
`Commons.NumberTheory.NumberField.Completion.surjective_units_residue_adicCompletion`,
`Commons.NumberTheory.NumberField.Completion.mem_ker_units_residue_adicCompletion_iff`,
`Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists`):
the principal units `1 + 𝔪` lie in the kernel of `φ`, because `ℓ ∉ 𝔪` (as `p ≠ ℓ`) makes the
`ℓ^n`-th power map on `1 + 𝔪` surjective — Hensel applied to the Kummer polynomial `X^{ℓ^n} - u`
whose residue `1` is an `ℓ^n`-th power — so every `u ∈ 1 + 𝔪` is an `ℓ^n`-th power for every `n`,
while `φ` lands in an `ℓ`-group of order dividing `ℓ^n`.  Hence `φ` factors through
`Oˣ ⧸ (1 + 𝔪) ≅ kˣ`, a cyclic group of order `q - 1`. -/
theorem card_dvd_of_isPGroup_quotient_adicUnits {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {ℓ p : ℕ} [Fact ℓ.Prime] [Fact p.Prime]
    (hres : CharP (NumberField.RingOfIntegers K ⧸ Q.asIdeal) p) (hne : p ≠ ℓ)
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup ℓ P)
    (φ : (Q.adicCompletionIntegers K)ˣ →* P) (hφ : Function.Surjective φ) :
    Nat.card P ∣ Nat.card (NumberField.RingOfIntegers K ⧸ Q.asIdeal) - 1 := by
  classical
  haveI : HenselianLocalRing (Q.adicCompletionIntegers K) :=
    Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing
      (R := NumberField.RingOfIntegers K) (K := K) Q
  let red : (Q.adicCompletionIntegers K)ˣ →* (IsLocalRing.ResidueField
      (Q.adicCompletionIntegers K))ˣ :=
    Units.map (IsLocalRing.residue (Q.adicCompletionIntegers K)).toMonoidHom
  have hred_surj : Function.Surjective red :=
    Commons.NumberTheory.NumberField.Completion.surjective_units_residue_adicCompletion Q
  have hℓ_ne : (ℓ : NumberField.RingOfIntegers K ⧸ Q.asIdeal) ≠ 0 := by
    haveI : CharP (NumberField.RingOfIntegers K ⧸ Q.asIdeal) p := hres
    intro h
    have hdvd : p ∣ ℓ := (CharP.cast_eq_zero_iff (NumberField.RingOfIntegers K ⧸ Q.asIdeal) p ℓ).mp h
    have hple : ℓ = p := ((Fact.out : ℓ.Prime).dvd_iff_eq (Fact.out : p.Prime).ne_one).mp hdvd
    exact hne hple.symm
  have hℓunit : IsUnit ((ℓ : ℕ) : Q.adicCompletionIntegers K) :=
    isUnit_natCast_adicCompletionIntegers Q hℓ_ne
  have hker : red.ker ≤ φ.ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    obtain ⟨m, hm⟩ := hP.exists_card_eq
    have hn0 : ℓ ^ m ≠ 0 := pow_ne_zero m (Fact.out : ℓ.Prime).ne_zero
    haveI : NeZero (ℓ ^ m) := ⟨hn0⟩
    have hunit : IsUnit ((ℓ ^ m : ℕ) : Q.adicCompletionIntegers K) := by
      rw [Nat.cast_pow]
      exact IsUnit.pow m hℓunit
    have hmem : Units.map (IsLocalRing.residue (Q.adicCompletionIntegers K)).toMonoidHom u ∈
        (powMonoidHom (ℓ ^ m)).range := by
      refine ⟨1, ?_⟩
      rw [powMonoidHom_apply, one_pow]
      exact hu.symm
    obtain ⟨w, hw⟩ :=
      Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow (R := Q.adicCompletionIntegers K)
        (ℓ ^ m) hunit u hmem
    rw [powMonoidHom_apply] at hw
    have hdvd : orderOf (φ w) ∣ ℓ ^ m := by
      rw [← hm]
      exact orderOf_dvd_natCard (φ w)
    calc φ u = φ (w ^ (ℓ ^ m)) := by rw [hw]
      _ = (φ w) ^ (ℓ ^ m) := by rw [map_pow]
      _ = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hmain : Nat.card P ∣ Nat.card (IsLocalRing.ResidueField
      (Q.adicCompletionIntegers K))ˣ :=
    card_dvd_of_surjective_ker_le red hred_surj φ hφ hker
  have hcard : Nat.card (IsLocalRing.ResidueField (Q.adicCompletionIntegers K))ˣ =
      Nat.card (NumberField.RingOfIntegers K ⧸ Q.asIdeal) - 1 := by
    rw [Nat.card_units]
    congr 1
    obtain ⟨e⟩ :=
      Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists (K := K) Q
    exact Nat.card_congr e.toEquiv
  rwa [hcard] at hmain

end NK.Reconstruct
