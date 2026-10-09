import Submission.NK.RankTheoryDeep.IdeleRankDefs
import Submission.NK.RankTheoryDeep.LocalDegree
import Submission.NK.RankTheoryDeep.dual_localUnits_infinite_eq_zero
import Submission.NK.RankTheoryDeep.dual_localUnits_eq_zero_of_residueChar_ne
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The places above `ℓ`, and the vanishing of the character modules away from them

* `NK.RankTheoryDeep.primeOfOver` — the height-one prime of `𝓞 K` attached to a prime ideal of
  `𝓞 K` lying over `ℓ` (needed because `Ideal.primesOver` is a set of *ideals*, while
  `Place.ofFinite` takes a `HeightOneSpectrum`);
* `NK.RankTheoryDeep.placesOverEll` — the finite set of places of `K` above `ℓ`;
* `NK.RankTheoryDeep.subsingleton_dual_localUnits_of_not_mem_placesOverEll` — every place outside
  that finite set contributes nothing to `Hom_cts(∏_v 𝒪_vˣ, ℤ_ℓ)`: at a finite place the residue
  characteristic is `p ≠ ℓ` (`dual_localUnits_eq_zero_of_residueChar_ne`), at an infinite place the
  local group is `ℝˣ` or `ℂˣ` (`dual_localUnits_infinite_eq_zero`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField

namespace NK.RankTheoryDeep

universe u

/-- The height-one prime of `𝓞 K` attached to a prime ideal of `𝓞 K` lying over `ℓ`. -/
noncomputable def primeOfOver (K : Type u) [Field K] [NumberField K] {ℓ : ℕ} [Fact ℓ.Prime]
    (q : ↥((Ideal.span {(ℓ : ℤ)}).primesOver (NumberField.RingOfIntegers K))) :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) :=
  ⟨q.1, q.2.1, by
    intro hbot
    have h1 : (Ideal.span {(ℓ : ℤ)}) = (⊥ : Ideal ℤ) := by
      rw [q.2.2.over, hbot, Ideal.under_bot]
    have h2 : (ℓ : ℤ) = 0 := Ideal.span_singleton_eq_bot.mp h1
    exact absurd h2 (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero : (ℓ : ℤ) ≠ 0)⟩

/-- **The finite set of places of `K` above `ℓ`**: the finite places whose residue characteristic
is `ℓ`, regarded as places of `K`. -/
noncomputable def placesOverEll (K : Type u) [Field K] [NumberField K] (ℓ : ℕ) [Fact ℓ.Prime] :
    Finset (NK.GlobalCFT.Place K) := by
  classical
  exact (Finset.univ : Finset
      ↥((Ideal.span {(ℓ : ℤ)}).primesOver (NumberField.RingOfIntegers K))).image
    (fun q => NK.GlobalCFT.Place.ofFinite (primeOfOver K q))

theorem not_mem_placesOverEll_ofInfinite (K : Type u) [Field K] [NumberField K]
    {ℓ : ℕ} [Fact ℓ.Prime] (w : NumberField.InfinitePlace K) :
    NK.GlobalCFT.Place.ofInfinite w ∉ placesOverEll K ℓ := by
  classical
  rw [placesOverEll, Finset.mem_image]
  rintro ⟨q, -, hq⟩
  exact NK.GlobalCFT.Place.ofInfinite_ne_ofFinite w (primeOfOver K q) hq.symm

/-- `dualMap` is `ℤ_ℓ`-linear for the pointwise module structure on the continuous dual. -/
theorem dualMap_smul {G H : Type u} [CommGroup G] [TopologicalSpace G] [CommGroup H]
    [TopologicalSpace H] {ℓ : ℕ} [Fact ℓ.Prime] (φ : G →* H) (hφ : Continuous ⇑φ)
    (a : PadicInt ℓ) (χ : NK.Reconstruct.Dual H ℓ) :
    NK.Reconstruct.dualMap ℓ φ hφ (a • χ)
      = a • NK.Reconstruct.dualMap ℓ φ hφ χ := by
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro x
  simp [NK.Reconstruct.dualMap_apply]

/-- **The places of `K` outside `placesOverEll K ℓ` contribute nothing**: at a finite place not
above `ℓ` the residue characteristic is `p ≠ ℓ` (Hensel: `1 + 𝔪` is `ℓ`-divisible), and at an
infinite place the local group is `ℝˣ` or `ℂˣ` (divisible modulo torsion). -/
theorem subsingleton_dual_localUnits_of_not_mem_placesOverEll (K : Type u) [Field K] [NumberField K]
    {ℓ : ℕ} [Fact ℓ.Prime] (v : NK.GlobalCFT.Place K) (hv : v ∉ placesOverEll K ℓ) :
    Subsingleton (NK.Reconstruct.Dual
      (↥(NK.GlobalCFT.Place.localUnits K v)) ℓ) := by
  classical
  rcases v with w | q
  · refine ⟨fun a b => ?_⟩
    rw [dual_localUnits_infinite_eq_zero (K := K) w a,
      dual_localUnits_infinite_eq_zero (K := K) w b]
  · by_cases hq : (ℓ : NumberField.RingOfIntegers K) ∈ q.asIdeal
    · refine absurd ?_ hv
      rw [placesOverEll, Finset.mem_image]
      exact ⟨⟨q.asIdeal, (primesOver_span_iff_mem K q).mpr hq⟩, Finset.mem_univ _, rfl⟩
    · obtain ⟨p, hpp, hpne, hch⟩ := exists_prime_charP_quotient_of_notMem K q hq
      haveI : Fact p.Prime := ⟨hpp⟩
      refine ⟨fun a b => ?_⟩
      rw [dual_localUnits_eq_zero_of_residueChar_ne (K := K) q hch hpne a,
        dual_localUnits_eq_zero_of_residueChar_ne (K := K) q hch hpne b]

end NK.RankTheoryDeep
