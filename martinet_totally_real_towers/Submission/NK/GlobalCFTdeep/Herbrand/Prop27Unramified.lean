/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFTdeep.Shared
import Submission.NK.GlobalCFTdeep.Herbrand.Prop27Unconditional
import Submission.NK.GlobalCFTdeep.Herbrand.hOne_localUnitSubRep_of_ramificationIdx_eq_one
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_tateCohomology_fiberUnitsRep_eq_one

/-!
# Milne's Proposition 2.7 for `S` containing the ramified primes

This file removes the last hypothesis of `herbrandEq_tIdelesRep_of_fibreTrivial`: the per-place
triviality of the cohomology of the local units.  That triviality is the classical statement

  for an unramified finite place `w | v`,  `Ĥ⁰(D_w, 𝒪_wˣ) = Ĥ¹(D_w, 𝒪_wˣ) = 0`,

which follows from the surjectivity of the norm on local units for unramified extensions
(`hZero_localUnitSubRep_of_ramificationIdx_eq_one`, here deduced from
`hOne_localUnitSubRep_of_ramificationIdx_eq_one` and Herbrand's theorem
`herbrandEq_localUnitSubRep_ofFinite`), together with Shapiro's lemma for the fibre
(`natCard_tateCohomology_fiberUnitsRep_eq_one`).

The resulting theorem is Milne's Proposition 2.7 with exactly the hypothesis under which Milne uses
it: `S` contains every ramified prime (and the archimedean places).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFT
open NK.GlobalCFTdeep

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- A finite place of `K` has an unramified place of `L` above it as soon as every place of `L`
above it has ramification index one; here we only need the existence of *some* place of `L` above
a given finite place of `K`. -/
theorem exists_heightOneSpectrum_liesOver {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q)
        (NK.GlobalCFT.Place.ofFinite Q) := by
  obtain ⟨P₀⟩ := (Ideal.nonempty_primesOver Q.asIdeal :
    Nonempty (Q.asIdeal.primesOver (NumberField.RingOfIntegers L)))
  exact ⟨{ asIdeal := P₀.1
           isPrime := P₀.2.1
           ne_bot := Ideal.ne_bot_of_mem_primesOver Q.ne_bot P₀.2 },
    NK.GlobalCFT.Place.liesOver_ofFinite P₀.2.2⟩

/-- **Milne, *CFT*, Proposition 2.7, unconditional apart from the choice of `S`.**  For a cyclic
extension `L/K` and a finite set `S` of places of `K` containing the archimedean places and every
ramified prime (in the sense that every finite place of `L` outside `T` has ramification index one
over `K`), with `T` the set of places of `L` above `S`,

  `h(𝕀_{L,T}) = ∏_{v ∈ S} |D_{w_v}| = ∏_{v ∈ S} [L_{w_v} : K_v]`. -/
theorem herbrandEq_tIdelesRep_of_unramifiedOutside [IsCyclic (L ≃ₐ[K] L)]
    (S : Finset (Place K)) (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v)
    (hSinf : ∀ a : NumberField.InfinitePlace K, Place.ofInfinite a ∈ S)
    (hunr : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      (∀ v ∈ S, ¬ Place.LiesOver (Place.ofFinite q) v) →
        q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    (w : (v : Place K) → v ∈ S → Place L)
    (hw : ∀ (v : Place K) (hv : v ∈ S), Place.LiesOver (w v hv) v) :
    HerbrandEq (tIdelesRep (L := L) T hT)
      (Finset.prod S.attach (fun v => Nat.card
        (decompositionSubgroup (K := K) (L := L) (w v.1 v.2)))) := by
  classical
  -- ## The per-place triviality of the cohomology of the local units
  have hfib : ∀ v : Place K, v ∉ S →
      Nat.card (tateCohomology (fiberUnitsRep (K := K) (L := L) v) 0) = 1 ∧
        Nat.card (tateCohomology (fiberUnitsRep (K := K) (L := L) v) 1) = 1 := by
    intro v hv
    -- `v` cannot be archimedean
    have hvf : v.IsFinite := by
      rw [Place.isFinite_iff_not_isInfinite]
      intro hvi
      obtain ⟨a, ha⟩ := Place.isInfinite_iff.mp hvi
      exact hv (ha ▸ hSinf a)
    obtain ⟨Q, rfl⟩ := Place.isFinite_iff.mp hvf
    -- choose a place of `L` above `Q`
    obtain ⟨q, hq⟩ := exists_heightOneSpectrum_liesOver (K := K) (L := L) Q
    have hqQ : q.asIdeal.LiesOver Q.asIdeal := by
      rcases hq with ⟨w', v'', h1, h2, h3⟩ | ⟨q'', Q'', h1, h2, h3⟩
      · exact absurd h1.symm (Place.ofInfinite_ne_ofFinite w' q)
      · rw [← Place.ofFinite_inj.mp h1, ← Place.ofFinite_inj.mp h2] at h3
        exact h3
    haveI : q.asIdeal.LiesOver Q.asIdeal := hqQ
    haveI : Fintype (decompositionSubgroup (K := K) (L := L) (Place.ofFinite q)) :=
      Fintype.ofFinite _
    -- `Place.ofFinite q` does not lie in `T`
    have hqT : Place.ofFinite q ∉ T := by
      intro hmem
      obtain ⟨v', hv', hlies⟩ := (hTS _).mp hmem
      have hfin' : v'.IsFinite :=
        (Place.isFinite_of_liesOver hlies).mp (Place.isFinite_ofFinite q)
      obtain ⟨Q', hQ'⟩ := Place.isFinite_iff.mp hfin'
      rw [hQ'] at hlies hv'
      have hqQ' : q.asIdeal.LiesOver Q'.asIdeal := by
        rcases hlies with ⟨w', v'', h1, h2, h3⟩ | ⟨q'', Q'', h1, h2, h3⟩
        · exact absurd h1.symm (Place.ofInfinite_ne_ofFinite w' q)
        · rw [← Place.ofFinite_inj.mp h1, ← Place.ofFinite_inj.mp h2] at h3
          exact h3
      have hQ'Q : Q' = Q := by
        haveI : q.asIdeal.LiesOver Q'.asIdeal := hqQ'
        apply IsDedekindDomain.HeightOneSpectrum.ext
        rw [Ideal.LiesOver.over (P := q.asIdeal) (p := Q'.asIdeal),
          Ideal.LiesOver.over (P := q.asIdeal) (p := Q.asIdeal)]
      rw [hQ'Q] at hv'
      exact hv hv'
    have hunrq : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 :=
      hunr q fun v' _ hlies => hqT ((hTS _).mpr ⟨v', by assumption, hlies⟩)
    -- the local computation at `q`
    have h1 : hOne (localUnitSubRep (K := K) (L := L) (Place.ofFinite q)) = 1 :=
      hOne_localUnitSubRep_of_ramificationIdx_eq_one (K := K) (L := L) Q q hunrq
    have h0 : hZero (localUnitSubRep (K := K) (L := L) (Place.ofFinite q)) = 1 := by
      have hE := herbrandEq_localUnitSubRep_ofFinite (K := K) (L := L) Q q
      rw [HerbrandEq] at hE
      rw [h1, mul_one] at hE
      exact hE
    exact natCard_tateCohomology_fiberUnitsRep_eq_one (K := K) (L := L) (Place.ofFinite Q) q hq
      h0 h1
  exact herbrandEq_tIdelesRep_of_fibreTrivial (K := K) (L := L) S T hT hTS hSinf w hw hfib

end NK.GlobalCFTdeep.Herbrand
