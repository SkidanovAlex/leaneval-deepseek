import Mathlib
import Submission.Work.SSGRoute.ZDataMup.swCoreDefs
import Submission.Work.SSGRoute.H9.escape_realisation_core_normalised
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Kummer-form history of the Schmidt–Wingberg recursion

`Work.SSGRoute.ZDataMup.HistInv` (in `ZDataMup/swCoreDefs.lean`) records a history of the §4
recursion as a sequence of *classes* `z_m` (plus their escape primes).  The final assembly of the
node `Work.SSGRoute.H9.sw_odd_kummer_core_proved` needs more: the chain at the last escape prime is
the two-place Hilbert reciprocity `χ b_i ψ_N = χ b_N ψ_i`, which is a statement about the *elements*
`b_i, b_N ∈ Kˣ` realising the classes, together with the escape normalisation `v_Q(b) ≡ −1 (mod p)`
(Schmidt–Wingberg condition (1)).  This file therefore fixes the Kummer form of the history:

* `histClass` — the class sequence `m ↦ z_m` read off a history of elements `m ↦ b_m` via the
  level-`K` Kummer cochain `ZSplit.nodeKummerCocharZMod`;
* `HistK` — the conjunction of invariants of a history `f : ℕ → (ValuationSubring Ω × (↥K)ˣ)`:
  finite, `N`-split, pairwise non-`K`-conjugate escape primes, not `K`-conjugate to the blocks of
  their own place set `histPlaces`; the realisation of `½y + histDatum` on the local groups of the
  blocks; the confinement of the ramification outside `cs(T_m) ∪ cs(Q_m)`; and the normalisation
  `χ_{b_m · u} = 0` on the local group of `Q_m` for a uniformiser `u` at the prime of `↥K` below
  `Q_m` (exactly the conclusion of `Work.SSGRoute.H9.escape_realisation_core_normalised`);
* `histClass_HistInv` — the bridge: the class sequence of a `HistK`-history satisfies the class-form
  invariant `Work.SSGRoute.ZDataMup.HistInv`, so that all the class-level bookkeeping proved in
  `ZDataMup/swCoreDefs.lean` (`histDatum_eq_zero_on_T0`, `hist_no_conjPlace_T0`, `shoe_box_matching`,
  `selection_matching`, `sibling_value_vanishing`, …) applies to it.
-/

namespace Work.SSGRoute.H9

open _root_.SSGRoute

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]

/-- **The class sequence of a history of elements**: the `m`-th class is the level-`K` Kummer
cochain of the `m`-th element, paired with the `m`-th escape prime. -/
noncomputable def histClass (K : IntermediateField k Ω) (ζ : Ω) (hζK : ζ ∈ K)
    (hζ : IsPrimitiveRoot ζ p) {n : ℕ} (f : Fin n → (ValuationSubring Ω × (↥K)ˣ)) :
    Fin n → (ValuationSubring Ω × ((Ω ≃ₐ[k] Ω) → ZMod p)) :=
  fun j => ((f j).1, Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f j).2)

/-- **The place set `T_m` of a Kummer-form history.** -/
noncomputable def histPlacesK (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (S : Finset (ValuationSubring Ω)) (ζ : Ω) (hζK : ζ ∈ K) (hζ : IsPrimitiveRoot ζ p) (m : ℕ)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) : Finset (ValuationSubring Ω) :=
  Work.SSGRoute.ZDataMup.histPlaces (p := p) K S (histClass (p := p) K ζ hζK hζ (fun j : Fin m => f j))

/-- **The datum of stage `m`** of a Kummer-form history: the accumulated corrections
`correctionDatum K ½y z_j Q_j` of the earlier stages. -/
noncomputable def histDatumK (K : IntermediateField k Ω) (ζ : Ω) (hζK : ζ ∈ K)
    (hζ : IsPrimitiveRoot ζ p) (S : Finset (ValuationSubring Ω))
    (y : (Ω ≃ₐ[k] Ω) → ZMod p) (m : ℕ) (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) :
    ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p :=
  Work.SSGRoute.ZDataMup.histDatum K y
    (histClass (p := p) K ζ hζK hζ (fun j : Fin m => f j))

/-- **The Kummer-form invariants of a history of the §4 recursion.**  A history
`f : ℕ → (ValuationSubring Ω × (↥K)ˣ)` consists of escape primes `Q_m` together with elements
`b_m ∈ Kˣ`; writing `z_m := χ_{b_m}` for the level-`K` Kummer cochains, the invariants are:

* `Q_m` is a finite place, split in `N`, not `K`-conjugate to any *earlier* escape prime, and not
  `K`-conjugate to any block of its own place set `T_m`;
* `z_m` realises the prescribed total `½y + histDatumK` on the local group of every block of `T_m`;
* `z_m` kills the inertia of every finite place outside `cs(T_m)` and outside the `K`-class of `Q_m`;
* the escape normalisation: there is a uniformiser `u` at the prime `𝔮` of `↥K` below `Q_m` (i.e.
  `FractionalIdeal.count 𝔮 (u) = 1`) such that `χ_{b_m · u}` vanishes on the local group of `Q_m`
  (equivalently `v_{Q_m}(b_m) ≡ −1 (mod p)`, Schmidt–Wingberg's condition (1)). -/
def HistK (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) : Prop :=
  (∀ m : ℕ, SSGRoute.IsFinPlace k ((f m).1)) ∧
  (∀ m : ℕ, SSGRoute.IsSplitIn k N ((f m).1)) ∧
  (∀ m l : ℕ, m < l → ¬ Work.SSGRoute.gesKConj K ((f m).1) ((f l).1)) ∧
  (∀ m : ℕ, ∀ A ∈ histPlacesK (p := p) K S ζ hζK hζ m f,
      ¬ Work.SSGRoute.gesKConj K A ((f m).1)) ∧
  (∀ m : ℕ, ∀ A ∈ histPlacesK (p := p) K S ζ hζK hζ m f,
      ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f m).2 σ =
          (2 : ZMod p)⁻¹ * y σ + histDatumK (p := p) K ζ hζK hζ S y m f A σ) ∧
  (∀ m : ℕ, ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ histPlacesK (p := p) K S ζ hζK hζ m f, ¬ Work.SSGRoute.gesKConj K A B) →
      (¬ Work.SSGRoute.gesKConj K ((f m).1) B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f m).2 σ = 0) ∧
  (∀ m : ℕ, ∃ u : (↥K)ˣ,
      (∃ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
        ((f m).1).comap (algebraMap ↥K Ω) =
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮 ∧
        FractionalIdeal.count ↥K 𝔮
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
            (u : ↥K)) = 1) ∧
      (∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k ((f m).1) →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ ((f m).2 * u) σ = 0))

/-- **The bridge to the class-form invariant.**  The class sequence of a `HistK`-history satisfies
`Work.SSGRoute.ZDataMup.HistInv`: additivity and local constancy come from
`ZSplit.nodeKummerCocharZMod_add` / `_locConst`, and the realisation and confinement clauses are
carried over verbatim. -/
theorem histClass_HistInv (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) (hf : HistK (p := p) K N ζ hζ hζK S y f) :
    Work.SSGRoute.ZDataMup.HistInv (p := p) K N S y
      (fun m => ((f m).1, Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f m).2)) := by
  obtain ⟨hfin, hsplit, hdisj, hexcl, hpres, hunr, hnorm⟩ := hf
  refine ⟨hfin, hsplit, hdisj, ?_, ?_, ?_, ?_, ?_⟩
  · intro m A hA
    exact hexcl m A hA
  · intro m
    exact Work.SSGRoute.ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ (f m).2
  · intro m x hx z hz
    exact Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ (f m).2 x hx z hz
  · intro m A hA σ hσ
    exact hpres m A hA σ hσ
  · intro m B hB hA hQ σ hσK hσI
    exact hunr m B hB hA hQ σ hσK hσI

end Work.SSGRoute.H9
