import Mathlib
import Submission.Work.DSG4b.Defs

set_option linter.style.haveILetI false

namespace Work.DSG4b

universe u

/-- A flat local homomorphism of (commutative) rings does not lower the Krull dimension: for
`R →+* S` with `IsLocalHom f` and `f.Flat`, `ringKrullDim R ≤ ringKrullDim S`.

This is the "going-down" lower bound for flat local maps; it is the ingredient that lets one deduce
`IsRegularLocalRing` of a flat local extension `S` (with
`spanFinrank (maximalIdeal S) ≤ spanFinrank (maximalIdeal R)`) from that of `R`, via
`ringKrullDim R ≤ ringKrullDim S ≤ (maximalIdeal S).spanFinrank ≤ (maximalIdeal R).spanFinrank`
together with `ringKrullDim_le_spanFinrank_maximalIdeal` (Mathlib).

Mathematically: `f` flat implies `Spec S → Spec R` is going-down; a maximal chain of primes in `R`
lifts to a chain in `S`, and for a local map the top prime `𝔪_R` is the contraction of `𝔪_S`. -/
theorem flat_local_le_ringKrullDim {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (f : R →+* S) [IsLocalHom f] (hf : f.Flat) :
    ringKrullDim R ≤ ringKrullDim S := by
  -- View `S` as an `R`-algebra through `f`.  Since `f` is flat, the algebra is flat, and
  -- flatness of the algebra is exactly the going-down property.
  letI : Algebra R S := f.toAlgebra
  haveI : Module.Flat R S := hf
  haveI : Algebra.HasGoingDown R S := Algebra.HasGoingDown.of_flat
  -- The maximal ideal of a local ring is its largest prime, so it is the top of the (inclusion
  -- ordered) prime spectrum; hence `ringKrullDim = Order.height ⊤`.
  -- It therefore suffices to compare the heights of the top elements, i.e. to lift chains of
  -- primes of `R` ending at `𝔪_R` to chains of primes of `S`.
  have key : (Order.height (⊤ : PrimeSpectrum R) : ℕ∞) ≤
      Order.height (⊤ : PrimeSpectrum S) := by
    rw [Order.height_le_iff']
    intro p hp
    -- `𝔪_S` lies over `p.last = 𝔪_R`, so it can serve as the top of the lifted chain.
    haveI : (IsLocalRing.maximalIdeal S).LiesOver (RelSeries.last p).asIdeal := by
      refine Ideal.LiesOver.mk ?_
      rw [Ideal.under_def, RingHom.algebraMap_toAlgebra, IsLocalRing.maximalIdeal_comap f, hp]
      simp
    obtain ⟨L, hlen, -, -⟩ :=
      Ideal.exists_ltSeries_of_hasGoingDown p (IsLocalRing.maximalIdeal S)
    calc (p.length : ℕ∞) = (L.length : ℕ∞) := by rw [hlen]
      _ ≤ Order.height (RelSeries.last L) := Order.length_le_height_last
      _ ≤ Order.height (⊤ : PrimeSpectrum S) := Order.height_mono le_top
  calc ringKrullDim R = ((Order.height (⊤ : PrimeSpectrum R) : ℕ∞) : WithBot ℕ∞) :=
        (Order.height_top_eq_krullDim (α := PrimeSpectrum R)).symm
    _ ≤ ((Order.height (⊤ : PrimeSpectrum S) : ℕ∞) : WithBot ℕ∞) := WithBot.coe_le_coe.mpr key
    _ = ringKrullDim S := Order.height_top_eq_krullDim

end Work.DSG4b
