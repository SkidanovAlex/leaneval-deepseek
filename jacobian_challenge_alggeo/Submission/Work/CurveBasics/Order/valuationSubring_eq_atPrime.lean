import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.Order

/-- The carrier of `valuationSubringAtPrime K v` is contained in any valuation subring whose center
on `A` is `v.asIdeal`. -/
private theorem valuationSubringAtPrime_le_of_center
    {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    (p : Ideal A) (hprime : p.IsPrime) (hne : p ≠ ⊥)
    {W : ValuationSubring K}
    (φ : A →+* ↥W) (hφ : ∀ a : A, (φ a : K) = algebraMap A K a)
    (hcenter : Ideal.comap φ (IsLocalRing.maximalIdeal ↥W) = p) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K ⟨p, hprime, hne⟩ ≤ W := by
  set v : IsDedekindDomain.HeightOneSpectrum A := ⟨p, hprime, hne⟩ with hv
  intro x hx
  change x ∈ (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v).toSubring at hx
  rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_toSubring] at hx
  rw [Subalgebra.mem_toSubring] at hx
  rcases hx with ⟨a, s, hs, rfl⟩
  apply mul_mem
  · rw [← hφ a]
    exact Subtype.property (φ a)
  · have hs' : s ∉ p := by simpa using hs
    have hφs : φ s ∉ IsLocalRing.maximalIdeal ↥W := by
      intro hmem
      have h2 : s ∈ Ideal.comap φ (IsLocalRing.maximalIdeal ↥W) := Ideal.mem_comap.mpr hmem
      rw [hcenter] at h2
      exact hs' h2
    obtain ⟨u, hu⟩ := IsLocalRing.notMem_maximalIdeal.mp hφs
    have huK : ((u : ↥W) : K) = algebraMap A K s := by rw [hu, hφ s]
    have hgoal : (((u⁻¹ : (↥W)ˣ) : ↥W) : K) = (algebraMap A K s)⁻¹ := by
      rw [← huK]
      refine eq_inv_of_mul_eq_one_right ?_
      rw [← Subring.coe_mul, Units.mul_inv]
      simp
    rw [← hgoal]
    exact Subtype.property _

/-- **A valuation subring of `K = Frac A` containing a Dedekind domain `A` whose center on `A` is
the nonzero prime `p` is the localization of `A` at `p`.**

`W` is a valuation subring of `K`, `A ⊆ K` with `K` its fraction field, `φ : A →+* ↥W` is the
inclusion of `A` into `W` (as a subring of `K`), the contraction of the maximal ideal of `W` along
`φ` is the nonzero prime ideal `p`, and `W` is a proper subring of `K`. Then `W` is
`IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p`, the localization of `A` at `p`
inside `K`.

Suggested proof: show `valuationSubringAtPrime K ⟨p, _, _⟩ ≤ W` and conclude with
`ValuationSubring.eq_of_le_of_ne_top`, whose `Ring.KrullDimLE 1` instance for
`valuationSubringAtPrime` is provided by Mathlib. For the inclusion, use
`IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_toSubring`, which identifies the carrier
with `(Localization.subalgebra.ofField K p.primeCompl _).toSubring`, and the fact that the carrier
of `subalgebra.ofField` is by definition (it is a `Subalgebra.copy`) the set of
`algebraMap A K a * (algebraMap A K s)⁻¹` with `a : A` and `s ∈ p.primeCompl`. Then
`algebraMap A K a ∈ W` since `φ a ∈ W`, and `(algebraMap A K s)⁻¹ ∈ W` because `s ∈ p.primeCompl`
means `s ∉ p`, so `φ s ∉ IsLocalRing.maximalIdeal ↥W` by `hcenter`, so `φ s` is a unit of `W` by
`IsLocalRing.notMem_maximalIdeal`, and the inverse of `φ s` in `K` is the image of the inverse unit.
-/
theorem valuationSubring_eq_atPrime
    {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    (p : Ideal A) (hprime : p.IsPrime) (hne : p ≠ ⊥)
    {W : ValuationSubring K} (hW : W ≠ ⊤)
    (φ : A →+* ↥W) (hφ : ∀ a : A, (φ a : K) = algebraMap A K a)
    (hcenter : Ideal.comap φ (IsLocalRing.maximalIdeal ↥W) = p) :
    W = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K ⟨p, hprime, hne⟩ := by
  refine (ValuationSubring.eq_of_le_of_ne_top
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K ⟨p, hprime, hne⟩)
    (valuationSubringAtPrime_le_of_center p hprime hne φ hφ hcenter) hW).symm

end Work.CurveBasics.Order
