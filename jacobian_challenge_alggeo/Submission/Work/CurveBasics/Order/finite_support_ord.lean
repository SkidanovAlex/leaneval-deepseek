/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finite support of the order of vanishing on a curve

The divisor of a nonzero rational function on a smooth proper curve has finite support: the
order of vanishing of `h : K(C)` is nonzero at only finitely many places.

The mathematical content is the following.  A nonzero `h ∈ K(C)` is a unit on some nonempty
affine open `U ⊆ C`, hence `ord h Q = 0` for every place `Q` whose point lies in `U`.  So the
support is contained in the complement of `U`.  That complement is a closed subset of `C`
avoiding the generic point, and since `C` is a Noetherian integral scheme all of whose local
rings have Krull dimension at most one, such a closed subset is finite:

* cover `C` by finitely many affine opens `Spec Γ(C, V)` (using Noetherianity);
* `Z ∩ V` corresponds to a proper closed subset `W` of `Spec Γ(C, V)`, which is the zero locus
  of a nonzero ideal `I`;
* every prime containing `I ≠ 0` has height one, hence is minimal over `I`, and there are only
  finitely many minimal primes over `I` in a Noetherian ring.
-/
import Mathlib
import Submission.Work.CurveBasics.Place.Coheight
import Submission.Work.CurveBasics.Point.isClosed_of_coheight_eq_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry
open scoped Classical

namespace Work.CurveBasics.Order

/-- In a Noetherian domain in which every prime has height at most one, a proper closed subset of
the spectrum is finite.  Indeed it is the zero locus of a nonzero ideal, and each of its primes
is minimal over that ideal. -/
theorem finite_of_isClosed_ne_univ {R : Type*} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    (W : Set (PrimeSpectrum R)) (hW : IsClosed W) (hne : W ≠ Set.univ)
    (hheight : ∀ p ∈ W, p.asIdeal.height ≤ (1 : ℕ∞)) : W.Finite := by
  have hWz : W = PrimeSpectrum.zeroLocus (↑(PrimeSpectrum.vanishingIdeal W) : Set R) := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hW.closure_eq]
  have hI : PrimeSpectrum.vanishingIdeal W ≠ ⊥ := by
    intro hbot
    rw [hbot, PrimeSpectrum.zeroLocus_bot] at hWz
    exact hne hWz
  have hfin : ((PrimeSpectrum.vanishingIdeal W).minimalPrimes).Finite :=
    Ideal.finite_minimalPrimes_of_isNoetherianRing R _
  have hsub : (fun p : PrimeSpectrum R => p.asIdeal) '' W ⊆
      (PrimeSpectrum.vanishingIdeal W).minimalPrimes := by
    rintro x ⟨p, hp, rfl⟩
    have hp' : p ∈ PrimeSpectrum.zeroLocus (↑(PrimeSpectrum.vanishingIdeal W) : Set R) := hWz ▸ hp
    rw [Ideal.minimalPrimes, Set.mem_ofPred_eq, Ideal.IsMinimalPrime, minimal_iff]
    refine ⟨⟨p.isPrime, (PrimeSpectrum.mem_zeroLocus p _).mp hp'⟩, ?_⟩
    intro q hq hqp
    by_contra hne'
    have hlt : q < p.asIdeal := lt_of_le_of_ne hqp (fun h => hne' h.symm)
    have hqprime : q.IsPrime := hq.1
    have hp1 : p.asIdeal.height ≤ ((1 : ℕ) : ℕ∞) := by simpa using hheight p hp
    have hqh : q.height < ((1 : ℕ) : ℕ∞) :=
      (Ideal.height_le_iff (p := p.asIdeal) (n := 1)).mp hp1 q hqprime hlt
    have hq0 : q.height = 0 := Order.lt_one_iff.mp (by simpa using hqh)
    have hqbot : q = ⊥ := Ideal.height_eq_zero_iff_eq_bot.mp hq0
    exact hI (le_bot_iff.mp (hq.2.trans_eq hqbot))
  exact Set.Finite.of_finite_image (hfin.subset hsub) (fun p _ q _ h => PrimeSpectrum.ext h)

/-- The part of a closed subset of a curve inside a nonempty affine open is finite, provided the
closed subset avoids the generic point. -/
theorem finite_inter_affineOpen {X : Scheme} [IsIntegral X] [IsNoetherian X]
    (Z : Set X) (hZcl : IsClosed Z) (hZgen : genericPoint X ∉ Z)
    (hco : ∀ z : X, Order.coheight z ≤ 1)
    (V : X.Opens) (hV : IsAffineOpen V) [hVne : Nonempty V] :
    (Z ∩ (V : Set X)).Finite := by
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  haveI : IsDomain Γ(X, V) := inferInstance
  have hWcl : IsClosed (hV.fromSpec ⁻¹' Z) := hZcl.preimage hV.fromSpec.continuous
  have hgenV : genericPoint X ∈ V :=
    (genericPoint_spec X).mem_open_set_iff V.isOpen |>.mpr ⟨hVne.some.1, trivial, hVne.some.2⟩
  obtain ⟨p₀, hp₀⟩ : ∃ p, hV.fromSpec p = genericPoint X := by
    have : genericPoint X ∈ Set.range hV.fromSpec := by
      rw [IsAffineOpen.range_fromSpec]; exact hgenV
    exact this
  have hWne : hV.fromSpec ⁻¹' Z ≠ Set.univ := by
    intro h
    have : p₀ ∈ hV.fromSpec ⁻¹' Z := h ▸ Set.mem_univ p₀
    simp only [Set.mem_preimage, hp₀] at this
    exact hZgen this
  have hheight : ∀ p ∈ hV.fromSpec ⁻¹' Z, p.asIdeal.height ≤ (1 : ℕ∞) := by
    intro p hp
    calc p.asIdeal.height = Order.coheight p := AlgebraicGeometry.idealHeight_eq_coheight _ p
      _ = Order.coheight (hV.fromSpec p) :=
        (AlgebraicGeometry.coheight_eq_of_isOpenImmersion hV.fromSpec).symm
      _ ≤ 1 := hco _
  have hWfin : (hV.fromSpec ⁻¹' Z).Finite :=
    finite_of_isClosed_ne_univ _ hWcl hWne hheight
  exact (hWfin.image hV.fromSpec).subset (by
    intro z hz
    obtain ⟨p, rfl⟩ : ∃ p, hV.fromSpec p = z := by
      have : z ∈ Set.range hV.fromSpec := by rw [IsAffineOpen.range_fromSpec]; exact hz.2
      exact this
    exact ⟨p, hz.1, rfl⟩)

/-- A closed subset of a Noetherian integral scheme of dimension at most one which avoids the
generic point is finite. -/
theorem finite_of_isClosed_of_genericPoint_notMem {X : Scheme} [IsIntegral X] [IsNoetherian X]
    (Z : Set X) (hZcl : IsClosed Z) (hZgen : genericPoint X ∉ Z)
    (hco : ∀ z : X, Order.coheight z ≤ 1) : Z.Finite := by
  let 𝒰 := X.affineCover
  have hcover : Z ⊆ ⋃ i, Set.range (𝒰.f i) := by
    rw [Scheme.Cover.iUnion_range]; exact Set.subset_univ _
  obtain ⟨t, ht⟩ := IsCompact.elim_finite_subcover (TopologicalSpace.NoetherianSpace.isCompact Z)
    (fun i => Set.range (𝒰.f i)) (fun i => IsOpenImmersion.isOpen_range _) hcover
  have hZeq : Z = ⋃ i ∈ (t : Set 𝒰.I₀), (Z ∩ Set.range (𝒰.f i)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp (ht hz)
      exact Set.mem_iUnion₂.mpr ⟨i, hi, hz, hzi⟩
    · intro hz
      obtain ⟨i, -, hzi, -⟩ := Set.mem_iUnion₂.mp hz
      exact hzi
  rw [hZeq]
  refine Set.Finite.biUnion t.finite_toSet ?_
  intro i _
  have hrange : Set.range (𝒰.f i) = ((Scheme.Hom.opensRange (𝒰.f i)) : Set X) := by
    ext z; exact Scheme.Hom.mem_opensRange
  rw [hrange]
  rcases isEmpty_or_nonempty (Scheme.Hom.opensRange (𝒰.f i)) with hV | hV
  · have hempty : (Z ∩ ((Scheme.Hom.opensRange (𝒰.f i)) : Set X)) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      exact hV.false ⟨z, hz.2⟩
    rw [hempty]
    exact Set.finite_empty
  · haveI : Nonempty (Scheme.Hom.opensRange (𝒰.f i)) := hV
    exact finite_inter_affineOpen Z hZcl hZgen hco _ (isAffineOpen_opensRange _)

open Work.CurveBasics in
theorem finite_support_ord {k : Type*} [Field k] (C : Curve k) (h : C.functionField) :
    {Q : C.Place | AlgebraicGeometry.Scheme.ord h Q.point ≠ 0}.Finite := by
  classical
  by_cases hh : h = 0
  · subst hh
    simp
  · obtain ⟨U, hU, f', hne, hgerm, hunit⟩ := AlgebraicGeometry.exists_isUnit_germ_eq C.left h hh
    -- `h` is a unit section on the nonempty affine open `U`, so its order vanishes on `U`
    have hzero : ∀ Q : C.Place, Q.point ∈ (U : C.left.Opens) →
        AlgebraicGeometry.Scheme.ord h Q.point = 0 := by
      intro Q hQ
      have h1 := AlgebraicGeometry.Scheme.ord_of_isUnit (X := C.left) hunit hQ
      rw [hgerm] at h1
      exact h1
    have hgenU : genericPoint C.left ∈ (U : C.left.Opens) := by
      refine (genericPoint_spec C.left).mem_open_set_iff (U : C.left.Opens).isOpen |>.mpr ?_
      exact ⟨hne.some.1, trivial, hne.some.2⟩
    have hcl : IsClosed (((U : C.left.Opens) : Set C.left))ᶜ :=
      (U : C.left.Opens).isOpen.isClosed_compl
    have hgen : genericPoint C.left ∉ (((U : C.left.Opens) : Set C.left))ᶜ :=
      Set.notMem_compl_iff.mpr hgenU
    have hfin : (((U : C.left.Opens) : Set C.left))ᶜ.Finite :=
      finite_of_isClosed_of_genericPoint_notMem _ hcl hgen (fun z => C.coheight_le_one z)
    have himg : ((fun Q : C.Place => Q.point) ''
        {Q : C.Place | AlgebraicGeometry.Scheme.ord h Q.point ≠ 0}).Finite := by
      refine hfin.subset ?_
      rintro z ⟨Q, hQ, rfl⟩
      exact Set.mem_compl fun hQ' => hQ (hzero Q hQ')
    exact Set.Finite.of_finite_image himg (fun Q _ Q' _ hh => Subtype.ext hh)

end Work.CurveBasics.Order
