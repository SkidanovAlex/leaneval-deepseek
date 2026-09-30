import Mathlib
import Submission.Work.SymQuot.Chart
import Submission.Work.SymQuot.Invariants.surjective_specMap_fixedPoints
import Submission.Work.SymQuot.Invariants.fixedPoints_isInvariant

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.SymQuot.Chart

/-- For a `G`-invariant affine open `U ⊆ X`, the fibres of the chart map
`U ⟶ chart U = Spec Γ(X,U)^G` are exactly the `G`-orbits: two points `x y` of `U` have the same
image in the chart if and only if `x` is in the orbit of `y` under the action of `G`.

This is the local model of the statement that the quotient map `X ⟶ X/G` has the orbits as its
fibres.  The ring-theoretic input is that for a finite group acting on a ring `B`, the primes of
`B` lying over a fixed prime of `B^G` form a single orbit
(`Algebra.IsInvariant.exists_smul_of_under_eq`). -/
theorem chartMap_fiber_orbit {G : Type*} [Group G] [Finite G] {X : AlgebraicGeometry.Scheme}
    (A : Work.SymQuot.GAction G X) {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)
    (hUi : A.IsInvariantOpen U) {x y : ↑U.toScheme}
    (h : A.chartMap U hUi x = A.chartMap U hUi y) :
    ∃ g : G, A.hom g (U.ι y) = U.ι x := by
  letI : MulSemiringAction G Γ(X, U) := A.sectionMulSemiringAction U hUi
  haveI : Algebra.IsInvariant (FixedPoints.subring Γ(X,U) G) Γ(X,U) G := inferInstance
  haveI : SMulCommClass G (FixedPoints.subring Γ(X,U) G) Γ(X,U) := ⟨fun g a b => by
    show g • ((a : Γ(X,U)) * b) = (a : Γ(X,U)) * (g • b)
    rw [MulSemiringAction.smul_mul, a.2 g]⟩
  -- Step 1: cancel the isomorphism `U ≅ Spec Γ(X,U)`, i.e. `U.toSpecΓ`.
  have h1 : Spec.map (CommRingCat.ofHom (Subring.subtype (FixedPoints.subring Γ(X,U) G)))
      (U.toSpecΓ x) = Spec.map (CommRingCat.ofHom (Subring.subtype (FixedPoints.subring Γ(X,U) G)))
      (U.toSpecΓ y) := by
    simpa only [Work.SymQuot.GAction.chartMap, Scheme.Hom.comp_apply] using h
  -- Step 2: translate this into an equality of the contractions of the two primes.
  have h2 : (U.toSpecΓ x).asIdeal.under (FixedPoints.subring Γ(X,U) G) =
      (U.toSpecΓ y).asIdeal.under (FixedPoints.subring Γ(X,U) G) := by
    have hh := congrArg PrimeSpectrum.asIdeal h1
    rw [Spec.map_apply, Spec.map_apply] at hh
    exact (PrimeSpectrum.comap_asIdeal (Subring.subtype (FixedPoints.subring Γ(X,U) G))
        (U.toSpecΓ x)).trans (hh.trans (PrimeSpectrum.comap_asIdeal
        (Subring.subtype (FixedPoints.subring Γ(X,U) G)) (U.toSpecΓ y)).symm)
  -- Step 3: the ring-theoretic orbit theorem.
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (A := FixedPoints.subring Γ(X,U) G)
    (B := Γ(X,U)) (G := G) (U.toSpecΓ x).asIdeal (U.toSpecΓ y).asIdeal
    (hP := PrimeSpectrum.isPrime (U.toSpecΓ x)) (hQ := PrimeSpectrum.isPrime (U.toSpecΓ y)) h2
  -- Step 4: `g • P = P.comap (sectionHom g)`, hence `Spec.map (sectionHom g)` maps the point
  -- corresponding to `x` to the point corresponding to `y`.
  have h4 : (U.toSpecΓ y).asIdeal = Ideal.comap (Work.SymQuot.GAction.sectionHom A U hUi g)
      (U.toSpecΓ x).asIdeal := by
    rw [hg]
    ext s
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_comap]
    show Work.SymQuot.GAction.sectionHom A U hUi (g⁻¹)⁻¹ s ∈ (U.toSpecΓ x).asIdeal ↔
      Work.SymQuot.GAction.sectionHom A U hUi g s ∈ (U.toSpecΓ x).asIdeal
    rw [inv_inv]
  have h5 : Spec.map (CommRingCat.ofHom (Work.SymQuot.GAction.sectionHom A U hUi g))
      (U.toSpecΓ x) = U.toSpecΓ y := by
    apply PrimeSpectrum.ext
    have key : (Spec.map (CommRingCat.ofHom (Work.SymQuot.GAction.sectionHom A U hUi g))
        (U.toSpecΓ x)).asIdeal =
        Ideal.comap (Work.SymQuot.GAction.sectionHom A U hUi g) (U.toSpecΓ x).asIdeal := by
      rw [Spec.map_apply]
      exact PrimeSpectrum.comap_asIdeal _ _
    rw [key]
    exact h4.symm
  -- Step 5: identify the two sides with the geometric action on `U`, via `toSpecΓ` naturality.
  have h6 : (A.hom g).resLE U U (le_of_eq (hUi g).symm) x = y := by
    have hn := congrArg (fun (φ : ↑U.toScheme ⟶ Spec Γ(X,U)) => φ x)
      (Scheme.Opens.toSpecΓ_SpecMap_appLE (A.hom g) U U (le_of_eq (hUi g).symm))
    simp only [Scheme.Hom.comp_apply] at hn
    have hn2 : Spec.map (CommRingCat.ofHom (Work.SymQuot.GAction.sectionHom A U hUi g))
        (U.toSpecΓ x) = U.toSpecΓ ((A.hom g).resLE U U (le_of_eq (hUi g).symm) x) := hn
    rw [hn2] at h5
    exact hU.isoSpec.hom.injective (by simpa only [IsAffineOpen.isoSpec_hom] using h5)
  -- Step 6: pass to the ambient scheme and invert the group element.
  refine ⟨g⁻¹, ?_⟩
  have h7 : U.ι y = A.hom g (U.ι x) := by
    have hres := congrArg (fun (φ : ↑U.toScheme ⟶ X) => φ x)
      (Scheme.Hom.resLE_comp_ι (A.hom g) (le_of_eq (hUi g).symm))
    simp only [Scheme.Hom.comp_apply] at hres
    rw [← hres, h6]
  rw [h7]
  have h8 := congrArg (fun (φ : X ⟶ X) => φ (U.ι x)) (A.inv_hom_inv g)
  simpa using h8

end Work.SymQuot.Chart
