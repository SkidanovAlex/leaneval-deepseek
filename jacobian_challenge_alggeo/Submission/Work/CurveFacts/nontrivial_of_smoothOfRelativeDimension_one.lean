import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A scheme smooth of relative dimension one over a field has at least two points

This file proves item **A3** of the closure design
(`Submission/Work/NOTES_LEAD_jacobian_closure.md` §2.A): a nonempty scheme which is smooth of
relative dimension one over a field has at least two points.  This supplies the hypothesis
`Nontrivial C.left` required by `Work.CurveBasics.Curve.ofOver`.

The proof implemented here is the following.  `SmoothOfRelativeDimension 1 f` gives, at a point
`x : X`, an affine open `V ∋ x` and an affine open `U ∋ f x` of `Spec K` with
`IsStandardSmoothOfRelativeDimension 1 ((f.appLE U V e).hom)`.  Since `Spec K` is a single point,
`U = ⊤`, so `Γ(Spec K, U) ≃+* K` and the composite `φ : K →+* Γ(X, V)` is standard smooth of
relative dimension one (the relative dimension adds).

The heart of the argument is the ring-theoretic statement
`primeSpectrum_nontrivial_of_isStandardSmoothOfRelativeDimension_one`: if `R` is a domain and a
Jacobson ring, `A` is nontrivial, and `φ : R →+* A` is standard smooth of relative dimension one,
then `PrimeSpectrum A` has at least two points.  It is proved as follows.
`RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial` writes `φ` as `g.comp C`
with `g : R[X] →+* A` *étale*.  Hence `A` is a flat, finitely presented `R[X]`-algebra, so the
induced map `Spec A ⟶ Spec (R[X])` is open (`PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation`,
Chevalley's theorem).  Its image is a nonempty open subset of `Spec (R[X])`; since `R[X]` is a
Jacobson domain that is not a field, this image contains a *closed* point `m` (a maximal ideal,
`PrimeSpectrum.exists_isClosed_singleton_of_isJacobsonRing`) as well as the *generic* point `⊥`
(every nonempty open set of a spectrum with a domain of sections contains the generic point), and
these are distinct.  Pulling back along `Spec A ⟶ Spec (R[X])` gives two distinct points of
`Spec A`.
-/

namespace Work.CurveFacts

universe u

open CategoryTheory AlgebraicGeometry

set_option linter.style.haveILetI false

/-- `R[X]` is not a field for a domain `R`: the variable `X` is a nonzero nonunit (its constant
coefficient is `0`). -/
lemma not_isField_mvPolynomial_fin_one {R : Type*} [CommRing R] [IsDomain R] :
    ¬ IsField (MvPolynomial (Fin 1) R) := by
  intro h
  have hx : (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) R) ≠ 0 := MvPolynomial.X_ne_zero _
  obtain ⟨b, hb⟩ := h.mul_inv_cancel hx
  have h1 : (0 : R) = 1 := by
    have := congrArg (MvPolynomial.constantCoeff (σ := Fin 1) (R := R)) hb
    rwa [map_mul, map_one, MvPolynomial.constantCoeff_X, zero_mul] at this
  exact zero_ne_one h1

/-- **The spectrum of a standard smooth algebra of relative dimension one is nontrivial.**
Let `R` be a domain and a Jacobson ring, `A` a nontrivial ring and `φ : R →+* A` standard smooth
of relative dimension one.  Then `PrimeSpectrum A` has at least two points. -/
theorem primeSpectrum_nontrivial_of_isStandardSmoothOfRelativeDimension_one
    {R A : Type*} [CommRing R] [CommRing A] [IsDomain R] [IsJacobsonRing R]
    {φ : R →+* A} (hφ : φ.IsStandardSmoothOfRelativeDimension 1) [Nontrivial A] :
    Nontrivial (PrimeSpectrum A) := by
  obtain ⟨g, -, hget⟩ := RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial hφ
  have hEt : RingHom.Etale g := hget
  letI : Algebra (MvPolynomial (Fin 1) R) A := g.toAlgebra
  have hEt' : Algebra.Etale (MvPolynomial (Fin 1) R) A := hEt
  haveI : Nonempty (PrimeSpectrum A) := PrimeSpectrum.nonempty_iff_nontrivial.mpr ‹Nontrivial A›
  have hopen : IsOpenMap (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin 1) R) A)) :=
    PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
  obtain ⟨m, hmW, hmc⟩ := PrimeSpectrum.exists_isClosed_singleton_of_isJacobsonRing
    (Set.range (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin 1) R) A)))
    hopen.isOpen_range (Set.range_nonempty _)
  -- The generic point lies in every nonempty open subset of `Spec R[X]`.
  have hbot : (⊥ : PrimeSpectrum (MvPolynomial (Fin 1) R)) ∈
      Set.range (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin 1) R) A)) := by
    by_contra hc
    obtain ⟨s, hs⟩ := (PrimeSpectrum.isOpen_iff _).mp hopen.isOpen_range
    have h1 : (⊥ : PrimeSpectrum (MvPolynomial (Fin 1) R)) ∈ PrimeSpectrum.zeroLocus s := by
      rw [← hs]; exact hc
    have h2 : s ⊆ (⊥ : Ideal (MvPolynomial (Fin 1) R)) := (PrimeSpectrum.mem_zeroLocus _ s).mp h1
    have h3 : PrimeSpectrum.zeroLocus s = Set.univ := by
      refine Set.eq_univ_iff_forall.mpr fun x => ?_
      exact (PrimeSpectrum.mem_zeroLocus x s).mpr fun a ha => by
        rw [Ideal.mem_bot.mp (h2 ha)]; exact x.asIdeal.zero_mem
    have hne : ¬ (Set.range (PrimeSpectrum.comap
        (algebraMap (MvPolynomial (Fin 1) R) A))).Nonempty := by
      rintro ⟨y, hy⟩
      exact (show y ∈ (Set.range (PrimeSpectrum.comap
        (algebraMap (MvPolynomial (Fin 1) R) A)))ᶜ by rw [hs, h3]; trivial) hy
    exact hne (Set.range_nonempty _)
  have hne : (⊥ : PrimeSpectrum (MvPolynomial (Fin 1) R)) ≠ m := by
    intro h
    have hmax : m.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal m).mp hmc
    have hlt : (⊥ : Ideal (MvPolynomial (Fin 1) R)) < m.asIdeal :=
      Ideal.bot_lt_of_maximal _ not_isField_mvPolynomial_fin_one
    rw [show m.asIdeal = (⊥ : Ideal (MvPolynomial (Fin 1) R)) from by rw [← h]; rfl] at hlt
    exact absurd hlt (lt_irrefl ⊥)
  obtain ⟨q₁, hq₁⟩ := hbot
  obtain ⟨q₂, hq₂⟩ := hmW
  exact ⟨q₁, q₂, fun h => hne (by rw [← hq₁, ← hq₂, h])⟩

/-- **A nonempty scheme smooth of relative dimension one over a field has at least two points.**
This is item A3 of the closure design (`Submission/Work/NOTES_LEAD_jacobian_closure.md` §2.A); it
supplies the hypothesis `Nontrivial C.left` required by `Work.CurveBasics.Curve.ofOver`.

Note on a possible misreading: `SmoothOfRelativeDimension 1 f` is *not* implied by "formally smooth
of relative dimension one": the class is `Locally (IsStandardSmoothOfRelativeDimension 1)`
(`MorphismProperty.HasRingHomProperty`), so it demands a finitely presented presentation.  In
particular `Spec K(t) → Spec K` does **not** satisfy it (`K(t)` is not finitely generated as a
`K`-algebra, so it admits no surjection from a polynomial ring over `K`), even though it is a
one-point formally smooth scheme.  So the claim is not contradicted by that example.

Proof route (the shortest one).  `SmoothOfRelativeDimension 1 f` gives, at a point `x ∈ X`, an
affine open `V ∋ x` with `A := Γ(X, V) ≠ 0` and a submersive `K`-presentation of `A` with
`Nat.card ι - Nat.card σ = 1`, i.e. `A ≅ K[X_ι]/I` with `I` generated by `card σ` elements and
`card ι = card σ + 1`.  Since `A ≠ 0` we have `I ≠ ⊤`.  Krull's height result gives
`height I ≤ card σ`, and `K[X_ι]` is a catenary, equidimensional domain of dimension `card ι`,
so `dim A = card ι - height I ≥ card ι - card σ = 1`.  In particular `A` is not a field
(`dim A ≥ 1 > 0`), so `A` has at least two prime ideals (a minimal one and a maximal one); hence
`Spec A ≅ V` and therefore `X` have at least two points, i.e. `Nontrivial X`.

An alternative route avoiding Krull's height result: `A` is standard smooth of relative dimension
one, so `Ω[A/K]` is free of rank one, hence `Ω[A/K] ≠ 0`; if `A` were a field it would be finite
over `K` (Zariski's result), and the fundamental exact sequence
`m/m² → Ω[A/K] ⊗ κ → Ω[κ/K] → 0` at the maximal ideal `m = 0` would force `Ω[A/K] = 0`.

The route implemented in this file is the étale-lifting argument of
`primeSpectrum_nontrivial_of_isStandardSmoothOfRelativeDimension_one`: the locally standard smooth
presentation of `Γ(X, V)` over `K` is refined (via
`RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`) to an étale map
`K[X] →+* Γ(X, V)`, and the openness of the induced map `Spec Γ(X, V) ⟶ Spec K[X]` together with
Jacobsonness of `K[X]` produces two distinct points of the affine chart `V`, hence of `X`. -/
theorem nontrivial_of_smoothOfRelativeDimension_one {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 1 f]
    [Nonempty X] : Nontrivial X := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨U, hU, V, hV, hxV, e, hss⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := f) x
  have hfxU : f x ∈ U := e hxV
  -- `Spec K` is a single point, so the affine open `U` is everything.
  have hUt : U = ⊤ := by
    refine SetLike.ext fun y => ⟨fun _ => trivial, fun _ => ?_⟩
    rw [Subsingleton.elim y (f x)]
    exact hfxU
  subst hUt
  have eKU : K ≃+* Γ(Spec (CommRingCat.of K), ⊤) :=
    Iso.commRingCatIsoToRingEquiv (Scheme.ΓSpecIso (CommRingCat.of K)).symm
  set φ : K →+* Γ(X, V) :=
    (f.appLE ⊤ V e).hom.comp (eKU : K →+* Γ(Spec (CommRingCat.of K), ⊤)) with hφdef
  have hφ : φ.IsStandardSmoothOfRelativeDimension 1 := by
    rw [hφdef]
    exact hss.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv eKU)
  haveI : Nontrivial Γ(X, V) :=
    PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨hV.isoSpec.hom ⟨x, hxV⟩⟩
  have hspec : Nontrivial (PrimeSpectrum Γ(X, V)) :=
    primeSpectrum_nontrivial_of_isStandardSmoothOfRelativeDimension_one hφ
  haveI : Nontrivial (Spec Γ(X, V)) := hspec
  -- `Spec Γ(X, V) ⟶ X` is an open immersion, hence injective on points.
  have hinj : Function.Injective ⇑(hV.fromSpec) :=
    (Scheme.Hom.isOpenEmbedding hV.fromSpec).isEmbedding.injective
  exact Function.Injective.nontrivial hinj

end Work.CurveFacts
