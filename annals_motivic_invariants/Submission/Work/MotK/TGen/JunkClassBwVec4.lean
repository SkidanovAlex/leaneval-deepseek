/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.TGen.ChartMaps
import Submission.Work.MotK.TGen.BwVec4Defs
import Submission.Work.MotK.TGen.BwVec4Prime
import Submission.Work.MotK.TGen.BwVec4Ker
import Submission.Work.CrauderKatz.BlowUp.fractionRing_algEquiv_of_algEquiv
import Submission.Work.CrauderKatz.BlowUp.fractionRing_mvPolynomial_finTwo
import Submission.Work.MotK.JunkClassLinearThree
import Submission.Work.MotK.CensusPrime.eq_span_of_height_one

set_option linter.unusedVariables false -- v435-speed

/-!
# `Work.MotK.TGen.JunkClassBwVec4` — every codimension-one point cut out by `ǧ₄` is junk

`bwVec a b h 4 = ǧ₄` is the denominator of the affine coordinates of the inverse link map
`χ = π_p ∘ kleinTwR` of the `T`-twisted Crauder–Katz link — geometrically the strict transform of
the hyperplane `{w₄ = 0}`.  It is a cubic in `K[x₀,x₁,x₂]` whose zero locus is a *rational*
surface: in the normal form `bwFpoly a b h = C γ - C β · X` (`X = X₂`), the relation `β·x = γ`
exhibits the second coordinate `x = γ/β` as a rational function of the first two, so the residue
field of `(ǧ₄)` is the rational surface `K(x₀,x₁) = RatFunc (RatFunc K)`, which is geometrically
ruled over `K`.  Hence every height-one prime containing `ǧ₄` is a junk divisor in the sense of
`Work.MotV.JunkClass`.

## The proof

* `bwVec_four_eq` (`Work.MotK.TGen.BwVec4Defs`) identifies `bwVec a b h 4` with the explicit cubic
  `bwF a b h = γ - β·X₂`, and `bwTau` (`X₂ ↦ X`, `X₀ ↦ C X₀`, `X₁ ↦ C X₁`) carries it to
  `bwFpoly a b h = C γ - C β·X`;
* `BwVec4Prime` (`Work.MotK.TGen.BwVec4Prime`): `bwVec a b h 4` is a prime element of
  `K[x₀,x₁,x₂]` (the cubic surface is irreducible), so `(bwVec a b h 4)` is the *only* height-one
  prime containing it (`Work.MotK.CensusPrime.eq_span_of_height_one`);
* `BwVec4Ker` (`Work.MotK.TGen.BwVec4Ker`): the evaluation map
  `bwTheta a b h : K[X₀,X₁][X] →ₐ[K] FractionRing (K[X₀,X₁])`, `X ↦ γ/β`, has kernel
  `(bwFpoly a b h)`; hence `K[X₀,X₁][X]/(bwFpoly) ↪ K(X₀,X₁)` has fraction field `K(X₀,X₁)`
  (`fractionRing_quotient_span` below, via the universal property of localisations);
* `bwVec4_fractionRing` assembles the chain
  `Frac (K[x₀,x₁,x₂]/(ǧ₄)) ≅ Frac (K[X₀,X₁][X]/(bwFpoly)) ≅ K(X₀,X₁) ≅ RatFunc (RatFunc K)`;
* the final steps are the height-one bookkeeping and `junkClass_of_resF_ratFunc_ratFunc`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotK.TGen

open MvPolynomial

noncomputable section

variable {K : Type} [Field K]

/-- **Step 3.**  From the kernel computation for `bwTheta` to the fraction field of the quotient:
`FractionRing (K[X₀,X₁][X]/(bwFpoly)) ≅ FractionRing (K[X₀,X₁])`.

The map `bwTheta a b h` induces `K[X₀,X₁][X]/(bwFpoly) ↪ FractionRing (K[X₀,X₁])` (injective
because its kernel is `(bwFpoly)` and the target is a field), whose image contains the image of
`K[X₀,X₁]`; hence the fraction field of the quotient is the fraction field of `K[X₀,X₁]`. -/
theorem fractionRing_quotient_span {a b h : K}
    (hker : RingHom.ker (bwTheta a b h) = Ideal.span {bwFpoly a b h}) :
    Nonempty (FractionRing (Polynomial (MvPolynomial (Fin 2) K) ⧸ Ideal.span {bwFpoly a b h})
      ≃ₐ[K] FractionRing (MvPolynomial (Fin 2) K)) := by
  letI : Algebra K (Polynomial (MvPolynomial (Fin 2) K) ⧸ Ideal.span {bwFpoly a b h}) :=
    Ideal.Quotient.algebra K
  have hnotunit : ¬ IsUnit (bwFpoly a b h) := by
    intro hunit
    have htop : (Ideal.span {bwFpoly a b h} :
        Ideal (Polynomial (MvPolynomial (Fin 2) K))) = ⊤ :=
      Ideal.span_singleton_eq_top.mpr hunit
    have hmem : (1 : Polynomial (MvPolynomial (Fin 2) K)) ∈ RingHom.ker (bwTheta a b h) := by
      rw [hker, htop]; trivial
    rw [RingHom.mem_ker, map_one] at hmem
    exact one_ne_zero hmem
  haveI : Nontrivial (Polynomial (MvPolynomial (Fin 2) K) ⧸ Ideal.span {bwFpoly a b h}) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (fun h => hnotunit (Ideal.span_singleton_eq_top.mp h))
  have hsub : Ideal.span {bwFpoly a b h} ≤ RingHom.ker (bwTheta a b h) := by rw [hker]
  let θbar : (Polynomial (MvPolynomial (Fin 2) K) ⧸ Ideal.span {bwFpoly a b h}) →ₐ[K]
      FractionRing (MvPolynomial (Fin 2) K) :=
    Ideal.Quotient.liftₐ (Ideal.span {bwFpoly a b h}) (bwTheta a b h)
      fun x hx => RingHom.mem_ker.mp (hsub hx)
  have hθbar_mk : ∀ x : Polynomial (MvPolynomial (Fin 2) K),
      θbar (Ideal.Quotient.mk (Ideal.span {bwFpoly a b h}) x) = bwTheta a b h x := fun _ => rfl
  have hθbar_C : ∀ s : MvPolynomial (Fin 2) K,
      θbar (Ideal.Quotient.mk (Ideal.span {bwFpoly a b h}) (Polynomial.C s))
        = algebraMap _ _ s := by
    intro s
    rw [hθbar_mk]
    exact bwTheta_C a b h s
  have hinj : Function.Injective θbar := by
    intro x y hxy
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hθbar_mk, hθbar_mk] at hxy
    have huv : u - v ∈ Ideal.span {bwFpoly a b h} := by
      rw [← hker, RingHom.mem_ker, map_sub, hxy, sub_self]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem u v).mpr huv
  letI : Algebra (Polynomial (MvPolynomial (Fin 2) K) ⧸ Ideal.span {bwFpoly a b h})
      (FractionRing (MvPolynomial (Fin 2) K)) := θbar.toRingHom.toAlgebra
  haveI hFR : IsFractionRing (Polynomial (MvPolynomial (Fin 2) K) ⧸ Ideal.span {bwFpoly a b h})
      (FractionRing (MvPolynomial (Fin 2) K)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro m
      rw [RingHom.algebraMap_toAlgebra, isUnit_iff_ne_zero]
      intro h0
      exact nonZeroDivisors.ne_zero m.2 (hinj (h0.trans (map_zero θbar).symm))
    · intro z
      obtain ⟨⟨s, m⟩, hsm⟩ := IsLocalization.surj (nonZeroDivisors (MvPolynomial (Fin 2) K)) z
      refine ⟨(Ideal.Quotient.mk (Ideal.span {bwFpoly a b h}) (Polynomial.C s),
        ⟨Ideal.Quotient.mk (Ideal.span {bwFpoly a b h}) (Polynomial.C m), ?_⟩), ?_⟩
      · show (∀ y : Polynomial (MvPolynomial (Fin 2) K) ⧸ Ideal.span {bwFpoly a b h},
            (Ideal.Quotient.mk (Ideal.span {bwFpoly a b h}) (Polynomial.C m)) * y = 0 →
              y = 0) ∧
          ∀ y : Polynomial (MvPolynomial (Fin 2) K) ⧸ Ideal.span {bwFpoly a b h},
            y * (Ideal.Quotient.mk (Ideal.span {bwFpoly a b h}) (Polynomial.C m)) = 0 → y = 0
        refine ⟨fun y hy => ?_, fun y hy => ?_⟩
        · have h1 : θbar (Ideal.Quotient.mk (Ideal.span {bwFpoly a b h}) (Polynomial.C m)) *
              θbar y = 0 := by rw [← map_mul, hy, map_zero]
          rw [hθbar_C m] at h1
          have h2 : algebraMap (MvPolynomial (Fin 2) K)
              (FractionRing (MvPolynomial (Fin 2) K)) m ≠ 0 := fun hc =>
            nonZeroDivisors.ne_zero m.2 (IsFractionRing.injective _ _ (by rw [hc, map_zero]))
          rcases mul_eq_zero.mp h1 with h | h
          · exact absurd h h2
          · exact hinj (by rw [h, map_zero])
        · have h1 : θbar y * algebraMap (MvPolynomial (Fin 2) K)
              (FractionRing (MvPolynomial (Fin 2) K)) m = 0 := by
            rw [← hθbar_C m, ← map_mul, hy, map_zero]
          have h2 : algebraMap (MvPolynomial (Fin 2) K)
              (FractionRing (MvPolynomial (Fin 2) K)) m ≠ 0 := fun hc =>
            nonZeroDivisors.ne_zero m.2 (IsFractionRing.injective _ _ (by rw [hc, map_zero]))
          rcases mul_eq_zero.mp h1 with h | h
          · exact hinj (by rw [h, map_zero])
          · exact absurd h h2
      · show z * θbar.toRingHom
            (Ideal.Quotient.mk (Ideal.span {bwFpoly a b h}) (Polynomial.C m))
          = θbar.toRingHom (Ideal.Quotient.mk (Ideal.span {bwFpoly a b h}) (Polynomial.C s))
        rw [show θbar.toRingHom (Ideal.Quotient.mk (Ideal.span {bwFpoly a b h}) (Polynomial.C m))
              = algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K)) m
              from hθbar_C m,
            show θbar.toRingHom (Ideal.Quotient.mk (Ideal.span {bwFpoly a b h}) (Polynomial.C s))
              = algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K)) s
              from hθbar_C s]
        simpa using hsm
    · intro x y hxy
      exact ⟨1, by rw [hinj hxy]⟩
  haveI : IsScalarTower K (Polynomial (MvPolynomial (Fin 2) K) ⧸ Ideal.span {bwFpoly a b h})
      (FractionRing (MvPolynomial (Fin 2) K)) :=
    ⟨fun r s t => by
      rw [Algebra.smul_def, Algebra.smul_def r s, map_mul, RingHom.algebraMap_toAlgebra,
        Algebra.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_assoc,
        show θbar.toRingHom ((algebraMap K (Polynomial (MvPolynomial (Fin 2) K) ⧸
            Ideal.span {bwFpoly a b h})) r)
          = algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) r from
          θbar.commutes r]⟩
  exact ⟨(IsLocalization.algEquiv
    (R := Polynomial (MvPolynomial (Fin 2) K) ⧸ Ideal.span {bwFpoly a b h})
    (M := nonZeroDivisors (Polynomial (MvPolynomial (Fin 2) K) ⧸ Ideal.span {bwFpoly a b h}))
    (FractionRing (Polynomial (MvPolynomial (Fin 2) K) ⧸ Ideal.span {bwFpoly a b h}))
    (FractionRing (MvPolynomial (Fin 2) K))).restrictScalars K⟩

/-- Transport of the quotient of `K[X₀,X₁,X₂]` by the cubic to the normal form in
`K[X₀,X₁][X]`, along the variable identification `bwTau`. -/
theorem bwVec4_quotient_algEquiv (a b h : K) :
    Nonempty ((MvPolynomial (Fin 3) K ⧸ Ideal.span {bwVec a b h 4}) ≃ₐ[K]
      (Polynomial (MvPolynomial (Fin 2) K) ⧸ Ideal.span {bwFpoly a b h})) := by
  refine ⟨Ideal.quotientEquivAlg (Ideal.span {bwVec a b h 4})
    (Ideal.span {bwFpoly a b h}) (bwTau K) ?_⟩
  rw [Ideal.map_span, Set.image_singleton, bwVec_four_eq]
  refine congrArg Ideal.span ?_
  ext x
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hx; rw [hx]; exact (bwTau_bwF a b h).symm
  · intro hx; rw [hx]; exact bwTau_bwF a b h

/-- **The residue field of the cubic `bwVec a b h 4` is the rational surface**
`RatFunc (RatFunc K) = K(x₀,x₁)`. -/
theorem bwVec4_fractionRing {a b h : K}
    (hker : RingHom.ker (bwTheta a b h) = Ideal.span {bwFpoly a b h}) :
    Nonempty (FractionRing (MvPolynomial (Fin 3) K ⧸ Ideal.span {bwVec a b h 4})
      ≃ₐ[K] RatFunc (RatFunc K)) := by
  obtain ⟨e1⟩ := bwVec4_quotient_algEquiv a b h
  obtain ⟨e2⟩ := Work.CrauderKatz.BlowUp.fractionRing_algEquiv_of_algEquiv
    (𝕜 := K) (Q := MvPolynomial (Fin 3) K ⧸ Ideal.span {bwVec a b h 4})
    (Q' := Polynomial (MvPolynomial (Fin 2) K) ⧸ Ideal.span {bwFpoly a b h}) e1
  obtain ⟨e3⟩ := fractionRing_quotient_span hker
  obtain ⟨e4⟩ := Work.CrauderKatz.BlowUp.fractionRing_mvPolynomial_finTwo K
  exact ⟨e2.trans (e3.trans e4)⟩

theorem JunkClassBwVec4 {K : Type} [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    ∀ x : Work.MotA.polySpec K 3, Order.coheight x = 1 →
      bwVec a b h 4 ∈ x.asIdeal → Work.MotV.JunkClass K x := by
  intro x hcoh hmem
  have hprime : Prime (bwVec a b h 4) := BwVec4Prime a b h ha hb hh
  have hspan : (Ideal.span {bwVec a b h 4}).IsPrime :=
    (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  have hheight : Ideal.height (Ideal.span {bwVec a b h 4}) = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hprime.ne_zero) hprime.not_isUnit
  -- a height-one prime containing the prime element `bwVec a b h 4` is its principal prime
  have hx : x.asIdeal = Ideal.span {bwVec a b h 4} := by
    haveI : x.asIdeal.IsPrime := x.isPrime
    exact Work.MotK.CensusPrime.eq_span_of_height_one (bwVec a b h 4) hspan hheight x.asIdeal
      (by rw [AlgebraicGeometry.idealHeight_eq_coheight]; exact hcoh) hmem
  have hxe : x = ⟨Ideal.span {bwVec a b h 4}, hspan⟩ := PrimeSpectrum.ext hx
  rw [hxe]
  exact Work.MotK.junkClass_of_resF_ratFunc_ratFunc K _
    (bwVec4_fractionRing (BwVec4Ker a b h ha hb hh))

end

end Work.MotK.TGen
