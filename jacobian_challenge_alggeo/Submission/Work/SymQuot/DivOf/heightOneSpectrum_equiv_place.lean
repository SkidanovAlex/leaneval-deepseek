/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Places of a curve in an affine open are the height one primes of its section ring

For a curve `C` over a field `F` and an affine open `V ⊆ C` such that `Γ(C,V)` is a Dedekind
domain, the places (closed points) of `C` lying in `V` are in bijection with the height one
primes of `Γ(C,V)`, the bijection being

`z ↦ placeIdeal C V z hz = ker (Γ(C,V) → κ(z))`.

The proof is the standard one and rests on the homeomorphism `hV.isoSpec : V ≅ Spec Γ(C,V)`:

* the point of `V` corresponding to a prime `p` is `hV.fromSpec p`, and
  `hV.primeIdealOf (hV.fromSpec p) = p` (`heightOne_primeIdealOf_fromSpec`);
* `hV.primeIdealOf` is injective (`heightOne_primeIdealOf_injective`), with the zero ideal
  corresponding to the generic point (`heightOne_primeIdealOf_genericPoint_eq_bot`);
* a closed point `z ∈ V` is not the generic point of `C`, so its prime ideal is nonzero
  (`heightOne_primeIdealOf_asIdeal_ne_bot_of_place`);
* conversely, a nonzero prime of the Dedekind domain `Γ(C,V)` is maximal, so the corresponding
  point of `V` is a closed point of `C`.
-/
import Mathlib
import Submission.Work.SymQuot.DivOf.AffineCurve
import Submission.Work.SymQuot.DivOf.placeIdeal_isMaximal
import Submission.Work.SymQuot.DivOf.placeIdeal_injective
import Submission.Work.SymQuot.DivOf.isDedekindDomain_sections

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.DivOf

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

/-! ### The correspondence between the points of `Spec Γ(X, U)` and the points of `U` -/

/-- The point of `U` corresponding to a prime `p` of `Γ(X, U)` has prime ideal `p`:
`hU.primeIdealOf` is inverse to `hU.fromSpec` on the points of `U`. -/
lemma heightOne_primeIdealOf_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (p : PrimeSpectrum Γ(X, U)) (hp : hU.fromSpec p ∈ U) :
    hU.primeIdealOf ⟨hU.fromSpec p, hp⟩ = p := by
  show hU.isoSpec.hom ⟨hU.fromSpec p, hp⟩ = p
  rw [show (⟨hU.fromSpec p, hp⟩ : U) = hU.isoSpec.inv p from Subtype.ext rfl]
  exact congrArg (fun f => f p) hU.isoSpec.inv_hom_id

/-- The prime ideal of a point of an affine open determines the point: `hU.primeIdealOf` is
injective, being the homeomorphism `hU.isoSpec` followed by the identification
`U.toSpecΓ : U ≅ Spec Γ(X, U)`. -/
lemma heightOne_primeIdealOf_injective {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Injective hU.primeIdealOf := by
  intro x y h
  have h2 : hU.fromSpec (hU.primeIdealOf x) = hU.fromSpec (hU.primeIdealOf y) :=
    congrArg hU.fromSpec h
  rw [hU.fromSpec_primeIdealOf x, hU.fromSpec_primeIdealOf y] at h2
  exact Subtype.ext h2

/-- The prime ideal of the generic point of `X` inside an affine open `U` is the zero ideal
(since `Γ(X, U)` is a domain). -/
lemma heightOne_primeIdealOf_genericPoint_eq_bot {X : Scheme.{u}} [IsIntegral X] {U : X.Opens}
    [Nonempty U] [IsDomain ↥(X.presheaf.obj (Opposite.op U))]
    (hU : IsAffineOpen U) (h : genericPoint X ∈ U) :
    hU.primeIdealOf ⟨genericPoint X, h⟩ = ⊥ := by
  have hpt : (⟨genericPoint X, h⟩ : U) =
      ⟨genericPoint X,
        ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)⟩ :=
    Subtype.ext rfl
  rw [hpt, hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]

/-- **The ideal of a place in an affine open is nonzero**: a closed point `z` of a curve lying in
an affine open `V` is not the generic point, so its prime ideal in `Γ(C,V)` is not the zero ideal.
Indeed the zero ideal of `Γ(C,V)` corresponds to the generic point of `V`, which is the generic
point of the curve. -/
lemma heightOne_primeIdealOf_asIdeal_ne_bot_of_place {F : Type u} [Field F]
    {C : Work.CurveBasics.Curve F} {V : C.left.Opens} [Nonempty V] (hV : IsAffineOpen V)
    [IsDedekindDomain ↥(C.left.presheaf.obj (Opposite.op V))]
    (z : Work.CurveBasics.Curve.Place C) (hz : z.point ∈ V) :
    (hV.primeIdealOf ⟨z.point, hz⟩).asIdeal ≠ ⊥ := by
  have hgen : genericPoint C.left ∈ V :=
    ((genericPoint_spec C.left).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›)
  intro hbot
  have hne : z.point ≠ genericPoint C.left := by
    intro heq
    have h1 : Order.coheight z.point = 1 := z.eq_coheight_one
    rw [heq, Work.CurveBasics.Curve.coheight_genericPoint] at h1
    exact absurd h1 (by norm_num)
  apply hne
  have hbot' : hV.primeIdealOf ⟨z.point, hz⟩ = (⊥ : PrimeSpectrum Γ(C.left, V)) :=
    PrimeSpectrum.ext (by simpa using hbot)
  have hA : z.point = hV.fromSpec (⊥ : PrimeSpectrum Γ(C.left, V)) := by
    have h := congrArg hV.fromSpec hbot'
    rwa [hV.fromSpec_primeIdealOf] at h
  have hB : hV.fromSpec (⊥ : PrimeSpectrum Γ(C.left, V)) = genericPoint C.left := by
    have h3 : hV.primeIdealOf ⟨genericPoint C.left, hgen⟩ = ⊥ :=
      heightOne_primeIdealOf_genericPoint_eq_bot hV hgen
    rw [← h3, hV.fromSpec_primeIdealOf]
  exact hA.trans hB

/-- **Places of a curve in an affine open are the height one primes of its section ring.**

For an affine open `V` of a curve `C` whose ring of sections `Γ(C,V)` is a Dedekind domain, the
places of `C` lying in `V` correspond bijectively to the height one primes of `Γ(C,V)`, and under
this correspondence a place `z` is sent to the ideal `placeIdeal C V z hz` of functions vanishing
at `z`. -/
theorem heightOneSpectrum_equiv_place {F : Type u} [Field F] {C : Work.CurveBasics.Curve F}
    {V : C.left.Opens} [Nonempty V] (hV : AlgebraicGeometry.IsAffineOpen V)
    [IsDedekindDomain ↥(C.left.presheaf.obj (Opposite.op V))] :
    ∃ e : {z : Work.CurveBasics.Curve.Place C // z.point ∈ V} ≃
        IsDedekindDomain.HeightOneSpectrum ↥(C.left.presheaf.obj (Opposite.op V)),
      ∀ z, (e z).asIdeal = Work.SymQuot.DivOf.placeIdeal C V z.1 z.2 := by
  classical
  -- the generic point of the curve lies in the nonempty open set `V`
  have hgen : genericPoint C.left ∈ V :=
    ((genericPoint_spec C.left).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›)
  -- the map sending a place to its prime ideal in `Γ(C,V)`
  let f : {z : Work.CurveBasics.Curve.Place C // z.point ∈ V} →
      IsDedekindDomain.HeightOneSpectrum Γ(C.left, V) := fun z =>
    ⟨(hV.primeIdealOf ⟨z.1.point, z.2⟩).asIdeal,
      (hV.primeIdealOf ⟨z.1.point, z.2⟩).isPrime,
      heightOne_primeIdealOf_asIdeal_ne_bot_of_place hV z.1 z.2⟩
  have hinj : Function.Injective f := by
    intro z w hzw
    have h1 : (hV.primeIdealOf ⟨z.1.point, z.2⟩).asIdeal =
        (hV.primeIdealOf ⟨w.1.point, w.2⟩).asIdeal := congrArg (fun v => v.asIdeal) hzw
    refine Subtype.ext (placeIdeal_injective hV z.2 w.2 ?_)
    rw [placeIdeal_eq_primeIdealOf hV z.1 z.2, placeIdeal_eq_primeIdealOf hV w.1 w.2]
    exact h1
  have hsurj : Function.Surjective f := by
    intro v
    let p : PrimeSpectrum Γ(C.left, V) := ⟨v.asIdeal, v.isPrime⟩
    -- the point of `V` corresponding to `v`
    have hpV : hV.fromSpec p ∈ V := by
      have h : hV.fromSpec p ∈ Set.range hV.fromSpec := Set.mem_range_self p
      simpa [IsAffineOpen.range_fromSpec] using h
    have hp_ne_bot : p ≠ ⊥ := by
      intro h
      exact v.ne_bot (by simpa using congrArg PrimeSpectrum.asIdeal h)
    -- it is a closed point of the curve, because a nonzero prime of a Dedekind domain is maximal
    have hclosed : IsClosed {hV.fromSpec p} := by
      rcases Work.CurveBasics.Curve.eq_genericPoint_or_isClosed C (hV.fromSpec p) with h | h
      · exfalso
        have hpb : p = ⊥ := by
          have h1 : hV.primeIdealOf ⟨hV.fromSpec p, hpV⟩ = p :=
            heightOne_primeIdealOf_fromSpec hV p hpV
          have h2 : hV.primeIdealOf ⟨hV.fromSpec p, hpV⟩ =
              hV.primeIdealOf ⟨genericPoint C.left, hgen⟩ :=
            congrArg hV.primeIdealOf (Subtype.ext h)
          rw [h2, heightOne_primeIdealOf_genericPoint_eq_bot hV hgen] at h1
          exact h1.symm
        exact hp_ne_bot hpb
      · exact h
    refine ⟨⟨⟨hV.fromSpec p, hclosed⟩, hpV⟩, ?_⟩
    refine IsDedekindDomain.HeightOneSpectrum.ext ?_
    show (hV.primeIdealOf ⟨hV.fromSpec p, hpV⟩).asIdeal = v.asIdeal
    rw [heightOne_primeIdealOf_fromSpec hV p hpV]
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, ?_⟩
  intro z
  change (hV.primeIdealOf ⟨z.1.point, z.2⟩).asIdeal = placeIdeal C V z.1 z.2
  rw [placeIdeal_eq_primeIdealOf hV z.1 z.2]

end Work.SymQuot.DivOf
