import Mathlib
import Submission.Work.MotAS.ASData

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Guides for the w-free AS link identities

Four lemmas, all stated over an arbitrary `CommRing R` with `(5 : R) = 0` (`h5`), i.e. *without*
the auxiliary root `w` of `X⁵ - X - g` that the statements of `Submission/Work/MotAS/ASLink.lean`
carry.  They are the AS (characteristic `5`) forms of the split identities of
`Submission/Work/MotK/KleinIdents.lean` (+ `MotK/KleinI4.lean`).

```
-- (1) the full vector form of `R^AS ∘ P^AS = s^AS · id`
theorem KleinTwScalarASv {R : Type*} [CommRing R] (a b g : R) (y : Fin 5 → R) (h5 : (5 : R) = 0) :
    kleinRAS a b g (kleinPAS a b g y) = fun i => kleinSecAS a b g y * y i

-- (2) `P^AS ∘ R^AS = s'^AS · id`
theorem KleinTwI2ASb {R : Type*} [CommRing R] (a b g : R) (z : Fin 5 → R) (h5 : (5 : R) = 0) :
    kleinPAS a b g (kleinRAS a b g z) = fun i => kleinSecDualAS a b g z * z i

-- (3) `s^AS (R^AS z) = s'^AS(z)³`, conditional on (2) *uniformly in the ring*
theorem KleinTwI4ASb {R : Type*} [CommRing R] (a b g : R) (z : Fin 5 → R) (h5 : (5 : R) = 0)
    (hI2 : ∀ {S : Type} [CommRing S], (5 : S) = 0 → ∀ (a' b' g' : S) (z' : Fin 5 → S),
      kleinPAS a' b' g' (kleinRAS a' b' g' z') = fun i => kleinSecDualAS a' b' g' z' * z' i) :
    kleinSecAS a b g (kleinRAS a b g z) = kleinSecDualAS a b g z ^ 3

-- (4) the unit condition of the link, w-free
theorem KleinLinkUnitAS_free {R : Type*} [CommRing R] (h5 : (5 : R) = 0) (a b g : R)
    (p v : Fin 5 → R) (hp : kleinQAS a b p = 0) :
    kleinGhomAS a b g p (kleinPAS a b g (kleinStereoAS a b p v))
      = -(kleinSecAS a b g (kleinStereoAS a b p v)) ^ 2 * kleinBilinAS a b p v
          * kleinFhomAS a b g p v
```

## (1) `KleinTwScalarASv`

`Work.MotAS.KleinTwScalarAS_vec` (`Submission/Work/MotAS/KleinTwScalarAS.lean`) is **already
proved**: in any commutative ring containing an element `w` with `w ^ 5 = w + g`, and with
`(5 : A) = 0`, one has `kleinRAS a b g (kleinPAS a b g y) = kleinSecAS a b g y • y`.  The file
also proves the *component `0`* of the w-free statement (`Work.MotAS.KleinTwScalarAS`) by the
standard descent, and this is the model to copy:

* trivial ring: `Subsingleton.elim`;
* otherwise let `p := X^5 - X - C g : Polynomial R` (monic of degree `5 > 0`), `S := AdjoinRoot p`,
  `w := AdjoinRoot.root p`, `hw : w ^ 5 = w + algebraMap R S g` and `h5S : (5 : S) = 0`;
* `AdjoinRoot.of.injective_of_monic_of_degree_pos` (with `Polynomial.monic_X_pow_sub`) makes
  `algebraMap R S` injective;
* apply `KleinTwScalarAS_vec` in `S` to the images of `a, b, g, y`;
* push the identity in `S` back to `R` on both sides using the naturality lemmas
  `KleinTwScalarAS_map_kleinPAS`, `KleinTwScalarAS_map_kleinRAS`, `KleinTwScalarAS_map_kleinSecAS`
  (all proved in the same file).

The entire proof is the one of `KleinTwScalarAS` with the final `congrFun … 0` removed, so it is
short.

## (2) `KleinTwI2ASb`

Split identity to transport: `Work.MotK.KleinIdents.kleinP_kleinR` (proved over any `CommRing`):
`kleinP a b (kleinR a b x) = fun i => kleinSecDual a b x * x i`.

* with `S := AdjoinRoot (X^5 - X - C g)` over `R`, `w := AdjoinRoot.root _`, `zS := φ ∘ z`
  (`φ := AdjoinRoot.of`), `ξ := fun i => ∑ j, asN w i j * zS j`:
  `asTransportR` (`Submission/Work/MotAS/ASTransportR.lean`) gives
  `kleinR (φ a) (φ b) ξ = (asM w).mulVec (kleinRAS (φ a) (φ b) (φ g) zS)`;
* `kleinP_kleinR` at `x := ξ` gives `kleinP (φ a) (φ b) (kleinR (φ a) (φ b) ξ)
  = fun i => kleinSecDual (φ a) (φ b) ξ * ξ i`;
* `asTransportP` gives `kleinP (φ a) (φ b) ξ = (asN w).mulVec (kleinPAS (φ a) (φ b) (φ g) zS)`,
  and `asTransportSD` (`Submission/Work/MotAS/asTransportSD.lean`, or
  `Work.MotAS.SDF2.AsTransportSDKey`) gives `kleinSecDual (φ a) (φ b) ξ = kleinSecDualAS … zS`;
* `asN_mulVec_injective` (`Submission/Work/MotAS/ASMatrix.lean`, needs `isUnit_288`, i.e. `h5S`)
  cancels `asN w`, giving the identity in `S`;
* descend to `R` with `AdjoinRoot.of.injective_of_monic_of_degree_pos` and the `map`-lemmas
  (`map_kleinPAS_mul_comm`, `map_kleinRAS_mul_comm` are in
  `Submission/Work/MotAS/kleinRAS_kleinPAS_mul_comm.lean`;
  a `map`-lemma for `kleinSecDualAS` is a one-liner:
  `simp only [kleinSecDualAS, map_add, map_mul, map_pow, map_natCast] <;> ring`).

This is *exactly* the `AdjoinRoot`-descent of `Submission/Work/MotAS/ASLink.lean`'s `kleinPAS_kleinRAS`
(the `w, hw` version), with the final map-lemma push-forward.  The same skeleton is used (and
written out in full) in `Submission/Work/MotAS/kleinRAS_kleinPAS_mul_comm.lean`.

## (3) `KleinTwI4ASb` — read carefully, the hypothesis must be uniform in the ring

`Work.MotK.KleinI4.lean` is the template: the identity is first reduced to the *multiplied* form
and then cancelled in a universal ring.

* **the multiplied form, in every `CommRing` with `(5 : R) = 0`.**  Let `x := kleinRAS a b g z`.
  `Work.MotAS.KleinTwScalarAS` (**proved**; component `0` of I1, w-free) at `y := x` gives
  `kleinRAS a b g (kleinPAS a b g x) 0 = x 0 * kleinSecAS a b g x`.
  The hypothesis `hI2` at `z` gives `kleinPAS a b g x = fun i => kleinSecDualAS a b g z * z i`;
  homogeneity of `R^AS` (`Work.MotAS.kleinRAS_smul`, proved) turns the left-hand side into
  `kleinSecDualAS a b g z ^ 3 * x 0`.  Hence
  `x 0 * kleinSecAS a b g x = x 0 * kleinSecDualAS a b g z ^ 3`.

* **cancellation needs the universal ring, hence the hypothesis is `∀ {S}, …`.**  A general
  `CommRing` is not a domain and `x 0` need not be a non-zero-divisor.  Copy `MotK/KleinI4.lean`:
  take `Univ := MvPolynomial (Fin 8) (ZMod 5)` (a **domain**, and `(5 : Univ) = 0` automatically),
  with the eight variables standing for `a, b, g, z 0, …, z 4`; the multiplied form holds in `Univ`
  (it is a general-ring identity), so the *only* thing needed from `hI2` in `Univ` is the identity
  itself — which is exactly why `hI2` is quantified over all rings with `(5 : S) = 0`.  In `Univ`,
  `x 0 = kleinRAS (X a) (X b) (X g) (X z) 0` is a **nonzero** polynomial: evaluating at
  `a = 1, b = 0, g = 0, z = (1,0,0,0,0)` leaves `-a⁴ z₀³ = -1 ≠ 0` (all other monomials of
  `kleinRAS0` involve `z i` with `i ≥ 1`), so `x 0` can be cancelled;
* push the result from `Univ` to `R` along the evaluation homomorphism
  (`MvPolynomial.eval₂Hom`), using the naturality lemmas
  (`KleinTwScalarAS_map_kleinRAS`, `KleinTwScalarAS_map_kleinSecAS`, and one-liners for
  `kleinPAS`/`kleinSecDualAS`).

The multiplied form is the only place `hI2` is used; the reviewer's warning ("`hI2` alone gives
only the multiplied identity") is exactly the point above.

## (4) `KleinLinkUnitAS_free`

`Work.MotAS.KleinLinkUnitAS` (`Submission/Work/MotAS/KleinLinkUnitAS.lean`) is **already proved**,
but its statement carries the extra root `w` (`hw : w ^ 5 = w + g`) and the ring `S` where it
holds.  The w-free version is obtained by the same `AdjoinRoot` descent:

* in `S := AdjoinRoot (X^5 - X - C g)` over `R`, with `w := AdjoinRoot.root _`, apply
  `KleinLinkUnitAS` to `φ a, φ b, φ g, w, φ ∘ p, φ ∘ v`, where `φ := AdjoinRoot.of`; the
  hypothesis `kleinQAS (φ a) (φ b) (φ ∘ p) = 0` is the image of `hp` (naturality of `kleinQAS`:
  `simp only [kleinQAS, map_add, map_mul, map_pow, map_ofNat] <;> ring`);
* the resulting identity lives in `S`; apply `φ` to both sides of the *statement in `R`* and use
  the naturality lemmas for `kleinGhomAS`, `kleinPAS`, `kleinStereoAS`, `kleinSecAS`, `kleinBilinAS`,
  `kleinFhomAS` (each is a one-liner `simp only [def_, map_add, map_mul, map_pow, map_sub, map_neg,
  map_ofNat] <;> ring`), then `AdjoinRoot.of.injective_of_monic_of_degree_pos`.

-/

namespace Work.MotAS

end Work.MotAS
