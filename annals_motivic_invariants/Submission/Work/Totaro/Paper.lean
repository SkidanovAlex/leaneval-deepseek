import Submission.Work.Totaro.Cohomology

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.Totaro.Paper` — the paper's appendix, as named inputs + proved consequences

This module records § *Stably birational geometry of K-trivial varieties* of Lin–Shinder,
*Motivic invariants of birational maps* (Annals **199** (1), 2024, tex 2826–3125) — the source of
the input which the CY3 and K3 chapters consume as `TotaroInput` — in two layers:

**The named inputs** (the paper's numbered statements, whose proofs use the negativity lemma,
separable uniruledness, `Proj` and Kollár's theory — none of which Mathlib has):

* `Work.Totaro.ThmBurtCY` — Theorem `thm:BurtCY`:
  (1) `pseudoIso_of_nef`: a birational map of smooth projective varieties with nef canonical
      classes is a pseudo-isomorphism (the negativity lemma);
  (2) `isoOver_of_pseudoIso`: the `Pic`/`NS` step of the paper's proof of the second clause — in
      Picard rank one, a pseudo-isomorphism of smooth projective varieties with nef canonical
      classes is an isomorphism (`Pic(X₂) ≅ Pic(X₁)`, `NS(X₂) ≅ NS(X₁)`, then
      `Proj ⊕_m H⁰(X_i, 𝒪(mH_i))`).
* `Work.Totaro.LemStbirCY` — Lemma `lem-stbirCY`: if `Z`, `Z'` are not separably uniruled and
  `W`, `W'` are separably rationally connected, then a birational map `Z × W ⇢ Z' × W'` descends
  to a birational map `Z ⇢ Z'`.  (The paper states the case `W = W'` — its application; the
  proof given there, which uses only that the *source* factor `W` is s.r.c. to contract, and the
  s.r.c. condition on the target factor for the inverse direction, gives this form.  The
  `W ≠ W'` form is what makes the "in particular `Z` is not stably birational to `Z'`" of
  `cor-CYnSB` go through without a dimension count.)
* `Work.Totaro.CorCYnSB` — Corollary `cor-CYnSB` in the shape in which the two chapters consume
  it: the same-`W` statement (field `not_birational_src`) and the affine form with arbitrary
  exponents (field `not_birational_affine`, the form `TotaroInput` needs).

**The proved layer** (the algebraic content of the appendix):

* `Work.Totaro.ThmBurtCY.isoOver_of_birational_of_nef` — the paper's clause (2) from (1) and the
  `Pic`/`NS` step;
* `Work.Totaro.corCYnSB_of_paper` — **`cor-CYnSB` from the paper's inputs**: `thm:BurtCY` +
  `lem-stbirCY` + the two geometric facts about `K`-trivial varieties (their canonical class is
  nef, since it is trivial; and they are not separably uniruled, Kollár *Rational curves on
  algebraic varieties* Corollary IV.1.11).  Both fields of `CorCYnSB` are produced, with the
  exponents of the affine form handled by `lem-stbirCY` at `W = 𝔸ⁿ`, `W' = 𝔸ᵐ`;
* `Work.Totaro.CorCYnSB.not_birational_cylinder` — the `W = ℙ¹` (i.e. `𝔸¹`) case, the form the
  `ℙ¹`-bundle bridge of the two links consumes;
* `Work.Totaro.CorCYnSB.not_birational_affine_same` — the same-exponent affine case;
* `Work.Totaro.CorCYnSB.not_stablyBirat_of_not_iso` — the `TotaroInput` field, for an arbitrary
  Picard-rank-one predicate family.

## Relation to the cohomological route

This route and the cohomological route of `Submission/Work/Totaro/Cohomology.lean` are independent:
this one is the paper's own, and its inputs are the *geometric* statements whose proofs use the
negative lemma, separable uniruledness, `Proj` and Kollár's theory; the other names a
cohomological certificate (`CohDistinguishing`) whose strength is discussed in `NOTES.md` §5b —
it is at least as strong as the conclusion, and morally equivalent to it, so the reduction which
loses nothing is the present one.  Both are used by `Submission/Work/Totaro/Interface.lean` to
produce the two `TotaroInput`s.  A consumer may take `CorCYnSB` (or the raw `ThmBurtCY` +
`LemStbirCY`) as the named input, in which case `Work.Totaro.CorCYnSB.not_stablyBirat_of_not_iso`
gives the same conclusion; note that the *cohomological* part of the paper's own argument is only
the non-isomorphism of the two centres (`¬ IsoOver`, `lem-nSBG2`), which both chapters already
have, everything else being geometric.

## Caveat on the named-predicate encoding

`IsNefCanonical`, `IsSeparablyRationallyConnected` and `IsNotSeparablyUniruled`
(`Work.Totaro.Defs`) are `Prop`-valued classes with no fields — the workspace's encoding of named
geometric predicates — so any *hypothesis* built from them is trivially satisfiable and the formal
statements above quantify over all varieties, not only over the intended geometric class.  This is
the same convention as `Work.CY3.TotaroInput` / `Work.K3.TotaroInput` themselves (and as
`Work.K3Inputs.CorCYnSB`); see `NOTES.md` §5.  The *content* of a named input is in its fields, not
in its predicate hypotheses.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.Totaro

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-! ## 1. The named inputs -/

/-- **Theorem `thm:BurtCY`** (Totaro; paper tex 2837–2905).

Let `X₁`, `X₂` be smooth projective varieties over a field with a birational map `φ : X₁ ⇢ X₂`, and
assume that `K_{X₁}`, `K_{X₂}` are nef.  Then `φ` is a pseudo-isomorphism.  If in addition
`NS(X₁)_ℚ` or `NS(X₂)_ℚ` is one-dimensional, then `φ` is an isomorphism.

The two clauses are recorded as named fields:

* `pseudoIso_of_nef` — the negativity-lemma clause (paper's proof: `K_Y ∼_ℚ g_i^*K_{X_i} + Z_i`
  for the normalisation `Y` of the graph, and the negativity lemma applied in both directions
  gives `Z₁ = Z₂`);
* `isoOver_of_pseudoIso` — the `Pic`/`NS`/`Proj` clause (paper's proof: a pseudo-isomorphism
  induces `Pic(X₂) ≅ Pic(X₁)` and `NS(X₂) ≅ NS(X₁)`; in rank one every nonzero effective divisor
  is ample, so `φ^*` preserves ampleness and
  `⊕_m H⁰(X₁, 𝒪(mH₁)) ≅ ⊕_m H⁰(X₂, 𝒪(mH₂))`, whence `Proj` gives an isomorphism).

The second clause of the theorem as stated in the paper is `isoOver_of_birational_of_nef` below,
proved from these two fields. -/
structure ThmBurtCY (𝕜 : Type) [Field 𝕜] (Pic1 : Pic1Family 𝕜) : Prop where
  /-- clause (1): nef canonical classes force a birational map to be a pseudo-isomorphism -/
  pseudoIso_of_nef : ∀ (X Y : Scheme.{0}) [Variety 𝕜 X] [Variety 𝕜 Y],
    IsNefCanonical 𝕜 X → IsNefCanonical 𝕜 Y → ∀ (φ : X.BirationalMap Y), IsPseudoIso φ
  /-- the `Pic`/`NS`/`Proj` step: in Picard rank one, a pseudo-isomorphism is an isomorphism -/
  isoOver_of_pseudoIso : ∀ (X Y : Scheme.{0}) [Variety 𝕜 X] [Variety 𝕜 Y],
    IsNefCanonical 𝕜 X → IsNefCanonical 𝕜 Y → Pic1 X → Pic1 Y →
    ∀ (φ : X.BirationalMap Y), IsPseudoIso φ → IsoOver 𝕜 X Y

variable {Pic1 : Pic1Family 𝕜}

/-- **The paper's clause (2) of `thm:BurtCY`**, from clauses (1) and the `Pic`/`NS` step: for
smooth projective varieties with nef canonical classes and Picard rank one, a birational map is an
isomorphism.  This is the clause used in `lem-nSBG2` of the two chapters. -/
theorem ThmBurtCY.isoOver_of_birational_of_nef (B : ThmBurtCY 𝕜 Pic1)
    {X Y : Scheme.{0}} [Variety 𝕜 X] [Variety 𝕜 Y]
    (hX : IsNefCanonical 𝕜 X) (hY : IsNefCanonical 𝕜 Y) (pX : Pic1 X) (pY : Pic1 Y)
    (h : Nonempty (X.BirationalMap Y)) : IsoOver 𝕜 X Y :=
  B.isoOver_of_pseudoIso X Y hX hY pX pY h.some (B.pseudoIso_of_nef X Y hX hY h.some)

/-- **Lemma `lem-stbirCY`** (paper tex 2975–3075): the descent of a birational map of products.

If `Z`, `Z'` are smooth projective varieties (of the same dimension) which are not separably
uniruled and `W`, `W'` are separably rationally connected, then every birational map
`Z × W ⇢ Z' × W'` descends to a birational map `Z ⇢ Z'` (the paper's `φ̄`, unique, making the
diagram commute).

The paper states the case `W = W'` (its application), where the descent of `φ` and of `φ⁻¹` uses
the *same* `W`; the proof given there uses only that the source factor is s.r.c. (to produce the
rational map `Z ⇢ Z'` out of `p = (Z × W ⇢ Z' × W' → Z')`) and that the target factor is s.r.c.
(for the inverse direction), so the `W ≠ W'` form is the same theorem.  It is this form which
makes the "in particular" of `cor-CYnSB` hold for arbitrary exponents. -/
structure LemStbirCY (𝕜 : Type) [Field 𝕜] : Prop where
  /-- the descent -/
  descends : ∀ (Z Z' W W' : Scheme.{0}) [Variety 𝕜 Z] [Variety 𝕜 Z'] [Variety 𝕜 W]
    [Variety 𝕜 W'] (_ : Variety 𝕜 (prodOver 𝕜 Z W)) (_ : Variety 𝕜 (prodOver 𝕜 Z' W')),
    IsNotSeparablyUniruled 𝕜 Z → IsNotSeparablyUniruled 𝕜 Z' →
    IsSeparablyRationallyConnected 𝕜 W → IsSeparablyRationallyConnected 𝕜 W' →
    Nonempty ((prodOver 𝕜 Z W).BirationalMap (prodOver 𝕜 Z' W')) → Nonempty (Z.BirationalMap Z')

/-- **Corollary `cor-CYnSB`** (paper tex 3103–3115), in the shape consumed by the two chapters and
in the `Work.K3Inputs.CorCYnSB` shape (the K3 clone of this statement).

* `not_birational_src` is the paper's statement verbatim: for non-isomorphic `K`-trivial varieties
  of Picard number one over an algebraically closed field and any separably rationally connected
  `W`, `Z × W` is not birational to `Z' × W`;
* `not_birational_affine` is the "in particular `Z` is not stably birational to `Z'`", in the
  exponent form `∃ n m, Z × 𝔸ⁿ ∼ Z' × 𝔸ᵐ` which is the definition of `Work.K3.StablyBirational`
  and hence exactly the field of the two chapters' `TotaroInput`.

The two fields are *not* interchangeable: the second is the first with `W` allowed to differ on the
two sides (`W = 𝔸ⁿ`, `W' = 𝔸ᵐ`).  Both are produced in `corCYnSB_of_paper` from the paper's
inputs. -/
structure CorCYnSB (𝕜 : Type) [Field 𝕜] (Pic1 : Pic1Family 𝕜) : Prop where
  /-- the paper's `cor-CYnSB`: the same separably rationally connected factor on both sides -/
  not_birational_src : ∀ (Z Z' W : Scheme.{0}) [Variety 𝕜 Z] [Variety 𝕜 Z'] [Variety 𝕜 W],
    IsKTrivial 𝕜 Z → IsKTrivial 𝕜 Z' → Pic1 Z → Pic1 Z' → ¬ IsoOver 𝕜 Z Z' →
    IsSeparablyRationallyConnected 𝕜 W →
    ∀ (_ : Variety 𝕜 (prodOver 𝕜 Z W)) (_ : Variety 𝕜 (prodOver 𝕜 Z' W)),
      ¬ Nonempty ((prodOver 𝕜 Z W).BirationalMap (prodOver 𝕜 Z' W))
  /-- the affine form with the two exponents allowed to differ: the form `TotaroInput` needs -/
  not_birational_affine : ∀ (Z Z' : Scheme.{0}) [Variety 𝕜 Z] [Variety 𝕜 Z'],
    IsKTrivial 𝕜 Z → IsKTrivial 𝕜 Z' → Pic1 Z → Pic1 Z' → ¬ IsoOver 𝕜 Z Z' →
    ∀ (n m : ℕ) (_ : Variety 𝕜 (prodOver 𝕜 Z (AffineN 𝕜 n)))
      (_ : Variety 𝕜 (prodOver 𝕜 Z' (AffineN 𝕜 m))),
      ¬ Nonempty ((prodOver 𝕜 Z (AffineN 𝕜 n)).BirationalMap (prodOver 𝕜 Z' (AffineN 𝕜 m)))

/-! ## 2. `cor-CYnSB` from the paper's inputs -/

/-- **The paper's proof of `cor-CYnSB`, as a theorem.**

Given `thm:BurtCY`, `lem-stbirCY` and the two facts about `K`-trivial varieties — their canonical
class is nef (it is trivial) and they are not separably uniruled (Kollár, *Rational curves on
algebraic varieties*, Corollary IV.1.11) — the corollary holds in both of its forms.

For the first field: a birational map `Z × W ⇢ Z' × W` descends to `Z ⇢ Z'` by `lem-stbirCY`, and
`thm:BurtCY` (2) then makes `Z ≅ Z'` over `𝕜`, contradicting `¬ IsoOver 𝕜 Z Z'`.  For the second
field the same argument is run with `W = 𝔸ⁿ`, `W' = 𝔸ᵐ` (both separably rationally connected). -/
theorem corCYnSB_of_paper (B : ThmBurtCY 𝕜 Pic1) (L : LemStbirCY 𝕜)
    (hnef : ∀ (X : Scheme.{0}) [Variety 𝕜 X], IsKTrivial 𝕜 X → IsNefCanonical 𝕜 X)
    (hSU : ∀ (X : Scheme.{0}) [Variety 𝕜 X], IsKTrivial 𝕜 X → IsNotSeparablyUniruled 𝕜 X) :
    CorCYnSB 𝕜 Pic1 where
  not_birational_src := fun Z Z' W _ _ _ hZ hZ' hP hP' hne hSRC hZW hZ'W hbir =>
    hne (B.isoOver_of_birational_of_nef (hnef Z hZ) (hnef Z' hZ') hP hP'
      (L.descends Z Z' W W hZW hZ'W (hSU Z hZ) (hSU Z' hZ') hSRC hSRC hbir))
  not_birational_affine := fun Z Z' _ _ hZ hZ' hP hP' hne n m hZn hZ'm hbir =>
    hne (B.isoOver_of_birational_of_nef (hnef Z hZ) (hnef Z' hZ') hP hP'
      (L.descends Z Z' (AffineN 𝕜 n) (AffineN 𝕜 m) hZn hZ'm (hSU Z hZ) (hSU Z' hZ')
        (isSeparablyRationallyConnected_affine 𝕜 n)
        (isSeparablyRationallyConnected_affine 𝕜 m) hbir))

/-! ## 3. Consequences of `CorCYnSB` -/

namespace CorCYnSB

/-- **`TotaroInput`'s field, from `cor-CYnSB`**: non-isomorphic `K`-trivial varieties of Picard
rank one are not stably birational. -/
theorem not_stablyBirat_of_not_iso (C : CorCYnSB 𝕜 Pic1)
    (X Y : Scheme.{0}) [Variety 𝕜 X] [Variety 𝕜 Y]
    (hX : IsKTrivial 𝕜 X) (hY : IsKTrivial 𝕜 Y) (pX : Pic1 X) (pY : Pic1 Y)
    (hne : ¬ IsoOver 𝕜 X Y) : ¬ StablyBirational 𝕜 X Y := by
  rintro ⟨n, m, vX, vY, hb⟩
  exact C.not_birational_affine X Y hX hY pX pY hne n m vX vY hb

/-- **The same-exponent affine case of the paper's corollary**: `Z × 𝔸ⁿ` is not birational to
`Z' × 𝔸ⁿ`.  This is the field `not_birational_src` at `W = 𝔸ⁿ`, and it is the form consumed by the
cylinder layer of the K3-INPUTS area (`Work.K3Inputs.StablyBirat` with exponents `(1,1)`). -/
theorem not_birational_affine_same (C : CorCYnSB 𝕜 Pic1)
    {Z Z' : Scheme.{0}} [Variety 𝕜 Z] [Variety 𝕜 Z']
    (hZ : IsKTrivial 𝕜 Z) (hZ' : IsKTrivial 𝕜 Z') (pZ : Pic1 Z) (pZ' : Pic1 Z')
    (hne : ¬ IsoOver 𝕜 Z Z') (n : ℕ)
    [hZn : Variety 𝕜 (prodOver 𝕜 Z (AffineN 𝕜 n))]
    [hZ'n : Variety 𝕜 (prodOver 𝕜 Z' (AffineN 𝕜 n))] :
    ¬ Nonempty ((prodOver 𝕜 Z (AffineN 𝕜 n)).BirationalMap (prodOver 𝕜 Z' (AffineN 𝕜 n))) :=
  C.not_birational_src Z Z' (AffineN 𝕜 n) hZ hZ' pZ pZ' hne
    (isSeparablyRationallyConnected_affine 𝕜 n) hZn hZ'n

/-- **The `W = ℙ¹` case of the paper's corollary**: the two centres are not birational after
multiplying by the affine line — the form of the `ℙ¹`-bundle bridge of the two links (their
exceptional divisors are `ℙ¹`-bundles over the centres, so `κ(Z)(t) ≅ κ(Z')(t)` would force
`Z × ℙ¹ ∼ Z' × ℙ¹`). -/
theorem not_birational_cylinder (C : CorCYnSB 𝕜 Pic1)
    {Z Z' : Scheme.{0}} [Variety 𝕜 Z] [Variety 𝕜 Z']
    (hZ : IsKTrivial 𝕜 Z) (hZ' : IsKTrivial 𝕜 Z') (pZ : Pic1 Z) (pZ' : Pic1 Z')
    (hne : ¬ IsoOver 𝕜 Z Z')
    [hZ1 : Variety 𝕜 (prodOver 𝕜 Z (AffineN 𝕜 1))]
    [hZ'1 : Variety 𝕜 (prodOver 𝕜 Z' (AffineN 𝕜 1))] :
    ¬ Nonempty ((prodOver 𝕜 Z (AffineN 𝕜 1)).BirationalMap
      (prodOver 𝕜 Z' (AffineN 𝕜 1))) :=
  C.not_birational_affine_same hZ hZ' pZ pZ' hne 1

/-- The distinguishing at the level of the two chapters' `TotaroInput` field, for an arbitrary
Picard-rank-one predicate family: the shape packaged into `Work.CY3.TotaroInput` and
`Work.K3.TotaroInput` in `Submission/Work/Totaro/Interface.lean`. -/
theorem not_stablyBirational_of_not_iso (C : CorCYnSB 𝕜 Pic1) :
    ∀ (X Y : Scheme.{0}) [Variety 𝕜 X] [Variety 𝕜 Y],
      IsKTrivial 𝕜 X → IsKTrivial 𝕜 Y → Pic1 X → Pic1 Y → ¬ IsoOver 𝕜 X Y →
      ¬ StablyBirational 𝕜 X Y :=
  fun X Y _ _ hX hY pX pY hne => C.not_stablyBirat_of_not_iso X Y hX hY pX pY hne

end CorCYnSB

end

end Work.Totaro
