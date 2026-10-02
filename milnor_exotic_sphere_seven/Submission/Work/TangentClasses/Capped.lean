import Mathlib
import Submission.Work.TangentClasses.Pontryagin
import Submission.Work.CharacteristicClasses.Capped

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-!
# `p₁(TX)` for the closed 8-manifold `X = D(ξ) ∪_F D⁸`, and its agreement with the existing class

`Submission/Work/CharacteristicClasses/Capped.lean` constructs a class
`Work.Milnor.cappedPontryaginClass F hF ∈ H⁴(X;ℤ)` for the closed `8`-manifold
`X = cappedSpace (cappedDatum F hF)`, *defined* as the unique class whose restriction to the disc
bundle `D(ξ) = Vk (-2)` is `p₁(ξ) · τ = 6 · τ`, where `τ` is the chosen generator of
`H⁴(D(ξ);ℤ) ≅ ℤ` and the restriction `cappedRestriction : H⁴(X;ℤ) → H⁴(D(ξ);ℤ)` is an
isomorphism (`Work.Milnor.cappedRestriction_isIso`) — so that class *is* determined by the disc
bundle.  The number `6 = p₁(ξ)` is computed in the characteristic-classes chapter.

This module gives the *tangent-bundle* meaning of that class, in the only shape available in this
workspace (which has no general Pontryagin classes of an arbitrary `TX`):

* `DiscTangentSplitting` is **the geometric input**, named: the restriction of the tangent bundle of
  `X` to the disc bundle is `π^*(TS⁴ ⊕ ξ)`.  It is encoded as
  * a bundle projection `proj : C(D(ξ), S⁴)` (the projection of the disc bundle), and
  * a class `G ∈ H⁴(S⁴;ℤ)` whose pullback along `proj` is the chapter's generator `τ` of
    `H⁴(D(ξ);ℤ)` up to sign.  This is the *normalisation of the chosen generators* (and the sign is
    the orientation of `τ`): since `proj^*` is an isomorphism (mathematically — the disc bundle
    deformation retracts onto the zero section, see `Submission/Work/TangentClasses/DiscProj.lean`
    for the injectivity and the conditional existence), there is a unique such `G` for each choice
    of sign;
* `p1Disc` is the class of `TX|_{D(ξ)}` computed from the clutching presentation `TS⁴ ⊕ ξ`, and
  `p1Disc_eq_pm_six_tau` evaluates it: **`p₁(TX)|_{D(ξ)} = ± 6 · τ`** — the chapter's
  `p₁(ξ) = 6`, Whitney additivity and `p₁(TS⁴) = 0` (`p1Pulled_tangent_sum_xi`), with the sign
  coming from the normalisation of the generator;
* `p1Tangent` is **`p₁(TX)`**: the unique class in `H⁴(X;ℤ)` restricting to `p1Disc` (uniqueness is
  `cappedRestriction_injective`; existence is `cappedRestriction_surjective`);
* **the main theorems of the module**:
  * `p1Tangent_eq_pm_cappedPontryaginClass` (**unconditional**): `p₁(TX)` agrees with the existing
    `Work.Milnor.cappedPontryaginClass F hF` up to sign — the sign being exactly the normalisation
    of the generator of `H⁴(S⁴;ℤ)`;
  * `p1Tangent_eq_cappedPontryaginClass` (**the consistency theorem**, for the natural normalisation
    `π^*G = τ`): the class the characteristic-classes chapter constructs *is* the first Pontryagin
    class of the tangent bundle;
  * `p1Tangent_six` (**unconditional**): `p₁(TX) = q · x` with `q ∈ {6, -6}` for every generator `x`
    of `H⁴(X;ℤ) ≅ ℤ` — the form consumed by the endgame
    (`Submission/Work/SignatureBordism/Obstruction.lean`).

**What is not determined.**  The second Pontryagin class `p₂(TX) ∈ H⁸(X;ℤ)` is *not* determined by
the restriction to the disc bundle: both `H⁸(D(ξ))` and `H⁸(D⁸)` vanish, so the Mayer–Vietoris
transgression kills the information (`Submission/NOTES.md` §14.7: for `ξ = L` the same data gives
`X = ℍP²` with `p₂ = 7 ≠ 0`).  Accordingly `p₂(TX)` is an *input* of the endgame, exactly as in
`Submission/Work/SignatureBordism/Obstruction.lean`; the `ClosedOriented8Manifold` structure of
`Submission/Work/TangentClasses/Bordism.lean` carries it as data.
-/

namespace Work.TangentClasses

open CategoryTheory
open Work.CharacteristicClasses

noncomputable section

variable (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8)
variable (hF : Work.Milnor.IsCappingDiffeo F)

/-- The disc bundle `D(ξ) = Vk (-2)` of Milnor's bundle. -/
abbrev DiscSpace : Type := Submission.Milnor.Vk (-2)

/-- **The geometric input for `p₁(TX)`.**  On the disc bundle `D(ξ) = Vk (-2)` of
`X = D(ξ) ∪_F D⁸` the tangent bundle restricts to `π^*(TS⁴ ⊕ ξ)`; we record this as

* a bundle projection `proj : C(D(ξ), S⁴)` (the projection of the disc bundle),
* a chosen generator `G` of `H⁴(S⁴;ℤ) ≅ ℤ`, normalised so that its pullback along `proj` is the
  chapter's generator `τ` of `H⁴(D(ξ);ℤ) ≅ ℤ`, up to sign (the sign is the orientation of `τ`; the
  positive normalisation `proj^*G = τ` is the one for which the identification of
  `p₁(TX)` with `Work.Milnor.cappedPontryaginClass` is exact, see
  `p1Tangent_eq_cappedPontryaginClass`),
* the clutching presentation `TS⁴ ⊕ ξ` of the rank-`8` bundle `π^*(TS⁴ ⊕ ξ)`.

Nothing else is assumed: the class `p1Disc` below is computed from this data alone, by the
characteristic-classes chapter's `p₁(ξ) = 6` together with Whitney additivity and the stable
triviality of `TS⁴`. -/
structure DiscTangentSplitting where
  /-- the projection of the disc bundle to `S⁴` -/
  proj : C(DiscSpace, S4)
  /-- the chosen generator of `H⁴(S⁴;ℤ)` -/
  G : H 4 S4
  /-- the normalisation of the generator: its pullback is the chapter's generator `τ`, up to sign -/
  G_pullback : (HMap proj 4).hom G = Work.Milnor.tauD ∨
    (HMap proj 4).hom G = -Work.Milnor.tauD

/-- **The first Pontryagin class of `TX` restricted to the disc bundle**: the class of
`π^*(TS⁴ ⊕ ξ)` computed from the clutching presentation. -/
def p1Disc (S : DiscTangentSplitting) : H 4 DiscSpace :=
  p1Pulled S.G S.proj (SpinBundle.tangentSphere.sum SpinBundle.xi)

/-- **The value of `p₁(TX)` on the disc bundle is `± 6 · τ`**: the bundle is `π^*(TS⁴ ⊕ ξ)`, whose
first Pontryagin class is `p₁(ξ) = 6` times the pullback of the generator (the tangent bundle of
`S⁴` being stably trivial); the sign is the normalisation of the generator. -/
theorem p1Disc_eq_pm_six_tau (S : DiscTangentSplitting) :
    p1Disc S = (6 : ℤ) • Work.Milnor.tauD ∨
      p1Disc S = -((6 : ℤ) • Work.Milnor.tauD) := by
  have h := p1Pulled_tangent_sum_xi S.G S.proj
  rw [p1Disc]
  rcases S.G_pullback with hG | hG
  · left
    rw [h, hG]
  · right
    rw [h, hG, zsmul_neg]

/-- **The first Pontryagin class `p₁(TX)` of the closed 8-manifold `X = D(ξ) ∪_F D⁸`**: the class in
`H⁴(X;ℤ)` whose restriction to the disc bundle is the class of `TX|_{D(ξ)}`.  The restriction is
injective (`Work.Milnor.cappedRestriction_injective`) so this class is *unique*; the definition
picks the class supplied by surjectivity (`Work.Milnor.cappedRestriction_surjective`). -/
def p1Tangent (S : DiscTangentSplitting) :
    H 4 (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)) :=
  Classical.choose (Work.Milnor.cappedRestriction_surjective F hF (p1Disc S))

/-- The defining property of `p1Tangent`: its restriction to the disc bundle is `p1Disc`. -/
theorem p1Tangent_restriction (S : DiscTangentSplitting) :
    (Work.Milnor.cappedRestriction F hF).hom (p1Tangent F hF S) = p1Disc S :=
  Classical.choose_spec (Work.Milnor.cappedRestriction_surjective F hF (p1Disc S))

/-- `p₁(TX)` is *determined* by its restriction to the disc bundle. -/
theorem p1Tangent_unique (P : H 4 (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))
    (S : DiscTangentSplitting)
    (hP : (Work.Milnor.cappedRestriction F hF).hom P = p1Disc S) :
    P = p1Tangent F hF S :=
  Work.Milnor.cappedRestriction_injective F hF (by rw [hP, p1Tangent_restriction])

/-- **`p₁(TX)` agrees with the existing class up to sign** — the sign being the normalisation of
the generator of `H⁴(S⁴;ℤ)` in the geometric input.  This statement needs no hypothesis. -/
theorem p1Tangent_eq_pm_cappedPontryaginClass (S : DiscTangentSplitting) :
    p1Tangent F hF S = Work.Milnor.cappedPontryaginClass F hF ∨
      p1Tangent F hF S = -Work.Milnor.cappedPontryaginClass F hF := by
  rcases p1Disc_eq_pm_six_tau S with h | h
  · left
    apply Work.Milnor.cappedRestriction_injective F hF
    rw [p1Tangent_restriction, h, Work.Milnor.cappedPontryaginClass_restriction]
  · right
    apply Work.Milnor.cappedRestriction_injective F hF
    rw [map_neg, Work.Milnor.cappedPontryaginClass_restriction, p1Tangent_restriction]
    exact h

/-- **THE CONSISTENCY THEOREM.**  For the natural normalisation of the chosen generator
(`proj^* G = τ`), the class constructed in the characteristic-classes chapter,
`Work.Milnor.cappedPontryaginClass F hF` — defined as *the* class restricting to `6 · τ` — is
exactly `p₁(TX)` as constructed here from the tangent bundle's clutching presentation on the disc
bundle.

The proof is the definition of `p1Tangent` (restrict to the disc bundle, where the two classes
agree) together with injectivity of that restriction. -/
theorem p1Tangent_eq_cappedPontryaginClass (S : DiscTangentSplitting)
    (hS : (HMap S.proj 4).hom S.G = Work.Milnor.tauD) :
    p1Tangent F hF S = Work.Milnor.cappedPontryaginClass F hF := by
  apply Work.Milnor.cappedRestriction_injective F hF
  rw [p1Tangent_restriction, Work.Milnor.cappedPontryaginClass_restriction]
  rw [p1Disc, p1Pulled_tangent_sum_xi, hS]

/-- **`p₁(TX)` is `±6` times every generator of `H⁴(X;ℤ) ≅ ℤ`** — the form in which the endgame
consumes the characteristic-class input.  This statement needs no hypothesis. -/
theorem p1Tangent_six (S : DiscTangentSplitting)
    (x : H 4 (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))
    (hx : ∀ z : H 4 (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)), ∃ a : ℤ, z = a • x) :
    ∃ q : ℤ, (q = 6 ∨ q = -6) ∧ p1Tangent F hF S = q • x := by
  rcases p1Tangent_eq_pm_cappedPontryaginClass F hF S with h | h
  · obtain ⟨q, hq, hq'⟩ := Work.Milnor.cappedPontryaginClass_six F hF x hx
    exact ⟨q, hq, by rw [h, hq']⟩
  · obtain ⟨q, hq, hq'⟩ := Work.Milnor.cappedPontryaginClass_six F hF x hx
    refine ⟨-q, ?_, by rw [h, hq', neg_zsmul]⟩
    rcases hq with h1 | h1 <;> rw [h1] <;> norm_num

/-! ## The vanishing of `H⁸` of the disc bundle, and the second Pontryagin class -/

/-- `e.inv (e.hom x) = x` for an isomorphism of `ℤ`-modules (the general form of the auxiliary
lemma of the characteristic-classes chapter). -/
lemma iso_inv_hom_apply {M N : ModuleCat ℤ} (e : M ≅ N) (x : M) :
    ModuleCat.Hom.hom e.inv (ModuleCat.Hom.hom e.hom x) = x := by
  have h := congrArg ModuleCat.Hom.hom e.hom_inv_id
  rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
  exact LinearMap.congr_fun h x

/-- **`H⁸(D(ξ);ℤ) = 0`**: the disc bundle is homotopy equivalent to `S⁴`, which has no cohomology
in degree `8` (`Work.Milnor.cohomology_Vk`).  Consequently *every* class of degree `8` on the disc
bundle — in particular the restriction of any second Pontryagin class — vanishes. -/
theorem eq_zero_of_H8_disc (z : H 8 DiscSpace) : z = 0 := by
  obtain ⟨e⟩ := Work.Milnor.cohomology_Vk (-2) 8
  have hk : (if (8 : ℕ) = 0 then 1 else 0) + (if (8 : ℕ) = 4 then 1 else 0) = 0 := by norm_num
  rw [hk] at e
  have h1 : ModuleCat.Hom.hom e.hom z = 0 := Subsingleton.elim _ _
  rw [← iso_inv_hom_apply e z, h1, map_zero]

/-- `H⁸(D(ξ);ℤ)` is a subsingleton. -/
theorem subsingleton_H8_disc : Subsingleton (H 8 DiscSpace) :=
  ⟨fun a b => by rw [eq_zero_of_H8_disc a, eq_zero_of_H8_disc b]⟩

/-- **The restriction `H⁸(X;ℤ) → H⁸(D(ξ);ℤ)` is the zero map** (`H⁸(D(ξ);ℤ) = 0`): the disc
bundle carries no information about the degree-`8` classes of `X`.  In particular the second
Pontryagin class `p₂(TX) ∈ H⁸(X;ℤ)` is *not* determined by the tangent-bundle identification on the
disc bundle (`Submission/NOTES.md` §14.7), unlike `p₁(TX)`, which the injectivity of the degree-`4`
restriction does determine. -/
theorem cappedRestriction_eight_eq_zero
    (z : H 8 (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF))) :
    (Work.Cohomology.singularCohomologyMap ℤ (TopCat.of DiscSpace)
      (TopCat.of (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))
      (Work.Milnor.cappedIncl F hF) 8).hom z = 0 :=
  eq_zero_of_H8_disc _

/-! ## The second Pontryagin class

`p₂(TX) ∈ H⁸(X;ℤ)` is *not* accessible by the method of this module.  The restriction of `TX` to
the disc bundle is `π^*(TS⁴ ⊕ ξ)`, whose second Pontryagin class vanishes for degree reasons — this
is a theorem, `eq_zero_of_H8_disc`: `H⁸(D(ξ);ℤ) = 0` — but it gives no information in `H⁸(X;ℤ)`: the disc bundle `D(ξ)` is homotopy equivalent to
`S⁴`, so `H⁸(D(ξ);ℤ) = 0` and the restriction map `H⁸(X;ℤ) → H⁸(D(ξ);ℤ)` is *zero* — not
injective.  `Submission/NOTES.md` §14.7 records the counterexample: for `ξ = L` (the tautological
quaternionic line bundle) the same gluing gives `X = ℍP²`, whose `p₂` is `7 ≠ 0` although both
pieces have vanishing `H⁸`.

Formally: the degree-`8` restriction is the zero map.

So `p₂(TX)` is data of the general theory of Pontryagin classes of a smooth 8-manifold
(`Submission/Work/TangentClasses/Bordism.lean` carries it as a field; the endgame
`Submission/Work/SignatureBordism/*` takes it as a parameter).  What this chapter *does* determine
is the **pairing** of `p₁(TX)` with the fundamental class, `⟨p₁(TX) ⌣ p₁(TX), [X]⟩ = 36 σ(X)`
(`Submission/Work/TangentClasses/Bordism.lean`), which is the other numerical input of the
Hirzebruch identity. -/

end

end Work.TangentClasses
