import Mathlib
import Submission.NK.NUV2.LC.RouteB.hasseSurjTopDefs
import Submission.NK.NUV2.LC.h2ProfiniteAddGroup
import Submission.NK.NUV2.LC.RouteB.card_open_local
import Submission.NK.UchidaKummer.Embedding.isKummerEmbeddingProblem
import Submission.NK.BrauerHasse.local_ofLevel_zero
import Submission.NK.NUV2.LC.RouteB.survivalSetup

/-!
# `onePlaceClasses`: the one-place classes of NSW (9.2.1)

**The statement.**  `NK.NUV2.LC.RouteB.onePlaceClasses` (`Submission/Work/NUV2/LC/RouteB/onePlaceClasses.lean`)
says: for `p` an odd prime, a number field `F` containing a primitive `p`-th root of unity `ζ`, a
separable closure `F'`, and a finite family `A i` of pairwise non-conjugate places of `F'` over
finite primes of `F`, there are global classes `a i ∈ H²(G_F, Z/p)` with

`loc (a i) (A i) ≠ 0`   and   `loc (a i) (A j) = 0` for `j ≠ i`.

It is *equivalent* to the classical Hasse surjectivity `Br(F)[p] ↠ ∏_v Br(F_v)[p]` (`HasseSurjTop p`,
see `Submission/Work/NUV2/LC/RouteB/hasseSurjTop.lean`, which derives `HasseSurjTop p` from this
lemma by `ZMod p`-linear algebra together with `Nat.card (LocalH2 …) = p`).

## The route (Kummer data + one level), and the one missing step

The *vanishing* half and the *non-vanishing* half of the construction come from different
mechanisms, and only the second is expensive:

1. **Kummer data in the number-field picture** (`exists_localPowClass_family`,
   `NK.UchidaKummer.Embedding`, proved): for the set `T = {𝔭 i}` of primes of `F` below the places
   `A i` there are units `c i ∈ Fˣ` with `localPowClass p (𝔭 i) (c i) ≠ 1` and
   `localPowClass p (𝔭 j) (c i) = 1` for `j ≠ i`.
2. **The Kummer level** `K = kummerSup p T c` (`NK.UchidaKummer.Embedding.KummerSup`), of degree
   `p ^ |T|` over `F` (`finrank_kummerSup`, proved), so that `Gal(K/F) ≅ (Z/p)^|T|` and the
   coordinate characters `π i : Gal(K/F) → Gal(F(c i^{1/p})/F) ≅ Z/p` exist.  At the prime `𝔭 i` the
   decomposition group `E i(K) ≤ Gal(K/F)` maps *isomorphically* onto `Gal(F(c i^{1/p})/F)`, while
   for `j ≠ i` the map `π i` kills `E j(K)` (`localDeg_eq_one_of_kummerSup`, proved).
3. **The level classes** `x i := H2.map (π i) (gen i) ∈ H²(Gal(K/F), Z/p) = LevelH2 p ⊤ K`, with
   `gen i ≠ 0` in `H²(Gal(F(c i^{1/p})/F), Z/p) ≅ Z/p`.  Then, at the level `K`,
   * `locLevel p ⊤ (A i).1 K (x i) = H2.map (π i)|_{E i(K)} (gen i) ≠ 0` (the restriction is an
     isomorphism), and
   * `locLevel p ⊤ (A j).1 K (x i) = 0` for `j ≠ i` (the restriction factors through the trivial
     group).
   These two statements together are the *level* form of the construction, isolated as
   `NK.NUV2.LC.RouteB.onePlaceLevelClassesNaive` (`Submission/Work/NUV2/LC/RouteB/onePlaceLevelClassesNaive.lean`,
   delegated).
4. **Vanishing in the colimit is then free** (`loc_ofLevel_eq_zero` below): the localisation of
   `ofLevel K (x i)` at `A j` is `LocalH2.ofLevel K (locLevel …)`, so any level class with vanishing
   level localisation has vanishing colimit localisation.  Hence `loc (a i) (A j) = 0` for `j ≠ i`
   costs nothing.
5. **The one genuinely arithmetic step is the survival at the own place**: the level localisation
   `locLevel p ⊤ (A i).1 K (x i) ≠ 0` does *not* imply
   `LocalH2.ofLevel K (locLevel p ⊤ (A i).1 K (x i)) ≠ 0`: `H2Profinite`/`LocalH2` are colimits along
   inflation maps, and a non-zero level class can die under inflation (`NOTES_open_two_place.md`,
   `NOTES_hasseSurjTop_route.md`).  Concretely, for the pair `Λ_K = Z/p ≤ Λ_L = Z/p²` the inflation
   `H²(Λ_K, Z/p) → H²(Λ_L, Z/p)` is **zero** (the pullback of the non-split extension
   `0 → Z/p → Z/p² → Z/p → 0` along `Z/p² ↠ Z/p` splits, as a two-line computation shows), so the
   survival is a real condition on the level `K` and on the Kummer data.

   The correct criterion (Hilbert 90 + the Kummer square) is: if `res_{Λ_K}(x)` is *not* killed by the
   Kummer map `H²(Λ_K, μ_p) → H²(Λ_K, K_wˣ)` of the local field `K_w`, then no level `L ≥ K` can kill
   `x`.  Indeed, killing at `L` gives `kummer_L(inf x) = 0 = infl^*(kummer_K (res x))`, and the
   inflation `infl^*` with units coefficients is injective (its kernel is the image of the
   transgression `H¹(Gal(L_w/K_w), L_wˣ) → H²(Λ_K, K_wˣ)`, and `H¹` of the units of a local field
   extension vanishes by Hilbert 90).  So survival follows from
   `kummer_K(res_{Λ_K}(x)) ≠ 0`, i.e. from the non-vanishing of the *local* Kummer image.

   This last condition is equivalent to `ζ_p ∉ N(K_wˣ)` (the norm criterion for cyclic algebras: the
   Kummer image of a level class is the cyclic algebra whose parameter is `ζ_p`), and it is
   *arrangeable*: the Kummer data can be strengthened so that the local `p`-th power class of `c i`
   at `𝔭 i` is not orthogonal to `ζ_p` (the norm group `N(K_wˣ)` has index `p` and contains
   `F_{𝔭 i}^{*p}`, so it is a proper subgroup of `F_{𝔭 i}^*`; weak approximation /
   `isKummerSurjective_of_weakApproximation` then produces a global element whose local class avoids
   it).  Equivalently, the local extension must be chosen so that the local character of the Kummer
   extension does not lift to a character into `Z/p²` — this is exactly the Bockstein/`Ext` picture:
   `H²(Λ_K, Z/p) ≅ Ext(Λ_K, Z/p)` and the inflation along `Λ_L ↠ Λ_K` is the pullback of extensions.

## Status

The two halves of the construction are separated: the *level* half is
`onePlaceLevelClassesNaive` (delegated, `Submission/Work/NUV2/LC/RouteB/onePlaceLevelClassesNaive.lean`)
and the *survival* half is step 5 above.  `loc_ofLevel_eq_zero` (proved below) is the bookkeeping
that turns the level vanishing into the colimit vanishing.

## Main results

* `loc_ofLevel_eq_zero` — the level localisation vanishing gives the colimit localisation vanishing.

## Status and the two remaining inputs (see `NOTES_onePlace_survival.md`)

The *vanishing* half of the construction is `loc_ofLevel_eq_zero` below (a level class with
vanishing level localisation has vanishing colimit localisation).  The *survival* half is

* `NK.NUV2.LC.RouteB.localH2_ofLevel_ne_zero_of_locL_kummerLevel_ne_zero` (**proved**, with the
  supporting modules `Submission/Work/NUV2/LC/RouteB/Survival/…`) — a level class with
  non-vanishing **local Kummer image** survives in the local colimit,

whose bookkeeping is in `Submission/Work/NUV2/LC/RouteB/survivalSetup.lean`, in particular the
fundamental **level independence of the vanishing of the localisation**

* `NK.NUV2.LC.RouteB.locUnits_eq_zero_iff_unitsLevelMapTower`.

The arithmetic input — a degree-`p` cyclic local extension `λ/κ` with `ζ_p ∉ N(λˣ)` — is
**proved** as `NK.NUV2.LC.RouteB.exists_cyclic_local_notMem_norm` (from the on-disk local
*existence theorem* `NK.LocalReciprocityLubinTate.existenceTheorem_adicCompletion`; it needs the
hypothesis `ζ_p ∉ κ^{p}`, which fails exactly when `μ_{p²} ⊆ κ`, and in that case the Kummer-image
criterion above is vacuous — there the units-coefficient cyclic-algebra dictionary

* `NK.NUV2.LC.RouteB.locUnitsZ_cyclicClass_eq_zero_iff` (delegated, in flight; the `ℤ`-world
  localisation `NK.NUV2.LC.RouteB.locUnitsZ` is in `Submission/Work/NUV2/LC/RouteB/localUnitsZ.lean`)

is the route.  See `NOTES_onePlace_survival.md` §5–§6 for the complete status and for what the
assembly still owes.
-/

namespace NK.NUV2.LC.RouteB

open NK.BrauerHasse

set_option autoImplicit false

variable {F F' : Type} [Field F] [NumberField F] [Field F'] [Algebra F F'] [IsSepClosure F F']

/-- **Vanishing of the level localisation gives vanishing of the colimit localisation.**

The localisation of the class of a finite level is computed at that level
(`NK.BrauerHasse.H2Profinite.loc_ofLevel_apply`), so if the level-localisation of `x` at the place
`A` is zero then the whole colimit localisation is zero.  This is the cheap half of the
one-place-classes construction: the classes produced by the Kummer embedding problem vanish at the
other places *at their own level*. -/
theorem loc_ofLevel_eq_zero (p : ℕ) (A : NK.BrauerHasse.OverFinitePrime F F')
    (K : FiniteGaloisIntermediateField F F')
    (x : NK.BrauerHasse.LevelH2 (K := F) (K' := F') p ⊤ K)
    (h : NK.BrauerHasse.locLevel p ⊤ A.1 K x = 0) :
    NK.BrauerHasse.H2Profinite.loc p ⊤
      (NK.BrauerHasse.H2Profinite.ofLevel K x) A = 0 := by
  rw [NK.BrauerHasse.H2Profinite.loc_ofLevel_apply, h,
    NK.BrauerHasse.local_ofLevel_zero]


end NK.NUV2.LC.RouteB
