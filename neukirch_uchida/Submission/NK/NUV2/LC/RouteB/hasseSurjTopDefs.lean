import Mathlib
import Submission.NK.NUV2.LC.RouteB.hasseSurjDefs

/-!
# `HasseSurjTop`: the classical Hasse surjectivity isolated from the level bookkeeping

`NK.NUV2.LC.RouteB.hasseSurj` asks for the classical Hasse/NSW (9.2.1) surjectivity in the
`H2Profinite`-colimit picture, for an **arbitrary open** subgroup `U ≤ Gal(K'/K)` with
`U ≤ rootFix ζ` (`ζ` a primitive `p`-th root, `p` odd).  This module isolates the *arithmetic*
content of that statement as a single `Prop`, `HasseSurjTop p`, in which the subgroup is `⊤`:

> for every number field `F`, every separable closure `F'` of `F`, every primitive `p`-th root of
> unity `ζ ∈ F` (so `μ_p ⊂ F` and the trivial coefficients `Z/p` are `μ_p`), and every finite
> family `A i` of pairwise distinct places of `F'` over finite primes of `F`, the localisation
> ```
> H²(Gal(F'/F), Z/p) → ∏_i H²(D_{A i}, Z/p)
> ```
> is surjective,

i.e., with `F` a number field containing `ζ_p` and `S` a finite set of non-archimedean places,
every family of local Brauer classes of order dividing `p` over `S` is realised by a global class:
`Br(F)[p] → ∏_{v ∈ S} Br(F_v)[p]` is onto.

## Why this is the right isolation

* The statement `HasseSurjTop p` is *exactly* the `U = ⊤` instance of the target, so it is **not
  circular** and it is a genuine theorem of global class field theory (classical Hasse; `p` odd so
  that the archimedean places, which are not among the `OverFinitePrime` places, contribute
  nothing).
* The passage from `HasseSurjTop p` to the general `HasseSurj p K K' ζ` is **pure level
  bookkeeping**: for `U` open with fixed field `F = K'^U` the level systems of `U` (levels
  `L : FiniteGaloisIntermediateField K K'` with the level group `U ⧸ (U ⊓ Gal(K'/L))`, whose
  arithmetic is `Z/p`) and of `⊤` over the base field `F` (levels `L : FiniteGaloisIntermediateField
  F K'` with group `Gal(L/F)`) have a *cofinal* common subsystem (the levels `L ⊇ F`, where
  `U ⧸ (U ⊓ Gal(K'/L)) ≅ Gal(L/F)`, cf. `NK.HassePrinciple.levelGroupMulEquivLevelGalois`), and
  the places of `K'` over finite primes of `K` that matter are exactly the places over the
  corresponding primes of `F` (`InOrbit` with respect to `U = Gal(K'/F)`), so that the two
  localisations agree.  This is the statement delegated as
  `NK.NUV2.LC.RouteB.hasseSurj_of_top`.
* The statement `HasseSurjTop p` itself is the workspace's crux in its leanest form; the routes to
  it are recorded in `Submission/Work/NUV2/LC/RouteB/NOTES_hasseSurj_route.md` (§2: cyclic classes
  + weak approximation, which needs no Hilbert reciprocity and no Hasse exact sequence).

## On-disk assets for a proof of `HasseSurjTop p` (read before starting)

* **The global Artin reciprocity law, PROVED**: `NK.CFTLib.artinReciprocityIdeal_proved`
  (`Submission/Work/CFTLib/ArtinReciprocityIdealProved.lean`), hence the global fundamental class
  (`NK.CFTLib.fundamentalClassElement`, `NK.GlobalCFTdeep.FundamentalClassElement`,
  `NK.GFC.fundamentalClassElement_unconditional`) and the class-formation axioms
  (`NK.GlobalCFTdeep.cohomologicalFieldAxiom_of_fundamentalClassElement`), the reciprocity
  isomorphisms, `H¹(Γ,C_L) = 0` (`NK.GlobalCFTdeep.H1All`).
* **Local Artin maps at the completions of cyclic global abelian levels, with the correct
  kernels**: `NK.CFTLib.IdeleHasse.localGlobalArtinMap_exists` (sorry-free) — for a cyclic global
  abelian `L/K` it produces `Φ = ∏_v λ_v : 𝕀_K →* Gal(L/K)`, surjective, killing `N_{L/K}𝕀_L`,
  with `Φ(onePlace v a) = 1 ↔ onePlace v a ∈ N_{L/K}𝕀_L`, i.e. the local factor `λ_v` has kernel
  exactly the local norm group; see `Submission/Work/NUV2/RouteC/NOTES_session_G_global_route.md`.
* **Hasse–Brauer–Noether injectivity** (the *kernel* half, proved): `NK.GlobalCFTdeep.hbnUnits`,
  and Shapiro for the idèles `NK.HassePrinciple.hbnIdele`.
* **Local Brauer/periodicity**: `NK.NUV2.LocalInvariant` (`Br(M/κ) ≃+ ZMod [M:κ]`),
  `NK.NUV2.LC.card_h2P_adicCompletion` (`|H²(G_κ, Z/p)| = p`), `NK.NUV2.ABHN.unitsLevelH2_card`,
  and the explicit cyclic cocycle/periodicity `NK.NUV2.RouteC.cyclic_cocycle`.
* **Weak approximation**: `NK.UchidaKummer.Approximation.isWeakApproximation`,
  `isKummerSurjective_of_weakApproximation` (`Kˣ/(Kˣ)^ℓ ↠ ∏_{𝔮∈S} K_𝔮ˣ/(K_𝔮ˣ)^ℓ`),
  `isOpenEllPowSubgroup`; the auxiliary Kummer fact
  `NK.NUV2.LC.RouteB.exists_notMem_pow_adicCompletion`.
* **Cup products, local symbols, and the local reciprocity law (Route E — sorry-free)**:
  `Submission/Work/NUV2/RouteE/` contains `deltaHomChar_naturality`, `mapCocycles₂_cup_eval`
  (`cupNaturality.lean`: the level inflation commutes with the `H⁰ × H²` cup product),
  `charValue`/`charValue_mul` (`levelSymbol.lean`: the character pairing of a level `H²` class),
  `exists_levelArtinMap` (`levelArtinMap.lean`), `levelInfHom`/`levelInfHom_comp`
  (`levelCoherent.lean`), `nonempty_reciprocityLaw_of_levelMaps` (`assembly.lean`), and
  `Submission/Work/NUV2/RouteC/` contains the explicit cyclic cocycle (`cyclic_cocycle.lean`) and
  `cup_pow.lean`; the cochain model is `NK.NUV2.LC.CupAux`, `NK.NUV2.LC.d_cup_trivial`,
  `NK.NUV2.LC.cupTrivial_descent`, `NK.HassePrinciple.CupAux`.  This is the machinery for the
  **cup-product / Kummer construction** of the one-place classes: at a level
  `L = F(a^{1/p}, b^{1/p})` the class `χ_a ∪ χ_b ∈ H²(Gal(L/F), μ_p)` has localisation the local
  Hilbert symbol `(a,b)_v`, which is non-zero precisely when the local extension is non-trivial and
  `b` is not a local norm — both arrangeable by weak approximation
  (`NK.NUV2.LC.RouteB/NOTES_hasseSurjTop_route.md` records this route and the precise gap).
* **The routes**: `Submission/Work/NUV2/LC/RouteB/NOTES_hasseSurj_route.md` — §1 the Hasse exact
  sequence (`Σ_v inv_v = 0`, needs Shapiro for the idèles in the restricted-product form, the unit
  `H³(Γ,Lˣ) = 0`, and the local–global compatibility of fundamental classes), and §2 the strictly
  cheaper **cyclic classes + weak approximation** route (no Hilbert reciprocity, no Hasse
  sequence): take a cyclic level `E/F` of degree `p` with every `v ∈ S` non-split, realise each
  local class `α_v ∈ Br(F_v)[p] = Br(E_w/F_v)` by an element `b_v ∈ F_v^*/N(E_w^*)`, lift the
  `b_v` to a single `b ∈ F^*` by weak approximation (the norm groups are open, they contain the
  `p`-th powers), and let `x` be the class of `b` under `F^*/N(E^*) ≅ H²(Γ,Eˣ) → Br(F)`
  (cyclic periodicity); then `loc_v(x) = α_v` for all `v ∈ S`.

## Main definition

* `NK.NUV2.LC.RouteB.HasseSurjTop` — the `⊤`-case, as a `Prop`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Pointwise

namespace NK.NUV2.LC.RouteB

/-- **The classical Hasse surjectivity at a number field (`⊤`-case of `HasseSurj`).**

For every number field `F` with separable closure `F'`, every primitive `p`-th root of unity
`ζ ∈ F` and every finite family of pairwise distinct places `A i` of `F'` over finite primes of
`F`, the localisation

  `H²(Gal(F'/F), Z/p) → ∏_i H²(D_{A i}, Z/p)`

is surjective.  Equivalently: `Br(F)[p] → ∏_{v ∈ S} Br(F_v)[p]` is onto for every finite set `S` of
non-archimedean places of `F` (for `p` odd, so that the archimedean places contribute nothing and
the trivial coefficients `Z/p` agree with `μ_p`).

This is the *arithmetic* content of `NK.NUV2.LC.RouteB.HasseSurj`; the passage from this
statement to the general open-`U` statement is the bookkeeping lemma
`NK.NUV2.LC.RouteB.hasseSurj_of_top`.

The hypotheses `hp : p.Prime` and `hodd : p ≠ 2` are carried *inside* the `Prop` (exactly as in
`HasseSurj`), so that `HasseSurjTop p` is the literal `U = ⊤` instance: for `p = 0` the
coefficients `ZMod 0 = ℤ` are *not* `μ_p` and `IsPrimitiveRoot ζ 0` holds for every `ζ` (so the
`p = 0` instance of the unguarded statement would be a different, `ℤ`-coefficient claim, not the
Brauer-theoretic one). -/
def HasseSurjTop (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 →
  ∀ {F F' : Type} [Field F] [NumberField F] [Field F'] [Algebra F F'] [IsSepClosure F F']
    (ζ : F') (hζ : IsPrimitiveRoot ζ p) (hζF : ∃ f : F, algebraMap F F' f = ζ)
    (ι : Type) [Fintype ι] (A : ι → NK.BrauerHasse.OverFinitePrime F F'),
    (∀ i j : ι, i ≠ j → ¬ InOrbit (K := F) (K' := F') ⊤ (A i).1 (A j).1) →
    Function.Surjective (fun x : NK.BrauerHasse.H2Profinite (K := F) (K' := F') p ⊤ =>
      fun i : ι => NK.BrauerHasse.H2Profinite.loc p ⊤ x (A i))

/-- The same statement in the *hypothesis shape* in which `HasseSurj` produces it: the `⊤`-case
of `HasseSurj` for a fixed pair `(K, K')` and a primitive root `ζ` that lies in the image of `K`. -/
theorem hasseSurj_of_top_top (p : ℕ) (h : HasseSurjTop p) (hp : p.Prime) (hodd : p ≠ 2)
    {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (ζ : K') (hζ : IsPrimitiveRoot ζ p) (hζK : ∃ k : K, algebraMap K K' k = ζ)
    (ι : Type) [Fintype ι] (A : ι → NK.BrauerHasse.OverFinitePrime K K')
    (hnot : ∀ i j : ι, i ≠ j → ¬ InOrbit (K := K) (K' := K') ⊤ (A i).1 (A j).1) :
    Function.Surjective (fun x : NK.BrauerHasse.H2Profinite (K := K) (K' := K') p ⊤ =>
      fun i : ι => NK.BrauerHasse.H2Profinite.loc p ⊤ x (A i)) :=
  h hp hodd (F := K) (F' := K') ζ hζ hζK ι A hnot

end NK.NUV2.LC.RouteB
