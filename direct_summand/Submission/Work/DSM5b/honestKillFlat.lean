import Mathlib
import Submission.Work.DSM5b.H0Defs

/-!
# Flat descent for the uniform honest killing (skeleton, session 5)

`Work.DSM5b.honestKillCoord` (and its Noetherian form `honestKillCoordNoeth`) concerns the *honest
coordinate complex* `HCX t ·`/`HCd t ·` over a ring `R`, for `t : ι → R`, `T ∈ R`, `t j₀ = T ^ e`.

When `t` and `T` come from a subring `R₀ ⊆ R` and `R` is **flat** over `R₀`, the complex over `R` is
the base change of the complex over `R₀` — each chart ring is, because `Algebra.adjoin` commutes
with base change and `R₀[t_k/t_S] ⊗_{R₀} R = R[t_k/t_S]` — so an exponent `T ^ N` killing the
cohomology over `R₀` kills the cohomology over `R` (`⊗_{R₀} R` is exact).  Applied to the Noetherian
subring `R₀ = 𝔽_p[T, t_i]` this transports `honestKillCoordNoeth` to `honestKillCoord` for
`R = R₀^{perf}`, where `R₀ → R₀^{perf}` **is** flat as soon as `R₀` is a polynomial ring:
`R₀ → R₀^{1/p}` is free (`R₀[X_i]/(X_i^p - T_i)`, monic), and `R₀ → R₀^{perf}` is a filtered colimit
of flat modules.  (This is exactly the flatness statement recorded in
`NOTES_perfectedRootKilling.md` §4; it is *false* for general perfect `R`, which is why §6 of those
notes is a separate flight.)

## Status of this skeleton (session 5)

Done here:

* `tS_algebraMap` — the denominator of the base-changed family is the image of the denominator;
* `locBC` — **the base-change map of the chart localisations** `R₀_{t_S} → R_{t_S}` (the identity on
  `R₀` and on fractions), built with the *general* `IsLocalization.liftAlgHom`;
* `locBC_algebraMap`, `locBC_chartGens` — it fixes `R₀` and carries chart generators to chart
  generators of the base-changed family.

**Correction of an earlier mis-diagnosis (worth recording).**  No extra `IsLocalization.Away`
instance is needed here, and none *can* be: the base-changed localisation `R ⊗_{R₀} R₀_{t_S}` is
**not** `IsLocalization.Away (tS t S)` over `R₀` — that would force every element to be
`b / (tS t S)^n` with `b ∈ R₀`, and `r / (tS t S)^n` for `r ∈ R ∖ R₀` is nobody's such element
(concretely, `IsLocalization`'s surjectivity condition fails).  The right tool is the general
`IsLocalization.liftAlgHom`, whose `IsLocalization M S` instance sits on the **source** `S = R₀_{t_S}`
(the built-in one) and whose target is any `R₀`-algebra — the call is
`IsLocalization.liftAlgHom (M := Submonoid.powers (tS t S)) (f := Algebra.ofId R₀ _) hf`.
(The `IsLocalization.Away.liftAlgHom` specialisation is *not* usable directly: its implicit source
`S` unifies with the target, because the target's denominator `tS (fun i => algebraMap R₀ R (t i)) S`
is `simp`-equal to `algebraMap R₀ R (tS t S)`.)

## What remains

1. `chartRing` base change: `Subalgebra.toSubmodule (chartRing (algebraMap ∘ t) S) =
   Submodule.span R ((chartRing t S).map (locBC t S) : Set _)`.  **The crux is now in place**: the
   generator-level `⊆`,
   * given `x` with `x * algebraMap ((algebraMap ∘ t) i) = algebraMap ((algebraMap ∘ t) k)`
     (`i ∈ S`), put `u := (isUnit_algebraMap_mem_self t S hi).unit` and
     `g := algebraMap (t k) * ↑u⁻¹`; then `g ∈ chartGens t S` (by `u`'s spec) and
     `locBC g` satisfies the **same** equation as `x` (`locBC_algebraMap` +
     `IsScalarTower.algebraMap_apply`), so `(x - locBC g) * algebraMap ((algebraMap ∘ t) i) = 0`;
     the coefficient is a unit (`isUnit_algebraMap_mem`), so `x = locBC g` — done,
   * then `chartGens (algebraMap ∘ t) S ⊆ locBC '' chartGens t S`; the `⊇` direction is
     `locBC_chartGens` composed with `Algebra.adjoin_le_iff`, and the two adjoins are related by
     `Algebra.adjoin R X = Submodule.span R (↑(Algebra.adjoin R₀ X))` (the adjoin over the tower);
     the statement itself elaborates as
     `Subalgebra.toSubmodule (chartRing (fun i => algebraMap R₀ R (t i)) S) = Submodule.span R
     ((chartRing t S).map (locBC (R := R) t S) : Set _)`;
2. the same for `rhoH`/`HCd`.  **The localisation-level heart is done**:
   `locBC_comp_locRes` / `locBC_comp_locRes_apply` — `locBC` commutes with the restriction maps
   `locRes` (both composites are `R₀`-algebra maps out of a localisation, so they agree by
   `IsLocalization.algHom_subsingleton`).  What remains here is to restrict `locBC` to the chart
   rings — `locBCRing : chartRing t S →ₐ[R₀] chartRing (algebraMap ∘ t) S`, obtained from
   `chartRingBaseChange` (in flight) — and then read off componentwise that the differential `HCd`
   of the base-changed complex is the base change of the differential `HCd`;
3. flat base change for homology: for flat `R₀ → R`, `ker (d ⊗ R) = ker d ⊗ R` and
   `range (d ⊗ R) = range d ⊗ R`, hence uniform honest killing over `R₀` implies it over `R`.
   **Status**: `Work.DSM5b.honestKillCoordFlat` (delegated) is the per-degree form of this; the
   pieces it needs are now all proved: `locBCRing`/`HCXb` (this file's sibling
   `Submission/Work/DSM5b/locBCRing.lean`), `hCdBaseChange`, `hcxbSpanTop`.

## The final application step: `R = R₀^{perf}` (design note)

To conclude `honestKillCoord` for `R = R₀^{perf}` (`R₀ = 𝔽_p[T, t_i]` a polynomial ring) one must
exhibit `R₀ → R₀^{perf}` as flat and feed it to `honestKillCoordFlat`.  Two facts are relevant:

* **`pthRootExtensionFree` (proved)** — `A[X_i]/(X_i^p - u_i)` is a *free* `A`-module.  This gives
  the first step `R₀ → R₀[X_i]/(X_i^p - T_i)` free, and by iteration every finite level free.
* **Mathlib's `PerfectClosure` is field-only** (`Mathlib/FieldTheory/PerfectClosure.lean`): there is
  **no ring-level perfect closure** in this pin.  The workspace's `Work.DSM5b.IsRootTower`
  (`Basic.lean`) describes root towers *inside* a ring but is not such a construction.  So this step
  needs either (a) the ring-level perfect closure as a filtered colimit of `p`-th root extensions
  (a filtered colimit of flat modules over the base is flat, so no purity of the transitions is
  needed), or (b) a direct identification of `R₀^{perf}` as the colimit inside the given perfect
  `R`.  This is the one piece of the flat-descent route that still has to be *designed*, not just
  proved.
-/

namespace Work.DSM5b

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

universe a

section BaseChange

variable {R₀ : Type a} [CommRing R₀] {R : Type a} [CommRing R] [Algebra R₀ R]
variable {ι : Type a} [DecidableEq ι]

/-- `tS` commutes with the algebra map: the denominator of the base-changed family is the image of
the denominator. -/
lemma tS_algebraMap (t : ι → R₀) (S : Finset ι) :
    tS (fun i => algebraMap R₀ R (t i)) S = algebraMap R₀ R (tS t S) := by
  simp only [tS, map_prod]

/-- **The base-change map of the chart localisations** `R₀_{t_S} → R_{t_S}`, the identity on `R₀`
and on fractions, built with the general `IsLocalization.liftAlgHom` (see the note in the header). -/
noncomputable def locBC (t : ι → R₀) (S : Finset ι) :
    Localization.Away (tS t S) →ₐ[R₀]
      Localization.Away (tS (fun i => algebraMap R₀ R (t i)) S) :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (tS t S))
    (f := Algebra.ofId R₀ _)
    (by
      rintro ⟨y, hy⟩
      obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff y (tS t S)).mp hy
      rw [map_pow]
      refine IsUnit.pow n ?_
      change IsUnit (algebraMap R₀
        (Localization.Away (tS (fun i => algebraMap R₀ R (t i)) S)) (tS t S))
      rw [IsScalarTower.algebraMap_apply R₀ R
        (Localization.Away (tS (fun i => algebraMap R₀ R (t i)) S)), ← tS_algebraMap]
      exact IsLocalization.Away.algebraMap_isUnit _)

@[simp] lemma locBC_algebraMap (t : ι → R₀) (S : Finset ι) (r : R₀) :
    locBC t S (algebraMap R₀ (Localization.Away (tS t S)) r)
      = algebraMap R₀ (Localization.Away (tS (fun i => algebraMap R₀ R (t i)) S)) r :=
  AlgHom.commutes _ r

/-- The base-change map sends the chart generators to the chart generators of the base-changed
family: `locBC (t_k/t_i) = (algebraMap t_k)/(algebraMap t_i)`.  This is the compatibility that makes
`chartRing` commute with the base change. -/
lemma locBC_chartGens (t : ι → R₀) (S : Finset ι) {x : Localization.Away (tS t S)}
    (hx : x ∈ chartGens t S) :
    locBC t S x ∈ chartGens (fun i => algebraMap R₀ R (t i)) S := by
  obtain ⟨i, hi, k, hk⟩ := hx
  refine ⟨i, hi, k, ?_⟩
  have h : locBC (R := R) t S (x * algebraMap R₀ (Localization.Away (tS t S)) (t i))
      = locBC (R := R) t S (algebraMap R₀ (Localization.Away (tS t S)) (t k)) :=
    congrArg (locBC (R := R) t S) hk
  simp only [map_mul, locBC_algebraMap] at h
  rw [show (algebraMap R (Localization.Away (tS (fun i => algebraMap R₀ R (t i)) S)))
        ((fun i => algebraMap R₀ R (t i)) i)
      = algebraMap R₀ (Localization.Away (tS (fun i => algebraMap R₀ R (t i)) S)) (t i)
      from IsScalarTower.algebraMap_apply R₀ R
        (Localization.Away (tS (fun i => algebraMap R₀ R (t i)) S)) (t i),
    show (algebraMap R (Localization.Away (tS (fun i => algebraMap R₀ R (t i)) S)))
        ((fun i => algebraMap R₀ R (t i)) k)
      = algebraMap R₀ (Localization.Away (tS (fun i => algebraMap R₀ R (t i)) S)) (t k)
      from IsScalarTower.algebraMap_apply R₀ R
        (Localization.Away (tS (fun i => algebraMap R₀ R (t i)) S)) (t k)]
  exact h

/-- **The scalar-consistency lemma for the base change**: the sign `(-1)^i` commutes with the
algebra map, so the alternating signs in `HCd` agree on the two sides of the base change. -/
lemma algebraMap_neg_one_pow {R₀ : Type a} [CommRing R₀] {R : Type a} [CommRing R]
    [Algebra R₀ R] (i : ℕ) :
    algebraMap R₀ R ((-1 : R₀) ^ i) = (-1 : R) ^ i := by
  rw [map_pow, map_neg, map_one]

/-- **Naturality of the base-change map with respect to the restriction maps** `locRes`: the
square

    R₀_{t_S} --locRes--> R₀_{t_T} --locBC--> R_{t_T}
      | locBC                                  ^ locRes
      v                                        |
    R_{t_S} ------------------locRes----------

commutes.  Both composites are `R₀`-algebra maps out of the localisation `R₀_{t_S}`, so they agree
by uniqueness (`IsLocalization.algHom_subsingleton`).  This is the localisation-level content of
step 2: it is what makes the differential `HCd` of the base-changed complex the base change of the
differential. -/
lemma locBC_comp_locRes (t : ι → R₀) {S T : Finset ι} (h : S ⊆ T) :
    ((locBC t T).comp (locRes t h) : Localization.Away (tS t S) →ₐ[R₀]
        Localization.Away (tS (fun i => algebraMap R₀ R (t i)) T))
      = ((locRes (fun i => algebraMap R₀ R (t i)) h).restrictScalars R₀).comp (locBC t S) := by
  haveI : Subsingleton (Localization.Away (tS t S) →ₐ[R₀]
      Localization.Away (tS (fun i => algebraMap R₀ R (t i)) T)) :=
    IsLocalization.algHom_subsingleton (Submonoid.powers (tS t S))
  exact Subsingleton.elim _ _

@[simp] lemma locBC_comp_locRes_apply (t : ι → R₀) {S T : Finset ι} (h : S ⊆ T)
    (y : Localization.Away (tS t S)) :
    locBC t T (locRes t h y)
      = locRes (fun i => algebraMap R₀ R (t i)) h (locBC t S y) :=
  DFunLike.congr_fun (locBC_comp_locRes t h) y

/-- **Each `algebraMap t_i` (`i ∈ S`) is a unit in the base-changed localisation**, because it is a
factor of the inverted denominator `tS (fun j => algebraMap R₀ R (t j)) S = ∏ j ∈ S, algebraMap (t j)`
(and a divisor of a unit is a unit).  This is the input of the `⊆` direction of the chart-ring base
change: it is what lets one cancel `algebraMap t_i` to identify an over-`R` chart generator with the
image of the corresponding over-`R₀` generator. -/
lemma isUnit_algebraMap_mem (t : ι → R₀) (S : Finset ι) {i : ι} (hi : i ∈ S) :
    IsUnit (algebraMap R
      (Localization.Away (tS (fun j => algebraMap R₀ R (t j)) S))
      ((fun j => algebraMap R₀ R (t j)) i)) := by
  have hdvd : (fun j => algebraMap R₀ R (t j)) i ∣ tS (fun j => algebraMap R₀ R (t j)) S :=
    Finset.dvd_prod_of_mem (fun j => algebraMap R₀ R (t j)) hi
  exact isUnit_of_dvd_unit
    (map_dvd (algebraMap R (Localization.Away (tS (fun j => algebraMap R₀ R (t j)) S))) hdvd)
    (IsLocalization.Away.algebraMap_isUnit (tS (fun j => algebraMap R₀ R (t j)) S))

/-- The over-`R₀` version of `isUnit_algebraMap_mem` (the specialisation `R = R₀`). -/
lemma isUnit_algebraMap_mem_self (t : ι → R₀) (S : Finset ι) {i : ι} (hi : i ∈ S) :
    IsUnit (algebraMap R₀ (Localization.Away (tS t S)) (t i)) := by
  have h := isUnit_algebraMap_mem (R := R₀) t S hi
  simpa using h

end BaseChange

end Work.DSM5b
