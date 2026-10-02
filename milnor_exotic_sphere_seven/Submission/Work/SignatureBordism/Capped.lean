import Mathlib
import Submission.Work.SignatureBordism.Rationalisation
import Submission.Work.Cohomology.capped_cupSquare_generates
import Submission.Work.Milnor.capped_generator_pairings
import Submission.Work.Milnor.capped_kronH_isIso
import Submission.Work.SignatureBordism.exists_capped_fundamentalClass

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The signature of the closed `8`-manifold `X = D(ξ) ∪_F D⁸`

Let `ξ = Vk (-2)` be the rank-`4` bundle over `S⁴` whose sphere bundle is Milnor's manifold
`M := Mk (-2)`, and let `X = D(ξ) ∪_F D⁸` be the closed oriented smooth `8`-manifold obtained by
gluing the disc bundle to a disc along a capping diffeomorphism `F` (the construction of
`Submission/Work/Milnor/CappedManifold.lean`).  Its integral cohomology is `ℤ` in degrees `0`, `4`
and `8` (`Work.Milnor.cohomology_capped_datum`), and the cup square of a generator of `H⁴(X;ℤ)` is a
generator of `H⁸(X;ℤ)` (`Work.Cohomology.capped_cupSquare_generates`) — Poincaré duality in the
middle degree, i.e. unimodularity of the intersection form.

The present file computes the **signature** `σ(X)`: for a generator `x` of `H⁴(X;ℤ)` and a
fundamental class `c ∈ H₈(X;ℤ)` (a generator, `exists_capped_fundamentalClass`), the middle
self-intersection `m = ⟨x ⌣ x, c⟩` is `±1` because `Work.Milnor.capped_generator_pairings` says
that the Kronecker pairing of two generators is `±1`.  Hence `H⁴(X;ℚ)` is one-dimensional with the
intersection form the `1 × 1` form `(m)`, and by
`Work.SignatureBordism.sigma_of_span_singleton`

  **`σ(X) = ±1`.**

This is the input `(i)` of the endgame of `Submission/NOTES.md` §14.8 in the form in which it is
consumed (`Work.Milnor.endgame_congruence_route'`); the remaining inputs are the
characteristic-class computation `p₁(X) = ±6·x` (parallel subproject,
`Submission/Work/CharacteristicClasses/`) and the dimension-`8` Hirzebruch identity
(`Submission/Work/SignatureBordism/Hirzebruch.lean`).

## Main results

* `Work.SignatureBordism.sigma_capped_eq_pm_one` — `σ(X) = 1 ∨ σ(X) = -1` for every fundamental
  class `c` of `X`;
* `Work.SignatureBordism.exists_capped_fundamentalClass` — `H₈(X;ℤ) ≅ ℤ` has a generator.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open TensorProduct

namespace Work.SignatureBordism

open Work.Cohomology

noncomputable section

/-- The simplicial set of the capped manifold `X = D(ξ) ∪_F D⁸`. -/
abbrev cappedSSet (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8)
    (hF : Work.Milnor.IsCappingDiffeo F) : SSet :=
  TopCat.toSSet.obj (TopCat.of (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))

variable (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8)
variable (hF : Work.Milnor.IsCappingDiffeo F)

/-- **Unimodularity of the middle self-intersection of `X = D(ξ) ∪_F D⁸`.**  If `x` generates
`H⁴(X;ℤ)`, its cup square generates `H⁸(X;ℤ)` and `c` generates `H₈(X;ℤ)`, then the
self-intersection number `m = ⟨x ⌣ x, c⟩` is `±1`.

This is input `(i)` of the endgame of `Submission/NOTES.md` §14.8 in its sharpest form
`m = ±1`: `Work.Cohomology.capped_cupSquare_generates` supplies an `x` whose cup square generates
(whence the intersection form on `H⁴(X;ℤ) = ℤ` is unimodular), and
`Work.Milnor.cgp_kronH_eval_generator` (from `Work.Milnor.capped_generator_pairings`) says that the
Kronecker pairing of two generators is `±1`. -/
theorem capped_selfIntersection_eq_pm_one (x : (cochainC ℤ (cappedSSet F hF)).homology 4)
    (hx : Submodule.span ℤ {x} = ⊤)
    (hxcup : ∀ y : (cochainC ℤ (cappedSSet F hF)).homology 8,
      ∃ a : ℤ, y = a • cupH' ℤ (cappedSSet F hF) 4 4 x x)
    (c : (chainC ℤ (cappedSSet F hF)).homology 8) (hc : Submodule.span ℤ {c} = ⊤) :
    interForm ℤ (cappedSSet F hF) 4 4 c x x = 1 ∨
      interForm ℤ (cappedSSet F hF) 4 4 c x x = -1 := by
  obtain ⟨e⟩ := Work.Milnor.cgp_homology_linEquiv_one F hF (n := 8) (by norm_num)
  have hpair := Work.Milnor.cgp_kronH_eval_generator
    (L := kronH ℤ (cappedSSet F hF) 8) ((Work.Milnor.capped_kronH_isIso F hF 8).2)
    (cupH' ℤ (cappedSSet F hF) 4 4 x x) ((span_singleton_eq_top_iff _).mpr hxcup) e c hc
  rw [interForm_apply]
  exact hpair

/-- **The signature of the capped manifold `X = D(ξ) ∪_F D⁸` is `±1`.**

For any fundamental class `c` (a generator of `H₈(X;ℤ) ≅ ℤ`) the signature of `X` — the signature
of the intersection form `y ↦ ⟨y ⌣ y, c⟩` on the rationalised middle cohomology
`H⁴(X;ℤ) ⊗ ℚ = ℚ` — is `1` or `-1`.

The proof: `Work.Cohomology.capped_cupSquare_generates` produces a generator `x` of `H⁴(X;ℤ)`
whose cup square `x ⌣ x` generates `H⁸(X;ℤ)`; the self-intersection `m = ⟨x ⌣ x, c⟩` is `±1` by
`Work.SignatureBordism.capped_selfIntersection_eq_pm_one`; then
`Work.SignatureBordism.sigma_eq_one_of_span_singleton` (resp. `..._neg_one`) computes the signature
of the resulting `1 × 1` form `(m)`. -/
theorem sigma_capped_eq_pm_one (c : (chainC ℤ (cappedSSet F hF)).homology 8)
    (hc : Submodule.span ℤ {c} = ⊤) :
    sigma 4 (cappedSSet F hF) c = 1 ∨ sigma 4 (cappedSSet F hF) c = -1 := by
  obtain ⟨x, hx, hxcup⟩ := capped_cupSquare_generates F hF
  have hx' : Submodule.span ℤ {x} = ⊤ := (span_singleton_eq_top_iff x).mpr hx
  rcases capped_selfIntersection_eq_pm_one F hF x hx' hxcup c hc with h | h
  · left; exact sigma_eq_one_of_span_singleton 4 (cappedSSet F hF) c x hx' h
  · right; exact sigma_eq_neg_one_of_span_singleton 4 (cappedSSet F hF) c x hx' h

/-- **The inputs `(i)` of the endgame, packaged.**  There is a generator `x` of `H⁴(X;ℤ)` and a
generator (fundamental class) `c` of `H₈(X;ℤ)` whose self-intersection number `⟨x ⌣ x, c⟩` is `±1`.
-/
theorem capped_endgame_inputs :
    ∃ (x : (cochainC ℤ (cappedSSet F hF)).homology 4)
      (c : (chainC ℤ (cappedSSet F hF)).homology 8),
      Submodule.span ℤ {x} = ⊤ ∧ Submodule.span ℤ {c} = ⊤ ∧
      (interForm ℤ (cappedSSet F hF) 4 4 c x x = 1 ∨
        interForm ℤ (cappedSSet F hF) 4 4 c x x = -1) := by
  obtain ⟨x, hx, hxcup⟩ := capped_cupSquare_generates F hF
  obtain ⟨c, hc⟩ := exists_capped_fundamentalClass F hF
  exact ⟨x, c, (span_singleton_eq_top_iff x).mpr hx, hc,
    capped_selfIntersection_eq_pm_one F hF x ((span_singleton_eq_top_iff x).mpr hx) hxcup c hc⟩

/-- **The signature of the capped manifold, existentially.**  `H₈(X;ℤ) ≅ ℤ` has a generator `c`
(`Work.SignatureBordism.exists_capped_fundamentalClass`) and for it the signature of `X` is `±1`
(`Work.SignatureBordism.sigma_capped_eq_pm_one`). -/
theorem exists_sigma_capped_eq_pm_one :
    ∃ c : (chainC ℤ (cappedSSet F hF)).homology 8, Submodule.span ℤ {c} = ⊤ ∧
      (sigma 4 (cappedSSet F hF) c = 1 ∨ sigma 4 (cappedSSet F hF) c = -1) := by
  obtain ⟨c, hc⟩ := exists_capped_fundamentalClass F hF
  exact ⟨c, hc, sigma_capped_eq_pm_one F hF c hc⟩

end

end Work.SignatureBordism
