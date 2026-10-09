/-
Copyright (c) 2025. All rights reserved.

# `Submission.Work.AbsoluteKummer` — Kummer theory in the absolute-Galois language

Umbrella module for the chapter.  Import everything with

```lean
import Submission.Work.AbsoluteKummer.All
```

## Continuous cohomology of `G_k` in low degrees

* `Work.AbsoluteKummer.IsLocallyConstant` (continuity into discrete coefficients),
  `Work.AbsoluteKummer.IsDiscreteModule` (continuity of the action);
* `Work.AbsoluteKummer.C1c`, `C2c`, `Z1`, `B1`, `Z2`, `B2`;
* `Work.AbsoluteKummer.H0 = M^G`, `H1 = Z¹/B¹`, `H2 = Z²/B²`, with `H1π`, `H2π`;
* functoriality `Work.AbsoluteKummer.mapH1` / `mapH2`
  (identity and composition: `mapH1_id_H1π`, `mapH1_comp_H1π`, `mapH2_id_H2π`, `mapH2_comp_H2π`);
* the compactness lemma `Work.AbsoluteKummer.finite_image_of_isLocallyConstant`.

## The finite-level (inflation) description

* `Work.AbsoluteKummer.Factorisation.exists_finiteGalois_le_ker` (and `..._le_ker_pair`): a locally
  constant function on `G_k` (resp. `G_k × G_k`) factors through a finite Galois quotient;
* `Work.AbsoluteKummer.Factorisation.exists_finiteGalois_cocycle`, `..._Z2`: every class in `H¹`
  (resp. `H²`) has a representative cocycle that descends to a finite Galois quotient;
* `Work.AbsoluteKummer.Inflation.inflH1_injective`: inflation from a finite quotient is injective,
  and the pull-back of a cocycle along a locally constant surjection is a continuous cocycle.

## Coefficients for `G_k`

* `Work.AbsoluteKummer.G k = Gal(k̄/k)`, definitionally `Field.absoluteGaloisGroup k`, with the
  module structures on `Additive (k̄)ˣ` and `Additive (μ_n(k̄))`, their discreteness
  (`isDiscreteModule_addUnits`, `isDiscreteModule_addRootsOfUnity`) and the triviality of the
  action on `μ_n` when `μ_n ⊆ k` (`smul_rootsOfUnity`, `B1_rootsOfUnity_eq_bot`).

## Hilbert 90 and Kummer theory

* `Work.AbsoluteKummer.exists_algEquiv_div_of_isCrossedHom` — Hilbert 90 for finite extensions;
* `Work.AbsoluteKummer.Hilbert90.exists_div_of_isCrossedHom` — **Hilbert 90 for `G_k`**;
* `Work.AbsoluteKummer.Hilbert90.H1_eq_zero` — the same as `H¹(G_k, k̄ˣ) = 0`;
* `Work.AbsoluteKummer.kummerEquiv` — the **Kummer isomorphism** `kˣ/(kˣ)^n ≃* H¹(G_k, μ_n)`, with
  `kummerEquiv_mk` computing its values and the additive form `kummerAddEquiv`;
* `Work.AbsoluteKummer.Kummer.kummerSES` — the Kummer sequence `1 → μ_n → k̄ˣ →^n k̄ˣ → 1` as a
  `ShortExactSeq`, and `Work.AbsoluteKummer.Kummer.kummerQuotientEquiv` — the Kummer isomorphism
  from it (with `Work.AbsoluteKummer.Kummer.nonempty_h0_addUnits_equiv`, `H⁰(G_k, k̄ˣ) ≃+ kˣ`).

## The arithmetic input and its `H¹` form

* `Work.AbsoluteKummer.Grunwald.sqClassLocalize_surjective` — **Grünwald in degree `2`** at the
  level of square classes (from `Work.QuadraticLocalGlobal.grunwald_degree_two`), with the
  distinctness correction `Function.Injective q`;
* `Work.AbsoluteKummer.Grunwald.sqClassLocalize_surjective_pi` — the same for `A = 𝔽₂^r`;
* `Work.AbsoluteKummer.grunwald_h1_surjective` — the same statement in `H¹` language (unconditional:
  `Work.AbsoluteKummer.localKummerTwo` discharges the local Kummer identification);
* `Work.AbsoluteKummer.grunwald_h1_surjective_pi` — the `A = μ₂^r` case;
* `Work.AbsoluteKummer.kummerEquivRatTwo` — the specialisation `ℚˣ/(ℚˣ)² ≃* H¹(G_ℚ, μ₂)`.

## The embedding-problem dictionary

* `Work.AbsoluteKummer.Embedding` — the `H¹`/`H²` dictionary (torsor structure, obstruction
  class, split problems, and the bridge to `Work.Properness.Setup.ScholzGrunwaldWangInput`).

## Short exact sequences

* `Work.AbsoluteKummer.ShortExactSeq` and the low-degree exact sequence, through `H²`:
  `Work.AbsoluteKummer.SES.exists_connecting_exact` (`H⁰(P) → H¹(M)`) and
  `Work.AbsoluteKummer.SES.exists_connecting_exact_H2` (`H¹(P) → H²(M)`).

See `NOTES.md` in this directory for the dictionary with Serre's *Galois Cohomology*, the precise
definitions, and the comparison with `Work.GroupCohomology` and `Work.Tate`.
-/
import Submission.Work.AbsoluteKummer.Defs
import Submission.Work.AbsoluteKummer.Basic
import Submission.Work.AbsoluteKummer.Coefficients
import Submission.Work.AbsoluteKummer.Kummer
import Submission.Work.AbsoluteKummer.Kummer.kummerMap_injective
import Submission.Work.AbsoluteKummer.Kummer.kummerMap_surjective
import Submission.Work.AbsoluteKummer.KummerBijective
import Submission.Work.AbsoluteKummer.SqClass
import Submission.Work.AbsoluteKummer.Rat
import Submission.Work.AbsoluteKummer.GrunwaldH1
import Submission.Work.AbsoluteKummer.Embedding
import Submission.Work.AbsoluteKummer.Factorisation.exists_finiteGalois_le_ker
import Submission.Work.AbsoluteKummer.Factorisation.exists_finiteGalois_cocycle
import Submission.Work.AbsoluteKummer.Factorisation.exists_finiteGalois_le_ker_pair
import Submission.Work.AbsoluteKummer.Factorisation.exists_finiteGalois_Z2
import Submission.Work.AbsoluteKummer.Inflation.inflH1_injective
import Submission.Work.AbsoluteKummer.Kummer.kummerSES
import Submission.Work.AbsoluteKummer.Kummer.nonempty_h0_addUnits_equiv
import Submission.Work.AbsoluteKummer.Kummer.kummerQuotientEquiv
import Submission.Work.AbsoluteKummer.Hilbert90.exists_div_of_isCrossedHom
import Submission.Work.AbsoluteKummer.Hilbert90.H1_eq_zero
import Submission.Work.AbsoluteKummer.Functoriality
import Submission.Work.AbsoluteKummer.Grunwald.sqClassLocalize_surjective
import Submission.Work.AbsoluteKummer.Grunwald.Pi
import Submission.Work.AbsoluteKummer.H1Pi.nonempty_h1_pi_equiv
import Submission.Work.AbsoluteKummer.SES
import Submission.Work.AbsoluteKummer.SES.Connecting
import Submission.Work.AbsoluteKummer.SES.range_mapH0_eq_ker_mapH0
import Submission.Work.AbsoluteKummer.SES.range_mapH1_eq_ker_mapH1
import Submission.Work.AbsoluteKummer.SES.ker_le_range_mapH0
import Submission.Work.AbsoluteKummer.SES.ker_mapH1_le_range_delta
import Submission.Work.AbsoluteKummer.SES.exists_connecting_exact
import Submission.Work.AbsoluteKummer.SES.exists_connecting_exact_H2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
