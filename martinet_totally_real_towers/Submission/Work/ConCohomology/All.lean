/-
Copyright: the martinet_totally_real_towers team.

# Continuous cohomology of profinite groups with discrete coefficients

One import for the whole chapter:

```lean
import Submission.Work.ConCohomology.All
```

## Contents

* `Defs.lean`   -- `IsDiscreteGModule`, `Cochain1/2/3`, `d0Fun/d1Fun/d2Fun`, `d0Hom/d1Hom/d2Hom`,
                   `IsCocycle1/2`, `Z1/B1/B1'/Z2/B2/B2'`, `fixedPoints/H0/H1/H2` and the `mk`/`mem` API.
* `Basic.lean`  -- `EqHom`, compatibility of the differentials with coefficient maps, `ContAddHom`,
                   local constancy of homomorphisms with open kernel.
* `Setup.lean`  -- `CoeffSES` (a short exact sequence of discrete `G`-modules) and the raw
                   connecting cochains `delta0Fun`, `delta1Fun`.
* `Functoriality.lean` -- coefficient change `H^n(A) → H^n(B)` and group change (restriction /
                   inflation / localisation) `H^n(G,M) → H^n(H,M)`.
* `GaloisUnits.lean` -- the Galois module `Additive Lˣ` and its discreteness.
* `Connecting.lean` -- the connecting maps `δ⁰ : H⁰(C) → H¹(A)`, `δ¹ : H¹(C) → H²(A)`.
* `LongExact.lean`, `exact_H0_C` ... `exact_H2_B` -- the long exact sequence in low degrees.
* `TrivialAction.lean` -- `H¹(G,M) ≃ ContAddHom G M` for trivial action.
* Hilbert 90: `hilbert90_finite_units`, `hilbert90_infinite_units`, `hilbert90_subsingleton_H1`.
* Kummer: `Kummer.lean` (the sequence `kummerSES`), `KummerConsequences.lean`,
                   `KummerGalois.lean` (the `Lˣ` statements), `nPowers_units_eq_top`,
                   `H1_nPowers_subsingleton`, `mem_fixedPoints_units_iff`.
* Group extensions: `Extension.lean` (`GroupExt`, conjugation, `tgFun`/`tgCochain`),
                   `isCocycle2_tgFun`, `tgFun_section_independence`,
                   `q_pullback_tgFun_is_coboundary`,
                   `pullback_coboundary_iff_exists_invariant_cocycle` (cochain-level
                   `ker(inf₂) = im(tg)`), `FiveTerm.lean` (the `Q`-action on `H¹(N,M)` and the
                   invariants `H1Invariants`), `ker_H2Res_eq_range_tg` (`H²`-level exactness),
                   `ker_res_eq_range_inf` (`ker(res) = im(inf)` at `H¹`).

-/

import Submission.Work.ConCohomology.Defs
import Submission.Work.ConCohomology.Basic
import Submission.Work.ConCohomology.Setup
import Submission.Work.ConCohomology.Functoriality
import Submission.Work.ConCohomology.GaloisUnits
import Submission.Work.ConCohomology.Connecting
import Submission.Work.ConCohomology.LongExact
import Submission.Work.ConCohomology.TrivialAction
import Submission.Work.ConCohomology.Kummer
import Submission.Work.ConCohomology.Extension
import Submission.Work.ConCohomology.invFun_spec
import Submission.Work.ConCohomology.invFun_eq_of
import Submission.Work.ConCohomology.invFun_add
import Submission.Work.ConCohomology.invFun_smul
import Submission.Work.ConCohomology.isCocycle1_delta0Fun
import Submission.Work.ConCohomology.isLocallyConstant_delta1Fun
import Submission.Work.ConCohomology.isCocycle2_delta1Fun
import Submission.Work.ConCohomology.delta1Fun_add_coboundary
import Submission.Work.ConCohomology.exists_cochain_delta1Fun_add_coboundary
import Submission.Work.ConCohomology.B1_eq_bot_of_trivial
import Submission.Work.ConCohomology.isCocycle1_iff_of_trivial
import Submission.Work.ConCohomology.exact_H0_C
import Submission.Work.ConCohomology.exact_H1_A
import Submission.Work.ConCohomology.exact_H1_B
import Submission.Work.ConCohomology.exact_H1_C
import Submission.Work.ConCohomology.exact_H2_A
import Submission.Work.ConCohomology.exact_H2_B
import Submission.Work.ConCohomology.hilbert90_finite_units
import Submission.Work.ConCohomology.hilbert90_infinite_units
import Submission.Work.ConCohomology.kummer_H1_surjective
import Submission.Work.ConCohomology.kummer_H2_injective
import Submission.Work.ConCohomology.ker_res_eq_range_inf
import Submission.Work.ConCohomology.isCocycle1_conjCochain
import Submission.Work.ConCohomology.conjCochain_mul
import Submission.Work.ConCohomology.conjCochain_coboundary
import Submission.Work.ConCohomology.conjCochain_inner
import Submission.Work.ConCohomology.isCocycle2_tgFun
import Submission.Work.ConCohomology.q_pullback_tgFun_is_coboundary
import Submission.Work.ConCohomology.tgFun_section_independence
import Submission.Work.ConCohomology.pullback_coboundary_iff_exists_invariant_cocycle
import Submission.Work.ConCohomology.KummerConsequences
import Submission.Work.ConCohomology.KummerGalois
import Submission.Work.ConCohomology.FiveTerm
import Submission.Work.ConCohomology.ker_H2Res_eq_range_tg
import Submission.Work.ConCohomology.hilbert90_subsingleton_H1
import Submission.Work.ConCohomology.mem_fixedPoints_units_iff
import Submission.Work.ConCohomology.nPowers_units_eq_top
import Submission.Work.ConCohomology.H1_nPowers_subsingleton
