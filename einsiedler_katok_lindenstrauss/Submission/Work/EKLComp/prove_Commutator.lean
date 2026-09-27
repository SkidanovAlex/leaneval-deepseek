import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLC7.Defs
import Submission.Work.EKLC7.CommutatorStep
import Submission.Work.EKLC7.PeriodSmallIter
import Submission.Work.EKLC7.CommutatorFromExistence
import Submission.Work.EKLC7.LeafwiseHoro
import Submission.Work.EKLC7.ProveProductWiring

/-!

# C7 — the commutator lemma (`P_Commutator`)

EKL Lemma 3.3 (= Einsiedler–Katok Lemma 6.1, Pisa 9.11): for an `A`-ergodic probability measure
`μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)` and distinct indices `i, j, k`, if neither `U_ij` nor `U_jk` is a
`μ`-cross-section then `μ` is `U_ik`-invariant.

## What is needed, and where it comes from

The frozen contract (`Submission/Work/EKLContract/Defs.lean`) phrases C7 as
`p_commutator : P_Leafwise → P_Product → P_Commutator`, and `EKLContract/Glue.lean` consumes it in
that form.  The commutator argument itself, however, only uses the **existence half** of `P_Leafwise`
plus the clauses (U3)–(U8) for the *root groups* `U_ij`; both are available as

* `Work.EKLC7.LeafwiseHoro : Work.EKLC7.P_LeafwiseEx` (existence of leafwise measures for every
  horospherical subgroup, Pisa Thm 6.3 — the whole `LeafNu*`/flower construction),
* `Work.EKLC7.RootPropsC7 : Work.EKLC7.P_RootProps` (clauses (U3), (U4), (U5), (U7), (U8) at the
  root groups; (U4) in the direction `AeHaar → IsUInvariant` consumed by the argument, (U5) by the
  EKL (8) argument, (U7) is EKL (4)/Pisa 7.16, (U8) the ergodic dichotomy),

and the assembly is `Work.EKLC7.commutator_step_raw` (`Submission/Work/EKLC7/CommutatorStepRaw.lean`),
packaged as `Work.EKLC7.commutator_of_existence` (`CommutatorFromExistence.lean`).  The remaining
ingredients — the two product formulae `ProductTriple` (from C5b), the commutator-translation
identity `FiberRelIter`, the small-support lemmas `SuppSmall`/`RootSupp`/`SuppSmallDerive`, the
period extraction `PeriodSmallIter` and `PerSub` — are all proved in `Submission/Work/EKLC7/`.

So the *only* external input of the proof below is C5b, `Work.EKLComp.prove_Product : P_Product`
(Pisa Prop. 8.5 / Cor. 8.8).  In particular the frozen component C5 (`P_Leafwise`, whose last
missing piece is the `(U4)` direction `IsUInvariant → AeHaar`, being closed in
`Submission/Work/EKLC7/AeHaarPLAN.md` / `Work.EKLC7.AeHaar_of_isUInvariant`) is *not* needed here.

Note for C5b: the C5b development (`Submission/Work/EKLProd/*.lean`) extracts only clauses **(U6)**
(Luzin) and **(U7)** (`A`-covariance) from its `hLeaf : P_Leafwise` hypothesis (see e.g.
`EKLProd/nuT_class_of_mem_shape.lean:192`, `EKLProd/prodFlower_nuT_class.lean:152`,
`EKLProd/nuT_aDiag_pow_invariant.lean:89`).  Both are proved for *every* horospherical subgroup as
`Work.EKLC7.P_LeafwiseLuzin.proved` and `Work.EKLC7.P_LeafwiseCov.proved`
(`Submission/Work/EKLC7/LeafwiseClauses.lean`), so C5b can be carried out against the clause
packages of that module instead of against the whole of C5.

## Status

* everything on the C7 side is proved and axiom-clean
  (`#print axioms Work.EKLC7.RootPropsC7 = [propext, Classical.choice, Quot.sound]`,
  same for `Work.EKLC7.commutator_of_existence`);
* `prove_Commutator` is complete for `P_Product` (`Work.EKLC7.prove_Product_c7`, the frozen
  component C5b); see `Submission/Work/EKLProd/` for that development.
* An *independent* second proof of `P_Product` (by the globalisation route, i.e. through the
  small product-box flower families of `Work.EKLProd.prodFlowerFam_exists_small` and the
  measure-theoretic reduction `Work.EKLGlobal.frozen_of_box_identities`) is
  `Work.EKLGlobal.prove_Product_via_global` in `Submission/Work/EKLGlobal/ProductConclusion.lean`.
-/

namespace Work.EKLComp

open MeasureTheory Filter Topology
open Work.EKLContract

theorem prove_Commutator : Work.EKLContract.P_Commutator :=
  Work.EKLC7.commutator_of_existence Work.EKLC7.LeafwiseHoro Work.EKLC7.prove_Product_c7

/-! The assembly is `Work.EKLC7.commutator_of_existence : P_LeafwiseEx → P_Product →
P_Commutator` (proved, axiom-clean, `Submission/Work/EKLC7/CommutatorFromExistence.lean`), and the
statement above is its instantiation at `Work.EKLC7.LeafwiseHoro` (the existence half of C5, proved)
and at `Work.EKLC7.prove_Product_c7 : P_Product`
(`Submission/Work/EKLC7/ProveProductWiring.lean`), which is the component statement of C5b
applied to the proved `Work.EKLC7.P_Leafwise_proved`; the only remaining input is therefore the
mathematical content of C5b, `Work.EKLComp.prove_Product_aux`. -/

end Work.EKLComp
