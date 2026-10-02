import Mathlib
import Submission.Work.Cohomology.RelCapHTransfer
import Submission.Work.Cohomology.relCapH_kronH_cup
import Submission.Work.Cohomology.RelCap
import Submission.Work.Cohomology.RelCupTransfer

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative cap/cup adjunction `⟨1, (u ⌣ u) ⌢ c⟩ = ⟨relIncl u, u ⌢ c⟩`

For a pair `(X,A)`, a relative class `u ∈ H⁴(X,A;ℤ)` and a relative homology class
`c ∈ H₈(X,A;ℤ)`, the two ways of evaluating the "self-intersection" of `u` against `c` agree:

  `⟨1, (u ⌣ u) ⌢ c⟩ = ⟨relIncl u, u ⌢ c⟩`,

where the left hand side is the augmentation `H₀(X;ℤ) → ℤ` (the Kronecker pairing with the unit
class `1 ∈ H⁰(X;ℤ)`) applied to the `(8,0)` relative cap product, and the right hand side is the
absolute Kronecker pairing of the image of `u` in `H⁴(X;ℤ)` with the `(4,4)` relative cap product.

Both sides are computed at the chain level: if `a` is a relative `4`-cocycle representing `u`,
`cc` a relative `8`-cycle representing `c` and `ẑ` an absolute `8`-chain lifting `cc`, then

* the left hand side is `(a ⌣ a)(ẑ)`, by the unit law for the `(n,0)` cap product
  (`relCapPair_cup_adjunction_aux_L`);
* the right hand side is `a(a ⌢ ẑ)`, by the `(4,4)` computation rule for the cap product
  (`relCapPair_cup_adjunction_aux_R`);

and these agree by the cap/cup identity `relKronecker_cap_cup`.

This is the chain-level form of the classical identity `(α ⌣ β) ⌢ c = α ⌢ (β ⌢ c)` (with `α = β`),
which on the capped manifold evaluates the self-intersection form of `X = Vk(-2) ∪ D⁸` by
transferring it to the relative pair `(Vk(-2), Mk(-2))`; see `Submission/NOTES.md`.

## Main results

* `relCapPair_cup_adjunction_aux_L`, `relCapPair_cup_adjunction_aux_R` — the two chain-level
  computations;
* `relCapPair_cup_adjunction` — the adjunction.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicTopology Limits

namespace Work.Cohomology.Crux

/-- **The `(n,0)` evaluation of the relative cap product against the unit class.**  For a relative
`n`-cocycle `w`, a relative `n`-cycle `cc` and an absolute `n`-chain `ẑ` lifting `cc`, the
Kronecker pairing of the unit class `1 ∈ H⁰(X;ℤ)` with `[w] ⌢ [cc] ∈ H₀(X;ℤ)` is the evaluation
`w(ẑ)` of the relative cocycle `w` on `ẑ`.

The computation goes through the chain level: `w ⌢ ẑ` is a `0`-chain, on which the augmentation
`unitCochain` is nothing but the evaluation of `w` (`kronecker_cap_cup` together with the right
unit law `cupUnit`). -/
theorem relCapPair_cup_adjunction_aux_L (X : TopCat) (A : Set X) {n : ℕ}
    (w : relKern ℤ X A n) (hw : relDiffLM ℤ X A n w = 0)
    (cc : (relChains X A).cycles (n + 0)) (zhat : (singularChains ℤ X).X (n + 0))
    (hzhat : (cokernel.π ((inclChains X A).f (n + 0))).hom zhat
      = (relChains_cokernelIso X A (n + 0)).hom ((relChains X A).iCycles (n + 0) cc)) :
    kronH ℤ (TopCat.toSSet.obj X) 0 (oneH ℤ (TopCat.toSSet.obj X))
        (relCapPair X A n 0 (relClassOf ℤ X A w hw)
          ((relChains X A).homologyπ (n + 0) cc))
      = kronecker ℤ (TopCat.toSSet.obj X) (w.1 : Cochain ℤ (TopCat.toSSet.obj X) n) zhat := by
  unfold relClassOf
  rw [relCapPair_apply X A n 0 (relCocycleOf ℤ X A w hw) cc]
  unfold oneH
  rw [kronH_apply_sing X (unitCochain ℤ (TopCat.toSSet.obj X))
      (cochainDiff_unitCochain ℤ (TopCat.toSSet.obj X))
      (relCapPairZ X A n 0 (relCocycleOf ℤ X A w hw) cc)]
  rw [relCapPairZ_iCycles X A n 0 (relCocycleOf ℤ X A w hw) cc]
  rw [iCycles_relCocycleOf ℤ X A w hw]
  rw [← hzhat]
  rw [relCapHalf_apply_incl X A w zhat]
  rw [show unitCochain ℤ (TopCat.toSSet.obj X)
        ((cap ℤ (TopCat.toSSet.obj X) (w.1 : Cochain ℤ (TopCat.toSSet.obj X) n) 0) zhat)
      = kronecker ℤ (TopCat.toSSet.obj X) (unitCochain ℤ (TopCat.toSSet.obj X))
          ((cap ℤ (TopCat.toSSet.obj X) (w.1 : Cochain ℤ (TopCat.toSSet.obj X) n) 0) zhat)
      from rfl]
  rw [kronecker_cap_cup ℤ (TopCat.toSSet.obj X) (w.1 : Cochain ℤ (TopCat.toSSet.obj X) n)
        (unitCochain ℤ (TopCat.toSSet.obj X)) zhat]
  rw [(cupUnit ℤ (TopCat.toSSet.obj X) (w.1 : Cochain ℤ (TopCat.toSSet.obj X) n)).2]

/-- **The `(4,4)` evaluation of the relative cap product.**  For a relative `4`-cocycle `a`, a
relative `8`-cycle `cc` and an absolute `8`-chain `ẑ` lifting `cc`, the pairing of the image of
`[a]` in `H⁴(X;ℤ)` with `[a] ⌢ [cc] ∈ H₄(X;ℤ)` is the evaluation of the relative square `a ⌣ a`
on `ẑ`. -/
theorem relCapPair_cup_adjunction_aux_R (X : TopCat) (A : Set X)
    (a : relKern ℤ X A 4) (ha : relDiffLM ℤ X A 4 a = 0)
    (cc : (relChains X A).cycles 8) (zhat : (singularChains ℤ X).X 8)
    (hzhat : (cokernel.π ((inclChains X A).f 8)).hom zhat
      = (relChains_cokernelIso X A 8).hom ((relChains X A).iCycles 8 cc)) :
    kronH ℤ (TopCat.toSSet.obj X) 4
      ((HomologicalComplex.homologyMap (relIncl ℤ X A) 4) (relClassOf ℤ X A a ha))
      ((relCapPair X A 4 4) (relClassOf ℤ X A a ha) (((relChains X A).homologyπ 8) cc))
    = kronecker ℤ (TopCat.toSSet.obj X) ((relCup ℤ X A 4 4 a a).1) zhat := by
  have hαc : relClassOf ℤ X A a ha
      = ((relComplex ℤ X A).homologyπ 4) (relCocycleOf ℤ X A a ha) := rfl
  rw [relIncl_homologyMap_relClassOf ℤ X A a ha]
  rw [hαc]
  rw [relCapPair_apply X A 4 4 (relCocycleOf ℤ X A a ha) cc]
  rw [kronH_apply_sing X (a.1 : Cochain ℤ (TopCat.toSSet.obj X) 4)
    (relClassOf_cochainDiff ℤ X A a ha)
    (relCapPairZ X A 4 4 (relCocycleOf ℤ X A a ha) cc)]
  rw [relCapPairZ_iCycles X A 4 4 (relCocycleOf ℤ X A a ha) cc]
  rw [iCycles_relCocycleOf ℤ X A a ha]
  rw [← hzhat]
  rw [relCapHalf_apply_incl (m := 4) X A a zhat]
  exact relKronecker_cap_cup ℤ X A a a zhat

theorem relCapPair_cup_adjunction {X : TopCat} {A : Set X}
    (u : Work.Cohomology.relCohomology ℤ X A 4)
    (c : (Work.Cohomology.relChains X A).homology 8) :
    Work.Cohomology.kronH ℤ (TopCat.toSSet.obj X) 0
        (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj X))
        (Work.Cohomology.relCapPair X A 8 0
          (Work.Cohomology.relCupH' ℤ X A 4 4 u u) c)
      = Work.Cohomology.kronH ℤ (TopCat.toSSet.obj X) 4
          ((HomologicalComplex.homologyMap (Work.Cohomology.relIncl ℤ X A) 4) u)
          (Work.Cohomology.relCapPair X A 4 4 u c) := by
  obtain ⟨a, ha, rfl⟩ := exists_relClassOf ℤ X A 4 u
  obtain ⟨cc, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((relChains X A).homologyπ 8)).mp inferInstance c
  rw [relCupH'_apply ℤ X A a a ha ha]
  obtain ⟨zhat, hzhat⟩ : ∃ zhat : (singularChains ℤ X).X 8,
      (cokernel.π ((inclChains X A).f 8)).hom zhat
        = (relChains_cokernelIso X A 8).hom ((relChains X A).iCycles 8 cc) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance _
  have hL := relCapPair_cup_adjunction_aux_L X A (n := 8) (relCup ℤ X A 4 4 a a)
      (relDiffLM_relCup_of_cocycles ℤ X A a a ha ha) cc zhat hzhat
  have hR := relCapPair_cup_adjunction_aux_R X A a ha cc zhat hzhat
  exact hL.trans hR.symm

end Work.Cohomology.Crux
