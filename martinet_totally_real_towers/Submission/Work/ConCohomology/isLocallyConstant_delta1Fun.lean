/-
Copyright: the martinet_totally_real_towers team.

# Local constancy of the degree `1 → 2` connecting cochain

The raw connecting cochain `S.delta1Fun c` attached to a (locally constant) `1`-cochain
`c : G → C` is defined by means of the *arbitrary* set-theoretic section `S.sect` of the
projection `B → C` and the set-theoretic inverse `S.invFun` of the injection `A → B`; neither
of these two choices is locally constant.  Nevertheless the composite is: the argument of
`S.invFun` is a sum of three terms each of which is locally constant, because

* `τ ↦ S.sect (c τ)` is locally constant (`sect` applied after the locally constant `c`; a
  locally constant function stays locally constant after post-composition with *any* function),
* `(σ, τ) ↦ σ • S.sect (c τ)` is locally constant since `B` is a discrete `G`-module
  (varying `σ` with the second argument in a local constancy set), and
* `(σ, τ) ↦ S.sect (c (σ * τ))` is locally constant since multiplication is continuous.

Finally, post-composition of a locally constant function with the *arbitrary* function
`S.invFun : B → A` preserves local constancy.
-/

import Mathlib
import Submission.Work.ConCohomology.Setup

set_option linter.unusedVariables false

namespace Work.ConCohomology

open Function

/-- The set-theoretic section of the projection, followed by the locally constant cochain `c`, is
locally constant: a locally constant function remains locally constant after post-composition with
an arbitrary function. -/
lemma isLocallyConstant_sect_comp {G : Type*} [Group G] [TopologicalSpace G]
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    (S : CoeffSES G A B C) (c : Cochain1 G C) :
    IsLocallyConstant fun τ : G => S.sect (c τ) :=
  c.isLocallyConstant.comp S.sect

/-- The argument of the connecting cochain `S.delta1Fun c` is locally constant in the pair
`(σ, τ)`, for `B` a discrete `G`-module. -/
lemma isLocallyConstant_delta1Fun_arg {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    [IsDiscreteGModule G A] [IsDiscreteGModule G B] [IsDiscreteGModule G C]
    (S : CoeffSES G A B C) (c : Cochain1 G C) :
    IsLocallyConstant fun p : G × G =>
      p.1 • S.sect (c p.2) - S.sect (c (p.1 * p.2)) + S.sect (c p.1) := by
  have hb : IsLocallyConstant fun τ : G => S.sect (c τ) := isLocallyConstant_sect_comp S c
  have h1 : IsLocallyConstant fun p : G × G => p.1 • S.sect (c p.2) :=
    isLocallyConstant_smul_comp (φ := fun p : G × G => S.sect (c p.2))
      (hb.comp_continuous continuous_snd) continuous_fst
  have h2 : IsLocallyConstant fun p : G × G => S.sect (c (p.1 * p.2)) :=
    hb.comp_continuous (continuous_fst.mul continuous_snd)
  have h3 : IsLocallyConstant fun p : G × G => S.sect (c p.1) :=
    hb.comp_continuous continuous_fst
  exact (h1.sub h2).add h3

lemma isLocallyConstant_delta1Fun {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    [IsDiscreteGModule G A] [IsDiscreteGModule G B] [IsDiscreteGModule G C]
    (S : CoeffSES G A B C) (c : Cochain1 G C) :
    IsLocallyConstant (S.delta1Fun (c : G → C)) :=
  (isLocallyConstant_delta1Fun_arg S c).comp S.invFun

end Work.ConCohomology
