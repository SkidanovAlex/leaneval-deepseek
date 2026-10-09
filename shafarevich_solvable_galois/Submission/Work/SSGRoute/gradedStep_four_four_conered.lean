import Mathlib
import Submission.Work.SSGRoute.gradedStep_three_three
import Submission.Work.SSGRoute.CC.DiagonalFourPort
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `(4,4)` diagonal graded step in a clash-free import cone

This module proves `Work.SSGRoute.gradedStep_four_four_conered`: the `(4,4)` diagonal instance of
Schmidt–Wingberg's graded step at `p = 2`, for an arbitrary finite group `G` and an involution
`δ ∈ G`, `δ ≠ 1`:

> every anti-fixed element `c` of the kernel `E(4,4) = ker(Q_{(5,1)} → Q_{(4,4)})` of the free
> `G`-operator group `F(n) = FreeGroup (Fin n × G)` is a `δ`-difference in the ambient quotient
> `Q_{(5,1)} = F(n)/F(n)^{(5,1)}`.

## Proof

The mathematics is the existing `(4,4)` computation: `Work.SSGRoute.CC.LNS3B.diagonal_four_general`,
a verbatim copy (in `Submission/Work/SSGRoute/CC/`) of `Work.SSGRoute.diagonal_four_general`
(`Submission/Work/SSGRoute/gradedStep_diagonal_zmodTwo_four.lean`), which is itself uniform in the
finite group.  It is stated for `G : Type 0`, so to obtain the universe-polymorphic statement here
we transport across an equivariant bijection of the free bases

  `(Fin n × G, (i,g) ↦ (i, δ*g))  ≃  (Fin d × ℤ/2, sheet swap)`,

exactly as in the `(3,3)` case (`gradedStep_three_three.lean`): `flowStep_iff_honestStep` identifies
the flow-quotient formulation with the honest-quotient one, `HonestStep_transport` moves the model
statement `LNS3B.diagonal_four_general` across the basis identification supplied by
`exists_equiv_fin_mul_zmodTwo`, and `flowStep_iff_honestStep` converts back.

## The clash-free cone

The existing proof lives behind `Submission.Work.SSGRoute.bf4_defs`, whose declaration
`Work.SSGRoute.V` collides with `Work.SSGRoute.V` of `Submission.Work.SSGRoute.TwoTwoStep`; the
caller of this module (`two_torsion_lift_two.lean`) necessarily has `TwoTwoStep` in its cone (via
`gradedStep_three_three → gradedStep_diagonal → TwoTwoAssembly`), and `two_torsion_lift_two` must
avoid `bf4_defs` (and `prop5.magnus_leadingTerm`).  The `CC` port copies exactly the modules of the
`(4,4)` proof that transitively import `bf4_defs` (`flg_fin4`, `flg_four_letters`,
`flg_four_letters_local`, `freeLieFourFixedGeneration`, the `mag4`/`magFour` cluster,
`flgThetaDefs`, and the `LNS3` realisation ports), redirecting their imports onto clean copies,
and replaces `bf4_defs` by the harmless subset `CC.Bf4Defs` (which drops the clashing `V`).  The
one further collision of the Magnus chain with `TwoTwoStep`, the helper `powSubgroup_mono`, is
renamed in the copy.  Consequently the import cone of the present module can be combined with
`gradedStep_three_three` (i.e. with `TwoTwoStep`) and with the rest of the `two_torsion_lift_two`
spine.
-/

namespace Work.SSGRoute
open Work.SSGRoute.CC

theorem gradedStep_four_four_conered (G : Type*) [Group G] [Fintype G] (n : ℕ) (δ : G)
    (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) :
    ∀ c : Work.CohomologicalShrinking.flowQuotient 2 G n
        (Work.CohomologicalShrinking.tauSucc 4 4).1
        (Work.CohomologicalShrinking.tauSucc 4 4).2,
      Work.SSGRoute.flowQuotSucc 2 G n 4 4 c = 1 →
      Work.CohomologicalShrinking.flowAction 2 G n
          (Work.CohomologicalShrinking.tauSucc 4 4).1
          (Work.CohomologicalShrinking.tauSucc 4 4).2 δ c = c⁻¹ →
      ∃ e : Work.CohomologicalShrinking.flowQuotient 2 G n
            (Work.CohomologicalShrinking.tauSucc 4 4).1
            (Work.CohomologicalShrinking.tauSucc 4 4).2,
        c = (Work.CohomologicalShrinking.flowAction 2 G n
              (Work.CohomologicalShrinking.tauSucc 4 4).1
              (Work.CohomologicalShrinking.tauSucc 4 4).2 δ e)⁻¹ * e := by
  classical
  set σ : Fin n × G ≃ Fin n × G := Work.Shrinking.freeOperatorGenPerm (G := G) n δ with hσdef
  have hσinv : ∀ x : Fin n × G, σ (σ x) = x := basisPerm_involutive G n δ hδ
  have hσfree : ∀ x : Fin n × G, σ x ≠ x := basisPerm_ne_self G n δ hδ1
  obtain ⟨d, e, he⟩ := Work.SSGRoute.exists_equiv_fin_mul_zmodTwo σ hσinv hσfree
  set τ : Fin d × Multiplicative (ZMod 2) ≃ Fin d × Multiplicative (ZMod 2) :=
    Work.Shrinking.freeOperatorGenPerm (G := Multiplicative (ZMod 2)) d
      (Multiplicative.ofAdd 1) with hτdef
  have hmodel : HonestStep (Fin d × Multiplicative (ZMod 2)) τ 4 4 :=
    (flowStep_iff_honestStep (Multiplicative (ZMod 2)) d 4 4 (Multiplicative.ofAdd 1)).mp
      (LNS3B.diagonal_four_general (Multiplicative (ZMod 2)) (Multiplicative.ofAdd 1)
        (by decide) (by decide) d)
  have hgen : HonestStep (Fin n × G) σ 4 4 :=
    HonestStep_transport e σ τ he 4 4 hmodel
  exact (flowStep_iff_honestStep G n 4 4 δ).mpr hgen

end Work.SSGRoute
