import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.RankOneUniqueness.qPt_surjective
import Submission.Work.RankOneUniqueness.qPt_injective

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.centralizer_le_H_of_mem_Q`

For a split rank-one group `IsSplitRankOne H Q t`, every non-trivial element `x` of the
unipotent radical `Q` has its centraliser in `G` contained in `H`.

The mechanism is the sharp transitivity of `Q` that is already available inside the
workspace: the points of `Ω = G ⧸ H` other than the base point `∞ = pt H` are exactly the
`qPt H t x = x·t·∞`, `x ∈ Q` (`RankOneUniqueness.qPt_surjective`), and this labelling is
injective (`RankOneUniqueness.qPt_injective`).  Hence a non-trivial `x ∈ Q` fixes `∞` and
nothing else: if `x` fixed `qPt H t q` then `qPt H t (x*q) = x • qPt H t q = qPt H t q`, so
`x*q = q` and `x = 1`.  An element `g` commuting with `x` therefore maps the fixed point
`∞` of `x` to another fixed point of `x`, i.e. `g • ∞ = ∞`, which is precisely `g ∈ H`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.Blueprint

namespace Work.ThmF.ChV3.Prove

theorem centralizer_le_H_of_mem_Q {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) :
    ∀ x ∈ Q, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ H := by
  intro x hxQ hxne g hg
  -- `g` commutes with `x`
  have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  -- `x` fixes the base point `∞ = pt H`
  have hxpt : x • Work.RankOneUniqueness.pt H = Work.RankOneUniqueness.pt H :=
    Work.RankOneUniqueness.smul_pt_of_mem H (h.le hxQ)
  -- consequently `x` fixes `g • ∞` as well
  have hfix : x • (g • Work.RankOneUniqueness.pt H) = g • Work.RankOneUniqueness.pt H := by
    rw [← mul_smul, ← hgx, mul_smul, hxpt]
  -- the action of a group element on the `Q`-labelling
  have hsmul : ∀ a b : G,
      a • Work.RankOneUniqueness.qPt H t b = Work.RankOneUniqueness.qPt H t (a * b) := by
    intro a b
    rw [Work.RankOneUniqueness.qPt_def, Work.RankOneUniqueness.smul_mk,
        Work.RankOneUniqueness.qPt_def, mul_assoc]
  -- `∞` is the only point fixed by `x`
  have hfixpt : g • Work.RankOneUniqueness.pt H = Work.RankOneUniqueness.pt H := by
    by_contra hne
    obtain ⟨q, hqQ, hqω⟩ := Work.RankOneUniqueness.qPt_surjective h hne
    have heq : Work.RankOneUniqueness.qPt H t (x * q) = Work.RankOneUniqueness.qPt H t q := by
      rw [← hsmul x q, hqω, hfix]
    have hxqq : x * q = q :=
      Work.RankOneUniqueness.qPt_injective h (Q.mul_mem hxQ hqQ) hqQ heq
    exact hxne (mul_right_cancel (hxqq.trans (one_mul q).symm))
  exact (Work.RankOneUniqueness.smul_pt_iff H g).mp hfixpt

end Work.ThmF.ChV3.Prove
