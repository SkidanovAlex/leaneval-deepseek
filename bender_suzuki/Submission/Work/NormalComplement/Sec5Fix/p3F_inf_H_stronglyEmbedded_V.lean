/-
# `Work.NormalComplement.Sec5Fix.p3F_inf_H_stronglyEmbedded_V`

Peterfalvi I Ch. II §4 **Prop. 1 (b)** applied at the two-point stabiliser itself:

with `H` strongly embedded, `t ∉ H` an involution, `D = H ⊓ H^t`, `V = C_D(t) = centD H t`
and `F = O^{2'}(C_G(V)) = p3F V`, the subgroup `F ⊓ H` is strongly embedded in `F`.

This is the specialisation `X = V`, `g = 1`, `M = H` of the clause (b) of `ChIIFourProp`
(`Submission.Blueprint.ChIIFourProp`); it is used in Ch. III §5 to run Appendix III on the
action of `F` on `Ω_V = fixedPts H V` (the kernel of that action being `Zact H t`, see
`Sec5Fix/Defs.lean`).

The three side conditions of Prop. 1 (b) are, in this situation:

* `3 ≤ |fixedPts H V|` (Ch. II §4 Prop. 2 (`a`)): `Work.ThreePoints.three_le_fixedPts_of_le_centD`
  at `X = V` (i.e. `le_rfl`);
* `Inv C_G(V) ⊆ F`: `Work.ThreePoints.involutions_le_p3F`;
* `F ≤ N_G(V)`: `Work.ThreePoints.p3cd_p3F_le_normalizer`.

Together with `V ≤ H = conj 1 H` this yields the conclusion, exactly as in the `X = A` variant
`Work.NormalComplement.p3F_inf_stronglyEmbedded`.
-/
import Mathlib
import Submission.Work.NormalComplement.Sec5Fix.Prelim
import Submission.Work.NormalComplement.Design.Extra

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/- The statement requested of this lemma spells the notion of strong embeddedness as
`LeanEval.GroupTheoryDefsPlaceholder.IsStronglyEmbedded`, a name that does not occur anywhere in
this workspace.  We introduce it here as an *abbreviation* of the real
`LeanEval.GroupTheory.Defs.IsStronglyEmbedded` (`ChallengeDeps.lean`), so that the requested
statement elaborates literally as written and is *definitionally* the intended one: the
abbreviation is reducible, hence interchangeable with the real notion in both directions. -/
namespace LeanEval
namespace GroupTheoryDefsPlaceholder

/-- `M` is strongly embedded in `X` — see the note above: an alias for
`LeanEval.GroupTheory.Defs.IsStronglyEmbedded`, kept so that the statement of
`Work.NormalComplement.Sec5Fix.p3F_inf_H_stronglyEmbedded_V` can be spelled exactly as requested.
-/
abbrev IsStronglyEmbedded {X : Type*} [Group X] (M : Subgroup X) : Prop :=
  LeanEval.GroupTheory.Defs.IsStronglyEmbedded M

end GroupTheoryDefsPlaceholder
end LeanEval

namespace Work.NormalComplement.Sec5Fix

open Submission.Blueprint
open LeanEval.GroupTheory.Defs

theorem p3F_inf_H_stronglyEmbedded_V (hC4 : Submission.Blueprint.ChIIFourProp) {G : Type}
    [Group G] [Finite G] {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G}
    {r : ℕ} (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) :
    LeanEval.GroupTheoryDefsPlaceholder.IsStronglyEmbedded
      ((Work.ThreePoints.p3F (Submission.Blueprint.centD H t) ⊓ H).subgroupOf
        (Work.ThreePoints.p3F (Submission.Blueprint.centD H t))) := by
  -- `V = C_D(t)` fixes at least three points of `Ω = G ⧸ H` (Ch. II §4 Prop. 2)
  have h3 : 3 ≤ (Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t)).ncard :=
    Work.ThreePoints.three_le_fixedPts_of_le_centD h.se h.invol h.notMem le_rfl
  -- `Inv C_G(V) ⊆ F = O^{2'}(C_G(V))`
  have hinv : Submission.Blueprint.involutions
      (Subgroup.centralizer (Submission.Blueprint.centD H t : Set G) : Set G) ⊆
      Work.ThreePoints.p3F (Submission.Blueprint.centD H t) :=
    Work.ThreePoints.involutions_le_p3F _
  -- `F ≤ N_G(V)`
  have hnorm : Work.ThreePoints.p3F (Submission.Blueprint.centD H t) ≤
      Subgroup.normalizer (Submission.Blueprint.centD H t : Set G) :=
    Work.ThreePoints.p3cd_p3F_le_normalizer _
  -- `V ≤ H = conj 1 H`: `H` is a fixed point of `V`
  have hVH : Submission.Blueprint.centD H t ≤ H := le_trans inf_le_left inf_le_left
  -- Ch. II §4 Prop. 1 (b) at `X = V`, `F = p3F V`, `g = 1`
  have hres := (hC4 G h.sit H h.se t h.invol h.notMem).1
    (Submission.Blueprint.centD H t) (Work.ThreePoints.p3F (Submission.Blueprint.centD H t))
    h3 hinv hnorm 1 (by simpa using hVH)
  simpa using hres

end Work.NormalComplement.Sec5Fix
