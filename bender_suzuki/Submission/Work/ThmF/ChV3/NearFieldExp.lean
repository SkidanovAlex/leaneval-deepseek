import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.NearField
import Submission.Work.ThmF.ChV3.AppXI

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.NearFieldExpProp` — App. XI Prop. 1, with its additive-group clause

App. XI Prop. 1 (the input of Ch. V §3 step (2), `ChV3/NearField.lean`) attaches to the standing
context a near-field `F` of order `f^m = |C_Q(P)| + 1` whose additive group is the quotient of the
subgroup `R = h15.R` by `N = Ker H Q P t = P`.  A finite near-field of characteristic `p` has
*elementary abelian* additive group (`(F,+)` is a vector space over its prime field `𝔽_p`) — this is
the abstract fact proved, sorry-free, as `Work.ThmF.ChV3.Prove.nearFieldExp` — and the preimage `R`
of `F` is the direct product `F⁺ × P` (the source's `T ≅ F⁺` inside step (11)).  Hence

`x ^ p = 1` for every `x ∈ R`, i.e. `R` is elementary abelian of order `p^{m+1}`.

Step (11) needs exactly this: the abelian `R` with `|R| = p^{m+1}` becomes elementary abelian of
rank `m + 1`, so that it has a complement `T` to `P` **and** exactly `p^m` subgroups of order `p`
outside `T` (the point count behind the sharp transitivity clause of `Step11Out.reg`).  `R`
abelian of order `p^{m+1}` alone would admit `ℤ/p² × (ℤ/p)^{m-1}` with `P` the order-`p` subgroup
of the `ℤ/p²` factor, which satisfies every clause of the *shadow* `NearFieldAppXIProp` (it has no
complement `T` at all).

`NearFieldFullAppXIProp` packages the two App. XI inputs the chain consumes — the shadow
`NearFieldAppXIProp` and the additive-group clause `NearFieldExpProp` — and *is* the single App. XI
input of the §3 assembly (`ChV3/Step16Plumbing.lean`'s `ChV3Prop16`).  It is stated separately from
`NearFieldAppXIProp` (rather than added to it) because `NearFieldAppXIProp` is destructured at a
fixed arity by `Submission/Work/S3/cq_ell_subgroup_isCyclic.lean`, a file of the neighbouring area
that must not be edited.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.ThmF.ChV3

/-- The additive group of the App. XI near-field is elementary abelian: `R` has exponent `p`. -/
def NearFieldExpProp : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (c : CtxF H Q t s r P) (h15 : Chain15 H Q t s r P) (hpf : Nat.card P = orderOf (s * t)),
    ∀ x ∈ h15.R, x ^ Nat.card P = 1

/-- **App. XI Prop. 1, complete form**: the near-field shadow of step (2) together with the
additive-group (splitting) clause needed by step (11). -/
def NearFieldFullAppXIProp : Prop := NearFieldAppXIProp ∧ NearFieldExpProp

/-- The shadow is the first component of the complete App. XI input. -/
theorem NearFieldFullAppXIProp.toShadow (h : NearFieldFullAppXIProp) : NearFieldAppXIProp := h.1

/-- The additive-group clause is the second component of the complete App. XI input. -/
theorem NearFieldFullAppXIProp.toExp (h : NearFieldFullAppXIProp) : NearFieldExpProp := h.2

end Work.ThmF.ChV3
