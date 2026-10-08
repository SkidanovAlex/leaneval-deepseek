import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.Tools.External

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Ctx` — the standing context of Peterfalvi II Ch. V §3 (Théorème F)

Moved (probe 04:45, 10-04) from the lead's design file `ThmF/_design/chV3_steps.lean`, where the
steps (1)–(17) are stated as `CtxF … → …`.  Step files of `ChV3/` import this module and state
their theorems in `namespace Work.ThmF.ChV3`.

(F2) is not a field: `G` is simple, so a normal subgroup of index `p` is absurd
(`Tools/hasNormalIndexP_iff` + `simple`).  (B1) enters only through `sit.2.1`; §2 Lemma 5 needs
none (see `ThmF/_design/lemma5_probe0445.lean`).
-/

set_option autoImplicit false
noncomputable section
open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.ThmF.ChV3

open Work.ThmF

variable {G : Type} [Group G] [Finite G]

/-- The standing context of §3: (B0)–(B2), `G` simple, the split rank-one datum, the structure
identity `t s t = r⁻¹ t r` (Ch. V §2 Lemma 1 b, `structureIdentity`), and (F1) for `P ≤ V` of
prime order. -/
structure CtxF (H Q : Subgroup G) (t s r : G) (P : Subgroup G) : Prop where
  sit : Situation G
  simple : IsSimpleGroup G
  split : IsSplitRankOne H Q t
  s_mem : s ∈ Q
  s_inv : orderOf s = 2
  r_mem : r ∈ Q
  sid : t * s * t = r⁻¹ * t * r
  P_le : P ≤ centD H t
  P_prime : (Nat.card P).Prime
  F1 : ¬ HasFourGroup ↥(Subgroup.centralizer (P : Set G))

/-- `C_Q(P)`. -/
abbrev CQ (Q P : Subgroup G) : Subgroup G := Q ⊓ Subgroup.centralizer (P : Set G)

/-- `Σ = C_W(P)`. -/
abbrev Sig (H : Subgroup G) (t : G) (P : Subgroup G) : Subgroup G :=
  W H t ⊓ Subgroup.centralizer (P : Set G)

/-- `p`-part of `n`. -/
def pPart (p n : ℕ) : ℕ := p ^ n.factorization p

end Work.ThmF.ChV3
