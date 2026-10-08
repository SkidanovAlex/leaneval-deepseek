/-
Copyright (c) 2024. All rights reserved.

# The type-`B` characterisation (module form)

Peterfalvi II p. 239: a Suzuki 2-group `P` of order `q³` is **of type `B`** iff `P / Z(P)` is
the direct sum of two isomorphic `𝔽₂[K]`-modules of order `q` (`K = ⟨ξ⟩`).  This is what the
consumers use:

* ThmF, Ch. V §2 Lemma 6 (`P. II` pp. 240–256),
* PSU3, Ch. VI §1 case c) and App. VIII.

They never use Higman's cocycle `bCocycle` for type `B`, so type `B` is defined here
*module-theoretically*, and no link with the first disjunct of `HigmanQ3Prop` is required.

The isomorphism `P/Z ≅ M ⊕ M` is recorded through its combinatorial shadow, which avoids
quotient types: the number of `ξ`-invariant "layers" `Z(P) ≤ M` with `|M| = q²` is `q + 1`
(it is exactly `2` otherwise).

See `NOTES_LEAD_probe1630.md`; the design statements are in `_design/typeB.lean`.

App. V (`appV_regular`, `appV_semilinear`, and its irreducible form) is needed for
`layers_card_dichotomy` and `typeB_scalar`; it is being formalised by the ThmF area
(`Submission/Work/ThmF/_design/prop3_appV.lean`, `REFS/peterfalvi_I_app5_9.md` App. V p. 211)
and is **not** to be proved twice here.
-/

import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-- `M` is a `ξ`-invariant layer: a subgroup with `Z(P) ≤ M`, invariant under `ξ`, of order
`q²` (`q = |Z(P)|`).  These are the `n`-dimensional `⟨ξ⟩`-submodules of `P / Z(P)` when
`|P| = q³`. -/
def IsXiLayer (ξ : MulAut P) (M : Subgroup P) : Prop :=
  Subgroup.center P ≤ M ∧ (∀ x ∈ M, ξ x ∈ M) ∧
    Nat.card M = Nat.card ↥(Subgroup.center P) ^ 2

/-- **Type `B` (module form).**  `P / Z(P) ≅ M ⊕ M` as `⟨ξ⟩`-modules, recorded through its
combinatorial shadow: there are `q + 1` invariant layers (there are exactly `2` otherwise). -/
def IsTypeB (ξ : MulAut P) : Prop :=
  Nat.card ↥(Subgroup.center P) + 1 ≤ Nat.card {M : Subgroup P // IsXiLayer ξ M}

/-- Standing hypothesis of the dichotomy: `P` is Suzuki of order `q³` and `ξ` has order `q - 1`
with `⟨ξ⟩` acting semiregularly on `P \ {1}` — the `K`-action of the consumers.

The fixed-point-freeness is required for **all** non-trivial powers of `ξ` (at the consumers:
Peterfalvi II Ch. V §1 Prop. 1 a), `C_Q(x) = 1` for `x ∈ K^#`): with only `ξ` itself
fixed-point-free a constituent could carry an eigenvalue of order dividing `q - 1`, of
dimension `< n`, and the dichotomy would fail. -/
structure FpfXi (ξ : MulAut P) : Prop where
  /-- `|P| = q³`. -/
  card_cube : Nat.card P = Nat.card ↥(Subgroup.center P) ^ 3
  /-- `ξ` has order `q - 1`. -/
  order : orderOf ξ = Nat.card ↥(Subgroup.center P) - 1
  /-- every non-trivial power of `ξ` is fixed-point-free. -/
  fpf : ∀ k : ℕ, ξ ^ k ≠ 1 → ∀ x : P, (ξ ^ k) x = x → x = 1

end Work.Higman
