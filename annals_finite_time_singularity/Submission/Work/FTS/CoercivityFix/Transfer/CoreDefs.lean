/-
# `Transfer/CoreDefs.lean` — the objects of the corrected transfer induction

The transfer `𝓛_Γ^T = 𝓛̂ + Corr` is proved coercive by running the paper's induction for the
*clean* operator and splitting the two defects `E1`, `E2` off at every level.  The algebraic
input of that splitting is *additivity of the pairing* on the sums
`𝓛̂(D_θf) + E1 α f`, `𝓛̂(D_zf) + E2 α f`, and Cauchy–Schwarz on the two error pairings.

The delivered version of those inputs (`Assembly.Comm2w`, `Assembly.AddOK`) asked for
`HkMem` and `BlocksCont`/`BlocksAdd`.  For the *transfer* this is unprovable: climbing the
recursion requires the two derivatives `D_θ`, `D_z` to be additive *at the next level down*,
and the block package alone does not give that (`D_z` additivity is a statement about
`deriv`, not about continuity).  This module replaces the block hypotheses by the finite-order
smooth class `Q0Sm` of `Transfer/Q0Sm.lean`, for which

* additivity of `D_θ`/`D_z` on the open quadrant is `Q0Sm.dth_add` / `Q0Sm.dz_add`,
* every hypothesis descends one level under `D_θ`, `D_z` (`Q0Sm.dth`, `Q0Sm.dz` and the
  `ℋ^k`-membership descent),

so that the recursion of the pairing is again provable — which is what makes the transfer
induction well founded.

* `CommSm α n IP` — the four algebraic clauses of the level-`n` pairing (congruence on `Qd`,
  additivity on `AddOKSm`, and the two commutator identities of `𝓛̂`).
* `AddOKSm α n f₁ f₂ g` — the hypotheses of `CommSm.add`: `C^n` on the open quadrant and
  `ℋⁿ`-membership of the three arguments.
* `CSQ α n IP CC` — Cauchy–Schwarz at level `n` for `C^n`, `ℋⁿ` arguments.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.CoercivityFix.Transfer.Q0Sm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The hypotheses of one additivity step of the transfer.**  The three arguments are
`C^n` on the open quadrant and lie in `ℋⁿ`; the smoothness is what makes `D_θ`/`D_z`
additive, the membership is what makes the `wip`-splittings legitimate. -/
def AddOKSm (α : ℝ) (n : ℕ) (f₁ f₂ g : Fn) : Prop :=
  Q0Sm n f₁ ∧ Q0Sm n f₂ ∧ Q0Sm n g ∧
    Work.Spaces.HkMem α n f₁ ∧ Work.Spaces.HkMem α n f₂ ∧ Work.Spaces.HkMem α n g

/-- **The algebraic inputs of the transfer at level `n`.**  The congruence needs no
regularity (the derivative is local and the quadrant is co-null); additivity needs
`AddOKSm`; the two commutator identities of `𝓛̂` are pointwise statements on `Qd` for a
`SmoothQuad` datum. -/
structure CommSm (α : ℝ) (n : ℕ) (IP : Fn → Fn → ℝ) : Prop where
  /-- congruence in the first argument on the open quadrant, with no membership -/
  congr : ∀ f f' g : Fn,
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) → IP f g = IP f' g
  /-- additivity in the first argument, from `C^n`-smoothness and `ℋⁿ`-membership -/
  add : ∀ f₁ f₂ g : Fn, AddOKSm α n f₁ f₂ g → IP (f₁ + f₂) g = IP f₁ g + IP f₂ g
  /-- `D_θ` commutes with `Lhat` exactly -/
  dthC : ∀ f : Fn, Work.FTS.LocData.SmoothQuad f → ∀ z θ : ℝ,
    (z, θ) ∈ Work.Construction.Qd →
    Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f) z θ
  /-- the `D_z` commutator of `Lhat` is the explicit defect `Ê₂` -/
  dzC : ∀ f : Fn, Work.FTS.LocData.SmoothQuad f → ∀ z θ : ℝ,
    (z, θ) ∈ Work.Construction.Qd →
    Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
        + Work.FTS.CoercivityFix.E2hat f z θ

/-- **Cauchy–Schwarz at level `n`** for `C^n` arguments in `ℋⁿ`.  This is the form in which
the two error pairings `IP (E1 α f) (D_θf)` and `IP (E2 α f) (D_zf)` are consumed: the two
defects are `C³` on the open quadrant (`Transfer/E1Parts/ContE1.lean`, `Transfer/E2_blocks.lean`)
and lie in `ℋⁿ` for `n ≤ 3`, but they are *not* `RegQ`, so the delivered `RegQ`-based
Cauchy–Schwarz bound does not apply. -/
def CSQ (α : ℝ) (n : ℕ) (IP : Fn → Fn → ℝ) (CC : ℝ) : Prop :=
  ∀ X Y : Fn, Q0Sm n X → Q0Sm n Y → Work.Spaces.HkMem α n X → Work.Spaces.HkMem α n Y →
    |IP X Y| ≤ CC * Work.Spaces.HkNorm α n X * Work.Spaces.HkNorm α n Y

end Work.FTS.CoercivityFix.Transfer
