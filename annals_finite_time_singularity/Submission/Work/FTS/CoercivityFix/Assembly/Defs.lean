/-
# `Assembly/Defs.lean` — the level package of the corrected induction

The corrected coercivity of `𝓛_Γ^T` on the one-condition class `CoerAdm` is proved by
running the paper's induction for the **clean operator** `Lhat = 𝓛 − Transport` and
transferring the result to `𝓛_Γ^T = Lhat + Corr` at the end.  This file fixes the two
notions the induction is phrased in.

## The level package `CoerData2`

The delivered step (`Submission/Work/FTS/CoercivityFix/StepCoer/step_coer.lean`) states its
level-`n` data on the class `RegQ α n`, which is one level *too low*: the pairing
`IP (Lhat f) f` that the coercivity clause is about pairs the *slots of `Lhat f`*, and
`Lhat` raises the slot depth by one, so the honest hypothesis on the slots is
`RegQ α (n+1)`.  With the class raised by one the induction climbs **one** level per step
(`RegQ α 2 → 3 → 4 → 5`), and `CoerAdm α f ⟹ RegQ α 5 f` closes it at level 4.
(`NOTES.md` §6 records the obstruction the naive formulation creates.)

`CoerData2 α n IP cc CC` carries the two clauses of the level-`n` data:

* `cs` — Cauchy–Schwarz against the honest `ℋⁿ`-norm, on `RegQ α n` (the level at which it
  is *consumed*: the defect `Ê₂ f`, which is at level `n` when `f` is at level `n+1`, is
  bounded by `cs` at level `n`);
* `coer` — coercivity of `Lhat` at level `n`, on `RegQ α (n+1)`.

The comparability clauses (`lo`, `up`) are *not* part of the package: the induction does not
use them, and they are proved directly for the concrete inner product at the end.

## The concrete inner product

`IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α` is the paper's recursion
`HkIPStep c₁ c₂ (HkIPStep c₁' c₂' (HkIPStep c₁'' c₂'' (H1IP α)))` (tex 686), i.e. the
inner product of `ℋ⁴` with the *small* step coefficients of the paper (design
`N45_DESIGN_LEAD.md` §5 T3): the coefficients are chosen at each level so that the
`Ê₂`-defect is absorbable (`StepSmall`), which is satisfiable for every positive coercivity
constant (`Step.exists_small_step_coeffs`).
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.CoercivityFix.Step
import Submission.Work.Coercivity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (RegQ)

set_option autoImplicit false

/-! ## The level package -/

/-- **The level-`n` data of the corrected induction.**  `cs` is the Cauchy–Schwarz bound
consumed at level `n`; `coer` is the coercivity of the clean operator `Lhat` at level `n`,
stated on `RegQ α (n+1)` because the pairing `IP (Lhat f) f` sees the slots of `Lhat f`,
one order deeper than those of `f`. -/
structure CoerData2 (α : ℝ) (n : ℕ) (IP : Fn → Fn → ℝ) (cc CC : ℝ) : Prop where
  /-- the coercivity constant is positive -/
  hcc : 0 < cc
  /-- the Cauchy–Schwarz constant is positive -/
  hCC : 0 < CC
  /-- Cauchy–Schwarz against the honest `ℋⁿ`-norm, on the level-`n` class -/
  cs : ∀ f g : Fn, RegQ α n f → RegQ α n g →
    |IP f g| ≤ CC * Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g
  /-- coercivity of `Lhat` at level `n` -/
  coer : ∀ f : Fn, RegQ α (n + 1) f →
    cc * Work.Spaces.HkSq α n f ≤ IP (Work.FTS.CoercivityFix.Lhat f) f

/-- **The regularity ports the step needs.**  Every field says how `RegQ`-membership
descends when a derivative is taken, or that a slot of the operator/defect is at level `n`
when the argument is at level `n+1` or `n+2`; the last field records the one-sided
comparison of the `ℋⁿ`-norm with the `ℋ^{n+1}`-norm. -/
structure StepReg2 (α : ℝ) (n : ℕ) : Prop where
  /-- `RegQ α (n+2) f → RegQ α n f` -/
  mono1 : ∀ f : Fn, RegQ α (n + 2) f → RegQ α n f
  /-- `RegQ α (n+2) f → RegQ α (n+1) f` -/
  mono2 : ∀ f : Fn, RegQ α (n + 2) f → RegQ α (n + 1) f
  /-- `D_θ` drops the level by one -/
  dth1 : ∀ f : Fn, RegQ α (n + 2) f → RegQ α (n + 1) (Work.Spaces.Dth f)
  /-- `D_z` drops the level by one -/
  dz1 : ∀ f : Fn, RegQ α (n + 2) f → RegQ α (n + 1) (Work.Spaces.Dz f)
  /-- `D_θ` drops the level by two -/
  dth2 : ∀ f : Fn, RegQ α (n + 2) f → RegQ α n (Work.Spaces.Dth f)
  /-- `D_z` drops the level by two -/
  dz2 : ∀ f : Fn, RegQ α (n + 2) f → RegQ α n (Work.Spaces.Dz f)
  /-- `Lhat (D_z f)` is at level `n` when `f` is at level `n+2` -/
  ldz : ∀ f : Fn, RegQ α (n + 2) f →
    RegQ α n (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f))
  /-- the defect `Ê₂ f` is at level `n` when `f` is at level `n+1` -/
  e2r : ∀ f : Fn, RegQ α (n + 1) f → RegQ α n (Work.FTS.CoercivityFix.E2hat f)
  /-- one-sided comparison of the `ℋⁿ`-norms of the three slots with `|f|_{n+1}` -/
  normSub : ∀ f : Fn, RegQ α (n + 2) f →
    Work.Spaces.HkSq α n f ≤ Work.Spaces.HkSq α (n + 1) f
      ∧ Work.Spaces.HkSq α n (Work.Spaces.Dth f) ≤ Work.Spaces.HkSq α (n + 1) f
      ∧ Work.Spaces.HkSq α n (Work.Spaces.Dz f) ≤ Work.Spaces.HkSq α (n + 1) f

/-- **The algebraic inputs of the step, membership-free for the congruence.**  The
congruence of the concrete inner product in its *first* argument on the open quadrant needs
**no** regularity hypothesis (derivatives are local and the quadrant is co-null: see
`StepAssembly/H1IP_congr_qd`), and the two commutator identities are pointwise statements
on the open quadrant. -/
structure Comm2 (α : ℝ) (n : ℕ) (IP : Fn → Fn → ℝ) : Prop where
  /-- congruence in the first argument on the open quadrant, with no membership -/
  congr : ∀ f f' g : Fn,
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) → IP f g = IP f' g
  /-- additivity in the first argument, on the level-`n` class -/
  add : ∀ f₁ f₂ g : Fn, RegQ α n f₁ → RegQ α n f₂ → RegQ α n g →
    IP (f₁ + f₂) g = IP f₁ g + IP f₂ g
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

/-! ## The concrete inner product of `ℋ⁴` -/

/-- **The paper's recursion with explicit step coefficients**: `IP4` in the vocabulary of
`Submission/Work/FTS/CoercivityStep` is `HkIPStep 1 1 (HkIPStep 1 1 (HkIPStep 1 1 (H1IP α)))`;
here the three coefficient pairs are *free*, because the corrected step absorbs the defect
by taking them small (`StepSmall`) instead of by a balance hypothesis on the constants. -/
def IP4 (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) (α : ℝ) : Fn → Fn → ℝ :=
  Work.Coercivity.HkIPStep c₁'' c₂''
    (Work.Coercivity.HkIPStep c₁' c₂' (Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α)))

/-- The recursion with the coefficients of the *first* step only (the level-`2` inner
product attached to the level-`1` base). -/
def IP2 (c₁ c₂ : ℝ) (α : ℝ) : Fn → Fn → ℝ :=
  Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α)

/-- The recursion iterated twice (the level-`3` inner product). -/
def IP3 (c₁ c₂ c₁' c₂' : ℝ) (α : ℝ) : Fn → Fn → ℝ :=
  Work.Coercivity.HkIPStep c₁' c₂' (IP2 c₁ c₂ α)

theorem IP4_eq (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) (α : ℝ) :
    IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
      = Work.Coercivity.HkIPStep c₁'' c₂'' (IP3 c₁ c₂ c₁' c₂' α) := rfl

theorem IP3_eq (c₁ c₂ c₁' c₂' : ℝ) (α : ℝ) :
    IP3 c₁ c₂ c₁' c₂' α = Work.Coercivity.HkIPStep c₁' c₂' (IP2 c₁ c₂ α) := rfl

theorem IP2_eq (c₁ c₂ : ℝ) (α : ℝ) :
    IP2 c₁ c₂ α = Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α) := rfl

end Work.FTS.CoercivityFix.Assembly
