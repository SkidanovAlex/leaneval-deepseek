/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/StepDataO.lean` — the open-class data of the coercivity
induction

The coercivity chapter's induction runs on the three structures of
`CoercivityFix/Assembly/Defs.lean`: `CoerData2` (the level-`n` coercivity and Cauchy–Schwarz
data), `StepReg2` (the regularity ports and the one-sided norm comparisons) and `Comm2` (the
algebraic inputs of the step).  All three are stated with the frozen class
`Work.FTS.Nonlin.RegQ`.

This file fixes their open-class analogues (`CoerData2O`, `StepReg2O`, `Comm2O`) — the same field
lists with `RegQo` (and `SmoothOpen` for the `dthC`/`dzC` commutator fields) in place of
`RegQ`/`SmoothQuad` — together with `CoerDataTO`, the open-class analogue of the *transfer*
induction's data `Transfer.CoerDataT` (`cs` on `RegQo`, `coer` on `CoerAdmO`).  They are the
vocabulary in which the open-class re-run of the coercivity chapter is phrased: the induction steps
are `StepCoerO.step_coer_O` (for `CoerData2O`) and the port of `Transfer/L4Main` (for `CoerDataTO`).

Everything here is `sorry`-free (the module only *defines* structures).
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.CoercivityFix.Assembly.Defs
import Submission.Work.FTS.CoercivityFix.Transfer.CoerDataT
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongPersist.IP6_lo_coeffs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The level-`n` data of the corrected induction.**  `cs` is the Cauchy–Schwarz bound
consumed at level `n`; `coer` is the coercivity of the clean operator `Lhat` at level `n`,
stated on `RegQo α (n+1)` because the pairing `IP (Lhat f) f` sees the slots of `Lhat f`,
one order deeper than those of `f`. -/
structure CoerData2O (α : ℝ) (n : ℕ) (IP : Fn → Fn → ℝ) (cc CC : ℝ) : Prop where
  /-- the coercivity constant is positive -/
  hcc : 0 < cc
  /-- the Cauchy–Schwarz constant is positive -/
  hCC : 0 < CC
  /-- Cauchy–Schwarz against the honest `ℋⁿ`-norm, on the level-`n` class -/
  cs : ∀ f g : Fn, RegQo α n f → RegQo α n g →
    |IP f g| ≤ CC * Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g
  /-- coercivity of `Lhat` at level `n` -/
  coer : ∀ f : Fn, RegQo α (n + 1) f →
    cc * Work.Spaces.HkSq α n f ≤ IP (Work.FTS.CoercivityFix.Lhat f) f

/-- **The regularity ports the step needs.**  Every field says how `RegQo`-membership
descends when a derivative is taken, or that a slot of the operator/defect is at level `n`
when the argument is at level `n+1` or `n+2`; the last field records the one-sided
comparison of the `ℋⁿ`-norm with the `ℋ^{n+1}`-norm. -/
structure StepReg2O (α : ℝ) (n : ℕ) : Prop where
  /-- `RegQo α (n+2) f → RegQo α n f` -/
  mono1 : ∀ f : Fn, RegQo α (n + 2) f → RegQo α n f
  /-- `RegQo α (n+2) f → RegQo α (n+1) f` -/
  mono2 : ∀ f : Fn, RegQo α (n + 2) f → RegQo α (n + 1) f
  /-- `D_θ` drops the level by one -/
  dth1 : ∀ f : Fn, RegQo α (n + 2) f → RegQo α (n + 1) (Work.Spaces.Dth f)
  /-- `D_z` drops the level by one -/
  dz1 : ∀ f : Fn, RegQo α (n + 2) f → RegQo α (n + 1) (Work.Spaces.Dz f)
  /-- `D_θ` drops the level by two -/
  dth2 : ∀ f : Fn, RegQo α (n + 2) f → RegQo α n (Work.Spaces.Dth f)
  /-- `D_z` drops the level by two -/
  dz2 : ∀ f : Fn, RegQo α (n + 2) f → RegQo α n (Work.Spaces.Dz f)
  /-- `Lhat (D_z f)` is at level `n` when `f` is at level `n+2` -/
  ldz : ∀ f : Fn, RegQo α (n + 2) f →
    RegQo α n (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f))
  /-- the defect `Ê₂ f` is at level `n` when `f` is at level `n+1` -/
  e2r : ∀ f : Fn, RegQo α (n + 1) f → RegQo α n (Work.FTS.CoercivityFix.E2hat f)
  /-- one-sided comparison of the `ℋⁿ`-norms of the three slots with `|f|_{n+1}` -/
  normSub : ∀ f : Fn, RegQo α (n + 2) f →
    Work.Spaces.HkSq α n f ≤ Work.Spaces.HkSq α (n + 1) f
      ∧ Work.Spaces.HkSq α n (Work.Spaces.Dth f) ≤ Work.Spaces.HkSq α (n + 1) f
      ∧ Work.Spaces.HkSq α n (Work.Spaces.Dz f) ≤ Work.Spaces.HkSq α (n + 1) f

/-- **The algebraic inputs of the step, membership-free for the congruence.**  The
congruence of the concrete inner product in its *first* argument on the open quadrant needs
**no** regularity hypothesis (derivatives are local and the quadrant is co-null: see
`StepAssembly/H1IP_congr_qd`), and the two commutator identities are pointwise statements
on the open quadrant. -/
structure Comm2O (α : ℝ) (n : ℕ) (IP : Fn → Fn → ℝ) : Prop where
  /-- congruence in the first argument on the open quadrant, with no membership -/
  congr : ∀ f f' g : Fn,
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) → IP f g = IP f' g
  /-- additivity in the first argument, on the level-`n` class -/
  add : ∀ f₁ f₂ g : Fn, RegQo α n f₁ → RegQo α n f₂ → RegQo α n g →
    IP (f₁ + f₂) g = IP f₁ g + IP f₂ g
  /-- `D_θ` commutes with `Lhat` exactly -/
  dthC : ∀ f : Fn, Work.FTS.EllipticEst.SmoothOpen f → ∀ z θ : ℝ,
    (z, θ) ∈ Work.Construction.Qd →
    Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f) z θ
  /-- the `D_z` commutator of `Lhat` is the explicit defect `Ê₂` -/
  dzC : ∀ f : Fn, Work.FTS.EllipticEst.SmoothOpen f → ∀ z θ : ℝ,
    (z, θ) ∈ Work.Construction.Qd →
    Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
        + Work.FTS.CoercivityFix.E2hat f z θ


/-! ## The open-class data of the *transfer* induction -/

/-- **The level-`n` data of the transfer induction**: the Cauchy–Schwarz bound of `IP` at
level `n` (on `RegQo α n`), together with the coercivity of the paper's operator `𝓛_Γ^T`
at level `n` on the thin class `CoerAdmO`. -/
structure CoerDataTO (α : ℝ) (n : ℕ) (IP : Fn → Fn → ℝ) (cc CC : ℝ) : Prop where
  /-- the coercivity constant is positive -/
  hcc : 0 < cc
  /-- the Cauchy–Schwarz constant is positive -/
  hCC : 0 < CC
  /-- Cauchy–Schwarz against the honest `ℋⁿ`-norm, on the level-`n` class -/
  cs : ∀ f g : Fn, RegQo α n f → RegQo α n g →
    |IP f g| ≤ CC * Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g
  /-- coercivity of `𝓛_Γ^T` at level `n`, on the one-condition class `CoerAdmO` -/
  coer : ∀ f : Fn, CoerAdmO α f →
    cc * Work.Spaces.HkSq α n f ≤ IP (Work.Coercivity.LGammaT α f) f

/-- **The one-sided norm comparison of the coercivity step on the open class** — the open-class
analogue of `Assembly.hnormD_all`, with the constant `1` (so that it serves as the `hnormD`
hypothesis of `StepCoerO.step_coer_O` and `step2_data_ge_O`). -/
theorem hnormD_all_O (α : ℝ) (hα : 0 < α) {n : ℕ} (hn : 1 ≤ n) :
    ∀ f : Fn, RegQo α (n + 1) f →
      Work.Spaces.HkSq α (n + 1) f
        ≤ 1 * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)
            + Work.Spaces.HkSq α n (Work.Spaces.Dz f)) := by
  intro f hf
  rw [one_mul]
  exact Work.FTS.StrongPersist.HkSq_succ_le_SO (α := α) hα n hn
    (Work.FTS.StrongPersist.q0Sm_of_smoothOpen hf.1 (n + 1)) hf.2.1


end Work.FTS.StrongEps.EpsE4Thr
