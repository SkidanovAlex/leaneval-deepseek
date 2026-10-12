import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Submission.Work.BoseFixR.RB67CanonGuarded
import Submission.Work.BoseGateFS.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.Reserve` — the `q2exLowerR` reserve is free

`BOSE_BOXFOCK_LEAD.md` §5.3/§7 (finding **F8**) gives the gate's `Q₂^ex` row a
*reserve* of `½·dNumOpR` on `RHi ∖ P_H^q`: the model's `n₊^H` starts at
`2K_L√(μa)`, while the physical `n₊^H` starts at `K_L√(μa)`, so the window
`[K_L√(μa), 4K_L√(μa)]` must be paid by the kinetic energy there.  Since the
reserved row is *weaker* than the unreserved FS §11 row (`Work.BoseK15`'s
`q2exLower`), the reserve costs nothing: it is the same statement plus a
nonnegative operator on the right.

* `qw_dNumOpR_nonneg` — `⟨Ψ, dNumOpR E R Ψ⟩ ≥ 0` for **any** region `R`, as soon
  as `|ℬ| ≤ 𝒜` (this is `Work.BoseFixR.RB67CanonGuarded`'s lemma with a general
  region).
* `q2exLowerR_of_q2exLower` — the gate's reserved row from the unreserved one.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseGateFS

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}

/-- **`dNumOpR` is positive** on any region: it is a sum over `R` of
`𝒟_k = ½(𝒜_k + √(𝒜_k² - ℬ_k²)) ≥ 0` times the positive operator `b_k†b_k`, and
`𝒟_k ≥ 0` as soon as `|ℬ_k| ≤ 𝒜_k`. -/
lemma qw_dNumOpR_nonneg (hAB : ∀ k : Mode, |E.B k| ≤ E.A k)
    (R : Mode → Prop) [DecidablePred R] (Ψ : F.H) :
    0 ≤ F.qw Ψ (F.dNumOpR E R) := by
  have h1 : F.qw Ψ (F.dNumOpR E R)
      = ∑ i ∈ (excited Mode).filter R, E.D i * F.qw Ψ (F.bNumOp E.alpha i) := by
    rw [Work.BoseB7.FockData.dNumOpR, Work.BoseB7.FockData.regionSum]
    exact Work.BoseB7A.qw_finset_sum F Ψ _ E.D (fun i => F.bNumOp E.alpha i)
  rw [h1]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (Work.BoseB7.FockData.Dcoef_nonneg (hAB i))
      (Work.BoseB7.bNumOp_nonneg F E.alpha i Ψ)

/-- **The reserved `Q₂^ex` row.**  The gate's `q2exLowerR` (with the reserve
`½·dNumOpR` on `RHi ∖ P_H^q`) follows from the unreserved FS §11 row, because
the reserve is a nonnegative operator in the quadratic form. -/
theorem q2exLowerR_of_q2exLower {ρ : ℝ}
    (hAB : ∀ k : Mode, |(KzEnvAt E ρ).B k| ≤ (KzEnvAt E ρ).A k) (Ψ : F.H)
    (hq2 : 2 * ρ * E.W1omega0 * F.qw Ψ (T.Gop E)
      ≤ F.qw Ψ (F.Q2ex (KzEnvAt E ρ))
        + (E.b / 400) * F.qw Ψ (T.gapOpT (KzEnvAt E ρ))) :
    2 * ρ * E.W1omega0 * F.qw Ψ (T.Gop E)
      ≤ F.qw Ψ (F.Q2ex (KzEnvAt E ρ)) + (E.b / 400) * F.qw Ψ (T.gapOpT (KzEnvAt E ρ))
        + (1 / 2) * F.qw Ψ (F.dNumOpR (KzEnvAt E ρ)
            (fun k => rHi F E k ∧ ¬ F.PHq E.KH E.aScat k)) := by
  have hpos : 0 ≤ F.qw Ψ (F.dNumOpR (KzEnvAt E ρ)
      (fun k => rHi F E k ∧ ¬ F.PHq E.KH E.aScat k)) :=
    qw_dNumOpR_nonneg hAB _ Ψ
  linarith

end Work.BoseGateFS
