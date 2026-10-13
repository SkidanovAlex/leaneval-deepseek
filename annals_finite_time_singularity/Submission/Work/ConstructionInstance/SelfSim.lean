/-
# `Work.ConstructionInstance.SelfSim` — the **constructed vorticity**, explicitly

Every field of the delivered input package that is *about the vorticity* is a statement about

  `ω(x,t) = λ̄(t)⁻¹·χ(ρ(x)/L)·F(ρ(x)^p/λ̄(t), θ(x))·e_θ(x)`   (`F = F_* + g`),

the **cut** self-similar vorticity of the construction: the `St1` cut-off `χ(ρ/L)` (a `C^∞` bump
equal to `1` on `[-1,1]` and `0` outside `(-2,2)`) makes the datum compactly supported, and — the
point of finding (F) below — it is what makes the **support box** `hSupp` a *theorem* rather than a
transported fact: on `preWindow T` the field vanishes identically outside `B(0,2L)`, independently
of the flow.  The *uncut* field `omegaS p g` decays but never vanishes, so no radius `R` supports
it and `hSupp` is false for it — the delivered `ConstructedSolution.hSupp` can therefore only be
honest for the cut field (or for a perturbation `g` that cancels `F_*` at infinity).

## Why the cut in the ansatz is forced (finding F)

`SlicesSupported ω R T` (and the interface field `hSupp`) require `ω y t ≠ 0 → ‖y‖ ≤ R`; for
`g = 0` the uncut field satisfies `omegaS p 0 y t ≠ 0` for every `y` with `ρ(y) > 0` (the profile
`F_*` is strictly positive on the open quadrant), so no finite `R` works.  Hence the honest
ansatz of `St0`–`St3` carries the cut-off, and every quantity about `ω` below is computed from
this *definition* rather than assumed.

## What is proved about it (all in this directory)

| statement | name |
|---|---|
| the support box `ω y t ≠ 0 → ‖y‖ ≤ R` (for `2L ≤ R`) | `selfSimVort_support` |
| the self-similar box `λ̄(t)‖ω(x,t)‖ ≤ 20p + Cg` | `selfSimVort_bdd` |
| the `∂ₜ` box `λ̄(t)²‖∂ₜω(x,t)‖ ≤ K(20p + Cg + Cg')` | `bddDt_selfSimVort` |
| divergence-freeness of the slices | `div_selfSimVort` |
| continuity on `coreRegion R × preWindow T` | `continuousOn_selfSimVort` |
| the `St5` lower bound | `exists_omegaSz_low_radius` (+ `Reduced.solVort_hansatz`) |
| the strip time-Hölder bound | `timeHolderOnBall_selfSimVort` (+ `timeHolderOnBall_of_timeDeriv_le`) |
| the pointwise ansatz (definitional) | `selfSimVort_apply` |
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.ConstructionInstance.Defs
import Submission.Work.ConstructionInstance.Basic
import Submission.Work.ConstructionInstance.Boxes
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

/-- **The constructed (cut) self-similar vorticity**:

  `selfSimVort p g L lam x t = λ̄(t)⁻¹ · χ(ρ(x)/L) · F(ρ(x)^p/λ̄(t), θ(x)) · e_θ(x)`. -/
def selfSimVort (p : ℝ) (g : ℝ → ℝ → ℝ) (L : ℝ) (lam : ℝ → ℝ) : R3 → ℝ → R3 :=
  fun x t => (lam t)⁻¹ •
    (Work.Stability.chi (Work.Cyl.rho x / L) • omegaSz p g (Work.Cyl.rho x ^ p / lam t) x)

theorem selfSimVort_apply (p : ℝ) (g : ℝ → ℝ → ℝ) (L : ℝ) (lam : ℝ → ℝ) (x : R3) (t : ℝ) :
    selfSimVort p g L lam x t = (lam t)⁻¹ •
      (Work.Stability.chi (Work.Cyl.rho x / L) • omegaSz p g (Work.Cyl.rho x ^ p / lam t) x) :=
  rfl

/-- **The support box**: the cut-off makes the field vanish outside `B(0, 2L)`, so any `R ≥ 2L`
works — independently of the flow, of `λ̄` and of `t`. -/
theorem selfSimVort_support {p : ℝ} {g : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 < L) {R : ℝ}
    (hR : 2 * L ≤ R) {lam : ℝ → ℝ} :
    ∀ t : ℝ, ∀ y : R3, selfSimVort p g L lam y t ≠ 0 → y ∈ Metric.closedBall 0 R := by
  intro t y hy
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hlt
  rw [not_le] at hlt
  have h2 : 2 ≤ Work.Cyl.rho y / L := by
    rw [Work.Cyl.rho_eq_norm, le_div_iff₀ hL]
    linarith
  rw [selfSimVort_apply, Work.Stability.chi_eq_zero (h2.trans (le_abs_self _)), zero_smul,
    smul_zero] at hy
  exact hy rfl

/-- **The self-similar box for the constructed vorticity**: for `λ̄(t) > 0`,
`λ̄(t)·‖ω(x,t)‖ ≤ 20p + Cg`, because the cut-off factor is in `[0,1]`. -/
theorem selfSimVort_bdd {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ} {Cg : ℝ}
    (hCg : 0 ≤ Cg) (hgbdd : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg)
    {L : ℝ} (hL : 0 < L) {lam : ℝ → ℝ} {t : ℝ} (ht : 0 < lam t) (x : R3) :
    lam t * ‖selfSimVort p g L lam x t‖ ≤ 20 * p + Cg := by
  have hz : 0 ≤ Work.Cyl.rho x ^ p / lam t :=
    div_nonneg (Real.rpow_nonneg (Work.Cyl.rho_nonneg x) p) ht.le
  have hbox := omegaSz_norm_le hp hp1 hCg hgbdd hz x
  have hchi : Work.Stability.chi (Work.Cyl.rho x / L) ≤ 1 := Work.Stability.chi_le_one _
  have hchi0 : 0 ≤ Work.Stability.chi (Work.Cyl.rho x / L) := Work.Stability.chi_nonneg _
  rw [selfSimVort_apply, mul_norm_inv_smul ht]
  calc ‖Work.Stability.chi (Work.Cyl.rho x / L) • omegaSz p g (Work.Cyl.rho x ^ p / lam t) x‖
      = |Work.Stability.chi (Work.Cyl.rho x / L)|
          * ‖omegaSz p g (Work.Cyl.rho x ^ p / lam t) x‖ := norm_smul _ _
    _ ≤ 1 * ‖omegaSz p g (Work.Cyl.rho x ^ p / lam t) x‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [abs_of_nonneg hchi0]; exact hchi
    _ ≤ 20 * p + Cg := by rw [one_mul]; exact hbox

end Work.ConstructionInstance
