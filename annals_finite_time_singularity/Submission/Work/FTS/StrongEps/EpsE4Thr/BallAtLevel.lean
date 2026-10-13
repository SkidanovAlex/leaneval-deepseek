/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EpsE4Thr/BallAtLevel.lean` — the two conversions between the barrier level `Y` and the small ball

The level-four energy barrier (`Work.FTS.Apriori.barrier_within` and its level-restricted form
`BarrierLevel.barrier_within_level`) runs at a *level* `Y` for the coercive pairing
`E τ = IP α x_τ x_τ`, while the a-priori bound the route needs is the *small ball*
`Xn α x_τ ≤ C₀ α²`.  The two are related by the comparability clauses of the open-class coercivity
interface `UnifIPO`:

* `lo : clo · HkSq α 4 f ≤ IP α f f` — so a level bound `IP α x x ≤ Y` with
  `Y ≤ clo (C₀ α²)²` gives the **ball** `Xn α x ≤ C₀ α²` (`ballAt_of_IP_eq`);
* `up : IP α f f ≤ Cup · HkSq α 4 f` — so a **strict** norm bound
  `Xn α x < √(clo/Cup)·(C₀ α²)` gives the strict level bound
  `IP α x x < clo (C₀ α²)²` (`IP_lt_level_of_norm_lt`).

The second conversion is the *sharp datum condition* of the level-four a-priori chapter: the
barrier starts at `τ = 0`, where the datum is only known to be in the `C₀ α²`-ball, so the level
`Y = clo (C₀ α²)²` can be strictly above `E 0 = IP α x₀ x₀` only if the datum is strictly inside
the ball by the factor `√(clo/Cup) ≤ 1` (equal to `1` iff `clo = Cup`).  This is the quantitative
form of the session-1 finding that the boundary case `C₀ = 1` is saturated; see
`NOTES_EpsE4Thr_session12.md`.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass

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

/-- **The small ball from a bound on the coercive pairing.**

If the pairing level `Y` of `x` is at most `clo·(C₀ α²)²`, then `x` lies in the `C₀ α²`-ball.
This is the step that turns the conclusion of the barrier (`IP α x_τ x_τ ≤ Y`) into the clause
`Xn α x_τ ≤ C₀ α²` of the a-priori bound, using the lower comparability `UnifIPO.lo`. -/
theorem ballAt_of_IP_eq {IP : ℝ → Fn → Fn → ℝ} {α₂ cc clo Cup Ccs : ℝ}
    (hIP : UnifIPO IP α₂ cc clo Cup Ccs) {α : ℝ} (hα : α ∈ Set.Ioc 0 α₂)
    {x : Fn} (hx : CoerAdmO α x) {Y C₀ : ℝ} (hC₀ : 0 ≤ C₀) (hY : IP α x x ≤ Y)
    (hYle : Y ≤ clo * (C₀ * α ^ 2) ^ 2) :
    Work.FTS.Nonlin.Xn α x ≤ C₀ * α ^ 2 := by
  have hclo : 0 < clo := hIP.pos.2.2.1
  have hlo := hIP.lo α hα x hx
  have hsq : Work.Spaces.HkSq α 4 x ≤ (C₀ * α ^ 2) ^ 2 := by
    have h : clo * Work.Spaces.HkSq α 4 x ≤ clo * (C₀ * α ^ 2) ^ 2 := le_trans hlo (le_trans hY hYle)
    exact le_of_mul_le_mul_left h hclo
  change Work.Spaces.HkNorm α 4 x ≤ C₀ * α ^ 2
  rw [Work.Spaces.HkNorm]
  have h1 : Real.sqrt (Work.Spaces.HkSq α 4 x) ≤ Real.sqrt ((C₀ * α ^ 2) ^ 2) :=
    Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hC₀ (pow_nonneg (by linarith [hα.1] : (0:ℝ) ≤ α) 2))] at h1

/-- **The small ball from the level, in the form the barrier produces it.**

The barrier returns `∀ τ, IP α x_τ x_τ ≤ Y`; composing with `ballAt_of_IP_eq` in the `CoerAdmO`
clause gives the a-priori ball. -/
theorem ballAt_of_energy_bound {IP : ℝ → Fn → Fn → ℝ} {α₂ cc clo Cup Ccs : ℝ}
    (hIP : UnifIPO IP α₂ cc clo Cup Ccs) {α : ℝ} (hα : α ∈ Set.Ioc 0 α₂)
    {x : ℝ → Fn} {Y C₀ T : ℝ} (hC₀ : 0 ≤ C₀) (hYle : Y ≤ clo * (C₀ * α ^ 2) ^ 2)
    (hcoer : ∀ τ ∈ Set.Ico 0 T, CoerAdmO α (x τ))
    (henergy : ∀ τ ∈ Set.Ico 0 T, IP α (x τ) (x τ) ≤ Y) :
    ∀ τ ∈ Set.Ico 0 T, Work.FTS.Nonlin.Xn α (x τ) ≤ C₀ * α ^ 2 :=
  fun τ hτ => ballAt_of_IP_eq hIP hα (hcoer τ hτ) hC₀ (henergy τ hτ) hYle

/-- **The strict level bound from a strict norm bound** (the sharp datum condition).

If the datum's `ℋ⁴`-size is strictly below `√(clo/Cup)·(C₀ α²)`, then its pairing level is strictly
below `clo (C₀ α²)²` — which is what the barrier needs at `τ = 0`.  The factor `√(clo/Cup) ≤ 1`
is the whole content: the barrier cannot be started from the mere ball `Xn α x ≤ C₀ α²` when
`clo < Cup`. -/
theorem IP_lt_level_of_norm_lt {IP : ℝ → Fn → Fn → ℝ} {α₂ cc clo Cup Ccs : ℝ}
    (hIP : UnifIPO IP α₂ cc clo Cup Ccs) {α : ℝ} (hα : α ∈ Set.Ioc 0 α₂)
    {x : Fn} (hx : CoerAdmO α x) {C₀ : ℝ}
    (hlt : Work.FTS.Nonlin.Xn α x < Real.sqrt (clo / Cup) * (C₀ * α ^ 2)) :
    IP α x x < clo * (C₀ * α ^ 2) ^ 2 := by
  have hCup : 0 < Cup := hIP.pos.2.2.2.1
  have hclo : 0 < clo := hIP.pos.2.2.1
  have hup := hIP.up α hα x hx
  have hsqeq : Work.Spaces.HkSq α 4 x = (Work.FTS.Nonlin.Xn α x) ^ 2 := by
    change Work.Spaces.HkSq α 4 x = (Work.Spaces.HkNorm α 4 x) ^ 2
    rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 x)]
  have hnorm : Work.FTS.Nonlin.Xn α x ^ 2 < clo / Cup * (C₀ * α ^ 2) ^ 2 := by
    have hnn : 0 ≤ Work.FTS.Nonlin.Xn α x := Work.Spaces.HkNorm_nonneg α 4 x
    have h2 : Work.FTS.Nonlin.Xn α x ^ 2 < (Real.sqrt (clo / Cup) * (C₀ * α ^ 2)) ^ 2 :=
      pow_lt_pow_left₀ hlt hnn (by norm_num)
    rwa [mul_pow, Real.sq_sqrt (div_nonneg hclo.le hCup.le)] at h2
  calc IP α x x ≤ Cup * Work.Spaces.HkSq α 4 x := hup
    _ = Cup * Work.FTS.Nonlin.Xn α x ^ 2 := by rw [hsqeq]
    _ < Cup * (clo / Cup * (C₀ * α ^ 2) ^ 2) := mul_lt_mul_of_pos_left hnorm hCup
    _ = clo * (C₀ * α ^ 2) ^ 2 := by field_simp

end Work.FTS.StrongEps.EpsE4Thr
