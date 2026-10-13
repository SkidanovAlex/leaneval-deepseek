/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/PzJepsStrict.lean` — the *strict* datum bound at the
barrier's scale `√(clo/Cup) · C₀ α²`

`AprioriP`'s small-ball clause is stated at the radius `C₀ α²`, and `h0` of the level-four barrier
(`apriori_fourth_of_barrier`, at the level `Y = clo·(C₀α²)²`) needs the *strict* datum inequality
`Xn α x₀ < √(clo/Cup) · C₀ α²` at the datum `x₀ = Pz (J_ε g₀)` (see `BarrierThreshold.lean`, and
`NOTES_EpsE4Thr_session6.md` for the ruling request: `hC₀ : 1 ≤ C₀` alone does not supply it).

This module proves that bound from the `EpsE4Thr` datum hypotheses, for small `ε`, as soon as
`1 < √(clo/Cup)·C₀`:

* the projection is invisible on `J_ε g₀`, because the class-`C` clause of `EpsDatum` carries the
  vanishing of the `L₁₂`-zero-mode (`Pz_self_of_l12`);
* `TauZero.Jeps_smallBall_one_lt` at the intermediate constant
  `C' := (√(clo/Cup)·C₀ + 1)/2 ∈ (1, √(clo/Cup)·C₀)` gives `Xn α (J_ε g₀) ≤ C' α² <
  √(clo/Cup)·C₀·α²` — strict, because `ε` is bounded by the *closed* interval `Ioc 0 ε₁` where the
  estimate is uniform and the gap `√(clo/Cup)·C₀ - C' > 0` is available.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.FTS.StrongEps.EpsE4Thr.TauZero
import Submission.Work.FTS.StrongEps.PZero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The strict datum bound at the barrier's scale.**

For a datum of the `hd`-class with `Xn α g₀ ≤ α²`, the projected mollified datum
`x₀ = Pz (J_ε g₀)` — which is `J_ε g₀` itself, by the `l12`-clause of `EpsDatum` — satisfies
`Xn α x₀ < √(clo/Cup) · C₀ α²` for all sufficiently small `ε`, provided
`1 < √(clo/Cup) · C₀`.  This is exactly the numeric condition that `BarrierThreshold.h0_of_datum_ratio`
needs to place the datum strictly below the barrier level `clo·(C₀α²)²`. -/
theorem Pz_Jeps_lt_ratio {α C₀ clo Cup : ℝ} {ρ : ℝ × ℝ → ℝ} {g₀ : Fn}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hclo : 0 < clo) (hCup : 0 < Cup) (hC₀ : 0 < C₀)
    (hratio : 1 < Real.sqrt (clo / Cup) * C₀)
    (hd : ∀ ε : ℝ, 0 < ε → Work.FTS.StrongEps.EpsDatum α ρ ε g₀)
    (h4 : Work.FTS.Nonlin.Xn α g₀ ≤ α ^ 2) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε ∈ Set.Ioc 0 ε₁,
      Work.FTS.Nonlin.Xn α (Pz (Work.FTS.StrongEps.Jeps ρ ε g₀))
        < Real.sqrt (clo / Cup) * (C₀ * α ^ 2) := by
  classical
  set s : ℝ := Real.sqrt (clo / Cup) * C₀ with hs
  have hs1 : 1 < s := hratio
  -- the intermediate constant, strictly between `1` and `s`
  set C' : ℝ := (s + 1) / 2 with hC'
  have hC'1 : 1 < C' := by rw [hC']; linarith
  obtain ⟨ε₁, hε₁, hball⟩ :=
    Jeps_smallBall_one_lt (α := α) (C₀ := C') (ρ := ρ) (g₀ := g₀) hρ hα hα1 hC'1 hd h4
  refine ⟨ε₁, hε₁, fun ε hε => ?_⟩
  have hlt : C' * α ^ 2 < s * α ^ 2 := by
    have h2 := pow_pos hα 2
    exact mul_lt_mul_of_pos_right (by rw [hC']; linarith) h2
  -- the projection is the identity on `J_ε g₀`
  have hPz : Pz (Work.FTS.StrongEps.Jeps ρ ε g₀) = Work.FTS.StrongEps.Jeps ρ ε g₀ :=
    Pz_self_of_l12 ((hd ε hε.1).2.2.l12)
  rw [hPz]
  have hgoal : s * α ^ 2 = Real.sqrt (clo / Cup) * (C₀ * α ^ 2) := by
    rw [hs]; ring
  exact lt_of_le_of_lt (hball ε hε) (by rw [← hgoal]; exact hlt)

end Work.FTS.StrongEps.EpsE4Thr
