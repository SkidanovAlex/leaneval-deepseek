/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/JepsSmoothOpen.lean` — `SmoothOpen` of `J_ε f`

Two small closure lemmas about the log-coordinate mollifier `Jeps` that the `P₀`-corrected chain
needs (the un-projected `E1` chapter states its results for the *raw* hypothesis
`∀ n, ContDiffOn ℝ n (Function.uncurry f) Quad`, whereas the projection's additivity lemma
`StrongPersist.IP6_add` asks for the `SmoothOpen` form of the *mollified* profile):

* `continuous_logPull_of_forall_contDiffOn` — `logPull f = fun x => f (exp x.1) (arctan (exp x.2))`
  is continuous as soon as `f` is `C⁰` on the open quadrant (the log map lands in `Q0`);
* `locallyIntegrable_logPull_of_forall_contDiffOn` — its local integrability;
* `smoothOpen_Jeps` — `SmoothOpen (J_ε f)` for `SmoothOpen f` and a *smooth* kernel
  (`Jeps_contDiffOn` + the local integrability above).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Jeps_contDiffOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The log map `x ↦ (exp x.1, arctan (exp x.2))` is continuous and lands in the open quadrant. -/
theorem continuous_logMap_quad :
    Continuous (fun x : ℝ × ℝ => (Real.exp x.1, Real.arctan (Real.exp x.2))) ∧
      ∀ x : ℝ × ℝ, (Real.exp x.1, Real.arctan (Real.exp x.2)) ∈ Quad := by
  constructor
  · exact (Real.continuous_exp.comp continuous_fst).prodMk
      (Real.continuous_arctan.comp (Real.continuous_exp.comp continuous_snd))
  · intro x
    refine ⟨Real.exp_pos x.1, ?_, ?_⟩
    · exact Real.arctan_pos.mpr (Real.exp_pos x.2)
    · exact Real.arctan_lt_pi_div_two _

/-- `logPull f` is continuous on `ℝ²` when `f` is `C⁰` on the open quadrant. -/
theorem continuous_logPull_of_forall_contDiffOn {f : Fn}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) : Continuous (logPull f) := by
  have hcont : ContinuousOn (Function.uncurry f) Quad := (hf 0).continuousOn
  have hmap := continuous_logMap_quad.1
  have hmaps := continuous_logMap_quad.2
  have hcomp : Continuous ((Function.uncurry f) ∘
      fun x : ℝ × ℝ => (Real.exp x.1, Real.arctan (Real.exp x.2))) :=
    ContinuousOn.comp_continuous hcont hmap hmaps
  exact hcomp

/-- `logPull f` is locally integrable when `f` is `C⁰` on the open quadrant. -/
theorem locallyIntegrable_logPull_of_forall_contDiffOn {f : Fn}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) :
    MeasureTheory.LocallyIntegrable (logPull f) volume :=
  (continuous_logPull_of_forall_contDiffOn hf).locallyIntegrable

/-- **`J_ε` preserves `SmoothOpen`** (for a smooth kernel): the conclusion of `Jeps_contDiffOn`
in the `SmoothOpen`-form used by the pairing's additivity lemma. -/
theorem smoothOpen_Jeps (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) {f : Fn}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) :
    Work.FTS.EllipticEst.SmoothOpen (Jeps ρ ε f) :=
  (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr
    (Jeps_contDiffOn ρ hρ hε (locallyIntegrable_logPull_of_forall_contDiffOn hf))

end Work.FTS.StrongEps
