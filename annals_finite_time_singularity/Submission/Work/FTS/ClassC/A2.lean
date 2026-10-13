/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS.ClassC.A2` — the level-`7` existence node on `ClassC` (design (A), item A2)

`ClassC` (`FTS/ClassC/Defs.lean`) supplies *exactly* the inputs of the corrected elliptic
existence node `Work.FTS.EllExist.ellClassOk_exists_of_inputs` at the weak-class level `7`
(the level at which the `U`-slot of the estimates is honest, design item A2):

* `reg : SmoothOpen g` and `fsm : ∀ m, ContDiffOn ℝ m (F_*(g)) (Ioi 0)` give
  `SmoothOpen (orthSource g)` (`FTS/EllExist/ClassCInputs`) and `HkMem α 7 (orthSource g)`
  (`FTS/EllExist/hkMem_orthSource_of_Fstar_smooth`);
* `tr : BdryTraces α 6 g` at `(a,b) = (0,0)` is the radial vanishing
  `z·(g(z,θ)·w z)² → 0` at `z → ∞`, which (since `w ≥ 1`) forces `g(z,θ) → 0` at every angle
  (`classC_tendsto_atTop`); with the decay of `F_*(g)` (`FTS/ClassC/fstar_tendsto_atTop_zero_of_classC`,
  which uses `mem : HkMem α 7 g`) this gives the decay of `orthSource g`
  (`EllExist.tendsto_orthSource_atTop_of`);
* `fsm` together with `IntegrableOn (F_*(g)(r)/r) (Ioi 0)` (from `reg` and `mem` via
  `FstarDivOpen.fstar_div_integrable_of_smoothOpen`) gives the three singular-term facts about
  `Gsing α g` (`Gsing_contDiffOn_ode_of_Fstar_facts`, `HasDerivAt_L12_of_Fstar_facts`) and
  `Gsing α g → 0` is `FTS/ClassC/gsing_tendsto_atTop_zero_of_classC`.

The output is `Work.FTS.EllExist.EllClassOk 8 α g Ψ` (level `8`, per the lead's ruling of
2026-10-08 09:50).  Everything is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.ClassC.A1
import Submission.Work.FTS.ClassC.classC_ellInputs
import Submission.Work.FTS.ClassC.fstar_tendsto_atTop_zero_of_classC
import Submission.Work.FTS.ClassC.gsing_tendsto_atTop_zero_of_classC
import Submission.Work.FTS.EllExist.ClassCInputs
import Submission.Work.FTS.EllExist.hkMem_orthSource_of_Fstar_smooth
import Submission.Work.FTS.EllExist.LevelK
import Submission.Work.FTS.PhiStar.thetaTraces_orthSource
import Submission.Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen
import Submission.Work.FTS.EllipticEst.Gsing_contDiffOn_ode_of_Fstar_facts
import Submission.Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The angular slices of a `ClassC` profile decay at `z → ∞`.**

`BdryTraces α 6 g` at `(a,b) = (0,0)` is `z·(g(z,θ)·w z)² → 0` at `+∞` for every `θ ∈ (0,π/2)`;
since `w z = (1+z)²/z² ≥ 1` and `z ≥ 1` on a neighbourhood of `+∞`, this forces `g(z,θ) → 0`.
At the two endpoints `θ = 0, π/2` the class field `norm` forces `g z θ = 0` identically. -/
theorem classC_tendsto_atTop {α : ℝ} {g : Fn} (h : ClassC α g) :
    ∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => g z θ) atTop (𝓝 0) := by
  intro θ hθ
  rcases lt_or_eq_of_le hθ.1 with h0 | h0
  · rcases lt_or_eq_of_le hθ.2 with h2 | h2
    · -- `θ` interior: the `BdryTraces` radial vanishing
      have hθI : θ ∈ Set.Ioo 0 (π / 2) := ⟨h0, h2⟩
      have hlimF : Tendsto (fun z => z * (g z θ * Work.Spaces.w z) ^ 2) atTop (𝓝 0) := by
        have h1 := (h.tr 0 0 (by norm_num)).1 θ hθI
        simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h1.2
      have hlimG : Tendsto (fun z => (g z θ) ^ 2) atTop (𝓝 0) := by
        refine squeeze_zero' ?_ ?_ hlimF
        · filter_upwards [eventually_ge_atTop (0 : ℝ)] with z hz
          exact sq_nonneg _
        · filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
          have hw1 : 1 ≤ Work.Spaces.w z := by
            rw [Work.Spaces.w, one_le_div (by positivity)]
            nlinarith
          have hgnn : 0 ≤ (g z θ) ^ 2 := sq_nonneg _
          have h1 : (g z θ) ^ 2 ≤ (g z θ * Work.Spaces.w z) ^ 2 := by
            rw [mul_pow]
            calc (g z θ) ^ 2 = (g z θ) ^ 2 * 1 := by ring
              _ ≤ (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 :=
                  mul_le_mul_of_nonneg_left (one_le_pow₀ hw1) hgnn
          have h2 : (g z θ * Work.Spaces.w z) ^ 2 ≤ z * (g z θ * Work.Spaces.w z) ^ 2 := by
            have := mul_le_mul_of_nonneg_right hz (sq_nonneg (g z θ * Work.Spaces.w z))
            simpa using this
          linarith
      have habs : Tendsto (fun z => |g z θ|) atTop (𝓝 0) := by
        have hsqrt : Tendsto (fun z => Real.sqrt ((g z θ) ^ 2)) atTop (𝓝 0) := by
          have hc := (Real.continuous_sqrt.tendsto 0).comp hlimG
          rw [Function.comp_def] at hc
          simpa using hc
        simpa only [Real.sqrt_sq_eq_abs] using hsqrt
      exact (tendsto_iff_norm_sub_tendsto_zero).mpr (by simpa using habs)
    · -- `θ = π/2`: `g` vanishes there by the class field `norm`
      subst h2
      have hz : ∀ z : ℝ, g z (π / 2) = 0 := by
        intro z
        have hthis := congr_fun (congr_fun h.norm z) (π / 2)
        rw [normTh_apply_of_not_mem
          (show (π / 2) ∉ Set.Ioo 0 (π / 2) from fun hc => absurd hc.2 (lt_irrefl _))] at hthis
        exact hthis.symm
      have : (fun z => g z (π / 2)) = fun _ : ℝ => (0 : ℝ) := funext hz
      rw [this]
      exact tendsto_const_nhds
  · -- `θ = 0`: `g` vanishes there by the class field `norm`
    subst h0
    have hz : ∀ z : ℝ, g z 0 = 0 := by
      intro z
      have hthis := congr_fun (congr_fun h.norm z) 0
      rw [normTh_apply_of_not_mem
        (show (0 : ℝ) ∉ Set.Ioo 0 (π / 2) from fun hc => absurd hc.1 (lt_irrefl _))] at hthis
      exact hthis.symm
    have : (fun z => g z 0) = fun _ : ℝ => (0 : ℝ) := funext hz
    rw [this]
    exact tendsto_const_nhds

/-- **The two first inputs of the repaired existence node** (smoothness of the orthogonalised
source, and its honesty at level `10 = 8 + 2`, the input level of
`EllExist.ellClassOk_exists_of_inputs_pp 8`), from the class fields (`mem10`, lead install
2026-10-11). -/
theorem classC_orthSource_inputs {α : ℝ} {g : Fn} (hα : 0 < α) (hα1 : α ≤ 1) (h : ClassC α g) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.orthSource g) ∧
    Work.Spaces.HkMem α 10 (Work.Elliptic.orthSource g) :=
  ⟨Work.FTS.EllExist.smoothOpen_orthSource_of_Fstar_smooth h.reg h.fsm,
    Work.FTS.EllExist.hkMem_orthSource_of_Fstar_smooth hα hα1 h.reg h.mem10 h.fsm⟩

/-- **The full elliptic input package of a `ClassC` profile, at level `8`.**

Assembles the five hypotheses of the level-`8` existence node from the class fields and the
auxiliary decay lemmas of the area. -/
theorem classC_ellInputs_full {α : ℝ} {g : Fn} (hα : 0 < α) (hα1 : α ≤ 1) (h : ClassC α g) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.orthSource g) ∧
    Work.Spaces.HkMem α 10 (Work.Elliptic.orthSource g) ∧
    (∀ θ ∈ Work.Spaces.Iθ,
      Tendsto (fun z => Work.Elliptic.orthSource g z θ) atTop (𝓝 0)) ∧
    (∀ m : ℕ, ContDiffOn ℝ (m : WithTop ℕ∞) (Work.Elliptic.Fstar g) (Set.Ioi 0)) ∧
    MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar g r / r) (Set.Ioi 0) := by
  have hFdec : Tendsto (fun z => Work.Elliptic.Fstar g z) atTop (𝓝 0) :=
    fstar_tendsto_atTop_zero_of_classC hα hα1 h.reg h.mem (classC_tendsto_atTop h)
  exact ⟨(classC_orthSource_inputs hα hα1 h).1, (classC_orthSource_inputs hα hα1 h).2,
    Work.FTS.EllExist.tendsto_orthSource_atTop_of (classC_tendsto_atTop h) hFdec,
    h.fsm,
    Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen α 8 g h.reg h.mem8⟩

/-- **A2: the level-`8` existence node on `ClassC`.**

Every profile of the linear class `C` has an elliptic stream function in `EllClassOk 8`.  The
level-`4` slots consume it through `ellClassOk_mono` (see `A4`/`Main`).

Lead install 2026-10-11: the node is the repaired `ellClassOk_exists_of_inputs_pp 8`
(input `HkMem α 10` of the orthogonalised source, from the class field `mem10`); the original
`ellClassOk_exists_of_inputs 8` rested on the false `PhiStar.bslOp_sol_exists 8`.

Lead install R6 2026-10-11 (`cbc/fts_ellnode_ruling.md` §4.4): the node is now
`ellClassOk_exists_of_inputs_tr` (`PhiStar.EllNode8tr_holds`), fed the θ-traces of the
orthogonalised source by `PhiStar.thetaTraces_orthSource` from the class field `thTr`;
`bslOp_sol_exists_pp` is no longer on the path. -/
theorem ellClassOk_exists_of_classC :
    ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ → ∀ g : Fn, ClassC α g →
      ∃ Ψ : Fn, Work.FTS.EllExist.EllClassOk 8 α g Ψ := by
  obtain ⟨α₁, hα₁pos, hmain⟩ := Work.FTS.EllExist.ellClassOk_exists_of_inputs_tr
  refine ⟨min α₁ (1 / 4), lt_min hα₁pos (by norm_num), ?_⟩
  intro α hα hαm g hg
  have hα₁ : α ≤ α₁ := le_trans hαm (min_le_left _ _)
  have hα4 : α ≤ 1 / 4 := le_trans hαm (min_le_right _ _)
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨hSm, hHk, hDec, hFsm, hFint⟩ := classC_ellInputs_full hα hα1 hg
  have hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 g) (-(3 * Work.Elliptic.Fstar g z / z)) z :=
    Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts g hFsm hFint
  obtain ⟨hGsm, hGode⟩ :=
    Work.FTS.EllipticEst.Gsing_contDiffOn_ode_of_Fstar_facts α g hα hFsm hFint hL12
  exact hmain α hα hα₁ g hSm hHk
    (Work.FTS.PhiStar.thetaTraces_orthSource hα hα1 hg.reg hg.fsm hg.thTr) hDec hGsm hGode
    (gsing_tendsto_atTop_zero_of_classC hα hg.reg hg.mem)

end Work.FTS.ClassC
