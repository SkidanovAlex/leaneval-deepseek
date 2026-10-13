/-
# `Submission/Work/FTS_LocDatum3a/Basic.lean` — the elementary datum facts for clause (3a′)

The producer of the strong-solution clause (3a′) needs, for the concrete separable datum

  `locG6 α L β = locR α L β(z) · Γ(θ)`   (`Work.FTS.LocDataExt.locG_locR_Gam`),

the following inputs of the mollifier chapter `Work.FTS.StrongEps`:

* `SmoothQuad (locG6 α L β)` hence `SmoothOpen` and all finite orders of smoothness on the open
  quadrant (`Work.FTS.StrongEps.softClass_Jeps`, `Jeps_contDiffOn` want
  `∀ n, ContDiffOn ℝ n (uncurry ·) Quad`);
* the axis condition `hax`: `z ↦ locG6 α L β z θ / z → 0` as `z → 0⁺` (it holds because `locR`
  vanishes identically for `z ≤ 3/4`, `L ≥ 1`);
* the local integrability of the log-pull-back: `LocallyIntegrable (logPull (locG6 α L β)) volume`
  (the log-pull-back is continuous: `locR` on `(-1,∞)` composed with `exp`, and `Γ` on `(0,π/2)`
  composed with `θ ↦ arctan (exp ζ)`).

Everything here is unconditional in `β` and needs only `1 ≤ L` for the axis condition.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_LocDatum3a.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_LocDatum3a

set_option autoImplicit false

/-! ## Smoothness of the datum -/

/-- `locG6 α L β` is `C^∞` on `(-1,∞) × (0,π/2)`: it is the separable product `locR · Γ` of a
`C^∞`-on-`(-1,∞)` radial factor with the angular factor `Γ`. -/
theorem smoothQuad_locG6 (α L β : ℝ) : Work.FTS.LocData.SmoothQuad (locG6 α L β) := by
  rw [locG6_eq_locR_mul]
  exact Work.FTS.LocDataExt.smoothQuad_sepGam (Work.FTS.LocDataExt.contDiffOn_locR α L β)

/-- `locG6 α L β` is `C^∞` on the open quadrant `(0,∞) × (0,π/2)`. -/
theorem smoothOpen_locG6 (α L β : ℝ) : Work.FTS.EllipticEst.SmoothOpen (locG6 α L β) := by
  rw [Work.FTS.EllipticEst.SmoothOpen, Work.FTS.EllipticEst.Q0]
  exact (smoothQuad_locG6 α L β).mono
    (Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num)) subset_rfl)

/-- All finite orders of smoothness of `locG6 α L β` on the open quadrant `Quad` of the mollifier
chapter (the hypothesis `hsm` of `Work.FTS.StrongEps.softClass_Jeps`). -/
theorem forall_contDiffOn_locG6 (α L β : ℝ) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (locG6 α L β)) Work.FTS.StrongEps.Quad := by
  have h := smoothQuad_locG6 α L β
  rw [Work.FTS.LocData.SmoothQuad, contDiffOn_infty] at h
  intro n
  refine (h n).mono ?_
  rw [Work.FTS.StrongEps.Quad]
  exact Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num)) subset_rfl

/-! ## The axis condition -/

/-- **The axis condition of the datum**: `z ↦ locG6 α L β z θ / z` tends to `0` at `0⁺`.  It is
immediate from `locR ≡ 0` on `(0, 3/4)` (which holds for `L ≥ 1`). -/
theorem hax_locG6 (α L β : ℝ) (hL : 1 ≤ L) :
    ∀ θ ∈ Set.Ioo 0 (π / 2),
      Tendsto (fun z : ℝ => locG6 α L β z θ / z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  intro θ _hθ
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hδ : (0 : ℝ) < min L (3 / 4) := lt_min hLpos (by norm_num)
  have hev : (fun z : ℝ => locG6 α L β z θ / z) =ᶠ[𝓝[>] (0 : ℝ)] fun _ => (0 : ℝ) := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with z hz
    have hz0 : 0 < z := hz.1
    have hzL : z ≤ L := le_of_lt (lt_of_lt_of_le hz.2 (min_le_left _ _))
    have hzb : z ≤ 3 / 4 := le_of_lt (lt_of_lt_of_le hz.2 (min_le_right _ _))
    have hzval : locG6 α L β z θ = 0 := by
      have h1 : Work.FTS.LocDataExt.locR α L β z = 0 :=
        Work.FTS.LocDataExt.locR_eq_zero_of_le hLpos hz0.le hzL hzb
      rw [locG6_eq_locR_mul]
      change Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ = 0
      rw [h1, zero_mul]
    rw [hzval, zero_div]
  exact tendsto_const_nhds.congr' hev.symm

/-- The axis condition of the datum in the `ε`-`δ` shape consumed by
`Work.FTS.StrongEps.softClass_Jeps` (`hax`), as opposed to the `Tendsto` shape `hax_locG6`
consumed by `Work.FTS.StrongEps.axis_Jeps`. -/
theorem hax_locG6_eps (α L β : ℝ) (hL : 1 ≤ L) :
    ∀ ε' > 0, ∃ δ > 0, ∀ z : ℝ, 0 < z → z < δ →
      ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) → |locG6 α L β z θ / z| ≤ ε' := by
  intro ε' hε'
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  refine ⟨min L (3 / 4), lt_min hLpos (by norm_num), fun z hz0 hz θ _hθ => ?_⟩
  have hzL : z ≤ L := le_of_lt (lt_of_lt_of_le hz (min_le_left _ _))
  have hzb : z ≤ 3 / 4 := le_of_lt (lt_of_lt_of_le hz (min_le_right _ _))
  have hzval : locG6 α L β z θ = 0 := by
    have h1 : Work.FTS.LocDataExt.locR α L β z = 0 :=
      Work.FTS.LocDataExt.locR_eq_zero_of_le hLpos hz0.le hzL hzb
    rw [locG6_eq_locR_mul]
    change Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ = 0
    rw [h1, zero_mul]
  rw [hzval, zero_div, abs_zero]
  exact hε'.le

/-! ## The log-pull-back -/

/-- **The log-pull-back of the datum is continuous.**  In the log coordinates
`(s, ζ) ↦ (exp s, arctan (exp ζ))` the datum becomes
`locR (exp s) · Γ (arctan (exp ζ))`, a product of a continuous function of `s` (the `C^∞`
radial factor composed with `exp`) and a continuous function of `ζ` (`Γ` on `(0,π/2)` composed
with `arctan ∘ exp`, whose values lie in `(0,π/2)`). -/
theorem continuous_logPull_locG6 (α L β : ℝ) :
    Continuous (Work.FTS.StrongEps.logPull (locG6 α L β)) := by
  have h1 : Continuous (fun s : ℝ => Work.FTS.LocDataExt.locR α L β (Real.exp s)) :=
    (Work.FTS.LocDataExt.contDiffOn_locR α L β).continuousOn.comp_continuous
      Real.continuous_exp (fun s => by
        show (-1 : ℝ) < Real.exp s
        linarith [Real.exp_pos s])
  have h2 : Continuous (fun ζ : ℝ => Work.Spaces.Gam α (Real.arctan (Real.exp ζ))) :=
    (Work.FTS.LocData.contDiffOn_Gam_Ioo α).continuousOn.comp_continuous
      (Real.continuous_arctan.comp Real.continuous_exp)
      (fun ζ => ⟨Real.arctan_pos.mpr (Real.exp_pos ζ), Real.arctan_lt_pi_div_two _⟩)
  have hfun : (fun x : ℝ × ℝ => Work.FTS.LocDataExt.locR α L β (Real.exp x.1)
        * Work.Spaces.Gam α (Real.arctan (Real.exp x.2)))
      = Work.FTS.StrongEps.logPull (locG6 α L β) := by
    funext x
    rw [locG6_eq_locR_mul]
    rfl
  rw [← hfun]
  exact (h1.comp continuous_fst).mul (h2.comp continuous_snd)

/-- **`logPull (locG6 α L β)` is locally integrable** (the hypothesis `hloc` of
`Work.FTS.StrongEps.softClass_Jeps`), being continuous. -/
theorem locallyIntegrable_logPull_locG6 (α L β : ℝ) :
    LocallyIntegrable (Work.FTS.StrongEps.logPull (locG6 α L β)) volume :=
  (continuous_logPull_locG6 α L β).locallyIntegrable

end Work.FTS_LocDatum3a
