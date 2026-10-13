/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/CoerAdmSlice.lean` — the `CoerAdm` clause of the level-four
barrier, reduced to the *one* missing ingredient `SmoothQuad`

`apriori_fourth_of_barrier` (the level-four barrier of `AprioriP`) consumes
`hcoer : ∀ τ ∈ Icc 0 T', Nonlin.CoerAdm α (slice (JfamP ρ ε g) τ)`, i.e. the four clauses

  `RegQ α 5 x`, `VanishTheta x`, `x 0 θ = 0 ∧ pz x 0 θ = 0` (on `Iθ`), `L₁₂ x 0 = 0`

of the projected mollified slice `x = Pz (J_ε (slice g τ))`.

Three of the four are *free* along a regular `P₀`-solution:

* `L₁₂ x 0 = 0` is the `l12` field of the class-`C` clause of `EpsDatumP`;
* `HkMem α 5 x` and `BdryTraces α 5 x` are the level-`7`/level-`6` fields of the same clause,
  monotonised (`HkMem_mono_open`);
* `VanishTheta x` and the axis *values* come from the defining `if` of `Jeps` (which vanishes off
  the open quadrant) together with the vanishing of `bump` at `θ = 0, π/2, z = 0`; the axis
  *radial derivative* `pz x 0 θ` is `0` for the interior angles by the same argument as in
  `EpsGdotThird.H6Adm_of_classC_of_eqzero` (`pz_zero_of_tendsto_div`, using the class-`C` axis
  condition `x z θ / z → 0`), and for the two endpoint angles the slice is *identically* zero in
  `z` (`pz_zero_of_eq_zero`).

That leaves exactly one genuinely analytic requirement: `LocData.SmoothQuad x`, i.e. `C^∞` of `x`
on the *strip* `(-1,∞) × (0,π/2)`.  Since `J_ε ·` is defined to be `0` off the quadrant and
`bump` vanishes for `z ≤ 1/2`, this is the statement that the `z`-slices of `x` are *flat at*
`z = 0`; it is **not** a consequence of `SmoothOpen`/`HkMem`/`BdryTraces` (the values on `z < 0`
are free).  This is interface item (B)/(G) of the owner message; the module makes it precise.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.DiagCurveIData
import Submission.Work.FTS.StrongEps.EpsGdotThird

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

/-! ## `bump` vanishes on the three boundary lines -/

theorem bump_eq_zero_theta_zero (z : ℝ) : Work.FTS.StrongEps.bump z 0 = 0 := by
  show Work.FTS.StrongEps.zCut z * Work.FTS.StrongEps.thCut 0 = 0
  rw [Work.FTS.StrongEps.bump_thCut_eq_zero_of_lt (by linarith [Real.pi_pos]), mul_zero]

theorem bump_eq_zero_theta_pi (z : ℝ) : Work.FTS.StrongEps.bump z (Real.pi / 2) = 0 := by
  show Work.FTS.StrongEps.zCut z * Work.FTS.StrongEps.thCut (Real.pi / 2) = 0
  rw [Work.FTS.StrongEps.bump_thCut_eq_zero_of_gt (by linarith [Real.pi_pos]), mul_zero]

theorem bump_eq_zero_z_zero (θ : ℝ) : Work.FTS.StrongEps.bump 0 θ = 0 := by
  show Work.FTS.StrongEps.zCut 0 * Work.FTS.StrongEps.thCut θ = 0
  rw [Work.FTS.StrongEps.bump_zCut_eq_zero_of_lt (by norm_num : (0 : ℝ) < 1 / 2), zero_mul]

/-! ## `CoerAdm` of the projected mollified slice -/

/-- **The `CoerAdm` clause of the level-four barrier**, reduced to `SmoothQuad`. -/
theorem coerAdm_slice_JfamP {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε T : ℝ} {g : Fam}
    (hreg : Work.FTS.StrongEps.EpsRegP α ρ ε T g)
    (hsq : ∀ τ ∈ Set.Icc (0 : ℝ) T, Work.FTS.LocData.SmoothQuad (slice (JfamP ρ ε g) τ)) :
    ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.Nonlin.CoerAdm α (slice (JfamP ρ ε g) τ) := by
  intro τ hτ
  have hCs : Work.FTS.ClassC.ClassC α (slice (JfamP ρ ε g) τ) := (hreg.2 τ hτ).2.2
  have hmem5 : Work.Spaces.HkMem α 5 (slice (JfamP ρ ε g) τ) :=
    Work.FTS.OpenPkg.HkMem_mono_open hCs.reg 5 (by norm_num) hCs.mem
  have htr5 : Work.FTS.Nonlin.BdryTraces α 5 (slice (JfamP ρ ε g) τ) :=
    fun a b hab => hCs.tr a b (le_trans hab (by norm_num))
  -- the endpoint vanishing, from the defining `if` of `Jeps` and from `bump`
  have h0 : ∀ z : ℝ, slice (JfamP ρ ε g) τ z 0 = 0 := by
    intro z
    show Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (slice g τ)) z 0 = 0
    rw [Work.FTS.StrongEps.Pz_apply,
      Work.FTS.StrongEps.Jeps_eq_zero_of_theta ρ ε (slice g τ)
        (by simp [Set.mem_Ioo]), bump_eq_zero_theta_zero z, mul_zero, sub_zero]
  have hpi : ∀ z : ℝ, slice (JfamP ρ ε g) τ z (Real.pi / 2) = 0 := by
    intro z
    show Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (slice g τ)) z (Real.pi / 2) = 0
    rw [Work.FTS.StrongEps.Pz_apply,
      Work.FTS.StrongEps.Jeps_eq_zero_of_theta ρ ε (slice g τ)
        (by simp [Set.mem_Ioo]), bump_eq_zero_theta_pi z, mul_zero, sub_zero]
  -- the axis values
  have hz0 : ∀ θ : ℝ, slice (JfamP ρ ε g) τ 0 θ = 0 := by
    intro θ
    show Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (slice g τ)) 0 θ = 0
    rw [Work.FTS.StrongEps.Pz_apply,
      Work.FTS.StrongEps.Jeps_eq_zero ρ ε (slice g τ) (by simp),
      bump_eq_zero_z_zero θ, mul_zero, sub_zero]
  -- the axis radial derivative
  have hpz0 : ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.pz (slice (JfamP ρ ε g) τ) 0 θ = 0 := by
    intro θ hθ
    have hslice : slice (JfamP ρ ε g) τ
        = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (slice g τ)) := rfl
    rw [hslice]
    by_cases hI : θ ∈ Set.Ioo 0 (Real.pi / 2)
    · refine Work.FTS.StrongEps.pz_zero_of_tendsto_div hI ?_ (hCs.axis θ hI)
      intro z hz
      have hzle : z ≤ 0 := by
        by_contra h
        exact hz ⟨not_le.mp h, hI⟩
      have hbz : Work.FTS.StrongEps.bump z θ = 0 := by
        show Work.FTS.StrongEps.zCut z * Work.FTS.StrongEps.thCut θ = 0
        rw [Work.FTS.StrongEps.bump_zCut_eq_zero_of_lt (by linarith), zero_mul]
      rw [Work.FTS.StrongEps.Pz_apply,
        Work.FTS.StrongEps.Jeps_eq_zero_of_le ρ ε (slice g τ) hzle, hbz,
        mul_zero, sub_zero]
    · -- `θ = 0` or `θ = π/2`: the slice is identically zero in `z`
      have hcases : θ = 0 ∨ θ = Real.pi / 2 := by
        rcases hθ with ⟨h1, h2⟩
        rcases eq_or_lt_of_le h1 with h | h
        · exact Or.inl h.symm
        · rcases eq_or_lt_of_le h2 with h' | h'
          · exact Or.inr h'
          · exact absurd ⟨h, h'⟩ hI
      refine Work.FTS.StrongEps.pz_zero_of_eq_zero (fun z => ?_)
      rcases hcases with h | h
      · rw [h]; exact h0 z
      · rw [h]; exact hpi z
  exact ⟨⟨hsq τ hτ, hmem5, htr5⟩, ⟨h0, hpi⟩, fun θ hθ => ⟨hz0 θ, hpz0 θ hθ⟩, hCs.l12⟩

end Work.FTS.StrongEps.EpsE4Thr
