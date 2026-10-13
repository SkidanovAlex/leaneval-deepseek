/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/OpenBarrier.lean` — the level-four barrier in the *open*
class, with its coercivity hypothesis **proved** from the solution's regularity

`apriori_fourth_of_barrier` (session 2) consumes

  `hcoer : ∀ τ ∈ Icc 0 T', Nonlin.CoerAdm α (slice (JfamP ρ ε g) τ)`,

and `CoerAdm` contains `RegQ α 5`, i.e. `LocData.SmoothQuad x` — `C^∞` of the projected slice on
the *strip* `z > -1`.  Along the route this is **not** available: `J_ε f` is defined to be `0` off
the open quadrant, so `SmoothQuad (J_ε f)` demands flatness of all `z`-derivatives at `z = 0⁺`,
which the honest data class does not supply (`EpsE4Thr/CoerAdmSlice.lean`; the class-`C` clause of
`EpsDatumP` gives `SmoothOpen`, never `SmoothQuad`).  Hence the frozen barrier cannot be applied on
the route.

This file supplies the repair:

* `coerAdmO_slice_JfamP` — the **open** class `CoerAdmO` of the projected mollified slice, proved
  from `EpsRegP` alone (the class-`C` clause of `EpsDatumP` supplies `SmoothOpen`, `HkMem α 5` and
  `BdryTraces α 5`; the angular and axis clauses come from the defining `if` of `Jeps` and from the
  vanishing of `bump`, exactly as in `CoerAdmSlice.lean`).  No `SmoothQuad` anywhere;
* `apriori_fourth_of_barrier_open` — the barrier with `UnifIPO` in place of the frozen `UnifIP`
  and with the coercivity class **produced** internally, so that the two hypotheses of the original
  (`hcoer`) are gone and only the honest regularity `EpsRegP` remains.

The single analytic obligation that is left is therefore
`UnifIPO (IP4 …) …` — the coercivity of the level-four pairing on the open-quadrant class, which
*is* satisfiable on the route (unlike the frozen `UnifIP`).

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongEps.EpsE4Thr.CoerAdmSlice
import Submission.Work.FTS.StrongEps.EpsStructP
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.EpsGdotThird
import Submission.Work.FTS.Apriori.Barrier

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

/-! ## `CoerAdmO` of the projected mollified slice — *proved*, with no `SmoothQuad` -/

/-- **The open coercivity class of the projected mollified slice**, from the solution's regularity
alone.  This is the exact analogue of `coerAdm_slice_JfamP` with `RegQ` replaced by `RegQo`, i.e.
with the (unavailable) `SmoothQuad` clause deleted.

Everything that is *not* `SmoothQuad` is derived as in `CoerAdmSlice.lean`:

* `L₁₂ x 0 = 0`, `SmoothOpen x`, `HkMem α 5 x`, `BdryTraces α 5 x` are the class-`C` clause of
  `EpsDatumP` at the fake time `τ` (monotonised in the order);
* `VanishTheta x` and the two axis *values* come from the defining `if` of `Jeps` (which vanishes
  off the open quadrant) and from the vanishing of `bump` at `θ = 0, π/2, z = 0`;
* the axis *radial derivative* `pz x 0 θ` is `0` for interior angles by the class-`C` axis
  condition `x z θ / z → 0` (`pz_zero_of_tendsto_div`), and for the two endpoint angles the slice
  is identically zero in `z` (`pz_zero_of_eq_zero`). -/
theorem coerAdmO_slice_JfamP {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε T : ℝ} {g : Fam}
    (hreg : Work.FTS.StrongEps.EpsRegP α ρ ε T g) :
    ∀ τ ∈ Set.Icc (0 : ℝ) T, CoerAdmO α (slice (JfamP ρ ε g) τ) := by
  intro τ hτ
  have hCs : Work.FTS.ClassC.ClassC α (slice (JfamP ρ ε g) τ) := (hreg.2 τ hτ).2.2
  have hmem5 : Work.Spaces.HkMem α 5 (slice (JfamP ρ ε g) τ) :=
    Work.FTS.OpenPkg.HkMem_mono_open hCs.reg 5 (by norm_num) hCs.mem
  have htr5 : Work.FTS.Nonlin.BdryTraces α 5 (slice (JfamP ρ ε g) τ) :=
    fun a b hab => hCs.tr a b (le_trans hab (by norm_num))
  -- the angular vanishing, from the defining `if` of `Jeps` and from `bump`
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
  exact ⟨⟨hCs.reg, hmem5, htr5⟩, ⟨h0, hpi⟩, fun θ hθ => ⟨hz0 θ, hpz0 θ hθ⟩, hCs.l12⟩

/-! ## The level-four barrier in the open class -/

/-- **The level-four barrier of the a-priori estimate, run against the open class.**

The energy `E s = IP α (slice s) (slice s)` starts strictly below the barrier level `Y` and has a
strictly negative within-derivative whenever it meets `Y`; the barrier lemma keeps it below `Y`,
and the *open* comparability clause `UnifIPO.lo` — applicable because `CoerAdmO` is **proved** for
the projected slice by `coerAdmO_slice_JfamP` — turns this into the small-ball bound
`Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ α²`.

Compared with `apriori_fourth_of_barrier` the hypothesis `hcoer`
(`∀ τ, Nonlin.CoerAdm α (slice (JfamP ρ ε g) τ)`, unavailable on the route) is replaced by the
solution's own regularity `EpsRegP`, and `UnifIP` by `UnifIPO`. -/
theorem apriori_fourth_of_barrier_open {α C₀ Y cc clo Cup Ccs α₂ : ℝ}
    {IP : ℝ → Fn → Fn → ℝ}
    {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {ε T T' : ℝ} {g : Fam} {E4' : ℝ → ℝ}
    (hIP : UnifIPO IP α₂ cc clo Cup Ccs) (hα : α ∈ Set.Ioc 0 α₂)
    (hC₀ : 0 < C₀) (hY0 : 0 < Y) (hY : Y ≤ clo * (C₀ * α ^ 2) ^ 2)
    (hreg : Work.FTS.StrongEps.EpsRegP α ρ ε T' g)
    (hcont : ContinuousOn
      (fun s => IP α (slice (JfamP ρ ε g) s) (slice (JfamP ρ ε g) s)) (Set.Icc 0 T'))
    (h0 : IP α (slice (JfamP ρ ε g) 0) (slice (JfamP ρ ε g) 0) < Y)
    (hderiv : ∀ τ ∈ Set.Ico 0 T', HasDerivWithinAt
      (fun s => IP α (slice (JfamP ρ ε g) s) (slice (JfamP ρ ε g) s)) (E4' τ) (Set.Icc 0 T') τ)
    (hneg : ∀ τ ∈ Set.Ico 0 T', IP α (slice (JfamP ρ ε g) τ) (slice (JfamP ρ ε g) τ) = Y →
      E4' τ < 0) :
    ∀ τ ∈ Set.Icc 0 T',
      Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 := by
  have hcoer : ∀ τ ∈ Set.Icc 0 T', CoerAdmO α (slice (JfamP ρ ε g) τ) :=
    coerAdmO_slice_JfamP hreg
  intro τ hτ
  have hbar : IP α (slice (JfamP ρ ε g) τ) (slice (JfamP ρ ε g) τ) ≤ Y :=
    Work.FTS.Apriori.barrier_within
      (E := fun s => IP α (slice (JfamP ρ ε g) s) (slice (JfamP ρ ε g) s))
      (E' := E4') hcont h0 hderiv hneg τ hτ
  have hSq : Work.Spaces.HkSq α 4 (slice (JfamP ρ ε g) τ) ≤ (C₀ * α ^ 2) ^ 2 :=
    le_of_mul_le_mul_left (le_trans (le_trans (hIP.lo α hα _ (hcoer τ hτ)) hbar) hY)
      hIP.pos.2.2.1
  have hZnn : 0 ≤ C₀ * α ^ 2 := by positivity
  have hnorm : Real.sqrt (Work.Spaces.HkSq α 4 (slice (JfamP ρ ε g) τ)) ≤ C₀ * α ^ 2 := by
    have h1 := Real.sqrt_le_sqrt hSq
    rwa [Real.sqrt_sq hZnn] at h1
  simpa [Work.Spaces.HkNorm, Work.FTS.Nonlin.Xn] using hnorm

end Work.FTS.StrongEps.EpsE4Thr
