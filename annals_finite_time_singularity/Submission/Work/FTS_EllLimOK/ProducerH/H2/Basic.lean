/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.ProducerH.H2.Basic` — the shared vocabulary of the box-`C²` chapter

This module fixes

* `Ctx α Ce E` — the standing hypothesis of the L3 producer `pkgBoxH_of_ellClassOk`: the
  level-`8` existence class together with the two frozen packages, for **every** `g` of the
  source class `ClassC α`;
* `mm θ = min θ (π/2 - θ)` — the angular distance to the nearer endpoint, the natural rate
  variable of the boundary Schauder analysis;
* a few elementary facts about `mm`, `Xn6` and `π`.

Nothing here is specific to the elliptic equation.
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_EllLimOK.RulingELF

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.H2

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The standing hypothesis** of the L3 producer: for every class-`C` profile `g` the
operator `E` produces a stream function `Ψ = E g` carrying the level-`8` existence class and
the two frozen packages (at the given constants `α`, `Ce`). -/
abbrev Ctx (α Ce : ℝ) (E : Fn →ₗ[ℝ] Fn) : Prop :=
  ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
    Work.FTS.EllExist.EllClassOk 8 α g (E g) ∧
      Work.FTS.VocabO.EllPkgGo α Ce g (E g) ∧
      Work.FTS.ClassC.EllPkgK α 6 Ce g (E g)

/-- The angular distance `mm θ = min θ (π/2 - θ)` to the nearer endpoint. -/
def mm (θ : ℝ) : ℝ := min θ (π / 2 - θ)

theorem mm_nonneg {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (π / 2)) : 0 ≤ mm θ :=
  le_min hθ.1 (by linarith [hθ.2])

theorem mm_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) : 0 < mm θ :=
  lt_min hθ.1 (by linarith [hθ.2])

theorem mm_le_theta (θ : ℝ) : mm θ ≤ θ := min_le_left _ _

theorem mm_le_pi_sub (θ : ℝ) : mm θ ≤ π / 2 - θ := min_le_right _ _

theorem mm_le_one {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (π / 2)) : mm θ ≤ 1 := by
  have hπ : π / 2 ≤ 1 ∨ True := Or.inr trivial
  rcases le_total θ (π / 2 - θ) with h | h
  · rw [mm, min_eq_left h]
    nlinarith [hθ.2, Real.pi_lt_four]
  · rw [mm, min_eq_right h]
    nlinarith [Real.pi_lt_four]

/-- `mm θ ≤ mm θ ^ β` for `β ≤ 1` and `θ ∈ (0,π/2)` (the min is at most `1`). -/
theorem self_le_mm_rpow {β θ : ℝ} (hβ : β ≤ 1) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    mm θ ≤ mm θ ^ β := by
  have h0 : 0 < mm θ := mm_pos hθ
  have h1 : mm θ ≤ 1 := mm_le_one ⟨hθ.1.le, hθ.2.le⟩
  calc mm θ = mm θ ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ mm θ ^ β := Real.rpow_le_rpow_of_exponent_ge h0 h1 hβ

theorem Xn6_nonneg (α : ℝ) (g : Fn) : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g :=
  Work.Spaces.HkNorm_nonneg α 6 g

end Work.FTS_EllLimOK.ProducerH.H2
