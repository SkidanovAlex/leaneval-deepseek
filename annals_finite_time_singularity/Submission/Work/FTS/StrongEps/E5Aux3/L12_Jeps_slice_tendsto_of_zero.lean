/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E5Aux3/L12_Jeps_slice_tendsto_of_zero.lean`

**`hl12` is exactly the mollifier error, once the unmollified zero mode vanishes.**

The E5 assembly's linchpin (`NOTES_session16.md` §2, `NOTES_session17.md` §2) is

    hl12 s :  Tendsto (fun k => L₁₂ (J_{ε k} (slice (G k) s)) 0) atTop (nhds 0)

It is a *consequence* of two facts about the plain slices `X k := slice (G k) s`:

* **the unmollified zero mode vanishes**, `L₁₂ (X k) 0 = 0` (for the scheme's solutions this is the
  conservation identity `L₁₂ (slice g τ) 0 = L₁₂ g₀ 0 = 0`, proved by differentiating under the
  integral: `E5Aux3.hasDerivWithinAt_L12_slice_of_majorant` + `PZeroAux.Pz_l12` + `pzNorm_pos`);
* **the mollifier error** `|L₁₂ (J_ε X) 0 − L₁₂ X 0| ≤ C ε ‖X‖_{ℋ⁵}`
  (`Work.FTS.StrongEps.L12_Jeps_sub_le`, proved).

This module records the second step in the shape the assembly consumes: unlike the sibling
`E5Aux3.hl12_of_classC` (which *derives* `L₁₂ X k 0 = 0` from `ClassC.l12`), it takes the vanishing
as a hypothesis, together with the `SmoothOpen`/`ℋ⁵`-data that the interface supplies for the
*plain* slices (`SmoothOpen (slice g τ)` is a conjunct of `EpsUniformMem`; `HkMem α 5` follows from
the interface's `HkMem α 6`, and `HkNorm α 5 ≤ HkNorm α 6` from monotonicity of the integrand).
This is the form in which `hl12` is assembled — the plain slices are *not* in class `C`.
-/
import Mathlib.Topology.Algebra.Ring.Real
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.L12_Jeps_sub_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux3

set_option autoImplicit false

/-- **`hl12` from the vanishing of the unmollified zero mode.**  For a sequence of profiles `X k`
which are `SmoothOpen` with honest `ℋ⁵`-membership and a common `ℋ⁵`-bound `B`, and whose
`L₁₂`-zero mode vanishes, the zero modes of the mollified profiles `J_{ε k} X k` tend to `0`
along any sequence `ε k ∈ (0,1]` with `ε k → 0`. -/
theorem L12_Jeps_slice_tendsto_of_zero {α B : ℝ} {ρ : ℝ × ℝ → ℝ} {ε : ℕ → ℝ}
    {X : ℕ → Work.FTS.Galerkin.Fn}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1)
    (hε : ∀ k : ℕ, ε k ∈ Set.Ioc 0 1)
    (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hsm : ∀ k : ℕ, Work.FTS.EllipticEst.SmoothOpen (X k))
    (hmem : ∀ k : ℕ, Work.Spaces.HkMem α 5 (X k))
    (hB : ∀ k : ℕ, Work.Spaces.HkNorm α 5 (X k) ≤ B)
    (h0 : ∀ k : ℕ, Work.Construction.L12 (X k) 0 = 0) :
    Filter.Tendsto (fun k : ℕ =>
        Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ (ε k) (X k)) 0)
      Filter.atTop (nhds 0) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongEps.L12_Jeps_sub_le ρ hρ
  have hmain : ∀ k : ℕ,
      |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ (ε k) (X k)) 0| ≤ (C * B) * ε k := by
    intro k
    have h := hC α hα (X k) (hsm k) (hmem k) (ε k) (hε k)
    rw [h0 k, sub_zero] at h
    calc |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ (ε k) (X k)) 0|
        ≤ C * ε k * Work.Spaces.HkNorm α 5 (X k) := h
      _ ≤ C * ε k * B :=
          mul_le_mul_of_nonneg_left (hB k) (le_of_lt (mul_pos hCpos (hε k).1))
      _ = (C * B) * ε k := by ring
  have habs : Filter.Tendsto
      (fun k : ℕ => |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ (ε k) (X k)) 0|)
      Filter.atTop (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      (Filter.Eventually.of_forall hmain) (by simpa using hε0.const_mul (C * B))
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr (by simpa [Function.comp_def] using habs)

end Work.FTS.StrongEps.E5Aux3
