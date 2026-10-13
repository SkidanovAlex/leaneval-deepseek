/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E5L12Datum.lean` — `EpsDatum` forces `L₁₂(g₀)(0) = 0`

This is the arithmetic that makes the **fourth interface repair** (session 13, `NOTES_session13.md`
§2) cost nothing downstream.

The scheme `∂_τ g = Pz (J_ε (epsWP))` preserves the `L₁₂`-zero mode exactly
(`PZeroAux.Pz_l12`), so the value `L₁₂ (slice g τ)(0)` is *constant in `τ`* and equal to
`L₁₂ g₀ 0`.  When that constant is nonzero the projected family does **not** converge to the
unprojected limit (they differ by a fixed multiple of the correction profile `bump`), which is what
breaks the `bd4` and `limApprox` clauses and, at the `dbd` clause, the conclusion of
`global_strong2` itself.  `EpsUniformMem` therefore has to carry `L₁₂ g₀ 0 = 0`.

The *producer* of `EpsUniformMem` is `EpsUniform_of_data` (E4), whose hypothesis is

  `hd : ∀ ε > 0, EpsDatum α ρ ε g₀`,  `EpsDatum α ρ ε h = SmoothOpen h ∧ HkMem α 6 h ∧
  ClassC α (J_ε h)`,

and the class-`C` clause of `EpsDatum` already contains `l12 : L₁₂ (J_ε h) 0 = 0`
(`ClassC.l12`).  Hence `hd` implies `L₁₂ g₀ 0 = 0` at once, by `L12_Jeps_sub_le`
(`|L₁₂ (J_ε g₀) 0 − L₁₂ g₀ 0| ≤ C ε ‖g₀‖_{ℋ⁵}`) with `ε → 0⁺`:

  `|L₁₂ g₀ 0| ≤ C ε ‖g₀‖_{ℋ⁵}` for every `ε ∈ (0,1]`,  hence `|L₁₂ g₀ 0| ≤ 0`.

So the repair adds **no** hypothesis to `EpsUniform_of_data`, to `EpsUniformMem_of_localStep_apriori`
or to `EpsUniformMem_of_data_lt`: the new conjunct is derived from data they already receive.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.EpsODEDefs
import Submission.Work.FTS.StrongEps.L12_Jeps_sub_le
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **`EpsDatum` forces the vanishing zero mode.**  If the datum `g₀` is a regular datum of the
scheme at every small `ε` (`EpsDatum α ρ ε g₀`, whose class-`C` clause gives
`L₁₂ (J_ε g₀) 0 = 0`), then `L₁₂ g₀ 0 = 0` — the missing conjunct of `EpsUniformMem`. -/
theorem l12_zero_of_epsDatum {α : ℝ} {ρ : ℝ × ℝ → ℝ} {g₀ : Fn}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ)
    (hd : ∀ ε : ℝ, 0 < ε → EpsDatum α ρ ε g₀) :
    Work.Construction.L12 g₀ 0 = 0 := by
  obtain ⟨C, hCpos, hC⟩ := L12_Jeps_sub_le ρ hρ
  have hsm : Work.FTS.EllipticEst.SmoothOpen g₀ := (hd 1 one_pos).1
  have hmem6 : Work.Spaces.HkMem α 6 g₀ := (hd 1 one_pos).2.1
  have hmem5 : Work.Spaces.HkMem α 5 g₀ :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm 5 (by norm_num) hmem6
  -- the bound `|L₁₂ g₀ 0| ≤ C ε ‖g₀‖_{ℋ⁵}` for every `ε ∈ Ioc 0 1`
  have hbound : ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      |Work.Construction.L12 g₀ 0| ≤ C * ε * Work.Spaces.HkNorm α 5 g₀ := by
    intro ε hε
    have hcl : Work.FTS.ClassC.ClassC α (Jeps ρ ε g₀) := (hd ε hε.1).2.2
    have h0 : Work.Construction.L12 (Jeps ρ ε g₀) 0 = 0 := hcl.l12
    have h := hC α hα g₀ hsm hmem5 ε hε
    rw [h0, zero_sub, abs_neg] at h
    exact h
  -- an explicit small `ε` gives the contradiction unless the value is zero
  by_contra hne
  have hpos : 0 < |Work.Construction.L12 g₀ 0| := by
    refine lt_of_le_of_ne (abs_nonneg _) fun h => hne (abs_eq_zero.mp h.symm)
  set N : ℝ := Work.Spaces.HkNorm α 5 g₀ with hN
  have hNnn : 0 ≤ N := Work.Spaces.HkNorm_nonneg α 5 g₀
  set ε : ℝ := min 1 (|Work.Construction.L12 g₀ 0| / (2 * (C * N + 1))) with hεdef
  have hεpos : 0 < ε := lt_min one_pos (div_pos hpos (by positivity))
  have hεle : ε ≤ 1 := min_le_left _ _
  have hlt : C * ε * N < |Work.Construction.L12 g₀ 0| := by
    have hε2 : ε ≤ |Work.Construction.L12 g₀ 0| / (2 * (C * N + 1)) := min_le_right _ _
    have hCN : 0 ≤ C * N := mul_nonneg hCpos.le hNnn
    have hstep : C * ε * N ≤ C * (|Work.Construction.L12 g₀ 0| / (2 * (C * N + 1))) * N :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hε2 hCpos.le) hNnn
    refine lt_of_le_of_lt hstep ?_
    have hden : (2 : ℝ) * (C * N + 1) ≠ 0 := by positivity
    have hEq : C * (|Work.Construction.L12 g₀ 0| / (2 * (C * N + 1))) * N
        = |Work.Construction.L12 g₀ 0| * (C * N / (2 * (C * N + 1))) := by
      field_simp
    rw [hEq]
    have hfrac : C * N / (2 * (C * N + 1)) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    simpa using mul_lt_mul_of_pos_left hfrac hpos
  exact absurd (hbound ε ⟨hεpos, hεle⟩) (not_le.mpr hlt)

end Work.FTS.StrongEps
