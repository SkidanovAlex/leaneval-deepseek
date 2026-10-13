/-
Copyright: work module for the Elgindi finite-time singularity project.

# `TT.weakGradBound2` — Step 1 for `z ∂_zΨ` in the weak class, from the a.e.-class machinery

The statement (`∃C > 0`, all `0 < α ≤ 1/4` and all weak data `Ψ`):

  `HkMem α 0 (z ∂_zΨ) ∧ α·√(HkSq α 0 (z∂_zΨ)) ≤ C·√(HkSq α 0 F)`.

This is the `G = z∂_zΨ`-half of Step 1 of Proposition `prop:H2` (Elgindi, Annals **194** (2021)),
needed by the assembly `TT.l2eta_weak_of_pieces`.

## Route

`TT.EllWeakPos α 0 F Ψ` is `H2W.Ae.AeData α Ψ F` (`Final.aeData_of_ellWeakPos'`, the two
solvability conditions being weakened from "for all `z`" to "for a.e. `z > 0`"), so the whole
almost-everywhere chapter applies:

* `AngAWeak.hkMem_grad_of` — the honesty `HkMem α 0 (z∂_zΨ)` from `AeData` (the radial
  Agmon–Nirenberg interpolation of `HkMem α 0 Ψ` and `HkMem α 0 (z²∂²Ψ)`);
* `Cores.AeStep2Aux.aeUHk_mem` — `HkMem α 0 Ψ`;
* `Cores.AeStep2Aux.aeUHk_bnd` — the `u`-half of Step 1, `‖Ψ‖_ρ ≤ C‖F‖_ρ`;
* `Dispatch.aeSigmaEnergyD` — the `σ`-weighted radial inequality
  `α²‖z∂_zΨ‖²_ρ ≤ C(‖F‖²_ρ + ‖Ψ‖²_ρ)`,

which combine into `α²‖z∂_zΨ‖²_ρ ≤ C(1 + C'²)‖F‖²_ρ`, i.e. the stated bound.  Every module in
the import cone of this file is `sorry`-free, so the result is axiom-clean
(`[propext, Classical.choice, Quot.sound]`).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Dispatch.aeSigmaEnergyD
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.aeUHk_mem
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.aeUHk_bnd
import Submission.Work.FTS.EllipticEst.AngAWeak.step1Ae
import Submission.Work.FTS.EllipticEst.Final.AeSigmaUpD

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-- **Step 1 for `z ∂_zΨ` in the weak class.** -/
theorem weakGradBound2 : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
      Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) ∧
      α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))
        ≤ C * Real.sqrt (Work.Spaces.HkSq α 0 F) := by
  obtain ⟨C₁, hC₁, hE⟩ := Work.FTS.EllipticEst.Dispatch.aeSigmaEnergyD
  obtain ⟨C₂, hC₂, hU⟩ := Work.FTS.EllipticEst.Cores.AeStep2Aux.aeUHk_bnd
  refine ⟨Real.sqrt (C₁ * (1 + C₂ ^ 2)) + 1, by positivity, ?_⟩
  intro α F Ψ hα hα4 hW
  have hA : Work.FTS.EllipticEst.H2W.Ae.AeData α Ψ F :=
    Work.FTS.EllipticEst.Final.aeData_of_ellWeakPos' hα hα4 hW
  have hF0 : 0 ≤ Work.Spaces.HkSq α 0 F := Work.Spaces.HkSq_nonneg α 0 F
  have hG0 : 0 ≤ Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad Ψ) :=
    Work.Spaces.HkSq_nonneg α 0 _
  -- the energy inequality and the `u`-half of Step 1
  obtain ⟨-, hE'⟩ := hE α Ψ F hA
  have hUm : Work.Spaces.HkMem α 0 Ψ :=
    Work.FTS.EllipticEst.Cores.AeStep2Aux.aeUHk_mem α Ψ F hA
  have hUn : Work.FTS.EllipticEst.H2W.Ae.nrm α Ψ
      ≤ C₂ * Work.FTS.EllipticEst.H2W.Ae.nrm α F := hU α Ψ F hA hUm
  have hΨsq : Work.Spaces.HkSq α 0 Ψ ≤ C₂ ^ 2 * Work.Spaces.HkSq α 0 F := by
    have h1 : (Work.FTS.EllipticEst.H2W.Ae.nrm α Ψ) ^ 2
        ≤ (C₂ * Work.FTS.EllipticEst.H2W.Ae.nrm α F) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hUn 2
    rw [Work.FTS.EllipticEst.H2W.Ae.nrm,
      Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 0 Ψ), mul_pow,
      Work.FTS.EllipticEst.H2W.Ae.nrm,
      Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 0 F)] at h1
    exact h1
  refine ⟨Work.FTS.EllipticEst.AngAWeak.hkMem_grad_of hA, ?_⟩
  -- the squared bound
  have hsq : α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad Ψ)
      ≤ C₁ * (1 + C₂ ^ 2) * Work.Spaces.HkSq α 0 F := by
    have h1 : C₁ * (Work.Spaces.HkSq α 0 F + Work.Spaces.HkSq α 0 Ψ)
        ≤ C₁ * (Work.Spaces.HkSq α 0 F + C₂ ^ 2 * Work.Spaces.HkSq α 0 F) := by
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC₁)
      linarith [hΨsq]
    have h2 : C₁ * (Work.Spaces.HkSq α 0 F + C₂ ^ 2 * Work.Spaces.HkSq α 0 F)
        = C₁ * (1 + C₂ ^ 2) * Work.Spaces.HkSq α 0 F := by ring
    linarith [hE', h1, h2]
  -- take square roots
  have hleft : (α * Real.sqrt (Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad Ψ))) ^ 2
      ≤ (Real.sqrt (C₁ * (1 + C₂ ^ 2)) * Real.sqrt (Work.Spaces.HkSq α 0 F)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hG0, mul_pow, Real.sq_sqrt (by positivity)]
    rw [Real.sq_sqrt hF0]
    exact hsq
  have hnon : 0 ≤ Real.sqrt (C₁ * (1 + C₂ ^ 2)) * Real.sqrt (Work.Spaces.HkSq α 0 F) := by
    positivity
  have hle : α * Real.sqrt (Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad Ψ))
      ≤ Real.sqrt (C₁ * (1 + C₂ ^ 2)) * Real.sqrt (Work.Spaces.HkSq α 0 F) := by
    have h1 : |α * Real.sqrt (Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad Ψ))|
        ≤ |Real.sqrt (C₁ * (1 + C₂ ^ 2)) * Real.sqrt (Work.Spaces.HkSq α 0 F)| :=
      sq_le_sq.mp hleft
    rwa [abs_of_nonneg (mul_nonneg (le_of_lt hα) (Real.sqrt_nonneg _)),
      abs_of_nonneg hnon] at h1
  calc α * Real.sqrt (Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad Ψ))
      ≤ Real.sqrt (C₁ * (1 + C₂ ^ 2)) * Real.sqrt (Work.Spaces.HkSq α 0 F) := hle
    _ ≤ (Real.sqrt (C₁ * (1 + C₂ ^ 2)) + 1) * Real.sqrt (Work.Spaces.HkSq α 0 F) := by
        have h3 : (0 : ℝ) ≤ Real.sqrt (Work.Spaces.HkSq α 0 F) := Real.sqrt_nonneg _
        nlinarith [hnon, h3]

end Work.FTS.EllipticEst.TT
