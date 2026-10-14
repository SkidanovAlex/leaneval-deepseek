import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.FTS.EpsEngine.mixed_logCoords
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop

set_option autoImplicit false

/-!
# `Prop.l0_first` — the first-order `Ψ`- and `Ψ/cos θ`-estimates in the weak class

The target is the pair of *first-order* conclusions of the elliptic chapter of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the incompressible
  Euler equations on `ℝ³`*, Annals of Math. **194** (2021),

at level `0` and in the weak hypothesis class `Work.FTS.EllipticEst.TT.EllWeakPos`: for every
datum of that class (`bslOp α Ψ = F` on the open quadrant, Dirichlet data, `C^∞` on the open
quadrant, the two pointwise moment conditions, and the `ℋ⁰`-honesty of `F`, `z²∂_zzΨ`, `∂_θθΨ`),

  `HkMem α 0 Ψ`, `HkMem α 0 (Ψ/cos θ)`, `√(HkSq α 0 Ψ) ≤ C√(HkSq α 0 F)`,
  `√(HkSq α 0 (Ψ/cos θ)) ≤ C√(HkSq α 0 F)`,

with `C` universal in `α ∈ (0,1/4]`.

## The route

`EllWeakPos α 0 F Ψ` implies the almost-everywhere class `H2W.Ae.AeData α Ψ F`
(`Prop.l0_bridge.aeData_of_ellWeakPos`: the only difference between the two classes is that the
moment conditions of `EllWeakPos` are pointwise while those of `AeData` are a.e.).

All the analysis is then the *proved* Step 1 of `prop:H2`
(`Work.FTS.EllipticEst.remov.AeStep1FullHolds : remov.AeStep1Full`), which in the class
`AeData α u G` supplies

* the three `ℋ⁰`-honesties `HkMem α 0 u`, `HkMem α 0 (z∂_zu)`, `HkMem α 0 (u/cos θ)`;
* the mass bound `‖u‖_ρ ≤ C‖G‖_ρ`;
* the radial first-order bound `α‖z∂_zu‖_ρ ≤ C‖G‖_ρ`;
* the first-order bound for the quotient, `‖u/cos θ‖_ρ ≤ C(‖G‖_ρ + α‖z∂_zu‖_ρ)`,

where `‖g‖_ρ = H2W.Ae.nrm α g = √(HkSq α 0 g)`.

Everything after that is arithmetic with square roots: `‖u‖_ρ ≤ C‖G‖_ρ` and
`‖u/cos θ‖_ρ ≤ C(‖G‖_ρ + α‖z∂_zu‖_ρ) ≤ C(1 + C)‖G‖_ρ`, so the single universal constant
`C(1+C) + 1` serves for both conclusions.

Note that the *first-order* `u/cos θ` bound of `AeStep1Full` is what is used here — it comes from
pairing `bslOp α u = G` against `u·w²σ` (the `sec²θ`-slot of that pairing), so neither the
angular second-order estimate (Step 2) nor the deep coercivity input `I₁` is needed for
`l0_first`.
-/

theorem l0_first : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
      Work.Spaces.HkMem α 0 Ψ ∧
      Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) ∧
      Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
        ≤ C * Real.sqrt (Work.Spaces.HkSq α 0 F) ∧
      Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ))
        ≤ C * Real.sqrt (Work.Spaces.HkSq α 0 F) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.remov.AeStep1FullHolds
  refine ⟨C * (1 + C) + 1, by positivity, ?_⟩
  intro α F Ψ hα hα4 hweak
  -- the weak class is the a.e. class
  have hA : Work.FTS.EllipticEst.H2W.Ae.AeData α Ψ F :=
    aeData_of_ellWeakPos hα hα4 hweak
  -- Step 1 of `prop:H2`, in the a.e. class
  obtain ⟨hmu, _hmU, hmb, hu, hU, hbar⟩ := hC α Ψ F hA
  have hF0 : 0 ≤ Work.FTS.EllipticEst.H2W.Ae.nrm α F := Real.sqrt_nonneg _
  have hC0 : 0 ≤ C := le_of_lt hCpos
  -- the `Ψ`-half: `nrm Ψ ≤ C nrm F ≤ (C(1+C)+1) nrm F`
  have h1 : Work.FTS.EllipticEst.H2W.Ae.nrm α Ψ
      ≤ (C * (1 + C) + 1) * Work.FTS.EllipticEst.H2W.Ae.nrm α F :=
    calc Work.FTS.EllipticEst.H2W.Ae.nrm α Ψ
        ≤ C * Work.FTS.EllipticEst.H2W.Ae.nrm α F := hu
      _ ≤ (C * (1 + C) + 1) * Work.FTS.EllipticEst.H2W.Ae.nrm α F :=
          mul_le_mul_of_nonneg_right (by nlinarith [hCpos]) hF0
  -- the `Ψ/cos θ`-half: absorb the radial term with `α nrm (grad Ψ) ≤ C nrm F`
  have h2 : Work.FTS.EllipticEst.H2W.Ae.nrm α (fun z θ => Ψ z θ / Real.cos θ)
      ≤ (C * (1 + C) + 1) * Work.FTS.EllipticEst.H2W.Ae.nrm α F :=
    calc Work.FTS.EllipticEst.H2W.Ae.nrm α (fun z θ => Ψ z θ / Real.cos θ)
        ≤ C * (Work.FTS.EllipticEst.H2W.Ae.nrm α F
            + α * Work.FTS.EllipticEst.H2W.Ae.nrm α
                (Work.FTS.EllipticEst.H2W.Ae.grad Ψ)) := hbar
      _ ≤ C * (Work.FTS.EllipticEst.H2W.Ae.nrm α F
            + C * Work.FTS.EllipticEst.H2W.Ae.nrm α F) :=
          mul_le_mul_of_nonneg_left (by linarith) hC0
      _ = (C * (1 + C)) * Work.FTS.EllipticEst.H2W.Ae.nrm α F := by ring
      _ ≤ (C * (1 + C) + 1) * Work.FTS.EllipticEst.H2W.Ae.nrm α F :=
          mul_le_mul_of_nonneg_right (by nlinarith [hCpos]) hF0
  exact ⟨hmu, hmb, by simpa only [Work.FTS.EllipticEst.H2W.Ae.nrm] using h1,
    by simpa only [Work.FTS.EllipticEst.H2W.Ae.nrm] using h2⟩

end Work.FTS.EllipticEst.Prop
