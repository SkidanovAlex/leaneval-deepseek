/-
Copyright: work module for the Elgindi finite-time singularity project.

# `TT.gammaHonesty` — the `σ_{2-γ}`-honesty of the `(1,1)`-slot of `A = z²∂_z²Ψ`

The target is the `hγ` input of `Work.FTS.EllipticEst.TT.aShiftSlot_le` (see
`Submission/Work/FTS/EllipticEst/TT/aShiftSlotReduction.lean`, hypothesis `hγ`): for every datum
of the weak class `EllWeakPos α 2 F Ψ` and every `0 < α ≤ 1/4`, the outer integrating function

  `z ↦ ∫_θ (D_z∂_θ A)² · w² · sin(2θ)^{2-γ}`,  `A := Aof Ψ = z²∂_z²Ψ`,

is honest (`IntegrableOn` on `Iz`).

## The proof

The function is *pointwise equal* to the outer integral of the `(1,1)`-slot of `A`, which is a
summand of the `ℋ²`-integrand of `A`:

* `TT.slot11_sq_eq` (proved with the aShift workstream) gives, for `θ ∈ Iθ`,
  `(mixed 1 1 A · Wt α)² = (D_z∂_θ A · sin(2θ)^{(2-γ)/2} · w)²`, and
  `(sin(2θ)^{(2-γ)/2})² = sin(2θ)^{2-γ}` turns the right-hand side into the target integrand;
* `mixed 1 1 A · Wt α` is continuous on the open quadrant (it is `D_z∂_θ` of the `SmoothOpen`
  function `A`) and its square is dominated by `HkIntegrand α 2 A` (the slot `(i,j) = (1,1)`,
  `TT.sq_le_HkIntegrand_mixed`), so `H2W.i2Mem_sq_of_le` — the standard "extract a summand of
  `HkMem`" lemma — makes its iterated integral honest.

Note that no hypothesis on `F` is used: the honesty of the slot comes from the certificate
`HkMem α 2 (Aof Ψ)` carried by `EllWeakPos` (`EllWeakPos.memA`).

The file is complete: both declarations below have honest proofs.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.aShiftSlotAux
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.H2W.Level0ADefs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.H2W.AeDataAof
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.H2W.hksqSplitAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

open MeasureTheory Set Filter

/-- **The pointwise identification of the target integrand with the `(1,1)`-slot of `A`.**
For `θ ∈ Iθ` the integrand `(D_z∂_θA)²·w²·sin(2θ)^{2-γ}` of the target equals the square of the
weighted slot `mixed 1 1 A · Wt α`.  (`Wt α = w · sin(2θ)^{-γ/2}`, so
`(mixed 1 1 A · Wt α)² = (D_z∂_θA · w · sin(2θ)^{1-γ/2})² = (D_z∂_θA)²·w²·sin(2θ)^{2-γ}`.) -/
theorem gammaHonesty_integrand_eq_slot11 (α : ℝ) (A : ℝ → ℝ → ℝ)
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Dz (Work.Spaces.pth A) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      = (Work.Spaces.mixed 1 1 A z θ * Work.Spaces.Wt α z θ) ^ 2 := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have h1 : (Real.sin (2 * θ) ^ ((2 - Work.Spaces.gam α) / 2)) ^ (2 : ℕ)
      = Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α) := by
    rw [rpow_sq_eq hs]
    ring
  rw [slot11_sq_eq α A hα hα4 hθ, ← h1]
  ring

theorem gammaHonesty {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Aof Ψ)) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iz := by
  -- `Ψ` and `A = z²∂_z²Ψ` are `C^∞` on the open quadrant, and `A` is honest in `ℋ²`.
  have hΨsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllipticEst.H2W.Aof Ψ) :=
    Work.FTS.EllipticEst.H2W.AeDataAofAux.smoothOpen_zsq_mul (hΨsm.pzIter 2)
  have hmemA : Work.Spaces.HkMem α 2 (Work.FTS.EllipticEst.H2W.Aof Ψ) := h.memA
  -- the weighted `(1,1)`-slot is continuous on the open quadrant …
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed 1 1 (Work.FTS.EllipticEst.H2W.Aof Ψ) p.1 p.2
        * Work.Spaces.Wt α p.1 p.2) ^ 2) Work.FTS.EllipticEst.Q0 :=
    (((hAsm.mixed 1 1).continuousOn).mul (Work.FTS.EllipticEst.continuousOn_Wt_Q0 α)).pow 2
  -- … and its iterated integral is honest, being a summand of the `ℋ²`-integrand of `A`.
  have hI2 : Work.Coercivity.I2Mem (fun z θ =>
      (Work.Spaces.mixed 1 1 (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ
        * Work.Spaces.Wt α z θ) ^ 2) :=
    Work.FTS.EllipticEst.H2W.i2Mem_sq_of_le (f := Work.FTS.EllipticEst.H2W.Aof Ψ) hmemA hcont
      (fun z hz θ hθ =>
        Work.Spaces.sq_le_HkIntegrand_mixed α 2 (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ 1 1
          le_rfl (by norm_num))
  -- the target function is the outer integral of the slot, pointwise.
  have hcongr : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Aof Ψ)) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      = fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed 1 1 (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 := by
    funext z
    exact MeasureTheory.setIntegral_congr_fun
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
      (fun θ hθ => gammaHonesty_integrand_eq_slot11 α (Work.FTS.EllipticEst.H2W.Aof Ψ)
        hα hα4 hθ)
  rw [hcongr]
  exact hI2.2

end Work.FTS.EllipticEst.TT
