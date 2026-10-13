/-
# `Work.FTS.EllSol.EllPkgAux.MollFatouAux` — vocabulary of the Fatou step

Shared definitions used by the proof of `mollFatou` and by the auxiliary lemmas about the
double mollification `Φ := zmoll G δ ε`:

* `tseq n = 1/(n+2)` — the diagonal sequence of parameters (all in `Params`, tending to `0`);
* `sKerd ε = deriv (sKer ε)` — the derivative kernel;
* `Hxyc G t s = Qext G (exp t) s` — the (uncurried) integrand of the double mollification,
  written in the logarithmic variable;
* `E2s G w = ∫_θ (∂_θ²G(w,θ))² σ_η` — the (unweighted) angular slice energy;
* `MGf G w` — the dominating function of the slice: it bounds `|G w θ|` for all
  `θ ∈ (0,π/2)` and is locally integrable in `w` (from the `ttIntS` integrability).

Nothing here is a statement of the target.
-/
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false

/-- The diagonal sequence of mollification parameters, `tₙ = 1/(n+2) ∈ (0, 1/2]`. -/
def tseq (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

theorem tseq_pos (n : ℕ) : 0 < tseq n := by
  simp only [tseq]
  positivity

theorem tseq_le_half (n : ℕ) : tseq n ≤ 1 / 2 := by
  rw [tseq, ← sub_nonpos]
  have hkey : (1:ℝ) / ((n:ℝ) + 2) - 1/2 = (2 - ((n:ℝ) + 2)) / (2*((n:ℝ)+2)) := by
    field_simp
  rw [hkey]
  have hn : (0:ℝ) ≤ (n:ℝ) := by positivity
  have h2 : (2:ℝ) - ((n:ℝ)+2) ≤ 0 := by linarith
  have h1 : (0:ℝ) ≤ 2*((n:ℝ)+2) := by linarith
  exact div_nonpos_of_nonpos_of_nonneg h2 h1

theorem tendsto_tseq : Tendsto tseq atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have h : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ht
  change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0)
  simpa only [one_div] using h

theorem params_tseq (n : ℕ) : Params (tseq n) (tseq n) :=
  ⟨tseq_pos n, tseq_le_half n, tseq_pos n, tseq_le_half n⟩

/-- The derivative of the mollifying kernel. -/
def sKerd (ε : ℝ) : ℝ → ℝ := deriv (Work.FTS.EllSol.PkgK5.K5c.sKer ε)

/-- The (uncurried, logarithmic-variable) integrand of the double mollification. -/
def Hxyc (G : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t s => Work.FTS.EllSol.PkgK5.K5c.Qext G (Real.exp t) s

/-- The unweighted angular slice energy `∫_{Iθ} (∂_θ²G(w,·))² σ_η`. -/
def E2s (G : ℝ → ℝ → ℝ) (w : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2
    * Work.FTS.EllipticEst.thEta θ

/-- **The dominating function of the angular slice of `G`.**  It is built from the interior
values of `G` and `∂_θG` at `θ = π/4` (continuous, hence locally bounded, in `w`) and from the
square root of the slice energy (locally integrable in `w` by the `ttIntS` integrability
hypothesis). -/
def MGf (G : ℝ → ℝ → ℝ) (w : ℝ) : ℝ :=
  1 + |G w (Real.pi / 4)| + |Work.Spaces.pth G w (Real.pi / 4)| + Real.sqrt (E2s G w)

/-- `sKer` is smooth. -/
theorem contDiff_sKer (ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (Work.FTS.EllSol.PkgK5.K5c.sKer ε) := by
  have hfun : Work.FTS.EllSol.PkgK5.K5c.sKer ε
      = fun t : ℝ => (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
          * Real.smoothTransition (1 - t ^ 2 / ε ^ 2) := by
    funext t
    simp only [Work.FTS.EllSol.PkgK5.K5c.sKer, Work.FTS.EllSol.PkgK5.K5c.sBump]
    rw [show t / ε = ε⁻¹ * t by rw [div_eq_inv_mul]]
    rw [show 1 - (ε⁻¹ * t) ^ 2 = 1 - t ^ 2 / ε ^ 2 by field_simp]
  rw [hfun]
  fun_prop

end Work.FTS.EllSol.EllPkgAux
