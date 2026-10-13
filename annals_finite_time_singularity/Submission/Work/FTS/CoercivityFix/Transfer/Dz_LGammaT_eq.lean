/-
# `Transfer/Dz_LGammaT_eq.lean` — the `D_z`-identity of the transfer

`𝓛_Γ^T f = 𝓛̂ f + Corr α f` (`CoercivityFix.LGammaT_eq_Lhat_add_Corr`), and `Corr` is the
angular factor `Γ(θ)` times the **radial** profile `radA α f z` (`Corr_eq_radA`).  Hence the
`D_z`-derivative splits into

* the clean operator's commutator `D_z(𝓛̂ f) = 𝓛̂(D_z f) + Ê₂ f`
  (`LhatCalc.Dz_Lhat`, proved), where `Ê₂ f = (2zf + 3zD_θf)/(1+z)²` is an *explicit bounded*
  function with no nonlocal term, and
* the differentiated transfer `D_z(Corr α f) z θ = Γ(θ)·radS α f z`, where
  `radS α f = z·(radA α f)'` is the radial profile of `Profiles.lean` (definitionally: the
  `z`-weighted derivative of `radA`, i.e. `−z(ampA)'·L₁₂f − ampA·z(L₁₂f)' + (z(ampB)'/c)·C₀ f`).

Since `D_z` falls on the radial factor only, the nonlocal term `L₁₂` is **not** differentiated in
the wrong slot: `z·(L₁₂ f)'` is an angular moment of `f`, not an `L₁₂` of a differentiated datum
(`Transfer.L12_deriv_eq`), which is exactly the design point T2 of `N45_DESIGN_LEAD.md` §5.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.CoercivityFix.Transfer.hasDerivAt_radA
import Submission.Work.FTS.CoercivityFix.Transfer.differentiableAt_Lhat_slice
import Submission.Work.FTS.CoercivityFix.LhatCalc.Dz_Lhat
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.Vocab

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

set_option autoImplicit false

/-! ## The `z`-derivative of the transfer defect `Corr` -/

/-- The `z`-slice of the transfer defect `Corr`: since `Corr α f z θ = Γ(θ)·radA α f z`
(`Corr_eq_radA`), differentiating in `z` multiplies the radial derivative by `Γ(θ)`.
The derivative of `radA` is `radS/z` (`Transfer.hasDerivAt_radA`). -/
theorem hasDerivAt_Corr_slice (α : ℝ) (f : ℝ → ℝ → ℝ) (hfH : Work.Coercivity.HardyHyp f)
    {z θ : ℝ} (hz : 0 < z) :
    HasDerivAt (fun t => Work.FTS.CoercivityFix.Corr α f t θ)
      (Work.Spaces.Gam α θ * (radS α f z / z)) z :=
  ((hasDerivAt_radA α f hfH hz).const_mul (Work.Spaces.Gam α θ)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun t => by
      simpa using Corr_eq_radA α f t θ))

/-- **The `D_z`-commutator of the transfer defect.**
With `Corr α f = Γ(θ)·radA α f z` and `radS α f z = z·∂_z(radA α f) z`, the `z`-derivative of
`Corr` is `Γ(θ)·radS α f z` — no `L₁₂` of a differentiated datum appears. -/
theorem Dz_Corr_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (hfH : Work.Coercivity.HardyHyp f) {z θ : ℝ}
    (hz : 0 < z) :
    Work.Spaces.Dz (Work.FTS.CoercivityFix.Corr α f) z θ
      = Work.Spaces.Gam α θ * radS α f z := by
  have h := hasDerivAt_Corr_slice (z := z) (θ := θ) α f hfH hz
  have hz0 : z ≠ 0 := ne_of_gt hz
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [h.deriv]
  field_simp

/-! ## The `D_z`-identity of the transfer -/

/-- **The `D_z`-commutator of the paper's operator `𝓛_Γ^T`.**

`D_z(𝓛_Γ^T f) = 𝓛̂(D_z f) + E₂ α f`, with the transfer defect
`E₂ α f = Ê₂ f + Γ(θ)·radS α f z`:

* `Ê₂ f = (2zf + 3zD_θf)/(1+z)²` is the `D_z`-commutator of the clean operator `𝓛̂` (explicit,
  bounded, `α`-free: `E2hat_abs_le`), and
* `Γ·radS` is the transfer defect produced by the nonlocal/projector terms, whose
  `z`-derivative falls on the **radial** factor only (`Dz_Corr_eq`).

This is the `D_z`-half of the split `𝓛_Γ^T = 𝓛̂ + Corr` of `N45_DESIGN_LEAD.md` §3.1/§5 T2,
the counterpart of `Dth_LGammaT_eq`. -/
theorem Dz_LGammaT_eq (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.LocData.SmoothQuad f) (hfH : Work.Coercivity.HardyHyp f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Spaces.Dz (Work.Coercivity.LGammaT α f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
        + Work.FTS.CoercivityFix.Transfer.E2 α f z θ := by
  -- the two halves of the decomposition `𝓛_Γ^T = 𝓛̂ + Corr`
  have hdiffL : DifferentiableAt ℝ (fun t => Work.FTS.CoercivityFix.Lhat f t θ) z :=
    differentiableAt_Lhat_slice hsm hz hθ hθ2
  have hhasC := hasDerivAt_Corr_slice (z := z) (θ := θ) α f hfH hz
  have hdiffC : DifferentiableAt ℝ (fun t => Work.FTS.CoercivityFix.Corr α f t θ) z :=
    hhasC.differentiableAt
  -- the clean operator's commutator
  have hL : z * deriv (fun t => Work.FTS.CoercivityFix.Lhat f t θ) z
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
        + Work.FTS.CoercivityFix.E2hat f z θ :=
    Work.FTS.CoercivityFix.LhatCalc.Dz_Lhat hsm hz hθ hθ2
  -- the transfer defect's commutator
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hC : z * deriv (fun t => Work.FTS.CoercivityFix.Corr α f t θ) z
      = Work.Spaces.Gam α θ * radS α f z := by
    rw [hhasC.deriv]
    field_simp
  -- the slices add, so the derivatives add
  have hslice : (fun t => Work.Coercivity.LGammaT α f t θ)
      = (fun t => Work.FTS.CoercivityFix.Lhat f t θ)
        + (fun t => Work.FTS.CoercivityFix.Corr α f t θ) := by
    funext t
    rw [Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr]
    rfl
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [hslice, deriv_add hdiffL hdiffC, mul_add, hL, hC,
    Work.FTS.CoercivityFix.Transfer.E2_eq]
  ring

end Work.FTS.CoercivityFix.Transfer
