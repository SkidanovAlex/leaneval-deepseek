/-
Copyright: work module for the Elgindi finite-time singularity project.

# `ProfRHSAux/L12Add` — additivity of `L₁₂` over `F = F_* + W`

`L₁₂(F_* + W) = L₁₂(F_*) + L₁₂(W)` as functions of `z` for `z ≥ 0` (the two densities are
integrable there), and the resulting pointwise decomposition of the stream function
`PhiTil α (Ftot α W) Φ` into its star and elliptic parts.
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Construction.Defs
import Submission.Work.FTS.LocData.L12_add_mul
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn
import Submission.Work.Stability.L12Add
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.ProfRHSAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Additivity of `L₁₂` over `F = F_* + W` -/

/-- **`L₁₂(F_* + W) = L₁₂(F_*) + L₁₂(W)` as functions of `z`, for `z ≥ 0`.**  This is
`Work.Stability.L12Add` with its three integrability inputs discharged from
`SmoothOpen W` and `HkMem α 4 W`. -/
theorem L12Ftot_add {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {W : ℝ → ℝ → ℝ}
    (hWs : Work.FTS.EllipticEst.SmoothOpen W) (hWm : Work.Spaces.HkMem α 4 W) :
    ∀ z ∈ Set.Ici (0 : ℝ),
      Work.Construction.L12 (Work.Construction.Ftot α W) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z
          + Work.Construction.L12 W z := by
  intro z hz
  have hz0 : (0 : ℝ) ≤ z := hz
  have h1 : MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K (Work.Construction.Fstar α)) (Set.Ioi z) :=
    Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn hα hα1 z hz0
  have h2 : MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K W) (Set.Ioi z) := by
    have hw : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K W) (Set.Ioi (0:ℝ)) :=
      Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem hWs hWm
    exact hw.mono_set (fun x hx => lt_of_le_of_lt hz0 hx)
  have h3 : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * (Work.Construction.Fstar α s θ + W s θ) / s)
      Work.Spaces.Iθ := by
    intro s hs
    have hs0 : 0 < s := lt_of_le_of_lt hz0 hs
    have hFs : MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.K θ * Work.Construction.Fstar α s θ / s) Work.Spaces.Iθ :=
      Work.Stability.integrableOn_slice_Fstar α hα s
    have hW : MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.K θ * W s θ / s) Work.Spaces.Iθ :=
      Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hWs hWm hs0
    refine (hFs.add hW).congr_fun (fun θ _ => ?_) measurableSet_Icc
    simp only [Pi.add_apply]
    ring
  exact Work.Stability.L12Add α hα h1 h2 h3

/-- The pointwise form of `L12Ftot_add` at the single point `z ≥ 0`. -/
theorem L12Ftot_add_point {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {W : ℝ → ℝ → ℝ}
    (hWs : Work.FTS.EllipticEst.SmoothOpen W) (hWm : Work.Spaces.HkMem α 4 W)
    {z : ℝ} (hz : 0 ≤ z) :
    Work.Construction.L12 (Work.Construction.Ftot α W) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 W z :=
  L12Ftot_add hα hα1 hWs hWm z hz

/-- **The decomposition of the stream function `Φ̃ = PhiTil α (Ftot α W) Φ`** into its star
part (`F_*`, `Φs`) and its elliptic part (`W`, `Φg`), given additivity of `L₁₂` on `F = F_*+W`. -/
theorem PhiTil_Ftot_decomp {α : ℝ} {Φs W Φg : ℝ → ℝ → ℝ}
    (hadd : ∀ z ∈ Set.Ici (0 : ℝ),
      Work.Construction.L12 (Work.Construction.Ftot α W) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z
          + Work.Construction.L12 W z)
    {z θ : ℝ} (hz : 0 ≤ z) :
    Work.Construction.PhiTil α (Work.Construction.Ftot α W)
        (fun z θ => Φs z θ + Φg z θ) z θ
      = Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
        + Work.Construction.PhiTil α W Φg z θ := by
  simp only [Work.Construction.PhiTil, Work.Construction.Theta]
  rw [hadd z hz]
  ring

end Work.FTS.StrongEps.EpsRLX.ProfRHSAux
