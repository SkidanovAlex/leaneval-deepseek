import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_RegExport.RXT.Sys.pert_tilde_contDiffOn
import Submission.Work.FTS_RegExport.RXT.Sys.pth_vop_pert_tendsto
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_RegExport.RXT.Slots.v2_thetaJetsTendsto
import Submission.Work.FTS_RegExport.RXT.Slots.v2_hkMem_pointwise_min
import Submission.Work.FTS_RegExport.RXT.Slots.v2_paramC2
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.velPert
import Submission.Work.FTS.RegExportIface.RXT.Leaves

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.vop_pert_pth_bd` — the `∂_θ`-slot of `𝒱(Φ̃)` is `O(Ce α^{-1/2} C₀α²)`

For the perturbation residual `Φ̃(τ) = PhiTil (pExp α) (g(τ)) (E (g(τ)))` of the dynamic
modulation, the `∂_θ`-slot of its transport coefficient `𝒱(Φ̃) = ∂_θΦ̃ - tan θ · Φ̃` is
bounded by the *product of the two constants already present in the hypotheses*:

`|∂_θ 𝒱(Φ̃) z θ| ≤ max Ce 0 · α^{-1/2} · (max C₀ 0 · α²)`.

This is precisely the `Vth` field of the elliptic package `EllPkgGo` — which bounds the *flat
angular coefficient norm* `CoefTh 1 (𝒱(Φ̃))` by `Ce · α^{-1/2} · Xn α g(τ)` for a class-`C`
datum — combined with the uniform `ℋ⁴`-smallness `Xn α (g(τ)) ≤ C₀α²` of `DynOK`.

## Route

1. `CoefTh l f = ∑_{b,i} [b+i ≤ l] supAbsO (D_z^bD_θ^i ∂_θf)` is a sum of nonnegative terms,
   so each of its summands is dominated by it (`TransportS.supAbsO_le_coefTh`); the
   `(b,i) = (0,0)` summand is `supAbsO (pth (𝒱(Φ̃)))`.
2. Inside the open quadrant, `|pth (𝒱(Φ̃)) z θ| ≤ supAbsO (pth (𝒱(Φ̃)))`
   (the `CoefThMem 1` half of `Vth` supplies the boundedness making `supAbsO` a genuine
   supremum rather than Lean's junk value).
3. Hence, for the class-`C` approximants `gn` of `LimApprox`,
   `|pth (𝒱(Φ̃_n)) z θ| ≤ CoefTh 1 (𝒱(Φ̃_n)) ≤ Ce · α^{-1/2} · Xn α (slice (gn n) τ)
   ≤ max Ce 0 α^{-1/2} (max C₀ 0 α²)`: the last step is the elementary case analysis on the
   signs of `Ce` and `C₀` (if `Ce ≤ 0` the middle term is `≤ 0`; if `C₀ ≤ 0` then `Xn = 0`
   as `Xn ≥ 0`; the remaining case is monotonicity).
4. The limit is taken with `le_of_tendsto'` and the jet convergence of `𝒱(Φ̃_n)` along the
   class-`C` approximants (`Sys.pth_vop_pert_tendsto`).
-/

namespace Work.FTS_RegExport.RXT.Sys

open Set Filter

set_option autoImplicit false

theorem vop_pert_pth_bd {α Ce C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∀ S > 0, ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.pth (Work.Construction.Vop (fun z θ => Work.Construction.PhiTil
          (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice g τ)
          (E (Work.FTS.Galerkin.slice g τ)) z θ)) z θ|
        ≤ max Ce 0 * (Work.FTS.Regularity.pExp α) ^ (-(1 / 2 : ℝ))
            * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) := by
  intro S hS τ hτ z θ hz hθ hθ2
  obtain ⟨gn, B, L, hApprox, _hLip, hJet, _hμ⟩ := hOK.2 S hS
  -- the jet convergence of the `∂_θ`-slot of `𝒱(Φ̃)` along the class-`C` approximants
  have hconv : Filter.Tendsto
      (fun n => |Work.Spaces.pth (Work.Construction.Vop (fun z θ => Work.Construction.PhiTil
          (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) τ)
          (E (Work.FTS.Galerkin.slice (gn n) τ)) z θ)) z θ|)
      Filter.atTop
      (nhds |Work.Spaces.pth (Work.Construction.Vop (fun z θ => Work.Construction.PhiTil
          (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice g τ)
          (E (Work.FTS.Galerkin.slice g τ)) z θ)) z θ|) := by
    exact (Work.FTS_RegExport.RXT.Sys.pth_vop_pert_tendsto hα hα13 hEL3 hOK hS hτ
      hApprox hJet z θ hz hθ hθ2).abs
  refine le_of_tendsto' hconv (fun n => ?_)
  obtain ⟨hCn, hXn, -⟩ := hApprox n τ hτ
  obtain ⟨hGo, _⟩ := hEll _ hCn
  -- ## the `CoefTh` route
  have hstep1 : |Work.Spaces.pth (Work.Construction.Vop (fun z θ => Work.Construction.PhiTil
        (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) τ)
        (E (Work.FTS.Galerkin.slice (gn n) τ)) z θ)) z θ|
      ≤ Work.FTS.H2.supAbsO (Work.Spaces.pth (Work.Construction.Vop (fun z θ =>
          Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (Work.FTS.Galerkin.slice (gn n) τ)
            (E (Work.FTS.Galerkin.slice (gn n) τ)) z θ))) := by
    obtain ⟨K, hK⟩ := hGo.Vth.1 0 0 (by norm_num)
    refine le_csSup ⟨K, ?_⟩ ⟨z, hz, θ, hθ, hθ2, rfl⟩
    rintro y ⟨z', hz', θ', hθ', hθ2', rfl⟩
    simpa [Work.Spaces.mixed] using hK z' θ' hz' hθ' hθ2'
  have hstep2 : Work.FTS.H2.supAbsO (Work.Spaces.pth (Work.Construction.Vop (fun z θ =>
        Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.Galerkin.slice (gn n) τ)
          (E (Work.FTS.Galerkin.slice (gn n) τ)) z θ)))
      ≤ Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (fun z θ =>
        Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.Galerkin.slice (gn n) τ)
          (E (Work.FTS.Galerkin.slice (gn n) τ)) z θ)) := by
    have h := Work.FTS.TransportS.supAbsO_le_coefTh (l := 1)
      (f := Work.Construction.Vop (fun z θ => Work.Construction.PhiTil
        (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) τ)
        (E (Work.FTS.Galerkin.slice (gn n) τ)) z θ)) (b := 0) (i := 0) (by norm_num)
    simpa [Work.Spaces.mixed] using h
  -- ## the constant
  have hstep3 : Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (fun z θ =>
        Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.Galerkin.slice (gn n) τ)
          (E (Work.FTS.Galerkin.slice (gn n) τ)) z θ))
      ≤ max Ce 0 * (Work.FTS.Regularity.pExp α) ^ (-(1 / 2 : ℝ))
          * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) := by
    have hαp : 0 < (Work.FTS.Regularity.pExp α) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_pos_of_pos (Work.FTS.Regularity.pExp_pos hα) _
    have hq : 0 ≤ (Work.FTS.Regularity.pExp α) ^ 2 := sq_nonneg _
    have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α)
        (Work.FTS.Galerkin.slice (gn n) τ) := Work.Spaces.HkNorm_nonneg _ _ _
    have hXnB : Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α)
          (Work.FTS.Galerkin.slice (gn n) τ)
        ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 :=
      le_trans hXn (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) hq)
    have h0 : 0 ≤ max Ce 0 * (Work.FTS.Regularity.pExp α) ^ (-(1 / 2 : ℝ))
        * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) :=
      mul_nonneg (mul_nonneg (le_max_right Ce 0) hαp.le)
        (mul_nonneg (le_max_right C₀ 0) hq)
    refine le_trans hGo.Vth.2 ?_
    rcases le_or_gt Ce 0 with hCe | hCe
    · have hneg : Ce * (Work.FTS.Regularity.pExp α) ^ (-(1 / 2 : ℝ))
          * Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice (gn n) τ) ≤ 0 := by
        rw [mul_assoc]
        exact mul_nonpos_of_nonpos_of_nonneg hCe (mul_nonneg hαp.le hXn0)
      linarith
    · rw [max_eq_left hCe.le]
      exact mul_le_mul_of_nonneg_left hXnB (mul_nonneg hCe.le hαp.le)
  exact le_trans (le_trans hstep1 hstep2) hstep3

end Work.FTS_RegExport.RXT.Sys
