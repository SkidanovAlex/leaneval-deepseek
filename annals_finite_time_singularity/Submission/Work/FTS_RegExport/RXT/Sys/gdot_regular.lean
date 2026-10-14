import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.Sys.JetCalc.RHSBound
import Submission.Work.FTS_RegExport.RXT.Sys.mixed_integral_identity
import Submission.Work.FTS_RegExport.RXT.coeff_C2
import Submission.Work.FTS_RegExport.RXT0.RXJets.jetBasic
import Submission.Work.FTS_RegExport.THL.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.gdot_regular` — S5c of the RX-St1 leaf plan

`∂_τg = −(Vz·D_zF + Vθ·∂_θF + cs·F)` is spatially `C²` with local bounds, i.e. `GdotLoc S g`.

The two halves of `GdotLoc`:

* `ContDiffOn ℝ 2 (uncurry (∂_τg(σ))) Q0` for `σ ∈ (0,S]`: `∂_τg(σ)` agrees on the open quadrant
  with `RHS σ = −(VR·D_zF + bR·D_θF + cR·F)` (`gdot_eq_RHS`), where `F = F_* + gS α (tauExt g)(σ)`
  is `C³` there and the three coefficients are `C²` (`hC2`); `ContDiffOn` is closed under
  products and sums (`contDiffOn_RHS`).
* the local jet bounds on a closed box `[a,b] × [c,d]` of the open quadrant, **uniformly in
  `σ ∈ (0,S]`**: `mixed j i (RHS σ)` is expanded by Leibniz and bounded by a fixed constant
  (`RHS_mixed_bound`); the `pz`/`pth` clauses of `GdotLoc` follow from the definitional relation
  `mixed (k+1) i f = z·∂_z (mixed k i f)` and from Clairaut, using that `z ≥ a` and
  `sin(2θ) ≥ (4/π)·min c (π/2 - d)` on the box.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem gdot_regular {S α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hVP : Work.FTS_RegExport.RXT.CoeffJets (Work.FTS.Regularity.pExp α)
      (Work.FTS.RegExportIface.RXT.μR α Φs E g) (Work.FTS.RegExportIface.RXT.GR α g)
      (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) S)
    (hC2 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.VR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.bR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0)
    (hEqF : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
      HasDerivAt (fun s => Work.FTS.Regularity.profFull α
          (Work.FTS.RegPkgGal.extG (Work.FTS.RegExportIface.RXT.GR α g)) z θ s)
        (-(Work.FTS.RegExportIface.RXT.VR α Φs E g z θ τ
            * Work.Spaces.Dz (fun z θ => Work.FTS.Regularity.profFull α
                (Work.FTS.RegPkgGal.extG (Work.FTS.RegExportIface.RXT.GR α g)) z θ τ) z θ
          + Work.FTS.RegExportIface.Vθ7 (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) z θ τ
            * Work.Spaces.pth (fun z θ => Work.FTS.Regularity.profFull α
                (Work.FTS.RegPkgGal.extG (Work.FTS.RegExportIface.RXT.GR α g)) z θ τ) z θ
          + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ τ
            * Work.FTS.Regularity.profFull α
                (Work.FTS.RegPkgGal.extG (Work.FTS.RegExportIface.RXT.GR α g)) z θ τ)) τ) :
    Work.FTS.RegExportIface.RXT.GdotLoc S g := by
  -- the same `(E)`-form, phrased with the packaged profile `profExt`
  have hEqF' : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
      HasDerivAt (fun s => profExt α g s z θ)
        (-(Work.FTS.RegExportIface.RXT.VR α Φs E g z θ τ
            * Work.Spaces.Dz (profExt α g τ) z θ
          + Work.FTS.RegExportIface.Vθ7 (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) z θ τ
            * Work.Spaces.pth (profExt α g τ) z θ
          + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ τ * profExt α g τ z θ)) τ :=
    fun z θ τ h1 h2 h3 h4 h5 => hEqF z θ τ h1 h2 h3 h4 h5
  -- the pointwise identity on the open quadrant
  have hid : ∀ σ ∈ Set.Ioc (0:ℝ) S, ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.FTS.Galerkin.gdot g σ z θ = RHS α Φs E g σ z θ :=
    fun σ hσ z θ hp =>
      gdot_eq_RHS hEqF' z θ σ hp.1 hp.2.1 hp.2.2 hσ.1 hσ.2
  -- `∂_τg(σ)` is `C²` on the open quadrant
  have hcd1 : ∀ σ ∈ Set.Ioc (0:ℝ) S,
      ContDiffOn ℝ 2 (Function.uncurry (Work.FTS.Galerkin.gdot g σ))
        Work.FTS.EllipticEst.Q0 := by
    intro σ hσ
    refine (contDiffOn_RHS hα hα13 hOK hC2 hσ).congr (fun p hp => ?_)
    exact hid σ hσ p.1 p.2 hp
  refine ⟨hcd1, ?_⟩
  -- the local jet bounds, uniformly in `σ`
  intro a b c d ha hab hc hcd hd
  obtain ⟨C, hC0, hCb⟩ := RHS_mixed_bound hα hα13 hS hOK hVP hC2 ha hab hc hcd hd
  -- the angular lower bound `sin(2θ) ≥ σ₀ > 0` on `[c,d]`
  set σ₀ : ℝ := (4 / π) * min c (π / 2 - d) with hσ₀def
  have hσ₀pos : 0 < σ₀ := by
    rw [hσ₀def]
    have h1 : 0 < min c (π / 2 - d) := lt_min hc (by linarith)
    positivity
  have hσ₀le : ∀ θ ∈ Set.Icc c d, σ₀ ≤ Real.sin (2 * θ) := by
    intro θ hθ
    have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨by linarith [hθ.1, hc], by linarith [hθ.2, hd]⟩
    have hmin : min c (π / 2 - d) ≤ min θ (π / 2 - θ) :=
      le_min (le_trans (min_le_left _ _) hθ.1)
        (le_trans (min_le_right _ _) (by linarith [hθ.2]))
    have h4π : (0 : ℝ) ≤ 4 / π := div_nonneg (by norm_num) Real.pi_pos.le
    have h1' : (4 / π) * min θ (π / 2 - θ) ≤ Real.sin (2 * θ) := by
      have hms := mul_le_mul_of_nonneg_left (Work.FTS.H2.min_le_sin θ hθIθ) h4π
      have h4 : (4 / π) * ((π / 4) * Real.sin (2 * θ)) = Real.sin (2 * θ) := by
        rw [← mul_assoc, show (4 : ℝ) / π * (π / 4) = 1 by field_simp, one_mul]
      linarith [hms, h4]
    calc σ₀ = (4 / π) * min c (π / 2 - d) := hσ₀def
      _ ≤ (4 / π) * min θ (π / 2 - θ) := mul_le_mul_of_nonneg_left hmin h4π
      _ ≤ Real.sin (2 * θ) := h1'
  refine ⟨max (C / a) (C / σ₀) + C + 1, ?_⟩
  intro σ hσ z hz θ hθ
  have hzpos : 0 < z := lt_of_lt_of_le ha hz.1
  have hθpos : 0 < θ := lt_of_lt_of_le hc hθ.1
  have hθlt : θ < Real.pi / 2 := lt_of_le_of_lt hθ.2 hd
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hzpos, hθpos, hθlt⟩
  have hsinpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  -- the jets of `∂_τg` are those of `RHS`
  have hcong : ∀ j i : ℕ, j + i ≤ 2 →
      Work.Spaces.mixed j i (Work.FTS.Galerkin.gdot g σ) z θ
        = Work.Spaces.mixed j i (RHS α Φs E g σ) z θ := by
    intro j i _
    have hEqOn : Set.EqOn (Function.uncurry (Work.FTS.Galerkin.gdot g σ))
        (Function.uncurry (RHS α Φs E g σ)) Work.FTS.EllipticEst.Q0 :=
      fun p hp => hid σ hσ p.1 p.2 hp
    have hc' := Work.FTS.RegPkgGal.mixed_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0
      hEqOn j i
    exact hc' hp
  have hdiff2 : ContDiffAt ℝ 2 (Function.uncurry (Work.FTS.Galerkin.gdot g σ)) (z, θ) :=
    (hcd1 σ hσ).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)
  have hdiva : 0 ≤ C / a := div_nonneg hC0 ha.le
  have hdivs : 0 ≤ C / σ₀ := div_nonneg hC0 hσ₀pos.le
  have hmaxnn : 0 ≤ max (C / a) (C / σ₀) := le_trans hdiva (le_max_left _ _)
  have hjet : ∀ j i : ℕ, j + i ≤ 2 →
      |Work.Spaces.mixed j i (Work.FTS.Galerkin.gdot g σ) z θ|
        ≤ max (C / a) (C / σ₀) + C + 1 := by
    intro j i hji
    have h1 := hCb σ hσ z hz θ hθ j i hji
    rw [hcong j i hji]
    linarith
  refine ⟨fun j i hji => hjet j i hji, fun j i hji => ⟨?_, ?_⟩⟩
  · -- `∂_z`
    have hj1 : j + 1 + i ≤ 2 := by
      rw [Nat.add_right_comm]
      exact Nat.succ_le_succ hji
    have hC' : |Work.Spaces.mixed (j + 1) i (Work.FTS.Galerkin.gdot g σ) z θ| ≤ C := by
      rw [hcong (j + 1) i hj1]
      exact hCb σ hσ z hz θ hθ (j + 1) i hj1
    rw [pz_mixed_eq (Work.FTS.Galerkin.gdot g σ) j i (ne_of_gt hzpos), abs_div,
      abs_of_pos hzpos]
    refine le_trans (div_le_div_of_nonneg_left (abs_nonneg _) ha (hz.1)) ?_
    refine le_trans (div_le_div_of_nonneg_right hC' ha.le) ?_
    linarith [le_max_left (C / a) (C / σ₀), hC0]
  · -- `∂_θ`
    have hji1 : j + (i + 1) ≤ 2 := by
      rw [← Nat.add_assoc]
      exact Nat.succ_le_succ hji
    have hC' : |Work.Spaces.mixed j (i + 1) (Work.FTS.Galerkin.gdot g σ) z θ| ≤ C := by
      rw [hcong j (i + 1) hji1]
      exact hCb σ hσ z hz θ hθ j (i + 1) hji1
    rw [pth_mixed_eq (f := Work.FTS.Galerkin.gdot g σ) hdiff2 (ne_of_gt hsinpos) hji, abs_div,
      abs_of_pos hsinpos]
    refine le_trans (div_le_div_of_nonneg_left (abs_nonneg _) hσ₀pos (hσ₀le θ hθ)) ?_
    refine le_trans (div_le_div_of_nonneg_right hC' hσ₀pos.le) ?_
    linarith [le_max_right (C / a) (C / σ₀), hC0]

end Work.FTS_RegExport.RXT.Sys
