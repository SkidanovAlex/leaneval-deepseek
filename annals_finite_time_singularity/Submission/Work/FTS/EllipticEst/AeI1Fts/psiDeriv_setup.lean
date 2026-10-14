import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zmollDzComm
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Gmaj6
import Submission.Work.FTS.StrongPersist.L3Rhs.L3MulDzBackupM
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.T1Q.SlotPtQ
import Submission.Work.RPFresh.slice_sq_le
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.pz_mixed_mul_le_4
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zmollDz2Eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllSol.PkgK5.K5c
open Work.Spaces (Dz pz)
open Work.EllipticEst.Core

local notation "Iθ" => Work.Spaces.Iθ

set_option maxHeartbeats 4000000

/-- **The engine applied to `D_z G`**: the second log-radial derivative of `zmoll G δ ε` is the
folded `D_z²G` against the log-kernel. -/
theorem zmoll_dz2_eq (G : ℝ → ℝ → ℝ) (hT : TraceClass G) (hF : FourInts G) (δ ε : ℝ)
    (hP : Params δ ε) :
    ∀ z : ℝ, 0 < z → ∀ θ ∈ Iθ,
      Dz (Dz (zmoll G δ ε)) z θ
        = ∫ t : ℝ, sKer δ (Real.log z - t)
            * (∫ s in Iθ, Kern (sKer ε) θ s * Dz (Dz G) (Real.exp t) s) := by
  obtain ⟨hsd1, hsd2, hsd3, hsd4, -, -, hsd7⟩ := slice_data hT
  obtain ⟨C₁, hC₁pos, hC₁int, hC₁b, hC₁int', hC₁b'⟩ := sliceL1_bound hT hF
  obtain ⟨C₂, hC₂pos, hC₂int, hC₂b⟩ := ddG_sliceL1_bound hT hF
  have hC₁nn : (0 : ℝ) ≤ C₁ := le_of_lt hC₁pos
  have hC₂nn : (0 : ℝ) ≤ C₂ := le_of_lt hC₂pos
  have hdnn : ∀ w : ℝ, 0 ≤ dIntS G w := by
    intro w
    rw [dIntS]
    exact mul_nonneg (sq_nonneg _) (MeasureTheory.setIntegral_nonneg
      (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)))
  have hddnn : ∀ w : ℝ, 0 ≤ ddIntS G w := by
    intro w
    rw [ddIntS]
    exact mul_nonneg (sq_nonneg _) (MeasureTheory.setIntegral_nonneg
      (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)))
  set F₂ : ℝ → ℝ := fun w => C₁ * (1 + dIntS G w) + C₂ * (1 + ddIntS G w) with hF₂def
  have hF₂int : ∀ a b : ℝ, 0 < a → a ≤ b → IntegrableOn F₂ (Set.Icc a b) := by
    intro a b ha hab
    rw [hF₂def]
    exact (hC₁int' a b ha hab).add (hC₂int a b ha hab)
  have hF₂b : ∀ w : ℝ, 0 < w → ∫ s in Iθ, |Dz G w s| ≤ F₂ w := by
    intro w hw
    rw [hF₂def]
    exact (hC₁b' w hw).trans (le_add_of_nonneg_right
      (mul_nonneg hC₂nn (by linarith [hddnn w])))
  have hF₂b' : ∀ w : ℝ, 0 < w → ∫ s in Iθ, |Dz (Dz G) w s| ≤ F₂ w := by
    intro w hw
    rw [hF₂def]
    exact (hC₂b w hw).trans (le_add_of_nonneg_left
      (mul_nonneg hC₁nn (by linarith [hdnn w])))
  have hc₂ := zmoll_dz_comm (u := Dz G) (F := F₂) hP hsd3 hsd4 hsd2 (hT.1.Dz).continuousOn
    (fun w hw s hs => (hT.1.Dz).hasDerivAt_slice hs hw) ((hT.1.Dz).pz).continuousOn
    hF₂int hF₂b hF₂b' (fun w hw => hsd7 w hw)
  have h1 := zmoll_dz_eq G hT hF δ ε hP
  intro z hz θ hθ
  have hdeq : deriv (fun z' : ℝ => Dz (zmoll G δ ε) z' θ) z
      = deriv (fun z' : ℝ => zmoll (Dz G) δ ε z' θ) z := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact h1 z' hz' θ hθ
  calc Dz (Dz (zmoll G δ ε)) z θ
      = z * deriv (fun z' : ℝ => Dz (zmoll G δ ε) z' θ) z := by rw [Dz, pz]
    _ = z * deriv (fun z' : ℝ => zmoll (Dz G) δ ε z' θ) z := by rw [hdeq]
    _ = Dz (zmoll (Dz G) δ ε) z θ := by rw [Dz, pz]
    _ = ∫ t : ℝ, sKer δ (Real.log z - t)
          * (∫ s in Iθ, Kern (sKer ε) θ s * Dz (Dz G) (Real.exp t) s) := hc₂ z hz θ hθ

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.psiDeriv_setup =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end


/-!
# `AeI1Fts/psiDeriv_setup` - helper lemmas for `psiDeriv_tendsto_zero`

All the analytic scaffolding of the target `psiDeriv_tendsto_zero`: the pointwise angular
facts, the slicewise integrability of `sigma U^2` and `sigma V^2`, the Clairaut transfer of the
mixed honesty, the a.e. endpoint bounds for the slice of `U u`, the a.e. strong measurability of
the inner `theta`-integral, the vanishing of the layer energies, the support of `(chi_eps)'` and
the elementary arithmetic used in the assembly.
-/
/-!
# `AeI1Fts/psiDeriv_tendsto_zero`

The `θ`-layer (boundary) term of the angular integration by parts with the cut-off
`χ_ε = SliceMixedAux.cut ε` vanishes as `ε → 0⁺`:

`∫_z cut n z · w z² · ∫_θ σ θ (χ_ε)' θ (U u z θ · V u z θ) dθ dz ⟶ 0`,

where `U u = z ∂_z u`, `V u = z ∂_z ∂_θ u = ∂_θ (U u)` (Clairaut) and `σ = sigE θ = sin(2θ)^{-η}`.

## Route

* `(χ_ε)'` is supported in `(ε/2,ε) ∪ (π/2-ε,π/2-ε/2)` and `|(χ_ε)'| ≤ 2M/ε` where `M` bounds
  `|prof'|`; hence the `θ`-integral is bounded by `(2M/ε)(L + R)` with `L`, `R` the two layer
  integrals of `σ|U||V|`.
* On each layer Cauchy–Schwarz gives `∫_layer σ|U||V| ≤ √(∫_layer σU²)√(∫_layer σV²)`
  (`Work.FTS.EllipticEst.AeI1Fts.layer_inner_le`), and the *sharp* endpoint bound for the slice
  of `U` (`Work.RPFresh.slice_sq_le` on the left, `Work.RPFresh.slice_sq_le_right` on the right,
  both with the explicit constant `2^η/(1+η)` and the *total* `σ`-energy `∫_θ σ V²`) gives
  `√(∫_layer σU²) ≤ ε √(2^η(π/4)^η/(2(1+η))) √(∫_θ σV²)`.  The `1/ε` cancels and the remaining
  factor is `√(∫_{(0,ε)} σV²) + √(∫_{(π/2-ε,π/2)} σV²) ⟶ 0`.
* The trace hypothesis `U u z · → 0` at both endpoints is `TT.AeI1.aeDzTraceHk` (a.e. in `z`).
* The `z`-integration is a dominated convergence with dominating function
  `4M · cut n z · w z² · ∫_θ σ V²`, integrable by `HkMem α 0 (V u)`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeI1Fts

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-! ## Pointwise angular facts -/


/-- The radial weight `w` is continuous on `(0,∞)`. -/
theorem continuousOn_w_Ioi : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
  rw [show (fun z : ℝ => Work.Spaces.w z) = fun z => (1 + z) ^ 2 / z ^ 2 from rfl]
  refine ContinuousOn.div ?_ ?_ ?_
  · exact (continuousOn_const.add continuousOn_id).pow 2
  · exact continuousOn_id.pow 2
  · intro z hz
    exact pow_ne_zero 2 (ne_of_gt hz)

/-- `w²` is a.e. strongly measurable on `(0,∞)`. -/
theorem aestronglyMeasurable_w_sq :
    AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
  (continuousOn_w_Ioi.pow 2).aestronglyMeasurable measurableSet_Ioi

/-! ## `σ U²` and `σ V²` are slicewise integrable -/


/-! ## The mixed honesty of `V u` -/


/-! ## The a.e. slice bound for `U u` -/


/-! ## Measurability of the inner integral -/


/-! ## The layer energies tend to zero -/


/-! ## The radial cut-off is measurable -/


/-! ## The support of `(χ_ε)'` -/


/-! ## Auxiliary arithmetic -/



end Work.FTS.EllipticEst.AeI1Fts
end
end
