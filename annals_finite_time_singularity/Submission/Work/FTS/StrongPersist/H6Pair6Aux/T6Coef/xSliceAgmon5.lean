import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.H2.T1Q.SliceSupOpen
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.SliceSup6
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

/-! ## The `∂_θ`-form of the second angular integral

The slice Agmon inequality `Work.H2.T1Q.SliceSupOpen` is stated with the plain derivative
`(∂_θ u)² · sin(2θ)^{2-γ}`; the weight used in the level-six pairing is the `D_θ`-normalised
one, `sin(2θ)^{-γ}·(D_z^5D_θA)²`.  Since `D_θ = sin(2θ)·∂_θ` and `D_z^bD_θA = sin(2θ)·∂_θ(D_z^bA)`
on the open quadrant (`Work.FTS.TransportS.SlotT2.supOpen_mixed_eq_sin_pth`), the two integrals
coincide: `sin(2θ)^{-γ}·(sin(2θ)·∂_θu)² = (∂_θu)²·sin(2θ)^{2-γ}`. -/

/-- The second angular integral of the slice Agmon estimate, rewritten from the plain
`∂_θ`-form into the weighted `D_z^5D_θA`-form. -/
theorem xSliceAgmon5_secondInt {α : ℝ} {A : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen A) {z : ℝ} (hz : 0 < z) :
    (∫ θ' in Work.Spaces.Iθ,
        (deriv (fun θ'' => Work.Spaces.DzIter 5 A z θ'') θ') ^ 2
          * (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α))
      = ∫ θ' in Work.Spaces.Iθ,
          (Real.sin (2 * θ')) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 5 1 A z θ') ^ 2 := by
  rw [MeasureTheory.setIntegral_congr_set Work.FTS.TransportS.SlotT2.supOpen_Iθ_ae_eq]
  rw [MeasureTheory.setIntegral_congr_set Work.FTS.TransportS.SlotT2.supOpen_Iθ_ae_eq]
  refine MeasureTheory.setIntegral_congr_fun
    (measurableSet_Ioo : MeasurableSet (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (fun θ' hθ' => ?_)
  have hsin : 0 < Real.sin (2 * θ') :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ'.1]) (by linarith [hθ'.2, Real.pi_pos])
  have hmix : Work.Spaces.mixed 5 1 A z θ'
      = Real.sin (2 * θ') * deriv (fun θ'' => Work.Spaces.DzIter 5 A z θ'') θ' :=
    Work.FTS.TransportS.SlotT2.supOpen_mixed_eq_sin_pth hF 5 hz hθ'
  have hkey : (Real.sin (2 * θ')) ^ (-(Work.Spaces.gam α))
        * (Real.sin (2 * θ')) ^ 2
      = (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α) := by
    have h2 : (Real.sin (2 * θ')) ^ 2 = (Real.sin (2 * θ')) ^ (2 : ℝ) :=
      (Real.rpow_natCast _ 2).symm
    rw [h2, ← Real.rpow_add hsin]
    ring_nf
  rw [hmix, mul_pow, ← hkey]
  ring

/-- **The slice Agmon inequality at order five.**

For `A` smooth on the open quadrant with honest `ℋ⁶`-membership and every `z > 0`,
`θ ∈ (0,π/2)`:
`(D_z^5A(z,θ))² ≤ (4/π)·∫_{Iθ}(D_z^5A(z,·))² + (200/(γ-1))·∫_{Iθ} sin(2·)^{-γ}·(D_z^5D_θA(z,·))²`.

This is the `b = 5` instantiation of the open-interval slice estimate
`Work.H2.T1Q.SliceSupOpen` at the slice `θ' ↦ D_z^5A(z,θ')`: the differentiability is
`SmoothOpen.DzIter` restricted to the open interval, the two integrability hypotheses are
`SixAux.integrableOn_sq6` (the mean term) and `SixAux.integrableOn_pth_weight6` (the
Dirichlet term, at `b = 5 ≤ 5`), and the second integral is recast in the `D_θ`-normalised
weight by `xSliceAgmon5_secondInt`. -/
theorem xSliceAgmon5 : ∀ (α : ℝ) (A : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.HkMem α 6 A →
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter 5 A z θ) ^ 2
        ≤ (4 / Real.pi) * (∫ θ' in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 A z θ') ^ 2)
          + (200 / (Work.Spaces.gam α - 1))
            * (∫ θ' in Work.Spaces.Iθ,
                (Real.sin (2 * θ')) ^ (-(Work.Spaces.gam α))
                  * (Work.Spaces.mixed 5 1 A z θ') ^ 2) := by
  intro α A hα hα1 hF hmem z θ hz hθ0 hθπ
  have hslice : ContDiffOn ℝ 1 (fun θ' => Work.Spaces.DzIter 5 A z θ')
      (Set.Ioo 0 (Real.pi / 2)) :=
    ((hF.DzIter 5).curry_θ hz).of_le (by simp [Work.Stability.smoothOrder])
  have hint2 := Work.FTS.StrongPersist.N6Trans.SixAux.integrableOn_sq6 (α := α) (f := A)
    hα hF hmem (b := 5) (by norm_num) (z := z) hz
  have hintp := Work.FTS.StrongPersist.N6Trans.SixAux.integrableOn_pth_weight6 (α := α) (f := A)
    hα hα1 hF hmem (b := 5) (by norm_num) (z := z) hz
  have hmain := Work.H2.T1Q.SliceSupOpen α (fun θ' => Work.Spaces.DzIter 5 A z θ')
    hα hα1 hslice hint2 hintp θ ⟨hθ0, hθπ⟩
  rw [xSliceAgmon5_secondInt hF hz] at hmain
  exact hmain

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
