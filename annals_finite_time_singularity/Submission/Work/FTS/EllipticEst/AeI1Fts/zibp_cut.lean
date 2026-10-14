import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Stability.ZcutSmoothCompact

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The radial integration by parts with the cut-off `χ_n = cut n`

With `Fp u` and `Fd u` the two `z`-integrands of `AeI1Fts/Defs`
(`Fd u z θ = z·(z ∂_z u)·∂_θθ u·w²`, `Fp` the three-term integrand of the pointwise identity
`∂_z(Fd u · θ) = w²·Fp u · θ`), the cut-off `χ_n = cut n` of `interpol_trunc_defs` is equal to
`1` on `[2/(n+1), 2(n+1)]` and supported in `(1/(n+1), 3(n+1))`, so both boundary terms of the
fundamental theorem of calculus vanish:

  `∫_{z>0} χ_n w² Fp u · θ = -∫_{z>0} (z χ_n') (z ∂_z u) (∂_θθ u) w²`.

The proof is `MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul` at `a = 0` applied to the pair
`(χ_n, z ↦ Fd u z θ)`, with both `u · v' = χ_n·(w² Fp u)` and `u' · v = χ_n'·Fd u` integrable
because they are continuous and compactly supported inside `(0,∞)`.
-/

namespace Work.FTS.EllipticEst.AeI1Fts

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 2000000

private theorem isOpen_qd : IsOpen qd := isOpen_Ioi.prod isOpen_Ioo

/-! ## The partial-derivative API on the open quadrant -/

/-- The curried `z`-partial of a `C^{n+1}` function is `C^n`, because it is the composition of
the Fréchet derivative with the evaluation at the direction `(1,0)`. -/
private theorem contDiffOn_uncurry_pz_succ {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) {n : ℕ} (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := by
    intro p hp
    exact Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (n := (n + 1 : ℕ)) (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := n) hV.uniqueDiffOn le_rfl
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- The curried `θ`-partial of a `C^{n+1}` function is `C^n`. -/
private theorem contDiffOn_uncurry_pth_succ {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) {n : ℕ} (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := by
    intro p hp
    exact Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (n := (n + 1 : ℕ)) (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := n) hV.uniqueDiffOn le_rfl
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

private theorem contDiffOn_pairMk (n : ℕ) (θ : ℝ) :
    ContDiffOn ℝ n (fun z : ℝ => (z, θ)) (Set.Ioi 0) :=
  contDiffOn_id.prodMk contDiffOn_const

/-- The `z`-slice of a jointly `C^n` function on the open quadrant is `C^n` on `(0,∞)`. -/
private theorem contDiffOn_slice {f : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ n (Function.uncurry f) qd) {θ : ℝ} (hθ : θ ∈ Iθo) :
    ContDiffOn ℝ n (fun z => f z θ) (Set.Ioi 0) := by
  have hpair : ContDiffOn ℝ n (fun z : ℝ => (z, θ)) (Set.Ioi 0) := contDiffOn_pairMk n θ
  exact (h.comp hpair (fun z hz => ⟨hz, hθ⟩)).congr (fun z _ => rfl)

/-- A slice of a jointly `C^n` function on the open quadrant is continuous on `(0,∞)`. -/
private theorem continuousOn_slice_of_contDiffOn {f : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ n (Function.uncurry f) qd) {θ : ℝ} (hθ : θ ∈ Iθo) :
    ContinuousOn (fun z => f z θ) (Set.Ioi 0) :=
  (contDiffOn_slice h hθ).continuousOn

/-! ## Continuity of the `z`-slices of the two integrands -/

private theorem continuousOn_wSq : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2)
    (Set.Ioi 0) := by
  have h : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
    show ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0)
    exact ((continuous_const.add continuous_id).pow 2).continuousOn.div
      ((continuous_id.pow 2).continuousOn) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
  exact h.pow 2



/-! ## The pointwise derivative identity for `Fd` -/


private theorem continuous_deriv_cut (n : ℕ) :
    Continuous (deriv (Work.FTS.EllipticEst.cut n)) := by
  have hcut : ContDiff ℝ ∞ (Work.FTS.EllipticEst.cut n) := Work.FTS.EllipticEst.cut_contDiff n
  exact ((contDiff_infty_iff_deriv.mp hcut).2).continuous



/-! ## Integrability on the half-line of a compactly supported continuous function -/

private theorem integrableOn_Ioi_of_Icc_support {f : ℝ → ℝ} {a b : ℝ} (_ha : 0 < a)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hzero : ∀ z, z ∉ Set.Icc a b → f z = 0) :
    IntegrableOn f (Set.Ioi 0) := by
  have hInd : Integrable ((Set.Icc a b).indicator f) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (hcont.integrableOn_compact isCompact_Icc)
  have hfun : f = (Set.Icc a b).indicator f := by
    funext z
    by_cases hz : z ∈ Set.Icc a b
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, hzero z hz]
  rw [hfun]
  refine ⟨hInd.aestronglyMeasurable.mono_measure Measure.restrict_le_self, ?_⟩
  calc ∫⁻ z, ‖(Set.Icc a b).indicator f z‖₊ ∂(volume.restrict (Set.Ioi 0))
      ≤ ∫⁻ z, ‖(Set.Icc a b).indicator f z‖₊ ∂(volume : Measure ℝ) :=
        lintegral_mono' Measure.restrict_le_self le_rfl
    _ < ⊤ := hInd.hasFiniteIntegral

/-! ## The cut-off `χ_n` vanishes outside its band, together with its derivative -/

private theorem deriv_cut_eq_zero_of_lt (n : ℕ) {z : ℝ} (hz : z < 1 / (n + 1 : ℝ)) :
    deriv (Work.FTS.EllipticEst.cut n) z = 0 := by
  have hEq : (fun y : ℝ => Work.FTS.EllipticEst.cut n y) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hz] with y hy
    exact Work.FTS.EllipticEst.cut_apply_zero_of_le n hy.le
  have := hEq.deriv_eq
  simpa using this

private theorem deriv_cut_eq_zero_of_gt (n : ℕ) {z : ℝ} (hz : 3 * (n + 1 : ℝ) < z) :
    deriv (Work.FTS.EllipticEst.cut n) z = 0 := by
  have hEq : (fun y : ℝ => Work.FTS.EllipticEst.cut n y) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact Work.FTS.EllipticEst.cut_apply_zero_of_ge n hy.le
  have := hEq.deriv_eq
  simpa using this


end

end Work.FTS.EllipticEst.AeI1Fts
