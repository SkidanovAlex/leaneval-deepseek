/-
Weighted radial integration by parts for the mixed weighted interpolation estimate.

`radial_ibp_weight`: for `φ, ψ` of class `C¹` on `(0,∞)` and a cut-off `ζ` of class `C¹` on
`(0,∞)` vanishing off `[a,b] ⊆ (0,∞)` (`0 < a < b`),

  `∫_0^∞ ζ w² φ (z ∂_z ψ) = -∫_0^∞ (∂_zζ) w² z φ ψ - ∫_0^∞ ζ w² (z ∂_zφ + b φ) ψ`,

with `w(z) = (1+z)²/z²` and `b(z) = (z-3)/(1+z)` the logarithmic derivative of `z w(z)²`
(`(z w²)' = b w²`).  All boundary terms vanish because `ζ` is compactly supported inside
`(0,∞)`; this generalises `ThetaU.radial_ibp_eta` (which requires *both* `φ` and `ψ` to be
supported in `[a,b]`).
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaU.OpenAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Alpha4

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- A function continuous on `(0,∞)` which vanishes off `[a,b]` (`0 < a ≤ b`) is integrable
on `(0,∞)`. -/
theorem integrableOn_Ioi_of_support_Icc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {F : ℝ → ℝ}
    (hF : ContinuousOn F (Set.Ioi 0))
    (hs : ∀ z ∈ Set.Ioi (0 : ℝ), z ∉ Set.Icc a b → F z = 0) :
    MeasureTheory.IntegrableOn F (Set.Ioi 0) := by
  have h1 : MeasureTheory.IntegrableOn F (Set.Ioo 0 a) := by
    refine MeasureTheory.integrableOn_zero.congr_fun (fun z hz => ?_) measurableSet_Ioo
    exact (hs z hz.1 (fun h => absurd h.1 (not_le_of_gt hz.2))).symm
  have h2 : MeasureTheory.IntegrableOn F (Set.Icc a b) :=
    (hF.mono (fun z hz => lt_of_lt_of_le ha hz.1)).integrableOn_compact isCompact_Icc
  have h3 : MeasureTheory.IntegrableOn F (Set.Ioi b) := by
    refine MeasureTheory.integrableOn_zero.congr_fun (fun z hz => ?_) measurableSet_Ioi
    exact (hs z (lt_trans (lt_of_lt_of_le ha hab) hz)
      (fun h => absurd h.2 (not_le_of_gt hz))).symm
  have h4 := h1.union (h2.union h3)
  rwa [show Set.Ioo (0 : ℝ) a ∪ (Set.Icc a b ∪ Set.Ioi b) = Set.Ioi 0 from ?_] at h4
  ext z
  simp only [Set.mem_union, Set.mem_Ioo, Set.mem_Icc, Set.mem_Ioi]
  constructor
  · rintro (⟨h1, -⟩ | ⟨h2, -⟩ | h3) <;> linarith
  · intro hz
    rcases lt_or_ge z a with h | h
    · exact Or.inl ⟨hz, h⟩
    · rcases le_or_gt z b with h' | h'
      · exact Or.inr (Or.inl ⟨h, h'⟩)
      · exact Or.inr (Or.inr h')

/-- The coefficient `b` is continuous on `(0,∞)`. -/
theorem bcoef_continuousOn : ContinuousOn Work.FTS.EllipticEst.ThetaU.bcoef (Set.Ioi 0) := by
  have h : Work.FTS.EllipticEst.ThetaU.bcoef = fun z : ℝ => (z - 3) / (1 + z) := rfl
  rw [h]
  refine ContinuousOn.div ((continuous_id.sub continuous_const).continuousOn)
    ((continuous_const.add continuous_id).continuousOn) ?_
  intro z hz
  have hz' : (0 : ℝ) < z := hz
  exact ne_of_gt (by linarith)

/-- `z ↦ w z ^ 2` is continuous on `(0,∞)`. -/
theorem continuousOn_w_sq : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have hw : ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (continuous_const.add continuous_id).continuousOn.pow 2
    · exact (continuous_id.continuousOn).pow 2
    · intro z hz
      have hz' : (0 : ℝ) < z := hz
      exact pow_ne_zero 2 (ne_of_gt hz')
  refine (hw.pow 2).congr ?_
  intro z hz
  simp only [Work.Spaces.w, Pi.pow_apply]

theorem radial_ibp_weight {a b : ℝ} (ha : 0 < a) (hab : a < b) {φ ψ ζ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ 1 φ (Set.Ioi 0)) (hψ : ContDiffOn ℝ 1 ψ (Set.Ioi 0))
    (hζ : ContDiffOn ℝ 1 ζ (Set.Ioi 0))
    (hsζ : ∀ z, (0 < z ∧ z < a) ∨ b < z → ζ z = 0) :
    (∫ z in Set.Ioi (0 : ℝ), ζ z * (Work.Spaces.w z) ^ 2 * φ z * (z * deriv ψ z))
      = - (∫ z in Set.Ioi (0 : ℝ), deriv ζ z * (Work.Spaces.w z) ^ 2 * z * φ z * ψ z)
        - (∫ z in Set.Ioi (0 : ℝ), ζ z * (Work.Spaces.w z) ^ 2
            * (z * deriv φ z + Work.FTS.EllipticEst.ThetaU.bcoef z * φ z) * ψ z) := by
  -- `ζ` vanishes off `[a,b]` in the region `z > 0`
  have hsupp : ∀ z ∈ Set.Ioi (0 : ℝ), z ∉ Set.Icc a b → ζ z = 0 := by
    intro z hz hzab
    rcases lt_or_ge z a with h | h
    · exact hsζ z (Or.inl ⟨hz, h⟩)
    · have hb : b < z := by
        by_contra hc
        push_neg at hc
        exact hzab ⟨h, hc⟩
      exact hsζ z (Or.inr hb)
  have hsupp' : ∀ z ∈ Set.Ioi (0 : ℝ), z ∉ Set.Icc a b → deriv ζ z = 0 := by
    intro z hz hzab
    have hev : ζ =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      rcases lt_or_ge z a with h | h
      · filter_upwards [isOpen_Ioo.mem_nhds (show z ∈ Set.Ioo (0:ℝ) a from ⟨hz, h⟩)] with y hy
        exact hsupp y hy.1 (fun hyab => absurd hyab.1 (not_le_of_gt hy.2))
      · have hb : b < z := by
          by_contra hc
          push_neg at hc
          exact hzab ⟨h, hc⟩
        filter_upwards [isOpen_Ioi.mem_nhds hb] with y hy
        exact hsupp y (lt_trans (lt_of_lt_of_le ha hab.le) hy)
          (fun hyab => absurd hyab.2 (not_le_of_gt hy))
    exact ((hasDerivAt_const (x := z) (c := 0)).congr_of_eventuallyEq hev).deriv
  -- the derivative facts
  have hderiv_ζ : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt ζ (deriv ζ z) z := fun z hz =>
    ((hζ.differentiableOn_one).differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  have hderiv_φ : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt φ (deriv φ z) z := fun z hz =>
    ((hφ.differentiableOn_one).differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  have hderiv_ψ : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt ψ (deriv ψ z) z := fun z hz =>
    ((hψ.differentiableOn_one).differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  -- the two functions of the integration by parts
  set u : ℝ → ℝ := fun z => ζ z * (z * (Work.Spaces.w z) ^ 2) * φ z with hu
  set u' : ℝ → ℝ := fun z =>
      deriv ζ z * (Work.Spaces.w z) ^ 2 * z * φ z
        + ζ z * (Work.Spaces.w z) ^ 2
          * (z * deriv φ z + Work.FTS.EllipticEst.ThetaU.bcoef z * φ z) with hu'
  have hderiv_u : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt u (u' z) z := by
    intro z hz
    have h1 : HasDerivAt (fun y : ℝ => y * (Work.Spaces.w y) ^ 2)
        (Work.FTS.EllipticEst.ThetaU.bcoef z * (Work.Spaces.w z) ^ 2) z :=
      Work.FTS.EllipticEst.ThetaU.hasDerivAt_mul_w_sq z hz
    have h2 : HasDerivAt (fun y : ℝ => ζ y * (y * (Work.Spaces.w y) ^ 2))
        (deriv ζ z * (z * (Work.Spaces.w z) ^ 2)
          + ζ z * (Work.FTS.EllipticEst.ThetaU.bcoef z * (Work.Spaces.w z) ^ 2)) z :=
      (hderiv_ζ z hz).mul h1
    have h3 : HasDerivAt (fun y : ℝ => ζ y * (y * (Work.Spaces.w y) ^ 2) * φ y)
        ((deriv ζ z * (z * (Work.Spaces.w z) ^ 2)
            + ζ z * (Work.FTS.EllipticEst.ThetaU.bcoef z * (Work.Spaces.w z) ^ 2)) * φ z
          + (ζ z * (z * (Work.Spaces.w z) ^ 2)) * deriv φ z) z :=
      h2.mul (hderiv_φ z hz)
    have heq : (fun y : ℝ => ζ y * (y * (Work.Spaces.w y) ^ 2) * φ y) = u := by
      rw [hu]
    rw [heq] at h3
    have hval : (deriv ζ z * (z * (Work.Spaces.w z) ^ 2)
          + ζ z * (Work.FTS.EllipticEst.ThetaU.bcoef z * (Work.Spaces.w z) ^ 2)) * φ z
          + (ζ z * (z * (Work.Spaces.w z) ^ 2)) * deriv φ z = u' z := by
      rw [hu']; ring
    rw [hval] at h3
    exact h3
  -- continuity of the pieces
  have hcont_u : ContinuousOn u (Set.Ioi 0) := by
    refine ContinuousOn.mul (ContinuousOn.mul hζ.continuousOn
      (continuousOn_id.mul continuousOn_w_sq)) hφ.continuousOn
  have hderiv_ζ_cont : ContinuousOn (deriv ζ) (Set.Ioi 0) :=
    hζ.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  have hderiv_φ_cont : ContinuousOn (deriv φ) (Set.Ioi 0) :=
    hφ.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  have hcont_u' : ContinuousOn u' (Set.Ioi 0) := by
    refine ContinuousOn.add (ContinuousOn.mul (ContinuousOn.mul
      (ContinuousOn.mul hderiv_ζ_cont continuousOn_w_sq) continuousOn_id) hφ.continuousOn) ?_
    refine ContinuousOn.mul (ContinuousOn.mul hζ.continuousOn continuousOn_w_sq)
      (ContinuousOn.add (continuousOn_id.mul hderiv_φ_cont)
        (bcoef_continuousOn.mul hφ.continuousOn))
  have hcont_ψ' : ContinuousOn (deriv ψ) (Set.Ioi 0) :=
    hψ.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  -- integrability
  have hIntF : MeasureTheory.IntegrableOn (fun z => u z * deriv ψ z) (Set.Ioi 0) := by
    refine integrableOn_Ioi_of_support_Icc ha hab.le (hcont_u.mul hcont_ψ') ?_
    intro z hz hzab
    rw [hu]; simp only
    rw [hsupp z hz hzab]; ring
  have hIntG : MeasureTheory.IntegrableOn (fun z => u' z * ψ z) (Set.Ioi 0) := by
    refine integrableOn_Ioi_of_support_Icc ha hab.le (hcont_u'.mul hψ.continuousOn) ?_
    intro z hz hzab
    rw [hu']; simp only
    rw [hsupp z hz hzab, hsupp' z hz hzab]; ring
  -- the boundary limits
  have hzero : Filter.Tendsto (fun z => u z * ψ z) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hev : (fun z => u z * ψ z) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] (fun _ => (0 : ℝ)) := by
      filter_upwards [Ioo_mem_nhdsGT ha] with z hz
      rw [hu]; simp only
      rw [hsupp z hz.1 (fun h => absurd h.1 (not_le_of_gt hz.2))]
      ring
    exact tendsto_const_nhds.congr' hev.symm
  have hinfty : Filter.Tendsto (fun z => u z * ψ z) Filter.atTop (nhds 0) := by
    have hev : (fun z => u z * ψ z) =ᶠ[Filter.atTop] (fun _ => (0 : ℝ)) := by
      filter_upwards [eventually_gt_atTop b] with z hz
      rw [hu]; simp only
      rw [hsupp z (lt_trans (lt_of_lt_of_le ha hab.le) hz)
        (fun h => absurd h.2 (not_le_of_gt hz))]
      ring
    exact tendsto_const_nhds.congr' hev.symm
  -- the integration by parts
  have hIBP : (∫ z in Set.Ioi (0 : ℝ), u z * deriv ψ z)
      = - ∫ z in Set.Ioi (0 : ℝ), u' z * ψ z := by
    have h := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (a' := 0) (b' := 0)
      (u := u) (u' := u') (v := ψ) (v' := deriv ψ) hderiv_u hderiv_ψ hIntF hIntG hzero hinfty
    simpa using h
  -- rewriting the left-hand side
  have hleft : (∫ z in Set.Ioi (0 : ℝ), ζ z * (Work.Spaces.w z) ^ 2 * φ z * (z * deriv ψ z))
      = ∫ z in Set.Ioi (0 : ℝ), u z * deriv ψ z := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
    rw [hu]; ring
  -- splitting `u' * ψ`
  have hsplit : (∫ z in Set.Ioi (0 : ℝ), u' z * ψ z)
      = (∫ z in Set.Ioi (0 : ℝ), deriv ζ z * (Work.Spaces.w z) ^ 2 * z * φ z * ψ z)
        + (∫ z in Set.Ioi (0 : ℝ), ζ z * (Work.Spaces.w z) ^ 2
            * (z * deriv φ z + Work.FTS.EllipticEst.ThetaU.bcoef z * φ z) * ψ z) := by
    have hcongr : (fun z => u' z * ψ z) = fun z =>
        deriv ζ z * (Work.Spaces.w z) ^ 2 * z * φ z * ψ z
          + ζ z * (Work.Spaces.w z) ^ 2
            * (z * deriv φ z + Work.FTS.EllipticEst.ThetaU.bcoef z * φ z) * ψ z := by
      funext z; rw [hu']; ring
    have h1 : MeasureTheory.IntegrableOn
        (fun z => deriv ζ z * (Work.Spaces.w z) ^ 2 * z * φ z * ψ z) (Set.Ioi 0) := by
      refine integrableOn_Ioi_of_support_Icc ha hab.le ?_ ?_
      · refine ContinuousOn.mul (ContinuousOn.mul (ContinuousOn.mul
          (ContinuousOn.mul hderiv_ζ_cont continuousOn_w_sq) continuousOn_id)
          hφ.continuousOn) hψ.continuousOn
      · intro z hz hzab
        rw [hsupp' z hz hzab]; ring
    have h2 : MeasureTheory.IntegrableOn
        (fun z => ζ z * (Work.Spaces.w z) ^ 2
            * (z * deriv φ z + Work.FTS.EllipticEst.ThetaU.bcoef z * φ z) * ψ z)
        (Set.Ioi 0) := by
      refine integrableOn_Ioi_of_support_Icc ha hab.le ?_ ?_
      · refine ContinuousOn.mul (ContinuousOn.mul
          (ContinuousOn.mul hζ.continuousOn continuousOn_w_sq)
          (ContinuousOn.add (continuousOn_id.mul hderiv_φ_cont)
            (bcoef_continuousOn.mul hφ.continuousOn))) hψ.continuousOn
      · intro z hz hzab
        rw [hsupp z hz hzab]; ring
    rw [hcongr, MeasureTheory.integral_add h1 h2]
  rw [hleft, hIBP, hsplit]
  ring

end Work.FTS.EllipticEst.Alpha4
