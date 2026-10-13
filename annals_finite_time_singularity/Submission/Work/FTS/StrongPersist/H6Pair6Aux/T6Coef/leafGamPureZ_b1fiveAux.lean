/-
# `T6Coef/leafGamPureZ_b1fiveAux` — the analytic infrastructure of the `b₁ = 5` crux case

Reusable helpers for the `(a,b,a₁,b₁) = (1,5,0,5)` case of `T6Coef.leafGamPureZ`: continuity of
the leaf weight and of the `σ^{-γ}`-weighted mixed slots on the open quadrant, the weight identity
`Wt² = w²σ^{-γ}`, the a.e. strong measurability of the angular slice integrals and of the radial
weight, and the slicewise integrability of the weighted mixed slots of an `ℋ⁶`-datum.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.slotCS_z
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

open scoped Real Topology
open MeasureTheory Set Filter

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
theorem sin_two_nonneg_of_Iθ' {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin(2θ) > 0` on the open interval `(0, π/2)`. -/
theorem sin_two_pos_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `γ - 1 = α/10`. -/
theorem hgam_const {α : ℝ} : Work.Spaces.gam α - 1 = α / 10 := Work.Spaces.gam_sub_one α

/-- The uncurried datum of an `SmoothOpen` field is continuous on the open quadrant. -/
theorem smoothOpen_continuousOn {F : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen F) :
    ContinuousOn (Function.uncurry F) Work.FTS.EllipticEst.Q0 :=
  (Work.FTS.EllipticEst.SmoothOpen.forall h 1).continuousOn

/-- The weight identity `Wt α z θ ^ 2 = w z ^ 2 * sin(2θ)^{-γ}` on `Iθ`. -/
theorem wt_sq (α : ℝ) (hα : 0 < α) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Iθ' hθ
  have hgam : Work.Spaces.gam α ≠ 0 := by
    have hg : Work.Spaces.gam α = 1 + α / 10 := rfl
    rw [hg]; intro h; linarith
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
  rw [show ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ ((2 : ℝ)) from
      (Real.rpow_natCast ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) 2).symm]
  rw [← Real.rpow_mul hs]
  rw [show (-(Work.Spaces.gam α / 2)) * (2 : ℝ) = -(Work.Spaces.gam α) by ring]

/-- Continuity of `σ^{-γ}·sin(2·)^{-γ}·(mixed j i f)²` on the open quadrant, for `i ≥ 1`. -/
theorem contOn_sig_mixed {α : ℝ} {f : ℝ → ℝ → ℝ} {j i : ℕ}
    (h : Work.FTS.EllipticEst.SmoothOpen f) (hi : 1 ≤ i) :
    ContinuousOn (fun p : ℝ × ℝ =>
        (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed j i f p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Q0 := by
  have hm : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2)
      Work.FTS.EllipticEst.Q0 := (smoothOpen_continuousOn (h.mixed j i))
  have hs : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)))
      Work.FTS.EllipticEst.Q0 := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
    refine h1.rpow_const (fun p hp => Or.inl ?_)
    exact ne_of_gt (sin_two_pos_of_Ioo
      ⟨(Work.FTS.EllipticEst.mem_Q0.mp hp).2.1, (Work.FTS.EllipticEst.mem_Q0.mp hp).2.2⟩)
  exact hs.mul (hm.pow 2)

/-- Continuity of `sin(2·)^{-γ}·|mixed 0 1 f|·|mixed 5 1 f|` on the open quadrant. -/
theorem contOn_sig_abs {α : ℝ} {f : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.SmoothOpen f) :
    ContinuousOn (fun p : ℝ × ℝ =>
        (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
          * (|Work.Spaces.mixed 0 1 f p.1 p.2| * |Work.Spaces.mixed 5 1 f p.1 p.2|))
      Work.FTS.EllipticEst.Q0 := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => |Work.Spaces.mixed 0 1 f p.1 p.2|)
      Work.FTS.EllipticEst.Q0 := (smoothOpen_continuousOn (h.mixed 0 1)).abs
  have h2 : ContinuousOn (fun p : ℝ × ℝ => |Work.Spaces.mixed 5 1 f p.1 p.2|)
      Work.FTS.EllipticEst.Q0 := (smoothOpen_continuousOn (h.mixed 5 1)).abs
  have hs : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)))
      Work.FTS.EllipticEst.Q0 := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
    refine h1.rpow_const (fun p hp => Or.inl ?_)
    exact ne_of_gt (sin_two_pos_of_Ioo
      ⟨(Work.FTS.EllipticEst.mem_Q0.mp hp).2.1, (Work.FTS.EllipticEst.mem_Q0.mp hp).2.2⟩)
  exact hs.mul (h1.mul h2)

/-- Continuity of the leaf weight `w²σ^{-γ}` on the open quadrant. -/
theorem contOn_leafGam (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hw : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2) Work.FTS.EllipticEst.Q0 := by
    have hfun : (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
        = fun p : ℝ × ℝ => ((1 + p.1) ^ 2 / p.1 ^ 2) ^ 2 := by funext p; rfl
    rw [hfun]
    refine ContinuousOn.pow ?_ 2
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hs : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)))
      Work.FTS.EllipticEst.Q0 := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
    refine h1.rpow_const (fun p hp => Or.inl ?_)
    exact ne_of_gt (sin_two_pos_of_Ioo
      ⟨(Work.FTS.EllipticEst.mem_Q0.mp hp).2.1, (Work.FTS.EllipticEst.mem_Q0.mp hp).2.2⟩)
  have hfun : (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2)
      = fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)) := by
    funext p; rfl
  rw [hfun]
  exact hw.mul hs

/-- The angular slice integral `z ↦ ∫_θ G z θ` of a function continuous on the open quadrant is
a.e. strongly measurable for the restricted radial measure. -/
theorem aesm_sliceIntegral {G : ℝ → ℝ → ℝ}
    (hG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) Work.FTS.EllipticEst.Q0) :
    MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ, G z θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
  (Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ => G p.1 p.2) hG).integral_prod_right'

/-- The radial weight is a.e. strongly measurable for the restricted radial measure. -/
theorem aesm_w : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => Work.Spaces.w z)
    (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hIz : (Work.Spaces.Iz : Set ℝ) =ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
  rw [MeasureTheory.Measure.restrict_congr_set hIz]
  have hcont : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
    have hfun : (fun z : ℝ => Work.Spaces.w z) = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := by funext z; rfl
    rw [hfun]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) (fun z hzz => pow_ne_zero 2 (ne_of_gt hzz))
  exact hcont.aestronglyMeasurable measurableSet_Ioi

/-- **Slicewise integrability of the `γ`-weighted mixed slots.**  For an `ℋ⁶`-datum `f` and
`a ≥ 1`, `a + b ≤ 6`, the angular slice `θ ↦ sin(2θ)^{-γ}(D_z^bD_θ^a f)(z,θ)²` is integrable,
for every `z > 0`. -/
theorem integrableOn_gamMixed_slice {α : ℝ} {f : ℝ → ℝ → ℝ} {b a : ℕ} (hα : 0 < α)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 6 f)
    (ha : 1 ≤ a) (hab : a + b ≤ 6) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iθ := by
  have hw2pos : 0 < (Work.Spaces.w z) ^ 2 := by
    have := Work.FTS.TransportS.SlotT2.supOpen_one_le_w hz
    positivity
  have hk : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 6 f z θ)
      Work.Spaces.Iθ := hmem.1 z (by simp only [Work.Spaces.Iz, Set.mem_Ici]; linarith)
  refine MeasureTheory.Integrable.mono' (hk.const_mul (((Work.Spaces.w z) ^ 2)⁻¹)) ?_ ?_
  · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _
      (contOn_sig_mixed hf ha) hz
  · refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ hθ0 hθ1 => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg
      (Real.rpow_nonneg (sin_two_nonneg_of_Iθ' ⟨le_of_lt hθ0, le_of_lt hθ1⟩) _) (sq_nonneg _))]
    have hθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have hWt := wt_sq α hα z θ hθ
    have hslot := Work.Spaces.sq_le_HkIntegrand_mixed α 6 f z θ a b ha hab
    have heq : (Work.Spaces.mixed b a f z θ * Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed b a f z θ) ^ 2 := by
      rw [mul_pow, hWt]; ring
    rw [heq] at hslot
    have hrw : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed b a f z θ) ^ 2
        = ((Work.Spaces.w z) ^ 2)⁻¹ * ((Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed b a f z θ) ^ 2) := by
      rw [show ((Work.Spaces.w z) ^ 2)⁻¹ * ((Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed b a f z θ) ^ 2)
          = (((Work.Spaces.w z) ^ 2)⁻¹ * (Work.Spaces.w z) ^ 2)
            * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed b a f z θ) ^ 2) from by ring,
        inv_mul_cancel₀ (ne_of_gt hw2pos), one_mul]
    rw [hrw]
    exact mul_le_mul_of_nonneg_left hslot (inv_nonneg.mpr (sq_nonneg _))


/-! ## The elementary fields of the crux case -/

/-- The `z`-slice functional `MX` multiplying the coefficient slot `D_z^5 A` in the crux case:
`(4/π)∫_θ(D_z^5A)² + (200/(γ-1))∫_θ sin(2θ)^{-γ}(D_z^5D_θA)²`. -/
noncomputable def b1fiveMX (α : ℝ) (A : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z =>
  (4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 A z θ) ^ 2)
    + (200 / (Work.Spaces.gam α - 1)) * (∫ θ in Work.Spaces.Iθ,
        (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 5 1 A z θ) ^ 2)

/-- The `z`-slice functional of the `γ`-weighted slot `D_θf`. -/
noncomputable def b1fivePz (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z =>
  ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
    * (Work.Spaces.mixed 0 1 f z θ) ^ 2

/-- The `z`-slice functional of the `γ`-weighted slot `D_z^5D_θf`. -/
noncomputable def b1fiveQz (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z =>
  ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
    * (Work.Spaces.mixed 5 1 f z θ) ^ 2

/-- The integrand of the crux case `(a,b,a₁,b₁) = (1,5,0,5)`. -/
noncomputable def b1fiveF (α : ℝ) (A f : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ := fun p =>
  Work.FTS.TransportS.leafGam α p.1 p.2
    * Work.Spaces.mixed 5 0 A p.1 p.2
    * Work.Spaces.mixed 0 1 f p.1 p.2
    * Work.Spaces.mixed 5 1 f p.1 p.2

/-- Almost every point of `μ = (volume.restrict Iz).prod (volume.restrict Iθ)` lies in the open
quadrant `Q0 = (0,∞) × (0,π/2)`. -/
theorem ae_mem_Q0_prod :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)), p ∈ Work.FTS.EllipticEst.Q0 := by
  have hz : Work.Spaces.Iz =ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
  have hθ : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := Real.pi / 2)).symm
  have hprod : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[MeasureTheory.volume.prod MeasureTheory.volume] Work.FTS.EllipticEst.Q0 := by
    simpa only [Work.FTS.EllipticEst.Q0] using MeasureTheory.Measure.set_prod_ae_eq hz hθ
  rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_congr_set hprod]
  exact MeasureTheory.ae_restrict_mem Work.FTS.EllipticEst.isOpen_Q0.measurableSet

/-- The level-one mixed slot `D_θf` is a.e. bounded by `C·Xn α f`. -/
theorem ae_abs_mixed01_le_Xn : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ),
    α ∈ Set.Ioc 0 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      |Work.Spaces.mixed 0 1 f p.1 p.2| ≤ C * Work.FTS.Nonlin.Xn α f := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
  refine ⟨C, hCpos, ?_⟩
  intro α f hα hsm h4
  filter_upwards [ae_mem_Q0_prod] with p hp
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact hC α f hα.1 hα.2 hsm h4 0 1 (by norm_num) (by norm_num) p.1 p.2 hz hθ0 hθ1

/-- Unfolding of the slice functional `b1fiveMX`. -/
theorem b1fiveMX_apply (α : ℝ) (A : ℝ → ℝ → ℝ) (z : ℝ) :
    b1fiveMX α A z
      = (4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 A z θ) ^ 2)
        + (200 / (Work.Spaces.gam α - 1)) * (∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed 5 1 A z θ) ^ 2) := rfl

/-- Unfolding of the slice functional `b1fiveQz`. -/
theorem b1fiveQz_apply (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    b1fiveQz α f z = ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed 5 1 f z θ) ^ 2 := rfl

/-- Unfolding of the slice functional `b1fivePz`. -/
theorem b1fivePz_apply (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    b1fivePz α f z = ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed 0 1 f z θ) ^ 2 := rfl

/-- Unfolding of the crux integrand `b1fiveF`. -/
theorem b1fiveF_apply (α : ℝ) (A f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    b1fiveF α A f p = Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed 5 0 A p.1 p.2
      * Work.Spaces.mixed 0 1 f p.1 p.2
      * Work.Spaces.mixed 5 1 f p.1 p.2 := rfl

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
