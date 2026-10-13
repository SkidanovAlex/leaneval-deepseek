import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.SgamBound.abs_deriv_sub_le_integral_abs_D2
import Submission.Work.FTS.EllipticEst.SgamBound.abs_sub_le_mul_abs_sub_of_deriv_bound
import Submission.Work.FTS.EllipticEst.SgamBound.integrableOn_abs_of_sq_mul_sEta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false

/-- Slicewise `σ`-weighted integrability of `∂_θθΨ`, from `Hon.memB`. -/
private theorem hon_pthIter2_sEta_integrableOn {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hz
  have h1 := h.memB.1 z hzI
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    refine MeasureTheory.IntegrableOn.congr_fun h1 (fun θ hθ => ?_) measurableSet_Icc
    rw [HkIntegrand_zero_eq, sq_profile_eq (Work.Spaces.pthIter 2 Ψ) z θ
      (sin_two_nonneg_of_mem_Iθ hθ)]
    rfl
  have hwz : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]
    exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hz))
  have hw : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 hwz
  have h3 : MeasureTheory.IntegrableOn
      (fun θ => ((Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.sEta θ) * ((Work.Spaces.w z) ^ 2)⁻¹) Work.Spaces.Iθ :=
    MeasureTheory.Integrable.mul_const h2 _
  refine MeasureTheory.IntegrableOn.congr_fun h3 (fun θ _ => ?_) measurableSet_Icc
  rw [← div_eq_mul_inv, div_eq_iff hw]
  ring

theorem HonSliceL1 (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (h : Hon α F Ψ) :
    ∀ z, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => |Ψ z θ| * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  intro z hz
  -- 0. the slice is smooth on the open angular interval
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    intro n
    have hf : ContDiff ℝ n (fun θ : ℝ => (z, θ)) := by fun_prop
    have hcomp := ContDiffOn.comp (f := fun θ : ℝ => (z, θ)) (g := Function.uncurry Ψ)
      (h.sm n) hf.contDiffOn (fun θ hθ => ⟨hz, hθ⟩)
    have heq : (Function.uncurry Ψ ∘ fun θ : ℝ => (z, θ)) = fun θ => Ψ z θ := rfl
    rw [heq] at hcomp
    exact hcomp
  -- 1. the `σ`-weighted second derivative is integrable
  have hint : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.TT.D2 (fun s => Ψ z s) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    refine MeasureTheory.IntegrableOn.congr_fun (hon_pthIter2_sEta_integrableOn h hz)
      (fun θ _ => ?_) measurableSet_Icc
    rfl
  have hcont2 : ContinuousOn (Work.FTS.EllipticEst.TT.D2 (fun s => Ψ z s))
      (Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContDiffOn ℝ 1 (deriv (fun s => Ψ z s)) (Set.Ioo 0 (Real.pi / 2)) :=
      (hsm 2).deriv_of_isOpen isOpen_Ioo (by norm_num)
    have h2 : ContDiffOn ℝ 0 (deriv (deriv (fun s => Ψ z s))) (Set.Ioo 0 (Real.pi / 2)) :=
      h1.deriv_of_isOpen isOpen_Ioo (by norm_num)
    have h3 : Work.FTS.EllipticEst.TT.D2 (fun s => Ψ z s)
        = deriv (deriv (fun s => Ψ z s)) := rfl
    rw [h3]
    exact h2.continuousOn
  have hD2abs : MeasureTheory.IntegrableOn
      (fun θ => |Work.FTS.EllipticEst.TT.D2 (fun s => Ψ z s) θ|) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.SgamBound.integrableOn_abs_of_sq_mul_sEta hcont2 hint
  -- 2. the slice is bounded
  have hπ4 : Real.pi / 4 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hbound1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv (fun s => Ψ z s) θ - deriv (fun s => Ψ z s) (Real.pi / 4)|
        ≤ ∫ x in Work.Spaces.Iθ, |Work.FTS.EllipticEst.TT.D2 (fun s => Ψ z s) x| :=
    fun θ hθ =>
      Work.FTS.EllipticEst.SgamBound.abs_deriv_sub_le_integral_abs_D2 hsm hD2abs hθ hπ4
  set E : ℝ := ∫ x in Work.Spaces.Iθ, |Work.FTS.EllipticEst.TT.D2 (fun s => Ψ z s) x| with hE
  have hE0 : 0 ≤ E := by
    rw [hE]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun x _ => abs_nonneg _)
  set K : ℝ := |deriv (fun s => Ψ z s) (Real.pi / 4)| + E with hK
  have hK0 : 0 ≤ K := by rw [hK]; exact add_nonneg (abs_nonneg _) hE0
  have hKbd : ∀ ξ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun s => Ψ z s) ξ| ≤ K := by
    intro ξ hξ
    have h1 := hbound1 ξ hξ
    have h2 : |deriv (fun s => Ψ z s) ξ|
        ≤ |deriv (fun s => Ψ z s) ξ - deriv (fun s => Ψ z s) (Real.pi / 4)|
          + |deriv (fun s => Ψ z s) (Real.pi / 4)| := by
      have := abs_add_le (deriv (fun s => Ψ z s) ξ - deriv (fun s => Ψ z s) (Real.pi / 4))
        (deriv (fun s => Ψ z s) (Real.pi / 4))
      simpa using this
    rw [hK, hE]
    linarith
  set M : ℝ := |Ψ z (Real.pi / 4)| + K * (Real.pi / 2) with hM
  have hM0 : 0 ≤ M := by
    rw [hM]; exact add_nonneg (abs_nonneg _) (mul_nonneg hK0 (by positivity))
  have hubd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |Ψ z θ| ≤ M := by
    intro θ hθ
    have h2 := Work.FTS.EllipticEst.SgamBound.abs_sub_le_mul_abs_sub_of_deriv_bound
      hsm hθ hπ4 hKbd
    have h3 : |θ - Real.pi / 4| ≤ Real.pi / 2 := by
      rw [abs_le]
      exact ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
    have h4 : K * |θ - Real.pi / 4| ≤ K * (Real.pi / 2) :=
      mul_le_mul_of_nonneg_left h3 hK0
    calc |Ψ z θ| = |(Ψ z θ - Ψ z (Real.pi / 4)) + Ψ z (Real.pi / 4)| := by
          rw [sub_add_cancel]
      _ ≤ |Ψ z θ - Ψ z (Real.pi / 4)| + |Ψ z (Real.pi / 4)| := abs_add_le _ _
      _ ≤ K * (Real.pi / 2) + |Ψ z (Real.pi / 4)| := by linarith
      _ = M := by rw [hM]; ring
  -- 3. the product with the bounded angular weight is integrable
  have hsinC2 : Continuous (fun θ : ℝ => Work.Elliptic.sinCos2 θ) := by
    simp only [Work.Elliptic.sinCos2]; fun_prop
  have hsinC2nn : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      0 ≤ Work.Elliptic.sinCos2 θ := by
    intro θ hθ
    rw [Work.Elliptic.sinCos2]
    have h1 : 0 ≤ Real.sin θ :=
      le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos]))
    exact mul_nonneg h1 (sq_nonneg _)
  have hsinC2le : ∀ θ : ℝ, Work.Elliptic.sinCos2 θ ≤ 1 := by
    intro θ
    rw [Work.Elliptic.sinCos2]
    rcases le_total (Real.sin θ) 0 with hs | hs
    · nlinarith [sq_nonneg (Real.cos θ)]
    · nlinarith [Real.sin_le_one θ, sq_nonneg (Real.cos θ), Real.cos_sq_le_one θ]
  have hst : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    have hpair : MeasureTheory.volume ({(0 : ℝ), Real.pi / 2} : Set ℝ) = 0 :=
      Set.Finite.measure_zero (by simp) MeasureTheory.volume
    have hpairab : ∀ᵐ x : ℝ, x ∉ ({(0 : ℝ), Real.pi / 2} : Set ℝ) := by
      rw [MeasureTheory.ae_iff]
      simpa only [not_not, Set.ofPred_mem_eq] using hpair
    filter_upwards [hpairab] with x hx
    refine propext ⟨?_, ?_⟩
    · intro hI
      rw [Work.Spaces.Iθ, Set.mem_Icc] at hI
      exact ⟨lt_of_le_of_ne hI.1 (fun hc => hx (Or.inl hc.symm)),
             lt_of_le_of_ne hI.2 (fun hc => hx (Or.inr hc))⟩
    · intro hI
      rw [Work.Spaces.Iθ, Set.mem_Icc]
      exact ⟨le_of_lt hI.1, le_of_lt hI.2⟩
  have hms : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set hst
  change MeasureTheory.Integrable (fun θ => |Ψ z θ| * Work.Elliptic.sinCos2 θ)
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  rw [hms]
  refine MeasureTheory.Integrable.of_bound ?_ (max M 0) ?_
  · exact ((hsm 0).continuousOn.abs.mul hsinC2.continuousOn).aestronglyMeasurable
      measurableSet_Ioo
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hψ0 := hsinC2nn θ hθ
    have hψ1 := hsinC2le θ
    have hu := hubd θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hψ0)]
    calc |Ψ z θ| * Work.Elliptic.sinCos2 θ ≤ M * Work.Elliptic.sinCos2 θ :=
          mul_le_mul_of_nonneg_right hu hψ0
      _ ≤ M * 1 := mul_le_mul_of_nonneg_left hψ1 hM0
      _ = M := mul_one M
      _ ≤ max M 0 := le_max_left _ _

end Work.FTS.EllipticEst.Honest
