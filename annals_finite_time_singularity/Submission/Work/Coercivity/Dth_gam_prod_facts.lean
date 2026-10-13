import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Coercivity.CTDefs
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Coercivity.rpow_neg_sq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open MeasureTheory Set Filter
open scoped Real Topology

theorem Dth_gam_prod_facts (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hs : Work.Spaces.SmoothNbhd f)
    (hsl : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.Dth f z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ)
    (hQ : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth f z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iz) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    ∧ MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    ∧ ∫ p, (Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ))
      = Work.Coercivity.CT.Ewgam α (Work.Spaces.Dth f) := by
  -- the open quadrant on which every weight is continuous
  set Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) with hQd_def
  have hQd_nbh : Qd ⊆ Spaces.nbhU := by
    rw [hQd_def]
    exact Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num))
      (Set.Ioo_subset_Ioo (by norm_num) (by linarith [Real.pi_pos]))
  have hsin_pos : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), 0 < Real.sin (2 * θ) := by
    intro θ hθ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have hcontDth : ContinuousOn (fun p : ℝ × ℝ => Spaces.Dth f p.1 p.2) Qd :=
    (Spaces.SmoothNbhd.Dth hs).continuousOn.mono hQd_nbh
  have hcontw : ContinuousOn (fun p : ℝ × ℝ => Spaces.w p.1) Qd := by
    rw [hQd_def]
    simp only [Spaces.w]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    exact pow_ne_zero 2 (ne_of_gt hp.1)
  have hcontsin : ContinuousOn
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Spaces.gam α / 2))) Qd := by
    rw [hQd_def]
    refine ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => ?_)
    exact Or.inl (ne_of_gt (hsin_pos p.2 hp.2))
  -- joint continuity of the weighted function, and of its square
  have hcont1 : ContinuousOn (fun p : ℝ × ℝ => Spaces.Dth f p.1 p.2 * Spaces.w p.1
      * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α / 2))) Qd :=
    (hcontDth.mul hcontw).mul hcontsin
  have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ => Spaces.Dth f p.1 p.2 * Spaces.w p.1
      * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α / 2)))
      ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) :=
    Spaces.aesm_of_continuousOn_Qd _ hcont1
  have hcont2 : ContinuousOn (fun p : ℝ × ℝ => (Spaces.Dth f p.1 p.2 * Spaces.w p.1
      * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α / 2))) ^ 2) Qd := hcont1.pow 2
  have haesm2 : AEStronglyMeasurable (fun p : ℝ × ℝ => (Spaces.Dth f p.1 p.2 * Spaces.w p.1
      * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α / 2))) ^ 2)
      ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) :=
    Spaces.aesm_of_continuousOn_Qd _ hcont2
  -- the pointwise identification of the squared weight with the `Ewgam` integrand
  have hpt : ∀ z θ, θ ∈ Spaces.Iθ →
      (Spaces.Dth f z θ * Spaces.w z * (Real.sin (2 * θ)) ^ (-(Spaces.gam α / 2))) ^ 2
        = (Spaces.Dth f z θ) ^ 2 * (Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := by
    intro z θ hθ
    have hs0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    rw [mul_pow, mul_pow, rpow_neg_sq (Real.sin (2 * θ)) (Spaces.gam α) hs0]
  -- the slices are integrable a.e.
  have hIz_ae : (volume.restrict Spaces.Iz) = volume.restrict (Set.Ioi (0 : ℝ)) := by
    apply Measure.restrict_congr_set
    exact (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
  have hpos : ∀ᵐ z ∂(volume.restrict Spaces.Iz), 0 < z := by
    rw [hIz_ae]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
  have hslice : ∀ᵐ z ∂(volume.restrict Spaces.Iz),
      Integrable (fun θ => (Spaces.Dth f z θ * Spaces.w z
        * (Real.sin (2 * θ)) ^ (-(Spaces.gam α / 2))) ^ 2) (volume.restrict Spaces.Iθ) := by
    filter_upwards [hpos] with z hz
    have h1 : Integrable
        (fun θ => (Spaces.Dth f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))
        (volume.restrict Spaces.Iθ) := hsl z hz
    have h2 : Integrable (fun θ => (Spaces.w z) ^ 2
        * ((Spaces.Dth f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))))
        (volume.restrict Spaces.Iθ) := h1.const_mul _
    refine h2.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [hpt z θ hθ]
    ring
  -- the function of the outer variable is integrable (this is the hypothesis `hQ`)
  have hHE : (fun z => ∫ θ, (Spaces.Dth f z θ * Spaces.w z
        * (Real.sin (2 * θ)) ^ (-(Spaces.gam α / 2))) ^ 2 ∂(volume.restrict Spaces.Iθ))
      = (fun z => ∫ θ in Spaces.Iθ, (Spaces.Dth f z θ) ^ 2 * (Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) := by
    funext z
    apply MeasureTheory.integral_congr_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact hpt z θ hθ
  have houter : Integrable (fun z => ∫ θ, (Spaces.Dth f z θ * Spaces.w z
        * (Real.sin (2 * θ)) ^ (-(Spaces.gam α / 2))) ^ 2 ∂(volume.restrict Spaces.Iθ))
      (volume.restrict Spaces.Iz) :=
    hQ.congr (Filter.Eventually.of_forall (fun z => congr_fun hHE.symm z))
  obtain ⟨hint, hval⟩ := Spaces.integrable_prod_of_iterated
    (μ := volume.restrict Spaces.Iz) (ν := volume.restrict Spaces.Iθ)
    (G := fun z θ => (Spaces.Dth f z θ * Spaces.w z * (Real.sin (2 * θ)) ^ (-(Spaces.gam α / 2))) ^ 2)
    (fun a b => sq_nonneg _) haesm2 hslice houter
  have hval' : ∫ p, (Spaces.Dth f p.1 p.2 * Spaces.w p.1
        * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α / 2))) ^ 2
        ∂((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ))
      = ∫ a, (∫ b, (Spaces.Dth f a b * Spaces.w a
          * (Real.sin (2 * b)) ^ (-(Spaces.gam α / 2))) ^ 2
          ∂(volume.restrict Spaces.Iθ)) ∂(volume.restrict Spaces.Iz) := hval
  refine ⟨haesm, ?_, ?_⟩
  · exact hint
  · rw [hval', hHE]
    rfl

end Work.Coercivity
