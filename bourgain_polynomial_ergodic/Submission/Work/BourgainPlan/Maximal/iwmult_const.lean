import Mathlib
import Submission.Work.BourgainPlan.Maximal.iw_superset
import Submission.Work.BourgainPlan.Maximal.interval_projection_memLp

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped ENNReal FourierTransform

noncomputable section

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

/-- The inverse Fourier transform depends only on the a.e. class of its argument. -/
lemma fourierInv_congr_ae {f g : ℝ → ℂ} (h : f =ᵐ[(volume : Measure ℝ)] g) :
    FourierTransformInv.fourierInv f = FourierTransformInv.fourierInv g := by
  funext x
  rw [Real.fourierInv_eq', Real.fourierInv_eq']
  exact integral_congr_ae (h.mono fun y hy => by simp only [hy])

/-- The fundamental-domain lift of the constant symbol `1` on the circle is the indicator of the
fundamental domain. -/
lemma circleLift_one_eq :
    Work.BourgainPlan.Thm52.circleLift (fun _ : Circ => (1 : ℂ))
      = fun x : ℝ => if x ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) then (1 : ℂ) else 0 := by
  funext x
  by_cases hx : x ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)
  · simp only [Work.BourgainPlan.Thm52.circleLift_of_mem hx, if_pos hx]
  · simp only [Work.BourgainPlan.Thm52.circleLift_of_notMem hx, if_neg hx]

/-- The lift of the constant symbol `1` agrees a.e. with the open-interval indicator, the form in
which the interval-multiplier bound `interval_projection_memLp` is available. -/
lemma circleLift_one_ae_eq :
    Work.BourgainPlan.Thm52.circleLift (fun _ : Circ => (1 : ℂ))
      =ᵐ[(volume : Measure ℝ)]
        fun ξ : ℝ => if ξ ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) then (1 : ℂ) else 0 := by
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ (1 / 2 : ℝ) := by
    rw [MeasureTheory.ae_iff]
    have hset : {x : ℝ | ¬x ≠ (1 / 2 : ℝ)} = {(1 / 2 : ℝ)} := by
      ext x; simp
    rw [hset]
    simp
  filter_upwards [hae] with x hx
  by_cases h : x ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)
  · have h2 : x ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := ⟨h.1, lt_of_le_of_ne h.2 hx⟩
    simp only [circleLift_one_eq, if_pos h, if_pos h2]
  · have h2 : x ∉ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := fun hh => h ⟨hh.1, hh.2.le⟩
    simp only [circleLift_one_eq, if_neg h, if_neg h2]

/-- **The constant symbol on the circle is an `L^{2r}(ℝ)`-multiplier.**  Its lift is the indicator
of the fundamental domain `(-1/2, 1/2)`, and the interval (Dirichlet) multiplier `1_{(-1/2,1/2)}` is
bounded on every `L^p(ℝ)`, `1 < p < ∞` (`Maximal.interval_projection_memLp`). -/
theorem iwmult_const (r : ℕ) (hr : 2 ≤ r) :
    ∃ A : ℝ, 0 < A ∧ Work.BourgainPlan.Maximal.IWMult r
      (fun _ : Work.BourgainPlan.IonescuWainger.Circle => (1 : ℂ)) A := by
  set p : ℝ := 2 * (r : ℝ) with hpdef
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hp1 : 1 < p := by rw [hpdef]; linarith
  have hp0 : 0 < p := by rw [hpdef]; linarith
  obtain ⟨C, hCpos, hC⟩ := interval_projection_memLp p hp1
  refine ⟨C, hCpos, ?_⟩
  intro g hg
  have hcongr : (fun x : ℝ => ‖FourierTransformInv.fourierInv
        (fun ξ : ℝ => Work.BourgainPlan.Thm52.circleLift (fun _ : Circ => (1 : ℂ)) ξ
          * FourierTransform.fourier g ξ) x‖ₑ ^ p)
      = fun x : ℝ => ‖FourierTransformInv.fourierInv
        (fun ξ : ℝ => (if ξ ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) then (1 : ℂ) else 0)
          * FourierTransform.fourier g ξ) x‖ₑ ^ p := by
    funext x
    have h_ae : (fun ξ : ℝ => Work.BourgainPlan.Thm52.circleLift (fun _ : Circ => (1 : ℂ)) ξ
          * FourierTransform.fourier g ξ)
        =ᵐ[(volume : Measure ℝ)]
          (fun ξ : ℝ => (if ξ ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) then (1 : ℂ) else 0)
            * FourierTransform.fourier g ξ) :=
      circleLift_one_ae_eq.mul (Filter.EventuallyEq.refl _ _)
    rw [fourierInv_congr_ae h_ae]
  rw [hcongr]
  by_cases hLp : MemLp g (ENNReal.ofReal p) volume
  · exact hC (-(1 / 2)) (1 / 2) (by norm_num) g hg hLp
  · have hiff := MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (μ := (volume : Measure ℝ)) (p := ENNReal.ofReal p) (f := g)
      (ne_of_gt (ENNReal.ofReal_pos.mpr hp0)) ENNReal.ofReal_ne_top hg.1
    rw [ENNReal.toReal_ofReal hp0.le] at hiff
    have htop : ∫⁻ x : ℝ, ‖g x‖ₑ ^ p = ⊤ := by
      refine eq_top_iff.mpr (le_of_not_gt fun hc => hLp ?_)
      exact hiff.mpr hc
    have hne : ENNReal.ofReal (C ^ p) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hCpos p))
    rw [htop, ENNReal.mul_top hne]
    exact le_top

end

end Work.BourgainPlan.Maximal
