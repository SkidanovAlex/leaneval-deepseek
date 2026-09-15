import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.RingTheory.PicardGroup

set_option linter.unusedVariables false

namespace Commons.Analysis.Fourier

open MeasureTheory

namespace FourierLaplaceFinAux

variable {d : ℕ}

/-- The continuous linear functional `v ↦ ∑ i, v i * (a i : ℂ)` on `Fin d → ℂ`. -/
noncomputable def dirCLM (a : EuclideanSpace ℝ (Fin d)) : (Fin d → ℂ) →L[ℂ] ℂ :=
  ∑ i, (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) i).smulRight ((a i : ℂ))

lemma dirCLM_apply (a : EuclideanSpace ℝ (Fin d)) (v : Fin d → ℂ) :
    dirCLM a v = ∑ i, v i * (a i : ℂ) := by
  simp [dirCLM]

@[fun_prop] lemma continuous_dirCLM : Continuous (fun a : EuclideanSpace ℝ (Fin d) => dirCLM a) := by
  rw [show (fun a : EuclideanSpace ℝ (Fin d) => dirCLM a)
      = (fun a => ∑ i, (ContinuousLinearMap.proj (R := ℂ)
          (φ := fun _ : Fin d => ℂ) i).smulRight ((a i : ℂ))) from rfl]
  fun_prop

lemma norm_dirCLM_le (a : EuclideanSpace ℝ (Fin d)) : ‖dirCLM a‖ ≤ ∑ i, ‖(a i : ℂ)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg (fun i _ => norm_nonneg _))
  intro v
  rw [dirCLM_apply]
  calc ‖∑ i, v i * ↑(a i)‖ ≤ ∑ i, ‖v i * ↑(a i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖v i‖ * ‖(↑(a i) : ℂ)‖ := by simp
    _ ≤ ∑ i, ‖v‖ * ‖(↑(a i) : ℂ)‖ := by
        apply Finset.sum_le_sum; intro i _
        gcongr
        exact norm_le_pi_norm v i
    _ = (∑ i, ‖(↑(a i) : ℂ)‖) * ‖v‖ := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- The box `[-σ,σ]^d` in `ℝ^d`. -/
def fBox (σ : ℝ) : Set (EuclideanSpace ℝ (Fin d)) := {ξ | ∀ i, ξ i ∈ Set.Icc (-σ) σ}

lemma norm_dirCLM_le_of_mem {σ : ℝ} {a : EuclideanSpace ℝ (Fin d)} (ha : a ∈ fBox σ) :
    ‖dirCLM a‖ ≤ σ * (d : ℝ) := by
  calc ‖dirCLM a‖ ≤ ∑ i, ‖(a i : ℂ)‖ := norm_dirCLM_le a
    _ = ∑ i, |a i| := by simp
    _ ≤ ∑ _i : Fin d, σ := by
        apply Finset.sum_le_sum; intro i _
        rw [abs_le]; exact ⟨(ha i).1, (ha i).2⟩
    _ = σ * (d : ℝ) := by simp [Finset.sum_const, mul_comm]

lemma norm_two_pi_I : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
  have h : (2 * Real.pi * Complex.I : ℂ) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, norm_mul, Complex.norm_I, mul_one,
    show ‖((2 * Real.pi : ℝ) : ℂ)‖ = |2 * Real.pi| from by simp, abs_of_nonneg (by positivity)]

lemma norm_sum_coord_le {σ : ℝ} {z x : Fin d → ℂ} (hx : ‖x - z‖ ≤ 1)
    {a : EuclideanSpace ℝ (Fin d)} (ha : a ∈ fBox σ) :
    ‖∑ i, x i * (a i : ℂ)‖ ≤ σ * ((∑ i, ‖z i‖) + (d : ℝ)) := by
  calc ‖∑ i, x i * (a i : ℂ)‖ ≤ ∑ i, ‖x i * (a i : ℂ)‖ := norm_sum_le _ _
    _ = ∑ i, ‖x i‖ * ‖(a i : ℂ)‖ := by simp
    _ ≤ ∑ i, (‖z i‖ + 1) * σ := by
        apply Finset.sum_le_sum; intro i _
        apply mul_le_mul
        · have h1 : ‖x i‖ ≤ ‖z i‖ + 1 := by
            calc ‖x i‖ = ‖z i + (x i - z i)‖ := by ring_nf
              _ ≤ ‖z i‖ + ‖x i - z i‖ := norm_add_le _ _
              _ ≤ ‖z i‖ + 1 := by
                  gcongr
                  calc ‖x i - z i‖ = ‖(x - z) i‖ := by simp
                    _ ≤ ‖x - z‖ := norm_le_pi_norm _ i
                    _ ≤ 1 := hx
          exact h1
        · rw [show ‖(a i : ℂ)‖ = |a i| from by simp, abs_le]
          exact ⟨(ha i).1, (ha i).2⟩
        · positivity
        · positivity
    _ = σ * ((∑ i, ‖z i‖) + (d : ℝ)) := by
        rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const]
        simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        ring

lemma norm_exp_le {σ : ℝ} {z x : Fin d → ℂ} (hx : ‖x - z‖ ≤ 1)
    {a : EuclideanSpace ℝ (Fin d)} (ha : a ∈ fBox σ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (∑ i, x i * (a i : ℂ)))‖ ≤
      Real.exp (2 * Real.pi * σ * ((∑ i, ‖z i‖) + (d : ℝ))) := by
  refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
  calc ‖(2 * Real.pi * Complex.I : ℂ) * (∑ i, x i * (a i : ℂ))‖
      = ‖(2 * Real.pi * Complex.I : ℂ)‖ * ‖∑ i, x i * (a i : ℂ)‖ := norm_mul _ _
    _ = 2 * Real.pi * ‖∑ i, x i * (a i : ℂ)‖ := by rw [norm_two_pi_I]
    _ ≤ 2 * Real.pi * (σ * ((∑ i, ‖z i‖) + (d : ℝ))) := by
        gcongr
        exact norm_sum_coord_le hx ha
    _ = 2 * Real.pi * σ * ((∑ i, ‖z i‖) + (d : ℝ)) := by ring

/-- The integrand `ξ ↦ exp(2πi ∑ yᵢξᵢ) h ξ`. -/
noncomputable def Phi (h : EuclideanSpace ℝ (Fin d) → ℂ) (y : Fin d → ℂ)
    (ξ : EuclideanSpace ℝ (Fin d)) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (∑ i, y i * (ξ i : ℂ))) * h ξ

/-- The candidate derivative of `Phi` in the `y`-variable. -/
noncomputable def dPhi (h : EuclideanSpace ℝ (Fin d) → ℂ) (x : Fin d → ℂ)
    (ξ : EuclideanSpace ℝ (Fin d)) : (Fin d → ℂ) →L[ℂ] ℂ :=
  h ξ • (Complex.exp (2 * Real.pi * Complex.I * (∑ i, x i * (ξ i : ℂ))) •
    (2 * Real.pi * Complex.I) • (dirCLM ξ))

lemma hasFDerivAt_Phi (h : EuclideanSpace ℝ (Fin d) → ℂ) (x : Fin d → ℂ)
    (ξ : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (fun y : Fin d → ℂ => Phi h y ξ) (dPhi h x ξ) x := by
  have h1 : HasFDerivAt (fun y : Fin d → ℂ => ∑ i, y i * (ξ i : ℂ)) (dirCLM ξ) x := by
    rw [show (fun y : Fin d → ℂ => ∑ i, y i * (ξ i : ℂ)) = (fun y => dirCLM ξ y) from by
      funext v; exact (dirCLM_apply ξ v).symm]
    exact (dirCLM ξ).hasFDerivAt
  have h2 : HasFDerivAt (fun y : Fin d → ℂ => 2 * Real.pi * Complex.I * (∑ i, y i * (ξ i : ℂ)))
      ((2 * Real.pi * Complex.I) • (dirCLM ξ)) x := h1.const_mul _
  have h3 := h2.cexp
  have h4 : HasFDerivAt
      (fun y : Fin d → ℂ => Complex.exp (2 * Real.pi * Complex.I * (∑ i, y i * (ξ i : ℂ))) * h ξ)
      (h ξ • (Complex.exp (2 * Real.pi * Complex.I * (∑ i, x i * (ξ i : ℂ))) •
        (2 * Real.pi * Complex.I) • (dirCLM ξ))) x :=
    h3.mul_const (h ξ)
  simpa [Phi, dPhi] using h4

lemma dPhi_apply (h : EuclideanSpace ℝ (Fin d) → ℂ) (x : Fin d → ℂ)
    (ξ : EuclideanSpace ℝ (Fin d)) (v : Fin d → ℂ) :
    dPhi h x ξ v = 2 * Real.pi * Complex.I * (∑ i, v i * (ξ i : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * (∑ i, x i * (ξ i : ℂ))) * h ξ := by
  rw [dPhi]
  simp only [smul_apply, dirCLM_apply, smul_eq_mul]
  ring

lemma norm_dPhi_le {σ : ℝ} {h : EuclideanSpace ℝ (Fin d) → ℂ} {z x : Fin d → ℂ}
    (hx : ‖x - z‖ ≤ 1) {a : EuclideanSpace ℝ (Fin d)} (ha : a ∈ fBox σ) :
    ‖dPhi h x a‖ ≤ Real.exp (2 * Real.pi * σ * ((∑ i, ‖z i‖) + (d : ℝ))) *
      (2 * Real.pi * (σ * (d : ℝ))) * ‖h a‖ := by
  rw [dPhi, norm_smul]
  have hexp : ‖Complex.exp (2 * Real.pi * Complex.I * (∑ i, x i * (a i : ℂ)))‖ ≤
      Real.exp (2 * Real.pi * σ * ((∑ i, ‖z i‖) + (d : ℝ))) := norm_exp_le hx ha
  have hdir : ‖dirCLM a‖ ≤ σ * (d : ℝ) := norm_dirCLM_le_of_mem ha
  have hinner : ‖Complex.exp (2 * Real.pi * Complex.I * (∑ i, x i * (a i : ℂ))) •
      (2 * Real.pi * Complex.I) • (dirCLM a)‖ ≤
      Real.exp (2 * Real.pi * σ * ((∑ i, ‖z i‖) + (d : ℝ))) * (2 * Real.pi * (σ * (d : ℝ))) := by
    rw [norm_smul, norm_smul, norm_two_pi_I]
    apply mul_le_mul hexp (mul_le_mul_of_nonneg_left hdir (by positivity)) (by positivity)
    positivity
  calc ‖h a‖ * ‖Complex.exp (2 * Real.pi * Complex.I * (∑ i, x i * (a i : ℂ))) •
        (2 * Real.pi * Complex.I) • (dirCLM a)‖
      ≤ ‖h a‖ * (Real.exp (2 * Real.pi * σ * ((∑ i, ‖z i‖) + (d : ℝ))) *
          (2 * Real.pi * (σ * (d : ℝ)))) := mul_le_mul_of_nonneg_left hinner (norm_nonneg _)
    _ = Real.exp (2 * Real.pi * σ * ((∑ i, ‖z i‖) + (d : ℝ))) *
          (2 * Real.pi * (σ * (d : ℝ))) * ‖h a‖ := by ring

end FourierLaplaceFinAux

theorem hasFDerivAt_fourierLaplace_fin {d : ℕ} {σ : ℝ} (hσ : 0 ≤ σ)
    {h : EuclideanSpace ℝ (Fin d) → ℂ} (hh : MeasureTheory.Integrable h)
    (hsupp : ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
      ξ ∉ {ξ : EuclideanSpace ℝ (Fin d) | ∀ i, ξ i ∈ Set.Icc (-σ) σ} → h ξ = 0) (z : Fin d → ℂ) :
    ∃ L : (Fin d → ℂ) →L[ℂ] ℂ,
      (∀ v, L v = ∫ ξ : EuclideanSpace ℝ (Fin d),
        (2 * Real.pi * Complex.I) * (∑ i, v i * (ξ i : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I * (∑ i, z i * (ξ i : ℂ))) * h ξ) ∧
      HasFDerivAt (fun y : Fin d → ℂ => ∫ ξ : EuclideanSpace ℝ (Fin d),
        Complex.exp (2 * Real.pi * Complex.I * (∑ i, y i * (ξ i : ℂ))) * h ξ) L z := by
  let Kz : ℝ := Real.exp (2 * Real.pi * σ * ((∑ i, ‖z i‖) + (d : ℝ)))
  let M : ℝ := Kz * (2 * Real.pi * (σ * (d : ℝ)))
  let bound : EuclideanSpace ℝ (Fin d) → ℝ := fun a => M * ‖h a‖
  have hbound_int : Integrable bound (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) :=
    hh.norm.const_mul M
  have hsupp_box : ∀ᵐ a ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
      a ∉ FourierLaplaceFinAux.fBox σ → h a = 0 := hsupp
  have hcont_exp : ∀ x : Fin d → ℂ, Continuous (fun a : EuclideanSpace ℝ (Fin d) =>
      Complex.exp (2 * Real.pi * Complex.I * (∑ i, x i * (a i : ℂ)))) := fun x => by fun_prop
  have hF_meas : ∀ᶠ x in nhds z, AEStronglyMeasurable (fun a => FourierLaplaceFinAux.Phi h x a)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) := by
    apply Filter.Eventually.of_forall
    intro x
    simp only [FourierLaplaceFinAux.Phi]
    exact (hcont_exp x).aestronglyMeasurable.mul hh.aestronglyMeasurable
  have hF_int : Integrable (fun a => FourierLaplaceFinAux.Phi h z a)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) := by
    refine Integrable.mono' (g := fun a => Kz * ‖h a‖) (hh.norm.const_mul Kz) ?_ ?_
    · simp only [FourierLaplaceFinAux.Phi]
      exact (hcont_exp z).aestronglyMeasurable.mul hh.aestronglyMeasurable
    · filter_upwards [hsupp_box] with a ha
      by_cases haB : a ∈ FourierLaplaceFinAux.fBox σ
      · simp only [FourierLaplaceFinAux.Phi]
        calc ‖Complex.exp (2 * Real.pi * Complex.I * (∑ i, z i * (a i : ℂ))) * h a‖
            = ‖Complex.exp (2 * Real.pi * Complex.I * (∑ i, z i * (a i : ℂ)))‖ * ‖h a‖ :=
              norm_mul _ _
          _ ≤ Kz * ‖h a‖ := by
              apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
              exact FourierLaplaceFinAux.norm_exp_le (x := z) (by simp) haB
      · have h0 : h a = 0 := ha haB
        simp [FourierLaplaceFinAux.Phi, h0]
  have hF'_meas : AEStronglyMeasurable (fun a => FourierLaplaceFinAux.dPhi h z a)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) := by
    have hcont : Continuous (fun a : EuclideanSpace ℝ (Fin d) =>
        Complex.exp (2 * Real.pi * Complex.I * (∑ i, z i * (a i : ℂ))) •
          (2 * Real.pi * Complex.I) • (FourierLaplaceFinAux.dirCLM a)) := by fun_prop
    simp only [FourierLaplaceFinAux.dPhi]
    exact hh.aestronglyMeasurable.smul hcont.aestronglyMeasurable
  have h_bound : ∀ᵐ a ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
      ∀ x ∈ Metric.ball z 1, ‖FourierLaplaceFinAux.dPhi h x a‖ ≤ bound a := by
    filter_upwards [hsupp_box] with a ha
    intro x hx
    by_cases haB : a ∈ FourierLaplaceFinAux.fBox σ
    · have hx' : ‖x - z‖ ≤ 1 := by
        simpa [dist_eq_norm] using (Metric.mem_ball.mp hx).le
      show ‖FourierLaplaceFinAux.dPhi h x a‖ ≤ M * ‖h a‖
      exact FourierLaplaceFinAux.norm_dPhi_le hx' haB
    · have h0 : h a = 0 := ha haB
      have hzero : FourierLaplaceFinAux.dPhi h x a = 0 := by
        rw [FourierLaplaceFinAux.dPhi, h0]
        ext v; simp
      rw [hzero, norm_zero]
      show (0 : ℝ) ≤ M * ‖h a‖
      rw [h0, norm_zero, mul_zero]
  have h_diff : ∀ᵐ a ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
      ∀ x ∈ Metric.ball z 1,
        HasFDerivAt (fun y : Fin d → ℂ => FourierLaplaceFinAux.Phi h y a)
          (FourierLaplaceFinAux.dPhi h x a) x :=
    Filter.Eventually.of_forall fun a => fun x _ => FourierLaplaceFinAux.hasFDerivAt_Phi h x a
  have hmain : HasFDerivAt (fun x : Fin d → ℂ => ∫ a, FourierLaplaceFinAux.Phi h x a)
      (∫ a, FourierLaplaceFinAux.dPhi h z a) z :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
      (F := fun x a => FourierLaplaceFinAux.Phi h x a)
      (F' := fun x a => FourierLaplaceFinAux.dPhi h x a)
      (bound := bound) (x₀ := z) (s := Metric.ball z 1)
      (Metric.ball_mem_nhds z (by norm_num)) hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  refine ⟨∫ a, FourierLaplaceFinAux.dPhi h z a, ?_, ?_⟩
  · intro v
    have hF'z_int : Integrable (fun a => FourierLaplaceFinAux.dPhi h z a)
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) := by
      refine Integrable.mono' hbound_int hF'_meas ?_
      filter_upwards [h_bound] with a ha
      exact ha z (Metric.mem_ball_self (by norm_num))
    rw [ContinuousLinearMap.integral_apply hF'z_int v]
    apply integral_congr_ae
    filter_upwards with a
    rw [FourierLaplaceFinAux.dPhi_apply]
  · exact hmain

end Commons.Analysis.Fourier