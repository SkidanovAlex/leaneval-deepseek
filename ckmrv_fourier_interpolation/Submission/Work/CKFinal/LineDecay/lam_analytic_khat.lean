import Mathlib
import Submission.Work.CKFinal.LineDecay.LamDefs
import Submission.Work.CKFinal.LineDecay.ContourPoint
import Submission.Work.CKFinal.LineDecay.AxisFacts
import Submission.Work.CKFinal.LineDecay.khat_tail_deviation
import Submission.Work.CKFinal.LineDecay.khat_phi_bound
import Submission.Work.CKFinal.LineDecay.khat_low_bound
import Submission.Work.CKFinal.LineDecay.analyticOnNhd_laplace_interval
import Submission.Work.CKFinal.LineDecay.analyticOnNhd_laplace_tail
import Submission.Work.CKFinal.LineDecay.analyticOnNhd_laplace_interval_affine
import Submission.Work.CKFinal.LineDecay.analytic_prelim

namespace Work.CKFinal.LineDecay

open UpperHalfPlane MeasureTheory
open scoped Topology Manifold

noncomputable section

/-- The half plane `{z : -π < z.re}` on which both sides of the `λ`-identity are analytic. -/
def lamPlane : Set ℂ := {z : ℂ | -(Real.pi) < z.re}

lemma isOpen_lamPlane : IsOpen lamPlane :=
  isOpen_lt continuous_const Complex.continuous_re

variable {ℓ : Work.Kernels.LogLambdaData} {d : ℕ} {τ : UpperHalfPlane}

/-- `Kax` at the axis point `i t` is the kernel at the contour point `zcb t`. -/
lemma Kax_zero_zcb (K : ℍ → ℍ → ℂ) {t : ℝ} (ht : 0 < t) : Kax K τ 0 t = K τ (zcb t) := by
  rw [Kax_eq K τ ht, zero_vadd]

/-- `Kax` at height `hsplit = 1` is the kernel at `x + i`. -/
lemma Kax_hsplit (K : ℍ → ℍ → ℂ) (x : ℝ) : Kax K τ x hsplit = K τ (x +ᵥ zcb 1) := by
  rw [Kax_eq K τ (by rw [hsplit]; norm_num : (0 : ℝ) < hsplit)]
  rfl

/-- `Aexp` is continuous in the contour parameter. -/
lemma continuous_Aexp (G : Fin 2 → Fin 2 → ℍ → ℂ) (τ : ℍ) :
    Continuous (fun t : ℝ => Work.Asymptotics.Aexp G τ t) := by
  simp only [Work.Asymptotics.Aexp]
  fun_prop

/-- **Analyticity of the low piece** `∫_0^1 K̂(τ,i t) e^{-zt} dt`. -/
theorem analyticOnNhd_lowInt (hd : d = 8 ∨ d = 24) (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2)
    (hy : 12 ≤ τ.im) :
    AnalyticOnNhd ℂ (fun z : ℂ => lowInt (Work.Kernels.Khat ℓ d) τ z) lamPlane := by
  have hcont : ContinuousOn (fun t : ℝ => Kax (Work.Kernels.Khat ℓ d) τ 0 t) (Set.Ioi 0) :=
    (khat_axis_continuous ℓ d hd hre hy).congr (fun t ht => Kax_zero_zcb _ ht)
  obtain ⟨M, hM⟩ := khat_low_bound ℓ d hd τ hre hy (axis_divisor_lower hre hy)
  have hbdd : ∃ M : ℝ, ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ‖Kax (Work.Kernels.Khat ℓ d) τ 0 t‖ ≤ M :=
    ⟨M, fun t ht => by rw [Kax_zero_zcb _ ht.1]; exact hM t ht⟩
  have h := analyticOnNhd_laplace_interval (g := fun t : ℝ => Kax (Work.Kernels.Khat ℓ d) τ 0 t)
    (a := 0) (b := 1) (by norm_num) (hcont.mono (fun t ht => ht.1)) hbdd
  exact h.mono (Set.subset_univ _)

/-- **Analyticity of the tail piece** `∫_1^∞ (K̂(τ,i t) - Aexp Ĝ(τ,t)) e^{-zt} dt`. -/
theorem analyticOnNhd_tailInt (hd : d = 8 ∨ d = 24) (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2)
    (hy : 12 ≤ τ.im) :
    AnalyticOnNhd ℂ (fun z : ℂ => tailInt (Work.Kernels.Khat ℓ d) (Ghat ℓ d) τ z) lamPlane := by
  have hcont0 := khat_axis_continuous ℓ d hd hre hy
  have hcont : ContinuousOn (fun t : ℝ => Kax (Work.Kernels.Khat ℓ d) τ 0 t
      - Work.Asymptotics.Aexp (Ghat ℓ d) τ t) (Set.Ici 1) :=
    ((hcont0.congr (fun t ht => Kax_zero_zcb _ ht)).mono
        (fun t ht => Set.mem_Ioi.mpr (lt_of_lt_of_le one_pos (Set.mem_Ici.mp ht)))).sub
      (continuous_Aexp (Ghat ℓ d) τ).continuousOn
  obtain ⟨C, N, hC, hb⟩ := khat_tail_deviation ℓ d hd τ hre hy hcont0
  refine analyticOnNhd_laplace_tail (ContinuousOn.aestronglyMeasurable hcont measurableSet_Ici)
    ⟨C, N, hC, fun t ht => ?_⟩
  have ht1 : (0 : ℝ) < t := lt_of_lt_of_le one_pos (Set.mem_Ici.mp ht)
  rw [Kax_zero_zcb _ ht1, Aexp_Ghat_eq ℓ d hd τ ht1]
  exact hb t ht

/-- **Analyticity of the `Φ` piece** `∫_1^∞ Φ(K̂,τ,t) e^{-zt} dt`. -/
theorem analyticOnNhd_phiInt (hd : d = 8 ∨ d = 24) (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2)
    (hy : 12 ≤ τ.im) :
    AnalyticOnNhd ℂ (fun z : ℂ => phiInt (Work.Kernels.Khat ℓ d) τ z) lamPlane := by
  have hdiv := axis_divisor_lower hre hy
  obtain ⟨C, N, hC, hb⟩ := khat_phi_bound ℓ d hd τ hre hy hdiv
  have hsub : Set.Ici (1 : ℝ) ⊆ Set.Ioi 0 :=
    fun t ht => Set.mem_Ioi.mpr (lt_of_lt_of_le one_pos (Set.mem_Ici.mp ht))
  have hcont : ContinuousOn (fun t : ℝ => Phi (Work.Kernels.Khat ℓ d) τ t) (Set.Ici 1) := by
    have h0 : ContinuousOn (fun t : ℝ => Kax (Work.Kernels.Khat ℓ d) τ 0 t) (Set.Ici 1) :=
      ((khat_axis_continuous ℓ d hd hre hy).congr (fun t ht => Kax_zero_zcb _ ht)).mono hsub
    have h1 : ContinuousOn (fun t : ℝ => Kax (Work.Kernels.Khat ℓ d) τ 1 t) (Set.Ici 1) :=
      (khat_shift_continuous ℓ d hd hre hy (Or.inl rfl)).congr
        (fun t ht => Kax_eq _ _ (Set.mem_Ioi.mp (hsub ht)))
    have h2 : ContinuousOn (fun t : ℝ => Kax (Work.Kernels.Khat ℓ d) τ (-1) t) (Set.Ici 1) :=
      (khat_shift_continuous ℓ d hd hre hy (Or.inr rfl)).congr
        (fun t ht => Kax_eq _ _ (Set.mem_Ioi.mp (hsub ht)))
    have hmain : ContinuousOn (fun t : ℝ => 2 * Kax (Work.Kernels.Khat ℓ d) τ 0 t
        - Kax (Work.Kernels.Khat ℓ d) τ (-1) t - Kax (Work.Kernels.Khat ℓ d) τ 1 t)
        (Set.Ici 1) :=
      ((continuousOn_const.mul h0).sub h2).sub h1
    simpa only [Phi] using hmain
  exact analyticOnNhd_laplace_tail
    (ContinuousOn.aestronglyMeasurable (μ := volume) hcont measurableSet_Ici) ⟨C, N, hC, hb⟩

/-- The exponent identity `z * (I * x - 1) = I * z * (x + i)` used for the horizontal pieces. -/
private lemma hor_exp_eq (z x : ℂ) :
    Complex.I * z * (x + (1 : ℂ) * Complex.I) = z * (Complex.I * x + (-1)) := by
  calc Complex.I * z * (x + (1 : ℂ) * Complex.I)
      = Complex.I * z * x + (Complex.I * Complex.I) * z := by ring
    _ = Complex.I * z * x + (-1) * z := by rw [Complex.I_mul_I]
    _ = z * (Complex.I * x + (-1)) := by ring

/-- **Analyticity of the first horizontal piece.** -/
theorem analyticOnNhd_horInt1 (hd : d = 8 ∨ d = 24) (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2)
    (hy : 12 ≤ τ.im) :
    AnalyticOnNhd ℂ (fun z : ℂ => horInt1 (Work.Kernels.Khat ℓ d) τ z) lamPlane := by
  have hseg := khat_segment_continuous ℓ d hd hre hy
  have hcont : ContinuousOn (fun x : ℝ => Kax (Work.Kernels.Khat ℓ d) τ (x - 1) hsplit)
      (Set.Ioo 0 1) := by
    have h1 : ContinuousOn (fun x : ℝ => Work.Kernels.Khat ℓ d τ ((x - 1) +ᵥ zcb 1))
        (Set.Ioo 0 1) := by
      refine hseg.comp (continuous_id.sub continuous_const).continuousOn ?_
      intro x hx
      rw [Set.mem_Icc]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact h1.congr (fun x _ => Kax_hsplit _ _)
  have hbdd : ∃ M : ℝ, ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ‖Kax (Work.Kernels.Khat ℓ d) τ (t - 1) hsplit‖ ≤ M := by
    obtain ⟨M, hM⟩ := khat_segment_bound ℓ d hd hre hy
    refine ⟨M, fun t ht => ?_⟩
    rw [Kax_hsplit _ _]
    exact hM (t - 1) (by
      rw [Set.mem_Icc]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have h := analyticOnNhd_laplace_interval_affine
    (g := fun x : ℝ => Kax (Work.Kernels.Khat ℓ d) τ (x - 1) hsplit)
    (a := 0) (b := 1) (by norm_num) hcont hbdd Complex.I (-1)
  have h' : AnalyticOnNhd ℂ (fun z : ℂ => ∫ t in (0 : ℝ)..1,
      Kax (Work.Kernels.Khat ℓ d) τ (t - 1) hsplit
        * Complex.exp (z * (Complex.I * (t : ℂ) + (-1)))) lamPlane :=
    h.mono (Set.subset_univ lamPlane)
  refine AnalyticOnNhd.congr isOpen_lamPlane h' ?_
  intro z _
  change (∫ t in (0 : ℝ)..1, Kax (Work.Kernels.Khat ℓ d) τ (t - 1) hsplit
      * Complex.exp (z * (Complex.I * (t : ℂ) + (-1))))
    = (∫ x in (0 : ℝ)..1, Kax (Work.Kernels.Khat ℓ d) τ (x - 1) hsplit
      * Complex.exp (Complex.I * z * ((x : ℂ) + (hsplit : ℂ) * Complex.I)))
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  rw [show Complex.I * z * ((x : ℂ) + (hsplit : ℂ) * Complex.I)
      = z * (Complex.I * (x : ℂ) + (-1)) from by
    change Complex.I * z * ((x : ℂ) + (1 : ℂ) * Complex.I) = z * (Complex.I * (x : ℂ) + (-1))
    exact hor_exp_eq z (x : ℂ)]

/-- **Analyticity of the second horizontal piece.** -/
theorem analyticOnNhd_horInt2 (hd : d = 8 ∨ d = 24) (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2)
    (hy : 12 ≤ τ.im) :
    AnalyticOnNhd ℂ (fun z : ℂ => horInt2 (Work.Kernels.Khat ℓ d) τ z) lamPlane := by
  have hseg := khat_segment_continuous ℓ d hd hre hy
  have hcont : ContinuousOn (fun x : ℝ => Kax (Work.Kernels.Khat ℓ d) τ (x + 1) hsplit)
      (Set.Ioo (-1) 0) := by
    have h1 : ContinuousOn (fun x : ℝ => Work.Kernels.Khat ℓ d τ ((x + 1) +ᵥ zcb 1))
        (Set.Ioo (-1) 0) := by
      refine hseg.comp (continuous_id.add continuous_const).continuousOn ?_
      intro x hx
      rw [Set.mem_Icc]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact h1.congr (fun x _ => Kax_hsplit _ _)
  have hbdd : ∃ M : ℝ, ∀ t ∈ Set.Ioo (-1 : ℝ) 0,
      ‖Kax (Work.Kernels.Khat ℓ d) τ (t + 1) hsplit‖ ≤ M := by
    obtain ⟨M, hM⟩ := khat_segment_bound ℓ d hd hre hy
    refine ⟨M, fun t ht => ?_⟩
    rw [Kax_hsplit _ _]
    exact hM (t + 1) (by
      rw [Set.mem_Icc]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have h := analyticOnNhd_laplace_interval_affine
    (g := fun x : ℝ => Kax (Work.Kernels.Khat ℓ d) τ (x + 1) hsplit)
    (a := -1) (b := 0) (by norm_num) hcont hbdd Complex.I (-1)
  have h' : AnalyticOnNhd ℂ (fun z : ℂ => ∫ t in (-1 : ℝ)..0,
      Kax (Work.Kernels.Khat ℓ d) τ (t + 1) hsplit
        * Complex.exp (z * (Complex.I * (t : ℂ) + (-1)))) lamPlane :=
    h.mono (Set.subset_univ lamPlane)
  refine AnalyticOnNhd.congr isOpen_lamPlane h' ?_
  intro z _
  change (∫ t in (-1 : ℝ)..0, Kax (Work.Kernels.Khat ℓ d) τ (t + 1) hsplit
      * Complex.exp (z * (Complex.I * (t : ℂ) + (-1))))
    = (∫ x in (-1 : ℝ)..0, Kax (Work.Kernels.Khat ℓ d) τ (x + 1) hsplit
      * Complex.exp (Complex.I * z * ((x : ℂ) + (hsplit : ℂ) * Complex.I)))
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  rw [show Complex.I * z * ((x : ℂ) + (hsplit : ℂ) * Complex.I)
      = z * (Complex.I * (x : ℂ) + (-1)) from by
    change Complex.I * z * ((x : ℂ) + (1 : ℂ) * Complex.I) = z * (Complex.I * (x : ℂ) + (-1))
    exact hor_exp_eq z (x : ℂ)]

/-- **Holomorphy of the two sides of the CKMRV identity in `z = λ = π r²`**, for the hatted pair
`(K̂^{(d)}, Ĝ)`.  Same argument as `lam_analytic_kfun`, with the pointwise inputs for the kernel
`Khat` in place of `Kfun` (the extra entire summand `exp(I τ z)` inside `LHSz` is harmless). -/
theorem lam_analytic_khat (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (hτ : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) (hy : 12 ≤ τ.im) :
    AnalyticOnNhd ℂ (Work.CKFinal.LHSz (Work.Kernels.Khat ℓ d) (Work.CKFinal.Ghat ℓ d) τ)
        {z : ℂ | -(Real.pi) < z.re}
    ∧ AnalyticOnNhd ℂ (Work.CKFinal.RHSz (Work.Kernels.Khat ℓ d) τ)
        {z : ℂ | -(Real.pi) < z.re} := by
  obtain ⟨hlam, -, hhigh⟩ := analytic_prelim
  have hlamP : AnalyticOnNhd ℂ Work.CKFinal.lamS lamPlane := hlam.mono (Set.subset_univ lamPlane)
  have hexpP : AnalyticOnNhd ℂ (fun z : ℂ => Complex.exp (Complex.I * (τ : ℂ) * z)) lamPlane := by
    have hlin : AnalyticOnNhd ℂ (fun z : ℂ => Complex.I * (τ : ℂ) * z) Set.univ :=
      (analyticOnNhd_const (v := Complex.I * (τ : ℂ))).mul analyticOnNhd_id
    exact (analyticOnNhd_cexp.comp hlin (fun z _ => Set.mem_univ _)).mono (Set.subset_univ lamPlane)
  have hlow := analyticOnNhd_lowInt (ℓ := ℓ) (d := d) (τ := τ) hd hτ hy
  have htail := analyticOnNhd_tailInt (ℓ := ℓ) (d := d) (τ := τ) hd hτ hy
  have hphi := analyticOnNhd_phiInt (ℓ := ℓ) (d := d) (τ := τ) hd hτ hy
  have hh1 := analyticOnNhd_horInt1 (ℓ := ℓ) (d := d) (τ := τ) hd hτ hy
  have hh2 := analyticOnNhd_horInt2 (ℓ := ℓ) (d := d) (τ := τ) hd hτ hy
  have hhi : AnalyticOnNhd ℂ (fun z : ℂ => Work.CKFinal.highPartC (Work.CKFinal.Ghat ℓ d) τ z)
      lamPlane := (hhigh (Work.CKFinal.Ghat ℓ d) τ).mono (Set.subset_univ lamPlane)
  constructor
  · change AnalyticOnNhd ℂ (fun z : ℂ => Work.CKFinal.LHSz (Work.Kernels.Khat ℓ d)
      (Work.CKFinal.Ghat ℓ d) τ z) lamPlane
    change AnalyticOnNhd ℂ (fun z : ℂ => Complex.exp (Complex.I * (τ : ℂ) * z)
      + (Work.CKFinal.lamS z * (Work.CKFinal.lowInt (Work.Kernels.Khat ℓ d) τ z
          + Work.CKFinal.tailInt (Work.Kernels.Khat ℓ d) (Work.CKFinal.Ghat ℓ d) τ z)
        + Work.CKFinal.highPartC (Work.CKFinal.Ghat ℓ d) τ z)) lamPlane
    exact hexpP.add ((hlamP.mul (hlow.add htail)).add hhi)
  · change AnalyticOnNhd ℂ (fun z : ℂ => Work.CKFinal.RHSz (Work.Kernels.Khat ℓ d) τ z) lamPlane
    change AnalyticOnNhd ℂ (fun z : ℂ => Work.CKFinal.lamS z
        * Work.CKFinal.lowInt (Work.Kernels.Khat ℓ d) τ z
      + (-Complex.I * Work.CKFinal.horInt1 (Work.Kernels.Khat ℓ d) τ z
          + Complex.I * Work.CKFinal.horInt2 (Work.Kernels.Khat ℓ d) τ z)
      + Work.CKFinal.phiInt (Work.Kernels.Khat ℓ d) τ z) lamPlane
    exact ((hlamP.mul hlow).add
      (((analyticOnNhd_const (v := -Complex.I)).mul hh1).add
        ((analyticOnNhd_const (v := Complex.I)).mul hh2))).add hphi

end

end Work.CKFinal.LineDecay
