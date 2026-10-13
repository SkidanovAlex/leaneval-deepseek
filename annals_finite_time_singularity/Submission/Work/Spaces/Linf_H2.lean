import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HardyTheta
import Submission.Work.Spaces.HardyZ
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 1000000


/-- At every point of the closed quadrant, a `SmoothNbhd` function is `C^∞`. -/
theorem contDiffAt_uncurry_of_SmoothNbhd {g : ℝ → ℝ → ℝ} (hsm : SmoothNbhd g) {z θ : ℝ}
    (hz : z ∈ Iz) (hθ : θ ∈ Iθ) : ContDiffAt ℝ ⊤ (Function.uncurry g) (z, θ) :=
  hsm.contDiffAt (isOpen_nbhU.mem_nhds (mem_nbhU hz hθ))

/-- The weighted squares of `∂_θ (D_z g)` and of the mixed derivative `D_z D_θ g` agree:
`(w z)² (∂_θ D_z g)² sin(2θ)^{2-γ} = (D_z D_θ g)² W²`.  This is the pointwise weight
bookkeeping that identifies the integrand of the angular Hardy inequality for `D_z g`
with the `(D_z D_θ g · W)²` term of the `H²`-integrand. -/
theorem pth_Dz_sq_rpow_eq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (g : ℝ → ℝ → ℝ)
    (hsm : SmoothNbhd g) :
    ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      (w z) ^ 2 * (pth (Dz g) z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - gam α)
      = (mixed 1 1 g z θ) ^ 2 * (Wt α z θ) ^ 2 := by
  intro z hz θ hθ
  have hcd : ContDiffAt ℝ 2 (Function.uncurry g) (z, θ) :=
    (contDiffAt_uncurry_of_SmoothNbhd hsm hz hθ).of_le (by norm_num)
  have hcomm : mixed 1 1 g z θ = Real.sin (2 * θ) * pth (Dz g) z θ := by
    show Dz (Dth g) z θ = Real.sin (2 * θ) * pth (Dz g) z θ
    rw [Dz_Dth_comm hcd]; rfl
  have hs : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [hθ.1]
    · linarith [hθ.2, Real.pi_pos]
  have hgam0 : 0 < gam α := gam_pos hα
  have hgam2 : gam α < 2 := by rw [gam]; linarith
  have hsγ : (Real.sin (2 * θ)) ^ (2 - gam α)
      = Real.sin (2 * θ) * Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(gam α)) := by
    rw [show (2 - gam α) = 2 + (-(gam α)) by ring,
        Real.rpow_add' hs (by linarith : 2 + (-(gam α)) ≠ 0), Real.rpow_two, pow_two]
  have hwt : Wt α z θ * Wt α z θ = w z * w z * (Real.sin (2 * θ)) ^ (-(gam α)) := by
    have h1 : Real.sin (2 * θ) ^ (-(gam α / 2)) * Real.sin (2 * θ) ^ (-(gam α / 2))
        = Real.sin (2 * θ) ^ (-(gam α)) := by
      rw [← Real.rpow_add' hs
            (by intro hh; linarith [hgam0, hh] : (-(gam α / 2)) + (-(gam α / 2)) ≠ 0),
          show (-(gam α / 2)) + (-(gam α / 2)) = -(gam α) by ring]
    rw [Wt, wTheta,
        show w z * Real.sin (2 * θ) ^ (-(gam α / 2)) * (w z * Real.sin (2 * θ) ^ (-(gam α / 2)))
          = w z * w z * (Real.sin (2 * θ) ^ (-(gam α / 2))
              * Real.sin (2 * θ) ^ (-(gam α / 2))) by ring,
        h1]
  simp only [pow_two]
  rw [hcomm, hsγ, hwt]
  ring


/-- Angular Hardy step on `D_z g`, written with the `H²`-integrand on the right.
`HardyTheta` applied to the function `D_z g` (which vanishes at `θ = 0` because of
`VanishTheta`) bounds `(D_z g)²` by an angular integral of `∂_θ (D_z g)` with the
weight `sin(2θ)^{2-γ}`; the pointwise identity `pth_Dz_sq_rpow_eq` rewrites that
integral as `∫_θ (D_z D_θ g · W)²`, which is dominated by `HkIntegrand`. -/
theorem Dz_HardyTheta_HkIntegrand (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (g : ℝ → ℝ → ℝ)
    (hsm : SmoothNbhd g) (hvt : VanishTheta g) (hmem : HkMem α 2 g) :
    ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      (Dz g z θ) ^ 2 * (w z) ^ 2
        ≤ (100 / (gam α - 1)) * ∫ σ in Iθ, HkIntegrand α 2 g z σ := by
  intro z hz θ hθ
  have hzle : (0 : ℝ) ≤ z := hz
  have hsm' : SmoothNbhd (Dz g) := SmoothNbhd.Dz hsm
  have h0 : Dz g z 0 = 0 := by
    simp only [Dz, pz]
    rw [show (fun z' => g z' 0) = (fun _ => (0 : ℝ)) from funext (fun z' => hvt.1 z')]
    simp
  have hgam2 : gam α < 2 := by rw [gam]; linarith
  have hc : 0 < 2 - gam α := by linarith
  have hHint : IntegrableOn
      (fun σ => (pth (Dz g) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) Iθ := by
    rcases eq_or_lt_of_le hzle with hz0 | hzpos
    · subst hz0
      have hzero : (fun σ => (pth (Dz g) 0 σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α))
          = (fun _ => (0 : ℝ)) := by
        funext σ
        have hp : pth (Dz g) 0 σ = 0 := by
          show deriv (fun θ' => Dz g 0 θ') σ = 0
          rw [show (fun θ' => Dz g 0 θ') = (fun _ => (0 : ℝ)) from funext (fun θ' => by simp [Dz]),
              deriv_const]
        rw [hp]; ring
      rw [hzero]; exact integrableOn_zero
    · have hw1 : 1 ≤ (w z) ^ 2 := by
        have : 1 ≤ w z := by
          rw [w]
          rw [one_le_div (by positivity : (0:ℝ) < z ^ 2)]
          nlinarith [sq_nonneg z]
        nlinarith [this]
      have hAES : AEStronglyMeasurable
          (fun σ => (pth (Dz g) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α))
          (volume.restrict Iθ) := by
        have h1 : AEStronglyMeasurable (fun σ => pth (Dz g) z σ) (volume.restrict Iθ) :=
          (measurable_deriv (fun θ' => Dz g z θ')).aestronglyMeasurable
        have h2 : AEStronglyMeasurable (fun σ => (Real.sin (2 * σ)) ^ (2 - gam α))
            (volume.restrict Iθ) :=
          ((by fun_prop : Continuous fun σ : ℝ => Real.sin (2 * σ))).rpow_const
            (fun σ => Or.inr hc.le) |>.aestronglyMeasurable
        exact (h1.pow 2).mul h2
      refine MeasureTheory.Integrable.mono' (hmem.1 z hz) hAES ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun σ hσ => ?_)
      have hsnn : 0 ≤ Real.sin (2 * σ) := by
        apply Real.sin_nonneg_of_nonneg_of_le_pi
        · linarith [hσ.1]
        · linarith [hσ.2, Real.pi_pos]
      have hfnn : 0 ≤ (pth (Dz g) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsnn _)
      have hP := pth_Dz_sq_rpow_eq α hα hα1 g hsm z hz σ hσ
      rw [Real.norm_eq_abs, abs_of_nonneg hfnn]
      calc (pth (Dz g) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)
          ≤ (w z) ^ 2 * ((pth (Dz g) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) :=
            le_mul_of_one_le_left hfnn hw1
        _ = (mixed 1 1 g z σ) ^ 2 * (Wt α z σ) ^ 2 := by rw [← mul_assoc]; exact hP
        _ ≤ HkIntegrand α 2 g z σ := by
            rw [← mul_pow]
            exact sq_le_HkIntegrand_mixed α 2 g z σ 1 1 le_rfl (by norm_num)
  have hHT := HardyTheta α hα hα1 (Dz g) z hsm' hz h0 hHint θ hθ
  have hcoef : 0 ≤ 100 / (gam α - 1) := by
    have : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
    exact div_nonneg (by norm_num) this.le
  have hEq : (w z) ^ 2 * ∫ σ in Iθ,
        (pth (Dz g) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)
      = ∫ σ in Iθ, (mixed 1 1 g z σ) ^ 2 * (Wt α z σ) ^ 2 := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun σ hσ => ?_)
    rw [← mul_assoc]
    exact pth_Dz_sq_rpow_eq α hα hα1 g hsm z hz σ hσ
  have hLe : ∫ σ in Iθ, (mixed 1 1 g z σ) ^ 2 * (Wt α z σ) ^ 2
      ≤ ∫ σ in Iθ, HkIntegrand α 2 g z σ :=
    MeasureTheory.setIntegral_mono_of_nonneg
      (fun σ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (fun σ _ => by
        rw [← mul_pow]
        exact sq_le_HkIntegrand_mixed α 2 g z σ 1 1 le_rfl (by norm_num))
      (hmem.1 z hz)
  calc (Dz g z θ) ^ 2 * (w z) ^ 2
      ≤ (100 / (gam α - 1)) * ((w z) ^ 2 * ∫ σ in Iθ,
          (pth (Dz g) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) := by
        have := mul_le_mul_of_nonneg_right hHT (sq_nonneg (w z))
        calc (Dz g z θ) ^ 2 * (w z) ^ 2
            ≤ ((100 / (gam α - 1)) * ∫ σ in Iθ,
                (pth (Dz g) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) * (w z) ^ 2 := this
          _ = (100 / (gam α - 1)) * ((w z) ^ 2 * ∫ σ in Iθ,
                (pth (Dz g) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) := by ring
    _ = (100 / (gam α - 1)) * ∫ σ in Iθ, (mixed 1 1 g z σ) ^ 2 * (Wt α z σ) ^ 2 := by
        rw [hEq]
    _ ≤ (100 / (gam α - 1)) * ∫ σ in Iθ, HkIntegrand α 2 g z σ :=
        mul_le_mul_of_nonneg_left hLe hcoef


/-- **Elgindi, `Linf_H2`.**  A function of `H²` on the closed quadrant is bounded in
`L^∞` by `C/√(γ-1)` times its `H²`-norm (paper, §H2, Corollary `Linfty`), with a
universal constant comfortably below the stated `100`. -/
theorem Linf_H2 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (g : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd g) (hvt : Work.Spaces.VanishTheta g)
    (hdec : Work.Spaces.DecayInZ 2 g) (hmem : Work.Spaces.HkMem α 2 g) :
    Work.Spaces.supAbs g ≤ 100 / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 2 g := by
  have hgam1 : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hcoef : 0 ≤ 100 / (gam α - 1) := div_nonneg (by norm_num) hgam1.le
  have hPhi_int : IntegrableOn (fun z => ∫ σ in Iθ, HkIntegrand α 2 g z σ) Iz := hmem.2
  have hbnd : IntegrableOn
      (fun z => (100 / (gam α - 1)) * ∫ σ in Iθ, HkIntegrand α 2 g z σ) Iz :=
    hPhi_int.const_mul _
  have hpoint : ∀ z ∈ Iz, ∀ θ ∈ Iθ, (g z θ) ^ 2 ≤ (100 / (gam α - 1)) * HkSq α 2 g := by
    intro z hz θ hθ
    have hAES : AEStronglyMeasurable
        (fun z' => (Dz g z' θ) ^ 2 * (w z') ^ 2) (volume.restrict Iz) := by
      have h1 : Measurable (fun z' => pz g z' θ) := by
        simpa [pz] using measurable_deriv (fun z'' => g z'' θ)
      have hD : Measurable (fun z' => Dz g z' θ) := measurable_id.mul h1
      have h2 : Measurable (fun z' => (Dz g z' θ) ^ 2) := by
        have : Measurable (fun z' => Dz g z' θ * Dz g z' θ) := hD.mul hD
        simpa [pow_two] using this
      have hw : Measurable w := by
        show Measurable (fun z : ℝ => (1 + z) ^ 2 / z ^ 2)
        have hnum : Measurable (fun z : ℝ => (1 + z) ^ 2) := by
          have h : Measurable (fun z : ℝ => (1 + z) * (1 + z)) :=
            (measurable_const.add measurable_id).mul (measurable_const.add measurable_id)
          simpa [pow_two] using h
        have hden : Measurable (fun z : ℝ => z ^ 2) := by
          have h : Measurable (fun z : ℝ => z * z) := measurable_id.mul measurable_id
          simpa [pow_two] using h
        exact hnum.div hden
      have hw2 : Measurable (fun z' => (w z') ^ 2) := by
        have : Measurable (fun z' => w z' * w z') := hw.mul hw
        simpa [pow_two] using this
      exact (h2.mul hw2).aestronglyMeasurable
    have hFint : IntegrableOn (fun z' => (Dz g z' θ) ^ 2 * (w z') ^ 2) Iz := by
      refine MeasureTheory.Integrable.mono' hbnd hAES ?_
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z' hz' => by
        have hstep := Dz_HardyTheta_HkIntegrand α hα hα1 g hsm hvt hmem z' hz' θ hθ
        have hFnn : 0 ≤ (Dz g z' θ) ^ 2 * (w z') ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
        rw [Real.norm_eq_abs, abs_of_nonneg hFnn]
        exact hstep)
    have hHZ : (g z θ) ^ 2 ≤ ∫ z' in Iz, (Dz g z' θ) ^ 2 * (w z') ^ 2 :=
      HardyZ g θ hsm hθ (by simpa using hdec 0 0 (by norm_num) θ hθ) hFint z hz
    have hIntLe : ∫ z' in Iz, (Dz g z' θ) ^ 2 * (w z') ^ 2
        ≤ (100 / (gam α - 1)) * HkSq α 2 g := by
      calc ∫ z' in Iz, (Dz g z' θ) ^ 2 * (w z') ^ 2
          ≤ ∫ z' in Iz, (100 / (gam α - 1)) * ∫ σ in Iθ, HkIntegrand α 2 g z' σ :=
            MeasureTheory.setIntegral_mono_of_nonneg
              (fun z' _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
              (fun z' hz' => Dz_HardyTheta_HkIntegrand α hα hα1 g hsm hvt hmem z' hz' θ hθ)
              hbnd
        _ = (100 / (gam α - 1)) * ∫ z' in Iz, ∫ σ in Iθ, HkIntegrand α 2 g z' σ := by
            rw [MeasureTheory.integral_const_mul]
        _ = (100 / (gam α - 1)) * HkSq α 2 g := rfl
    exact le_trans hHZ hIntLe
  have hsup : supAbs g ≤ Real.sqrt ((100 / (gam α - 1)) * HkSq α 2 g) :=
    supAbs_le (fun z hz θ hθ => Real.abs_le_sqrt (hpoint z hz θ hθ))
  have hAle : (100 / (gam α - 1)) * HkSq α 2 g
      ≤ (100 / Real.sqrt (gam α - 1)) ^ 2 * HkSq α 2 g := by
    rw [div_pow, Real.sq_sqrt hgam1.le]
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (by norm_num : (100 : ℝ) ≤ 100 ^ 2) hgam1.le)
      (HkSq_nonneg α 2 g)
  have hsqrt : Real.sqrt ((100 / (gam α - 1)) * HkSq α 2 g)
      ≤ (100 / Real.sqrt (gam α - 1)) * HkNorm α 2 g := by
    calc Real.sqrt ((100 / (gam α - 1)) * HkSq α 2 g)
        ≤ Real.sqrt ((100 / Real.sqrt (gam α - 1)) ^ 2 * HkSq α 2 g) := Real.sqrt_le_sqrt hAle
      _ = (100 / Real.sqrt (gam α - 1)) * Real.sqrt (HkSq α 2 g) := by
          rw [Real.sqrt_mul (sq_nonneg _),
              Real.sqrt_sq (div_nonneg (by norm_num) (Real.sqrt_nonneg _))]
      _ = (100 / Real.sqrt (gam α - 1)) * HkNorm α 2 g := rfl
  exact le_trans hsup hsqrt

end Work.Spaces
