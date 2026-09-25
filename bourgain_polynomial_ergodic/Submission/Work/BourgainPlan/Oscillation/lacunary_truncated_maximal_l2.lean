import Mathlib
import Submission.Work.BourgainPlan.Oscillation.defs
import Submission.Work.BourgainPlan.Oscillation.Lacunary.defs
import Submission.Work.BourgainPlan.Oscillation.Lacunary.mmClosed_series
import Submission.Work.BourgainPlan.Oscillation.Lacunary.hlMaxZ_conv_kap
import Submission.Commons.Analysis.Fourier.plancherel_trig_polynomial
import Submission.Work.BourgainPlan.Oscillation.Lacunary.boundary_tsum_sq_le
import Submission.Work.BourgainPlan.Oscillation.Lacunary.bb_estimates
import Submission.Work.Analysis.Geometric.tsum_min_geometric_le

open MeasureTheory Finset
open scoped BigOperators ENNReal

namespace Work.BourgainPlan.Oscillation
namespace Lacunary

noncomputable section

/-! ## Basic characters and window -/

def Echar (x : ℤ) (θ : ℝ) : ℂ := Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))

lemma norm_Echar (x : ℤ) (θ : ℝ) : ‖Echar x θ‖ = 1 := by
  unfold Echar; rw [Complex.norm_exp]
  have : (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ))).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_zero]

lemma continuous_Echar (x : ℤ) : Continuous (Echar x) := by unfold Echar; fun_prop

lemma norm_exp_two_pi_I (z : ℤ) (θ : ℝ) :
    ‖Complex.exp (2*Real.pi*Complex.I*((z:ℤ):ℂ)*(θ:ℂ))‖ = 1 := by
  have h : (2*Real.pi*Complex.I*((z:ℤ):ℂ)*(θ:ℂ))
      = ((2*Real.pi*((z:ℤ):ℂ)*(θ:ℂ) : ℂ)) * Complex.I := by push_cast; ring
  rw [h, Complex.norm_exp]
  have hre : (((2*Real.pi*((z:ℤ):ℂ)*(θ:ℂ) : ℂ)) * Complex.I).re = 0 := by
    rw [Complex.mul_re]; simp
  rw [hre, Real.exp_zero]

lemma rpow_two_ofReal (z : ℂ) : (‖z‖ₑ) ^ (2:ℝ) = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [ENNReal.rpow_two, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg z) 2]

lemma enorm_norm_eq (z : ℂ) : ‖(‖z‖ : ℝ)‖ₑ = ‖z‖ₑ := by
  rw [← ofReal_norm, Real.norm_of_nonneg (norm_nonneg z), ofReal_norm]

lemma measurable_trigP (s : Finset ℤ) (f : ℤ → ℂ) : Measurable (trigP s f) := by
  unfold trigP
  exact Finset.measurable_sum _ (fun j _ =>
    measurable_const.mul (Complex.measurable_exp.comp (by fun_prop)))

lemma norm_trigP_le (s : Finset ℤ) (f : ℤ → ℂ) (θ : ℝ) :
    ‖trigP s f θ‖ ≤ ∑ j ∈ s, ‖f j‖ := by
  unfold trigP
  calc ‖∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℤ) : ℂ) * (θ : ℂ))‖
      ≤ ∑ j ∈ s, ‖f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℤ) : ℂ) * (θ : ℂ))‖ :=
        norm_sum_le _ _
    _ = ∑ j ∈ s, ‖f j‖ := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [norm_mul, Complex.norm_exp]
        have : (2 * Real.pi * Complex.I * ((j : ℤ) : ℂ) * (θ : ℂ)).re = 0 := by
          simp [Complex.mul_re, Complex.mul_im]
        rw [this, Real.exp_zero, mul_one]

lemma norm_win (s : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) (θ : ℝ) :
    ‖piCut θ * trigP s f θ * Echar x θ‖ ≤ ∑ j ∈ s, ‖f j‖ := by
  calc ‖piCut θ * trigP s f θ * Echar x θ‖
      ≤ ‖piCut θ‖ * ‖trigP s f θ‖ * ‖Echar x θ‖ := le_of_eq (by rw [norm_mul, norm_mul])
    _ ≤ 1 * (∑ j ∈ s, ‖f j‖) * 1 :=
        mul_le_mul (mul_le_mul (piCut_norm_le θ) (norm_trigP_le s f θ) (norm_nonneg _)
          (by norm_num)) (le_of_eq (norm_Echar x θ)) (norm_nonneg _) (by positivity)
    _ = ∑ j ∈ s, ‖f j‖ := by ring

lemma norm_win' (s : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) (θ : ℝ) :
    ‖piCut θ * trigP s f θ * Echar x θ‖ ≤ ‖trigP s f θ‖ := by
  calc ‖piCut θ * trigP s f θ * Echar x θ‖
      ≤ ‖piCut θ‖ * ‖trigP s f θ‖ * ‖Echar x θ‖ := le_of_eq (by rw [norm_mul, norm_mul])
    _ ≤ 1 * ‖trigP s f θ‖ * 1 :=
        mul_le_mul (mul_le_mul (piCut_norm_le θ) le_rfl (norm_nonneg _) (by norm_num))
          (le_of_eq (norm_Echar x θ)) (norm_nonneg _) (by positivity)
    _ = ‖trigP s f θ‖ := by ring

lemma continuous_mmClosed {ρ : ℝ} (hρ : 0 < ρ) (i : ℕ) : Continuous (mmClosed ρ i) := by
  unfold mmClosed
  exact Continuous.div continuous_const (by fun_prop)
    (fun θ => ne_of_gt (mmClosed_denom_pos hρ i θ))

lemma measurable_piCut : Measurable piCut :=
  Measurable.ite (p := fun θ : ℝ => θ ≤ (1/2:ℝ)) measurableSet_Iic
    (measurable_const : Measurable (fun _ : ℝ => (1 : ℂ)))
    (measurable_const : Measurable (fun _ : ℝ => (0 : ℂ)))

lemma measurable_phi {ρ : ℝ} (hρ : 0 < ρ) (i : ℕ) : Measurable (phi ρ i) := by
  have hm : Measurable (fun θ : ℝ => (mmClosed ρ i θ : ℂ)) :=
    Complex.measurable_ofReal.comp (continuous_mmClosed hρ i).measurable
  exact measurable_piCut.mul hm

lemma measurable_bb {ρ : ℝ} (hρ : 0 < ρ) (i : ℕ) : Measurable (bb ρ i) := by
  have hind : Measurable (fun θ : ℝ => if |θ| ≤ cc ρ i then (1 : ℂ) else 0) :=
    Measurable.ite (p := fun θ : ℝ => |θ| ≤ cc ρ i)
      (measurableSet_le continuous_abs.measurable measurable_const)
      measurable_const measurable_const
  exact hind.sub (measurable_phi hρ i)

/-! ## The reference probability measure `(0,1]` -/

noncomputable def mu01 : Measure ℝ := volume.restrict (Set.Ioc (0:ℝ) 1)

lemma intervalIntegral_eq_mu01 (F : ℝ → ℂ) :
    (∫ θ in (0:ℝ)..1, F θ) = ∫ θ, F θ ∂mu01 := by
  show (∫ θ in (0:ℝ)..1, F θ) = ∫ θ, F θ ∂(volume.restrict (Set.Ioc (0:ℝ) 1))
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]

lemma intervalIntegral_eq_mu01_real (F : ℝ → ℝ) :
    (∫ θ in (0:ℝ)..1, F θ) = ∫ θ, F θ ∂mu01 := by
  show (∫ θ in (0:ℝ)..1, F θ) = ∫ θ, F θ ∂(volume.restrict (Set.Ioc (0:ℝ) 1))
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]

lemma isFiniteMeasure_mu01 : IsFiniteMeasure mu01 :=
  ⟨by rw [mu01, Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩

/-! ## The operators -/

noncomputable def gseq (s : Finset ℤ) (f : ℤ → ℂ) (k : ℤ) : ℂ :=
  ∫ θ, piCut θ * trigP s f θ * Echar k θ ∂mu01

noncomputable def Gker (ρ : ℝ) (i : ℕ) (s : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) (z : ℤ) (θ : ℝ) : ℂ :=
  (kap ρ i z : ℂ) *
    (Complex.exp (2*Real.pi*Complex.I*((z:ℤ):ℂ)*(θ:ℂ)) * (piCut θ * trigP s f θ * Echar x θ))

def Tint (ρ : ℝ) (i : ℕ) (s : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) : ℂ :=
  ∫ θ in (0:ℝ)..1, (if |θ| ≤ cc ρ i then (1:ℂ) else 0) * trigP s f θ * Echar x θ

def Aint (ρ : ℝ) (i : ℕ) (s : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) : ℂ :=
  ∫ θ in (0:ℝ)..1, phi ρ i θ * trigP s f θ * Echar x θ

def Bint (ρ : ℝ) (i : ℕ) (s : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) : ℂ :=
  ∫ θ in (0:ℝ)..1, bb ρ i θ * trigP s f θ * Echar x θ

/-! ## Integrability helpers -/

lemma integrable_Ioc_of_bound {h : ℝ → ℂ} (hh : Measurable h) {C : ℝ} (hC : ∀ θ, ‖h θ‖ ≤ C) :
    Integrable h mu01 := by
  have hfin : volume (Set.Ioc (0:ℝ) 1) < ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  show IntegrableOn h (Set.Ioc (0:ℝ) 1) volume
  exact IntegrableOn.of_bound hfin hh.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

lemma integrable_Ioc_of_bound_real {h : ℝ → ℝ} (hh : Measurable h) {C : ℝ}
    (hC : ∀ θ, ‖h θ‖ ≤ C) : Integrable h mu01 := by
  have hfin : volume (Set.Ioc (0:ℝ) 1) < ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  show IntegrableOn h (Set.Ioc (0:ℝ) 1) volume
  exact IntegrableOn.of_bound hfin hh.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

lemma kap_nonneg {ρ : ℝ} (hρ : 1 < ρ) (i : ℕ) (z : ℤ) : 0 ≤ kap ρ i z := by
  have hρ0 : (0:ℝ) < ρ := by linarith
  unfold kap
  exact mul_nonneg (div_nonneg (one_sub_lam_pos hρ0 i).le (one_add_lam_pos hρ0 i).le)
    (pow_nonneg (lam_nonneg hρ0 i) _)

lemma norm_kap {ρ : ℝ} (hρ : 1 < ρ) (i : ℕ) (z : ℤ) : ‖(kap ρ i z : ℂ)‖ = kap ρ i z := by
  rw [norm_ofReal_complex, abs_of_nonneg (kap_nonneg hρ i z)]

lemma summable_kap {ρ : ℝ} (hρ : 1 < ρ) (i : ℕ) : Summable (fun z : ℤ => kap ρ i z) := by
  have hρ0 : (0:ℝ) < ρ := by linarith
  have hlam0 : 0 ≤ lam ρ i := lam_nonneg hρ0 i
  have hnorm : ‖lam ρ i‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hlam0]; exact lam_lt_one hρ0 i
  have hgeo : Summable (fun n : ℕ => (lam ρ i) ^ n) := summable_geometric_of_norm_lt_one hnorm
  have hA : Summable (fun n : ℕ => (1 - lam ρ i) / (1 + lam ρ i) * (lam ρ i) ^ n) :=
    hgeo.mul_left _
  rw [summable_int_iff_summable_nat_and_neg]
  refine ⟨?_, ?_⟩
  · refine hA.congr (fun n => ?_)
    unfold kap; rw [Int.natAbs_natCast]
  · refine hA.congr (fun n => ?_)
    unfold kap; rw [Int.natAbs_neg, Int.natAbs_natCast]

lemma norm_trigP_integrable (s : Finset ℤ) (f : ℤ → ℂ) :
    Integrable (fun θ => ‖trigP s f θ‖) mu01 := by
  refine integrable_Ioc_of_bound_real (C := ∑ j ∈ s, ‖f j‖) ?_ ?_
  · exact (measurable_trigP s f).norm
  · intro θ; rw [Real.norm_of_nonneg (norm_nonneg _)]; exact norm_trigP_le s f θ

lemma intervalIntegrable_Tint (ρ : ℝ) (i : ℕ) (s : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    IntervalIntegrable (fun θ => (if |θ| ≤ cc ρ i then (1:ℂ) else 0) * trigP s f θ * Echar x θ)
      volume 0 1 := by
  have hmeas : Measurable (fun θ => (if |θ| ≤ cc ρ i then (1:ℂ) else 0) * trigP s f θ * Echar x θ) :=
    ((Measurable.ite (p := fun θ : ℝ => |θ| ≤ cc ρ i)
      (measurableSet_le continuous_abs.measurable measurable_const)
      measurable_const measurable_const).mul (measurable_trigP s f)).mul
      (continuous_Echar x).measurable
  have hC : ∀ θ, ‖(if |θ| ≤ cc ρ i then (1:ℂ) else 0) * trigP s f θ * Echar x θ‖
      ≤ ∑ j ∈ s, ‖f j‖ := by
    intro θ
    have h1 : ‖(if |θ| ≤ cc ρ i then (1:ℂ) else 0)‖ ≤ 1 := by split <;> simp
    calc ‖(if |θ| ≤ cc ρ i then (1:ℂ) else 0) * trigP s f θ * Echar x θ‖
        ≤ ‖(if |θ| ≤ cc ρ i then (1:ℂ) else 0)‖ * ‖trigP s f θ‖ * ‖Echar x θ‖ :=
          le_of_eq (by rw [norm_mul, norm_mul])
      _ ≤ 1 * (∑ j ∈ s, ‖f j‖) * 1 :=
          mul_le_mul (mul_le_mul h1 (norm_trigP_le s f θ) (norm_nonneg _) (by norm_num))
            (le_of_eq (norm_Echar x θ)) (norm_nonneg _) (by positivity)
      _ = ∑ j ∈ s, ‖f j‖ := by ring
  have hfin : volume (Set.uIoc (0:ℝ) 1) < ⊤ := by
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1), Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  rw [intervalIntegrable_iff]
  exact IntegrableOn.of_bound hfin hmeas.aestronglyMeasurable _ (Filter.Eventually.of_forall hC)

lemma intervalIntegrable_Aint (ρ : ℝ) (hρ : 1 < ρ) (i : ℕ) (s : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    IntervalIntegrable (fun θ => phi ρ i θ * trigP s f θ * Echar x θ) volume 0 1 := by
  have hmeas : Measurable (fun θ => phi ρ i θ * trigP s f θ * Echar x θ) :=
    ((measurable_phi (by linarith) i).mul (measurable_trigP s f)).mul (continuous_Echar x).measurable
  have hC : ∀ θ, ‖phi ρ i θ * trigP s f θ * Echar x θ‖ ≤ ∑ j ∈ s, ‖f j‖ := by
    intro θ
    have h1 : ‖phi ρ i θ‖ ≤ 1 := phi_norm_le (by linarith) i θ
    calc ‖phi ρ i θ * trigP s f θ * Echar x θ‖
        ≤ ‖phi ρ i θ‖ * ‖trigP s f θ‖ * ‖Echar x θ‖ := le_of_eq (by rw [norm_mul, norm_mul])
      _ ≤ 1 * (∑ j ∈ s, ‖f j‖) * 1 :=
          mul_le_mul (mul_le_mul h1 (norm_trigP_le s f θ) (norm_nonneg _) (by norm_num))
            (le_of_eq (norm_Echar x θ)) (norm_nonneg _) (by positivity)
      _ = ∑ j ∈ s, ‖f j‖ := by ring
  have hfin : volume (Set.uIoc (0:ℝ) 1) < ⊤ := by
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1), Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  rw [intervalIntegrable_iff]
  exact IntegrableOn.of_bound hfin hmeas.aestronglyMeasurable _ (Filter.Eventually.of_forall hC)

lemma intervalIntegrable_Bint (ρ : ℝ) (hρ : 1 < ρ) (i : ℕ) (s : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    IntervalIntegrable (fun θ => bb ρ i θ * trigP s f θ * Echar x θ) volume 0 1 := by
  have hmeas : Measurable (fun θ => bb ρ i θ * trigP s f θ * Echar x θ) :=
    ((measurable_bb (by linarith) i).mul (measurable_trigP s f)).mul (continuous_Echar x).measurable
  have hC : ∀ θ, ‖bb ρ i θ * trigP s f θ * Echar x θ‖ ≤ 2 * ∑ j ∈ s, ‖f j‖ := by
    intro θ
    have h1 : ‖bb ρ i θ‖ ≤ 2 := bb_norm_le (by linarith) i θ
    calc ‖bb ρ i θ * trigP s f θ * Echar x θ‖
        ≤ ‖bb ρ i θ‖ * ‖trigP s f θ‖ * ‖Echar x θ‖ := le_of_eq (by rw [norm_mul, norm_mul])
      _ ≤ 2 * (∑ j ∈ s, ‖f j‖) * 1 :=
          mul_le_mul (mul_le_mul h1 (norm_trigP_le s f θ) (norm_nonneg _) (by norm_num))
            (le_of_eq (norm_Echar x θ)) (norm_nonneg _) (by positivity)
      _ = 2 * ∑ j ∈ s, ‖f j‖ := by ring
  have hfin : volume (Set.uIoc (0:ℝ) 1) < ⊤ := by
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1), Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  rw [intervalIntegrable_iff]
  exact IntegrableOn.of_bound hfin hmeas.aestronglyMeasurable _ (Filter.Eventually.of_forall hC)

theorem Tint_split (ρ : ℝ) (hρ : 1 < ρ) (i : ℕ) (s : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    Tint ρ i s f x = Aint ρ i s f x + Bint ρ i s f x := by
  unfold Tint Aint Bint
  have hcongr : ∀ θ, (if |θ| ≤ cc ρ i then (1:ℂ) else 0) * trigP s f θ * Echar x θ
      = phi ρ i θ * trigP s f θ * Echar x θ + bb ρ i θ * trigP s f θ * Echar x θ := by
    intro θ
    have h : (if |θ| ≤ cc ρ i then (1:ℂ) else 0) = phi ρ i θ + bb ρ i θ := by
      unfold bb; ring
    rw [h]; ring
  rw [intervalIntegral.integral_congr (fun θ _ => hcongr θ),
    intervalIntegral.integral_add (intervalIntegrable_Aint ρ hρ i s f x)
      (intervalIntegrable_Bint ρ hρ i s f x)]
theorem Aint_eq_conv (ρ : ℝ) (hρ : 1 < ρ) (i : ℕ) (s : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    Aint ρ i s f x = ∑' z : ℤ, (kap ρ i z : ℂ) * gseq s f (x - z) := by
  have hA : Aint ρ i s f x = ∫ θ, phi ρ i θ * trigP s f θ * Echar x θ ∂mu01 := by
    unfold Aint; rw [intervalIntegral_eq_mu01]
  rw [hA]
  have hpt : ∀ θ, phi ρ i θ * trigP s f θ * Echar x θ = ∑' z, Gker ρ i s f x z θ := by
    intro θ
    have step1 : (∑' z : ℤ, Gker ρ i s f x z θ)
        = (∑' z : ℤ, (kap ρ i z : ℂ) * Complex.exp (2*Real.pi*Complex.I*((z:ℤ):ℂ)*(θ:ℂ)))
            * (piCut θ * trigP s f θ * Echar x θ) := by
      rw [show (∑' z : ℤ, Gker ρ i s f x z θ)
          = ∑' z : ℤ, ((kap ρ i z : ℂ) * Complex.exp (2*Real.pi*Complex.I*((z:ℤ):ℂ)*(θ:ℂ)))
              * (piCut θ * trigP s f θ * Echar x θ) from
            tsum_congr (fun z => by unfold Gker; ring)]
      exact tsum_mul_right
    rw [step1, ← mmClosed_series ρ hρ i θ]
    unfold phi; ring
  rw [show (∫ θ, phi ρ i θ * trigP s f θ * Echar x θ ∂mu01)
      = ∫ θ, ∑' z, Gker ρ i s f x z θ ∂mu01 from
    integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have hbb : ∀ z θ, ‖Gker ρ i s f x z θ‖ ≤ kap ρ i z * (∑ j ∈ s, ‖f j‖) := by
    intro z θ
    show ‖(kap ρ i z : ℂ) * (Complex.exp (2*Real.pi*Complex.I*((z:ℤ):ℂ)*(θ:ℂ))
        * (piCut θ * trigP s f θ * Echar x θ))‖ ≤ kap ρ i z * (∑ j ∈ s, ‖f j‖)
    rw [norm_mul, norm_mul, norm_kap hρ i z, norm_exp_two_pi_I, one_mul]
    exact mul_le_mul_of_nonneg_left (norm_win s f x θ) (kap_nonneg hρ i z)
  have hInt : ∀ z : ℤ, Integrable (Gker ρ i s f x z) mu01 := by
    intro z
    have hmeas : Measurable (Gker ρ i s f x z) := by
      show Measurable (fun θ : ℝ => (kap ρ i z : ℂ) *
        (Complex.exp (2*Real.pi*Complex.I*((z:ℤ):ℂ)*(θ:ℂ))
          * (piCut θ * trigP s f θ * Echar x θ)))
      exact measurable_const.mul ((Complex.measurable_exp.comp (by fun_prop)).mul
        ((measurable_piCut.mul (measurable_trigP s f)).mul (continuous_Echar x).measurable))
    exact integrable_Ioc_of_bound hmeas (fun θ => hbb z θ)
  have hSumm : Summable (fun z : ℤ => ∫ θ, ‖Gker ρ i s f x z θ‖ ∂mu01) := by
    refine Summable.of_nonneg_of_le
      (f := fun z : ℤ => kap ρ i z * ∫ θ, ‖trigP s f θ‖ ∂mu01) (fun z => ?_) (fun z => ?_) ?_
    · exact integral_nonneg (fun θ => norm_nonneg (Gker ρ i s f x z θ))
    · calc ∫ θ, ‖Gker ρ i s f x z θ‖ ∂mu01
          ≤ ∫ θ, kap ρ i z * ‖trigP s f θ‖ ∂mu01 := by
            refine integral_mono_of_nonneg
              (Filter.Eventually.of_forall (fun θ => norm_nonneg (Gker ρ i s f x z θ)))
              ?_ (Filter.Eventually.of_forall (fun θ => ?_))
            · refine integrable_Ioc_of_bound_real (C := kap ρ i z * ∑ j ∈ s, ‖f j‖) ?_ ?_
              · exact measurable_const.mul (measurable_trigP s f).norm
              · intro θ
                rw [Real.norm_of_nonneg (mul_nonneg (kap_nonneg hρ i z) (norm_nonneg _))]
                exact mul_le_mul_of_nonneg_left (norm_trigP_le s f θ) (kap_nonneg hρ i z)
            · show ‖(kap ρ i z : ℂ) * (Complex.exp (2*Real.pi*Complex.I*((z:ℤ):ℂ)*(θ:ℂ))
                  * (piCut θ * trigP s f θ * Echar x θ))‖ ≤ kap ρ i z * ‖trigP s f θ‖
              rw [norm_mul, norm_mul, norm_kap hρ i z, norm_exp_two_pi_I, one_mul]
              exact mul_le_mul_of_nonneg_left (norm_win' s f x θ) (kap_nonneg hρ i z)
        _ = kap ρ i z * ∫ θ, ‖trigP s f θ‖ ∂mu01 := by
            rw [integral_const_mul]
    · exact (summable_kap hρ i).mul_right _
  rw [← integral_tsum_of_summable_integral_norm hInt hSumm]
  refine tsum_congr (fun z => ?_)
  unfold Gker
  rw [integral_const_mul]
  congr 1
  unfold gseq
  have hg : (fun θ : ℝ => Complex.exp (2*Real.pi*Complex.I*((z:ℤ):ℂ)*(θ:ℂ))
        * (piCut θ * trigP s f θ * Echar x θ))
      = (fun θ : ℝ => piCut θ * trigP s f θ * Echar (x - z) θ) := by
    funext θ
    have hexp : Complex.exp (2*Real.pi*Complex.I*((z:ℤ):ℂ)*(θ:ℂ)) * Echar x θ = Echar (x - z) θ := by
      unfold Echar
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc Complex.exp (2*Real.pi*Complex.I*((z:ℤ):ℂ)*(θ:ℂ)) * (piCut θ * trigP s f θ * Echar x θ)
        = piCut θ * trigP s f θ
            * (Complex.exp (2*Real.pi*Complex.I*((z:ℤ):ℂ)*(θ:ℂ)) * Echar x θ) := by ring
      _ = piCut θ * trigP s f θ * Echar (x - z) θ := by rw [hexp]
  rw [hg]

lemma ofReal_integral_mu01 {g : ℝ → ℝ} (hg : Integrable g mu01) (hgn : 0 ≤ᵐ[mu01] g) :
    ENNReal.ofReal (∫ θ in (0:ℝ)..1, g θ) = ∫⁻ θ, ENNReal.ofReal (g θ) ∂mu01 := by
  rw [intervalIntegral_eq_mu01_real]
  exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg hgn

lemma fourier_coe_eq_Echar (n : ℤ) (x : ℝ) :
    (fourier (T := (1:ℝ)) (-n) (x : AddCircle (1:ℝ)) : ℂ) = Echar n x := by
  rw [fourier_coe_apply, Echar]
  congr 1
  push_cast
  ring

lemma fourierCoeffOn_eq_Echar (F : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn (by norm_num : (0:ℝ) < 1) F n = ∫ θ in (0:ℝ)..1, F θ * Echar n θ := by
  rw [fourierCoeffOn_eq_integral F n (by norm_num : (0:ℝ) < (1:ℝ))]
  simp only [sub_zero, div_one, one_smul]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  show (fourier (T := (1:ℝ) - 0) (-n) (x : AddCircle ((1:ℝ) - 0)) : ℂ) • F x
      = F x * Echar n x
  rw [fourier_coe_apply, smul_eq_mul, mul_comm, Echar]
  congr 1
  rw [show (2 * ↑Real.pi * Complex.I * ↑(-n) * ↑x / ↑((1:ℝ) - 0))
      = -(2 * ↑Real.pi * Complex.I * ↑n * ↑x) by
    rw [show ((1:ℝ) - 0) = 1 by norm_num]; push_cast; ring]


lemma memLp_bbtrig (ρ : ℝ) (hρ : 1 < ρ) (i : ℕ) (s : Finset ℤ) (f : ℤ → ℂ) :
    MemLp (fun θ => bb ρ i θ * trigP s f θ) 2 mu01 := by
  haveI := isFiniteMeasure_mu01
  refine MemLp.of_bound (((measurable_bb (by linarith) i).mul (measurable_trigP s f)).aestronglyMeasurable)
    (2 * ∑ j ∈ s, ‖f j‖) ?_
  filter_upwards with θ
  rw [norm_mul]
  exact mul_le_mul (bb_norm_le (by linarith) i θ) (norm_trigP_le s f θ) (norm_nonneg _) (by norm_num)

lemma coeff_Bint (ρ : ℝ) (i : ℕ) (s : Finset ℤ) (f : ℤ → ℂ) (n : ℤ) :
    fourierCoeffOn (by norm_num : (0:ℝ) < 1) (fun θ => bb ρ i θ * trigP s f θ) n
      = Bint ρ i s f n := by
  rw [fourierCoeffOn_eq_Echar]
  unfold Bint
  exact intervalIntegral.integral_congr (fun θ _ => by ring)

lemma summable_sq_Bint (ρ : ℝ) (hρ : 1 < ρ) (i : ℕ) (s : Finset ℤ) (f : ℤ → ℂ) :
    Summable (fun n : ℤ => ‖Bint ρ i s f n‖ ^ 2) := by
  have h := (hasSum_sq_fourierCoeffOn (a := (0:ℝ)) (b := 1) (by norm_num)
    (f := fun θ => bb ρ i θ * trigP s f θ) (memLp_bbtrig ρ hρ i s f)).summable
  refine h.congr (fun n => ?_)
  rw [coeff_Bint ρ i s f n]

lemma tsum_sq_Bint (ρ : ℝ) (hρ : 1 < ρ) (i : ℕ) (s : Finset ℤ) (f : ℤ → ℂ) :
    ∑' n : ℤ, ‖Bint ρ i s f n‖ ^ 2 = ∫ θ in (0:ℝ)..1, ‖bb ρ i θ‖ ^ 2 * ‖trigP s f θ‖ ^ 2 := by
  have h := tsum_sq_fourierCoeffOn (a := (0:ℝ)) (b := 1) (by norm_num)
    (f := fun θ => bb ρ i θ * trigP s f θ) (memLp_bbtrig ρ hρ i s f)
  simp only [sub_zero, inv_one, one_smul] at h
  rw [show (∑' n : ℤ, ‖Bint ρ i s f n‖ ^ 2)
      = ∑' n : ℤ, ‖fourierCoeffOn (by norm_num : (0:ℝ) < 1)
          (fun θ => bb ρ i θ * trigP s f θ) n‖ ^ 2 from
      tsum_congr (fun n => by rw [coeff_Bint ρ i s f n]), h]
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  rw [norm_mul, mul_pow]

lemma plancherel_bb_ENN (ρ : ℝ) (hρ : 1 < ρ) (i : ℕ) (s : Finset ℤ) (f : ℤ → ℂ) :
    ∑' n : ℤ, (‖Bint ρ i s f n‖ₑ) ^ (2:ℝ)
      = ∫⁻ θ, (‖bb ρ i θ‖ₑ) ^ (2:ℝ) * (‖trigP s f θ‖ₑ) ^ (2:ℝ) ∂mu01 := by
  have hsum := summable_sq_Bint ρ hρ i s f
  rw [show (∑' n : ℤ, (‖Bint ρ i s f n‖ₑ) ^ (2:ℝ))
      = ENNReal.ofReal (∑' n : ℤ, ‖Bint ρ i s f n‖ ^ 2) from by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hsum]
    exact tsum_congr (fun n => rpow_two_ofReal _),
    tsum_sq_Bint ρ hρ i s f]
  rw [ofReal_integral_mu01 ?_ ?_]
  · refine lintegral_congr (fun θ => ?_)
    rw [ENNReal.ofReal_mul (sq_nonneg _), rpow_two_ofReal, rpow_two_ofReal]
  · refine integrable_Ioc_of_bound_real
      (h := fun θ => ‖bb ρ i θ‖ ^ 2 * ‖trigP s f θ‖ ^ 2)
      (C := (2 * ∑ j ∈ s, ‖f j‖) ^ 2) ?_ ?_
    · exact Measurable.mul (Measurable.pow_const (Measurable.norm
        (measurable_bb (show (0:ℝ) < ρ by linarith) i)) 2)
        (Measurable.pow_const (Measurable.norm (measurable_trigP s f)) 2)
    · intro θ
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      have h1 : ‖bb ρ i θ‖ ≤ 2 := bb_norm_le (by linarith) i θ
      have h2 : ‖trigP s f θ‖ ≤ ∑ j ∈ s, ‖f j‖ := norm_trigP_le s f θ
      have h3 : ‖bb ρ i θ‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (bb ρ i θ), h1]
      have h4 : ‖trigP s f θ‖ ^ 2 ≤ (∑ j ∈ s, ‖f j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h2 2
      calc ‖bb ρ i θ‖ ^ 2 * ‖trigP s f θ‖ ^ 2 ≤ 4 * (∑ j ∈ s, ‖f j‖) ^ 2 :=
            mul_le_mul h3 h4 (sq_nonneg _) (by norm_num)
        _ = (2 * ∑ j ∈ s, ‖f j‖) ^ 2 := by ring
  · filter_upwards with θ using mul_nonneg (sq_nonneg _) (sq_nonneg _)

lemma iSup_mul_self_le {ι : Type*} (f : ι → ENNReal) :
    (⨆ i, f i) * (⨆ i, f i) ≤ ⨆ i, f i * f i := by
  have h : (⨆ i, f i) * (⨆ i, f i) = ⨆ i, ⨆ j, f j * f i := by
    rw [ENNReal.mul_iSup]
    exact iSup_congr (fun i => by rw [ENNReal.iSup_mul])
  rw [h]
  refine iSup_le fun i => iSup_le fun j => ?_
  rcases le_total (f i) (f j) with hh | hh
  · exact le_trans (mul_le_mul' le_rfl hh) (le_iSup (fun k => f k * f k) j)
  · exact le_trans (mul_le_mul' hh le_rfl) (le_iSup (fun k => f k * f k) i)

lemma iSup_rpow_two {ι : Type*} (f : ι → ENNReal) :
    (⨆ i, f i) ^ (2 : ℝ) = ⨆ i, (f i) ^ (2 : ℝ) := by
  have hL : (⨆ i, f i) ^ (2:ℝ) = (⨆ i, f i) * (⨆ i, f i) := by
    rw [ENNReal.rpow_two, pow_two]
  have hR : (⨆ i, (f i) ^ (2:ℝ)) = ⨆ i, f i * f i := by
    refine iSup_congr (fun i => ?_)
    rw [ENNReal.rpow_two, pow_two]
  rw [hL, hR]
  exact le_antisymm (iSup_mul_self_le f)
    (iSup_le fun i => mul_le_mul' (le_iSup f i) (le_iSup f i))

lemma hlMaxZ_congr {H H' : ℤ → ENNReal} (h : ∀ k, H k = H' k) (x : ℤ) :
    hlMaxZ H x = hlMaxZ H' x := by
  unfold hlMaxZ
  refine iSup_congr (fun a => iSup_congr (fun b => iSup_congr (fun hab => ?_)))
  congr 1
  exact Finset.sum_congr rfl (fun k _ => h k)

theorem Aint_bound (ρ : ℝ) (hρ : 1 < ρ) (i : ℕ) (s : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    ‖Aint ρ i s f x‖ₑ ≤ hlMaxZ (fun k : ℤ => ‖gseq s f k‖ₑ) x := by
  rw [Aint_eq_conv ρ hρ i s f x]
  calc ‖∑' z : ℤ, (kap ρ i z : ℂ) * gseq s f (x - z)‖ₑ
      ≤ ∑' z : ℤ, ‖(kap ρ i z : ℂ) * gseq s f (x - z)‖ₑ := enorm_tsum_le_tsum_enorm
    _ = ∑' z : ℤ, ENNReal.ofReal (kap ρ i z) * ‖gseq s f (x - z)‖ₑ := by
        refine tsum_congr (fun z => ?_)
        rw [enorm_mul, ← ofReal_norm, norm_kap hρ i z]
    _ ≤ hlMaxZ (fun k : ℤ => ‖gseq s f k‖ₑ) x := hlMaxZ_conv_kap ρ hρ i (fun k : ℤ => ‖gseq s f k‖ₑ) x

/-! ## Summability of the boundary layers -/

lemma bb_summable (ρ : ℝ) (hρ : 1 < ρ) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    Summable (fun i : ℕ => ‖bb ρ i θ‖ ^ 2) := by
  have hr4 : (1:ℝ) < ρ^4 := one_lt_pow₀ hρ (by norm_num)
  have hgeom := Work.Analysis.Geometric.tsum_min_geometric_le (ρ^4) (θ^4) hr4 (by positivity)
  have hmaj : Summable (fun i : ℕ => Cpt * min (θ^4*(ρ^4)^i) ((θ^4)⁻¹*((ρ^4)⁻¹)^i)) :=
    hgeom.1.mul_left Cpt
  refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_) hmaj
  have h := bb_sq_le_cc ρ hρ i θ h0 h1
  rwa [min_cc_eq ρ i θ] at h

/-! ## More helpers -/

lemma intervalIntegrable_of_bound_real {h : ℝ → ℝ} (hh : Measurable h) {C : ℝ}
    (hC : ∀ θ, ‖h θ‖ ≤ C) : IntervalIntegrable h volume 0 1 := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact integrable_Ioc_of_bound_real hh hC

lemma memLp_piCut_trig (s : Finset ℤ) (f : ℤ → ℂ) :
    MemLp (fun θ => piCut θ * trigP s f θ) 2 mu01 := by
  haveI := isFiniteMeasure_mu01
  refine MemLp.of_bound (p := 2) (μ := mu01) (f := fun θ => piCut θ * trigP s f θ)
    ((measurable_piCut.mul (measurable_trigP s f)).aestronglyMeasurable)
    (∑ j ∈ s, ‖f j‖) ?_
  filter_upwards with θ
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (piCut_norm_le θ) (norm_nonneg _) |>.trans_eq (one_mul _) |>.trans
    (norm_trigP_le s f θ)

lemma coeff_gseq (s : Finset ℤ) (f : ℤ → ℂ) (n : ℤ) :
    fourierCoeffOn (by norm_num : (0:ℝ) < 1) (fun θ => piCut θ * trigP s f θ) n = gseq s f n := by
  rw [fourierCoeffOn_eq_Echar, intervalIntegral_eq_mu01]
  unfold gseq
  exact integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))

lemma trig_lintegral (s : Finset ℤ) (f : ℤ → ℂ) :
    ∫⁻ θ, (‖trigP s f θ‖ₑ) ^ (2:ℝ) ∂mu01 = ENNReal.ofReal (∑ j ∈ s, ‖f j‖ ^ 2) := by
  rw [show (∫⁻ θ, (‖trigP s f θ‖ₑ) ^ (2:ℝ) ∂mu01)
      = ∫⁻ θ, ENNReal.ofReal (‖trigP s f θ‖ ^ 2) ∂mu01 from
      lintegral_congr (fun θ => rpow_two_ofReal _)]
  rw [← ofReal_integral_mu01 ?_ ?_]
  · congr 1
    show (∫ θ in (0:ℝ)..1, ‖trigP s f θ‖ ^ 2) = ∑ j ∈ s, ‖f j‖ ^ 2
    exact (Commons.Analysis.Fourier.plancherel_trig_polynomial s f).symm
  · refine integrable_Ioc_of_bound_real (C := (∑ j ∈ s, ‖f j‖) ^ 2) ?_ ?_
    · exact (measurable_trigP s f).norm.pow_const 2
    · intro θ
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_trigP_le s f θ) 2
  · filter_upwards with θ using sq_nonneg _

lemma gseq_lintegral_le (s : Finset ℤ) (f : ℤ → ℂ) :
    ∫⁻ x : ℤ, ‖gseq s f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (∑ j ∈ s, ‖f j‖ ^ 2) := by
  have hF := memLp_piCut_trig s f
  have hsum : Summable (fun n : ℤ => ‖gseq s f n‖ ^ 2) :=
    (hasSum_sq_fourierCoeffOn (a := (0:ℝ)) (b := 1) (by norm_num)
      (f := fun θ => piCut θ * trigP s f θ) hF).summable |>.congr (fun n => by rw [coeff_gseq])
  have hval : ∑' n : ℤ, ‖gseq s f n‖ ^ 2
      = ∫ θ in (0:ℝ)..1, ‖piCut θ * trigP s f θ‖ ^ 2 := by
    have h := tsum_sq_fourierCoeffOn (a := (0:ℝ)) (b := 1) (by norm_num)
      (f := fun θ => piCut θ * trigP s f θ) hF
    simp only [sub_zero, inv_one, one_smul] at h
    rw [show (∑' n : ℤ, ‖gseq s f n‖ ^ 2)
        = ∑' n : ℤ, ‖fourierCoeffOn (by norm_num : (0:ℝ) < 1)
            (fun θ => piCut θ * trigP s f θ) n‖ ^ 2 from
        tsum_congr (fun n => by rw [coeff_gseq]), h]
  have hmono : (∫ θ in (0:ℝ)..1, ‖piCut θ * trigP s f θ‖ ^ 2)
      ≤ ∫ θ in (0:ℝ)..1, ‖trigP s f θ‖ ^ 2 := by
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ (fun θ _ => ?_)
    · refine intervalIntegrable_of_bound_real (C := (∑ j ∈ s, ‖f j‖) ^ 2) ?_ ?_
      · exact ((measurable_piCut.mul (measurable_trigP s f)).norm.pow_const 2)
      · intro θ
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        have h1 : ‖piCut θ * trigP s f θ‖ ≤ ∑ j ∈ s, ‖f j‖ := by
          rw [norm_mul]
          exact (mul_le_of_le_one_left (norm_nonneg _) (piCut_norm_le θ)).trans (norm_trigP_le s f θ)
        exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    · refine intervalIntegrable_of_bound_real (C := (∑ j ∈ s, ‖f j‖) ^ 2) ?_ ?_
      · exact ((measurable_trigP s f).norm.pow_const 2)
      · intro θ
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_trigP_le s f θ) 2
    · rw [norm_mul]
      have h1 : ‖piCut θ‖ * ‖trigP s f θ‖ ≤ ‖trigP s f θ‖ :=
        mul_le_of_le_one_left (norm_nonneg _) (piCut_norm_le θ)
      exact pow_le_pow_left₀ (by positivity) h1 2
  rw [show (∫⁻ x : ℤ, ‖gseq s f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count)
      = ENNReal.ofReal (∑' n : ℤ, ‖gseq s f n‖ ^ 2) from by
    rw [lintegral_count]
    rw [ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hsum]
    exact tsum_congr (fun n => rpow_two_ofReal _)]
  rw [hval]
  refine ENNReal.ofReal_le_ofReal ?_
  refine hmono.trans (le_of_eq ?_)
  show (∫ θ in (0:ℝ)..1, ‖trigP s f θ‖ ^ 2) = ∑ j ∈ s, ‖f j‖ ^ 2
  exact (Commons.Analysis.Fourier.plancherel_trig_polynomial s f).symm

lemma f_lintegral (s : Finset ℤ) (f : ℤ → ℂ) (hf : ∀ n, n ∉ s → f n = 0) :
    ∫⁻ x : ℤ, ‖f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count
      = ENNReal.ofReal (∑ j ∈ s, ‖f j‖ ^ 2) := by
  rw [lintegral_count]
  rw [show (∑' x : ℤ, ‖f x‖ₑ ^ (2:ℝ))
      = ∑' x : ℤ, ENNReal.ofReal (‖f x‖ ^ 2) from tsum_congr (fun x => rpow_two_ofReal _)]
  rw [show (∑' x : ℤ, ENNReal.ofReal (‖f x‖ ^ 2))
      = ∑ x ∈ s, ENNReal.ofReal (‖f x‖ ^ 2) from
      tsum_eq_sum (fun x hx => by rw [hf x hx, norm_zero]; norm_num)]
  rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => sq_nonneg _)]

lemma add_sq_le (a b : ENNReal) : (a + b) ^ (2:ℝ) ≤ 4 * (a ^ (2:ℝ) + b ^ (2:ℝ)) := by
  simp only [ENNReal.rpow_two, pow_two]
  have hm : a + b ≤ 2 * (a ⊔ b) := by rw [two_mul]; exact add_le_add le_sup_left le_sup_right
  calc (a + b) * (a + b) ≤ (2 * (a ⊔ b)) * (2 * (a ⊔ b)) := mul_le_mul' hm hm
    _ = 4 * ((a ⊔ b) * (a ⊔ b)) := by ring
    _ ≤ 4 * (a * a + b * b) := mul_le_mul_of_nonneg_left (by
        rcases le_total a b with h | h
        · rw [sup_eq_right.mpr h]; exact le_add_of_nonneg_left (by positivity)
        · rw [sup_eq_left.mpr h]; exact le_add_of_nonneg_right (by positivity)) (by norm_num)

theorem Bint_bound (ρ : ℝ) (hρ : 1 < ρ) (B : ℝ) (hB : 0 < B)
    (hBound : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      ∑' i : ℕ, (‖bb ρ i θ‖ₑ) ^ (2:ℝ) ≤ ENNReal.ofReal B)
    (s : Finset ℤ) (f : ℤ → ℂ) (hf : ∀ n, n ∉ s → f n = 0) :
    ∫⁻ x : ℤ, (⨆ i : ℕ, ‖Bint ρ i s f x‖ₑ) ^ (2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal B * ∫⁻ x : ℤ, ‖f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
  have hstep1 : ∀ x : ℤ, (⨆ i : ℕ, ‖Bint ρ i s f x‖ₑ) ^ (2:ℝ)
      ≤ ∑' i : ℕ, (‖Bint ρ i s f x‖ₑ) ^ (2:ℝ) := by
    intro x
    rw [iSup_rpow_two]
    exact iSup_le fun i => ENNReal.le_tsum (f := fun i => ‖Bint ρ i s f x‖ₑ ^ (2:ℝ)) i
  calc ∫⁻ x : ℤ, (⨆ i : ℕ, ‖Bint ρ i s f x‖ₑ) ^ (2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ∫⁻ x : ℤ, (∑' i : ℕ, (‖Bint ρ i s f x‖ₑ) ^ (2:ℝ)) ∂MeasureTheory.Measure.count :=
        lintegral_mono hstep1
    _ = ∑' i : ℕ, ∫⁻ x : ℤ, (‖Bint ρ i s f x‖ₑ) ^ (2:ℝ) ∂MeasureTheory.Measure.count :=
        lintegral_tsum (fun i => (measurable_of_countable _).aemeasurable)
    _ = ∑' i : ℕ, ∫⁻ θ, (‖bb ρ i θ‖ₑ) ^ (2:ℝ) * (‖trigP s f θ‖ₑ) ^ (2:ℝ) ∂mu01 := by
        refine tsum_congr (fun i => ?_)
        rw [lintegral_count]
        exact plancherel_bb_ENN ρ hρ i s f
    _ = ∫⁻ θ, (∑' i : ℕ, (‖bb ρ i θ‖ₑ) ^ (2:ℝ)) * (‖trigP s f θ‖ₑ) ^ (2:ℝ) ∂mu01 := by
        rw [← lintegral_tsum (μ := mu01)
          (f := fun i θ => (‖bb ρ i θ‖ₑ) ^ (2:ℝ) * (‖trigP s f θ‖ₑ) ^ (2:ℝ))
          (fun i => (((measurable_bb (show (0:ℝ) < ρ by linarith) i).enorm.pow_const 2).mul
            ((measurable_trigP s f).enorm.pow_const 2)).aemeasurable)]
        refine lintegral_congr (fun θ => ?_)
        rw [ENNReal.tsum_mul_right]
    _ ≤ ∫⁻ θ, ENNReal.ofReal B * (‖trigP s f θ‖ₑ) ^ (2:ℝ) ∂mu01 := by
        refine lintegral_mono_ae ?_
        filter_upwards [MeasureTheory.ae_restrict_mem (μ := volume) measurableSet_Ioc] with θ hθ
        exact mul_le_mul_of_nonneg_right (hBound θ hθ.1.le hθ.2) (by positivity)
    _ = ENNReal.ofReal B * ∫⁻ θ, (‖trigP s f θ‖ₑ) ^ (2:ℝ) ∂mu01 :=
        lintegral_const_mul _ (Measurable.pow_const (Measurable.enorm (measurable_trigP s f)) 2)
    _ = ENNReal.ofReal B * ∫⁻ x : ℤ, ‖f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
        rw [trig_lintegral, f_lintegral s f hf]

/-! ## The Hardy--Littlewood maximal bound for the smooth sequence -/

lemma hlMaxZ_max_l2 (Chl : ℝ)
    (hChl : ∀ g : ℤ → ℝ,
      ∫⁻ x : ℤ, (⨆ (a : ℤ) (b : ℤ) (_ : a ≤ x ∧ x ≤ b),
          ((b - a + 1).toNat : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.Icc a b, ‖g k‖ₑ) ^ (2:ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (Chl ^ (2:ℝ)) * ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count)
    (s : Finset ℤ) (f : ℤ → ℂ) :
    ∫⁻ x : ℤ, (hlMaxZ (fun k : ℤ => ‖gseq s f k‖ₑ) x) ^ (2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (Chl ^ (2:ℝ))
          * ∫⁻ x : ℤ, ‖gseq s f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
  have h := hChl (fun k : ℤ => ‖gseq s f k‖)
  have h1 : (fun x : ℤ => (⨆ (a : ℤ) (b : ℤ) (_ : a ≤ x ∧ x ≤ b),
        ((b - a + 1).toNat : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.Icc a b, ‖(fun k : ℤ => ‖gseq s f k‖) k‖ₑ) ^ (2:ℝ))
      = fun x : ℤ => (hlMaxZ (fun k : ℤ => ‖gseq s f k‖ₑ) x) ^ (2:ℝ) := by
    funext x
    rw [show (⨆ (a : ℤ) (b : ℤ) (_ : a ≤ x ∧ x ≤ b),
        ((b - a + 1).toNat : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.Icc a b, ‖(fun k : ℤ => ‖gseq s f k‖) k‖ₑ)
        = hlMaxZ (fun k : ℤ => ‖gseq s f k‖ₑ) x from
      hlMaxZ_congr (fun k => enorm_norm_eq (gseq s f k)) x]
  have h2 : (fun x : ℤ => ‖(fun k : ℤ => ‖gseq s f k‖) x‖ₑ ^ (2:ℝ))
      = fun x : ℤ => ‖gseq s f x‖ₑ ^ (2:ℝ) := by
    funext x; rw [enorm_norm_eq]
  rw [h1, h2] at h
  exact h

end
end Lacunary

open Lacunary

theorem lacunary_truncated_maximal_l2 (ρ : ℝ) (hρ : 1 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → f n = 0) →
      ∫⁻ x : ℤ, (⨆ (i : ℕ), ‖∫ θ in (0:ℝ)..1,
          (if |θ| ≤ ρ ^ (-(i : ℤ)) then (1 : ℂ) else 0) *
            (∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (θ : ℂ))) *
            Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))‖ₑ) ^ (2 : ℝ)
        ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C ^ 2) *
          ∫⁻ x : ℤ, ‖f x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
  obtain ⟨B, hBpos, hBound⟩ := boundary_tsum_sq_le ρ hρ
  obtain ⟨Chl, hChlpos, hChl⟩ := Commons.Analysis.HardyLittlewood.discrete_maximal_lp (p := 2) (by norm_num)
  refine ⟨Real.sqrt (4 * Chl ^ 2 + 4 * B), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro f s hf
  have hBoundENN : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      ∑' i : ℕ, (‖bb ρ i θ‖ₑ) ^ (2:ℝ) ≤ ENNReal.ofReal B := by
    intro θ h0 h1
    rw [show (∑' i : ℕ, (‖bb ρ i θ‖ₑ) ^ (2:ℝ))
        = ENNReal.ofReal (∑' i : ℕ, ‖bb ρ i θ‖ ^ 2) from by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) (bb_summable ρ hρ θ h0 h1)]
      exact tsum_congr (fun i => rpow_two_ofReal _)]
    exact ENNReal.ofReal_le_ofReal (hBound θ h0 h1)
  have hAint : ∫⁻ x : ℤ, (⨆ i : ℕ, ‖Aint ρ i s f x‖ₑ) ^ (2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (Chl ^ (2:ℝ))
          * ∫⁻ x : ℤ, ‖gseq s f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
    refine (lintegral_mono (fun x => ?_)).trans (hlMaxZ_max_l2 Chl hChl s f)
    exact ENNReal.rpow_le_rpow (iSup_le fun i => Aint_bound ρ hρ i s f x) (by norm_num)
  have hBint := Bint_bound ρ hρ B hBpos hBoundENN s f hf
  have hG := gseq_lintegral_le s f
  have hNs := f_lintegral s f hf
  set N : ENNReal := ∫⁻ x : ℤ, ‖f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count with hN
  have key : ∀ x : ℤ, (⨆ (i : ℕ), ‖Tint ρ i s f x‖ₑ) ^ (2:ℝ)
      ≤ 4 * ((⨆ i : ℕ, ‖Aint ρ i s f x‖ₑ) ^ (2:ℝ)
        + (⨆ i : ℕ, ‖Bint ρ i s f x‖ₑ) ^ (2:ℝ)) := by
    intro x
    have h1 : (⨆ i : ℕ, ‖Tint ρ i s f x‖ₑ)
        ≤ (⨆ i : ℕ, ‖Aint ρ i s f x‖ₑ) + (⨆ i : ℕ, ‖Bint ρ i s f x‖ₑ) := by
      refine iSup_le fun i => ?_
      rw [Tint_split ρ hρ i s f x]
      exact (enorm_add_le (Aint ρ i s f x) (Bint ρ i s f x)).trans
        (add_le_add (le_iSup (fun i : ℕ => ‖Aint ρ i s f x‖ₑ) i)
          (le_iSup (fun i : ℕ => ‖Bint ρ i s f x‖ₑ) i))
    calc (⨆ i : ℕ, ‖Tint ρ i s f x‖ₑ) ^ (2:ℝ)
        ≤ ((⨆ i : ℕ, ‖Aint ρ i s f x‖ₑ) + (⨆ i : ℕ, ‖Bint ρ i s f x‖ₑ)) ^ (2:ℝ) :=
          ENNReal.rpow_le_rpow h1 (by norm_num : (0:ℝ) ≤ 2)
      _ ≤ 4 * ((⨆ i : ℕ, ‖Aint ρ i s f x‖ₑ) ^ (2:ℝ)
          + (⨆ i : ℕ, ‖Bint ρ i s f x‖ₑ) ^ (2:ℝ)) := add_sq_le _ _
  have harith : (4:ENNReal) * (ENNReal.ofReal (Chl ^ (2:ℝ)) * N) + 4 * (ENNReal.ofReal B * N)
      = ENNReal.ofReal ((Real.sqrt (4 * Chl ^ 2 + 4 * B)) ^ 2) * N := by
    have hA : (4:ENNReal) * ENNReal.ofReal (Chl ^ (2:ℝ)) = ENNReal.ofReal (4 * Chl ^ 2) := by
      rw [show (4:ENNReal) = ENNReal.ofReal 4 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4), Real.rpow_two]
    have hB' : (4:ENNReal) * ENNReal.ofReal B = ENNReal.ofReal (4*B) := by
      rw [show (4:ENNReal) = ENNReal.ofReal 4 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
    rw [← mul_assoc, ← mul_assoc, ← add_mul, hA, hB',
      ← ENNReal.ofReal_add (by positivity) (by positivity), Real.sq_sqrt (by positivity)]
  calc ∫⁻ x : ℤ, (⨆ (i : ℕ), ‖Tint ρ i s f x‖ₑ) ^ (2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ∫⁻ x : ℤ, 4 * ((⨆ i : ℕ, ‖Aint ρ i s f x‖ₑ) ^ (2:ℝ)
          + (⨆ i : ℕ, ‖Bint ρ i s f x‖ₑ) ^ (2:ℝ)) ∂MeasureTheory.Measure.count :=
        lintegral_mono key
    _ = 4 * (∫⁻ x : ℤ, (⨆ i : ℕ, ‖Aint ρ i s f x‖ₑ) ^ (2:ℝ) ∂MeasureTheory.Measure.count
        + ∫⁻ x : ℤ, (⨆ i : ℕ, ‖Bint ρ i s f x‖ₑ) ^ (2:ℝ) ∂MeasureTheory.Measure.count) := by
        rw [lintegral_const_mul _ (measurable_of_countable _)]
        congr 1
        rw [lintegral_add_left (measurable_of_countable _)]
    _ ≤ 4 * (ENNReal.ofReal (Chl ^ (2:ℝ))
          * ∫⁻ x : ℤ, ‖gseq s f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count
        + ENNReal.ofReal B * N) := by
        refine mul_le_mul_of_nonneg_left (add_le_add hAint ?_) (by norm_num)
        rw [hN]; exact hBint
    _ ≤ 4 * (ENNReal.ofReal (Chl ^ (2:ℝ)) * N + ENNReal.ofReal B * N) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) (by norm_num)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [hNs]
        exact hG
    _ = ENNReal.ofReal ((Real.sqrt (4 * Chl ^ 2 + 4 * B)) ^ 2) * N := by
        rw [mul_add]; exact harith
    _ = ENNReal.ofReal ((Real.sqrt (4 * Chl ^ 2 + 4 * B)) ^ 2)
          * ∫⁻ x : ℤ, ‖f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by rw [hN]

end Work.BourgainPlan.Oscillation
