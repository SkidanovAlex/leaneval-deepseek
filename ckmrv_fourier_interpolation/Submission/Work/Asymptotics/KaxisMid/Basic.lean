/-
# Global bounds for the CKMRV middle-range estimate

This file collects the global inputs of the middle-range bound
`Work.Asymptotics.KaxisMid.Kaxis_local_middle` for the CKMRV kernel: bounds for the scale
`S τ = 1 + (im τ)⁻¹ + |τ|` on the relevant compact sets, the resulting bound for the *cleared*
kernel `KfunClear` (from `Work.Asymptotics.KClear_mg2`, Theorem 4.9(4) of the paper), and the
non-vanishing of `Δ` on compact sets.

The metric estimates are all stated for the *Euclidean* distance `‖τ - z‖` on `ℍ ⊆ ℂ`; the
hyperbolic metric of `ℍ` is not used here.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.Theorem31
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.KClear_mg2
import Submission.Work.Kernels.ClassicalFacts.DeltaFun_basic
import Submission.Work.Kernels.ClearLink.KPlusClear_eq_smul
import Submission.Work.Kernels.ClearLink.KMinusClear_eq_smul
import Submission.Work.Residues.KPlusClear_diag
import Submission.Work.Residues.KMinusClear_diag
import Submission.Work.Asymptotics.KClear_S_vanishing
import Submission.Work.Asymptotics.orbit_imagAxis_of_mem_DomainD
import Submission.Work.Asymptotics.eq_one_or_neg_one_or_S_of_smul_imagAxis

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped Topology MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Asymptotics.KaxisMid

open Work.Kernels

/-! ## The scale -/

lemma continuous_scale : Continuous (scale : ℍ → ℝ) := by
  have h1 : Continuous (fun z : ℍ => (z.im)⁻¹) :=
    UpperHalfPlane.continuous_im.inv₀ (fun z => z.im_ne_zero)
  have h2 : Continuous (fun z : ℍ => ‖(z : ℂ)‖) :=
    continuous_norm.comp UpperHalfPlane.continuous_coe
  have h3 : scale = fun z : ℍ => 1 + (z.im)⁻¹ + ‖(z : ℂ)‖ := rfl
  rw [h3]
  exact (continuous_const.add h1).add h2

theorem exists_scale_bound_of_isCompact {S : Set ℍ} (hS : IsCompact S) :
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ S, scale z ≤ R := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨z₀, _, hmax⟩ := hS.exists_isMaxOn hne continuous_scale.continuousOn
    exact ⟨scale z₀, scale_pos z₀, fun z hz => (isMaxOn_iff.mp hmax) z hz⟩

/-- On the Euclidean ball `‖z - c‖ ≤ r` with `r < im c` the scale is bounded.  Only the
elementary estimates `im z ≥ im c - r` and `‖z‖ ≤ ‖c‖ + r` are used. -/
theorem exists_scale_bound_euclidean {c : ℍ} {r : ℝ} (hr : r < c.im) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℍ, ‖(z : ℂ) - (c : ℂ)‖ ≤ r → scale z ≤ R := by
  have hpos : 0 < c.im - r := by linarith [c.im_pos, hr]
  refine ⟨max (1 + (c.im - r)⁻¹ + (‖(c : ℂ)‖ + r)) 1,
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun z hz => ?_⟩
  have hnorm : ‖(z : ℂ)‖ ≤ ‖(c : ℂ)‖ + r := by
    have h1 : ‖(z : ℂ)‖ ≤ ‖(z : ℂ) - (c : ℂ)‖ + ‖(c : ℂ)‖ := by
      have := norm_add_le ((z : ℂ) - (c : ℂ)) (c : ℂ)
      simpa using this
    linarith [h1, hz]
  have him : c.im - r ≤ z.im := by
    have h1 : |((z : ℂ) - (c : ℂ)).im| ≤ ‖(z : ℂ) - (c : ℂ)‖ := Complex.abs_im_le_norm _
    have h2 : ((z : ℂ) - (c : ℂ)).im = z.im - c.im := by
      simp [Complex.sub_im, UpperHalfPlane.coe_im]
    have h3 : ‖(z : ℂ) - (c : ℂ)‖ ≤ r := hz
    have h4 : -(r) ≤ z.im - c.im := by
      rw [← h2]; exact (abs_le.mp (le_trans h1 h3)).1
    linarith
  have hinv : (z.im)⁻¹ ≤ (c.im - r)⁻¹ := inv_anti₀ hpos him
  have hkey : scale z ≤ 1 + (c.im - r)⁻¹ + (‖(c : ℂ)‖ + r) := by
    simp only [scale]
    linarith [hinv, hnorm]
  exact le_trans hkey (le_max_left _ _)

/-! ## The cleared kernel is bounded on a box in terms of the scale bounds -/

theorem exists_bound_KfunClear_of_scale_bounds (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {S T : Set ℍ} {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (hb₁ : ∀ τ ∈ S, scale τ ≤ R₁) (hb₂ : ∀ z ∈ T, scale z ≤ R₂) :
    ∃ M : ℝ, 0 < M ∧ ∀ τ ∈ S, ∀ z ∈ T, ‖KfunClear ℓ d τ z‖ ≤ M := by
  obtain ⟨α, N, M, hα, hN, hM, h⟩ := (KClear_mg2 ℓ d hd).1
  refine ⟨max (α * R₁ ^ N * R₂ ^ M) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun τ hτ z hz => ?_⟩
  refine le_trans (h τ z) ?_
  have h1 : (scale τ) ^ N ≤ R₁ ^ N :=
    Real.rpow_le_rpow (scale_pos τ).le (hb₁ τ hτ) hN
  have h2 : (scale z) ^ M ≤ R₂ ^ M :=
    Real.rpow_le_rpow (scale_pos z).le (hb₂ z hz) hM
  calc α * (scale τ) ^ N * (scale z) ^ M
      ≤ α * R₁ ^ N * R₂ ^ M := by
        apply mul_le_mul _ h2 (Real.rpow_nonneg (scale_pos z).le M) (by positivity)
        exact mul_le_mul_of_nonneg_left h1 hα
    _ ≤ max (α * R₁ ^ N * R₂ ^ M) 1 := le_max_left _ _

/-! ## `Δ` is bounded away from zero on compact sets -/

theorem exists_lower_DeltaFun {S : Set ℍ} (hS : IsCompact S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ S, δ ≤ ‖DeltaFun z‖ := by
  have hcont : Continuous (fun z : ℍ => DeltaFun z) :=
    (CuspForm.holo' CuspForm.discriminant).continuous
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨z₀, hz₀S, hmin⟩ := hS.exists_isMinOn hne (Continuous.norm hcont).continuousOn
    refine ⟨‖DeltaFun z₀‖, norm_pos_iff.mpr (ClassicalFacts.DeltaFun_ne_zero z₀), fun z hz => ?_⟩
    exact (isMinOn_iff.mp hmin) z hz

end Work.Asymptotics.KaxisMid
