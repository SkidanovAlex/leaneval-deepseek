import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Submission.ScatKernelChosen
import Submission.Work.SmallBoxA0.laplacian_comp_isometry
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory Metric
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The weak scattering equation, transported to `g₀ = v(1-w₀)` with `w₀ := Classical.choose h`:
for every test function `φ`, `∫ φ·g₀ = -2 ∫ w₀·Δφ`. -/
lemma integral_g0_mul_test {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v)
    (φ : ℝ³ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∫ x, φ x * Submission.BoseGases.g0 v h x
      = -2 * ∫ x, Classical.choose h x * (Laplacian.laplacian φ) x := by
  have hspec := Classical.choose_spec h
  have heq := hspec.2.eq φ ⟨hφ, hφc⟩
  have h1 : ∫ x, φ x * Submission.BoseGases.g0 v h x
      = ∫ x, v x * (1 - Classical.choose h x) * φ x := by
    congr 1 with x
    rw [show Submission.BoseGases.g0 v h x = v x * (1 - Classical.choose h x) from rfl]
    ring
  rw [h1]
  linarith

/-- Integrating against a radial function is invariant under a linear isometry. -/
lemma integral_radial_comp_isometry {w : ℝ³ → ℝ} (hw : BoseGases.IsRadial w)
    (B : ℝ³ ≃ₗᵢ[ℝ] ℝ³) (F : ℝ³ → ℝ) :
    ∫ x, w x * F (B x) = ∫ x, w x * F x := by
  have h1 := (B.measurePreserving).integral_comp' (f := B.toMeasurableEquiv)
    (fun y => w (B.symm y) * F y)
  simp only [LinearIsometryEquiv.coe_toMeasurableEquiv,
    LinearIsometryEquiv.symm_apply_apply] at h1
  rw [h1]
  apply integral_congr_ae
  filter_upwards with y
  rw [hw (B.symm y) y (by rw [LinearIsometryEquiv.norm_map])]

lemma g0_rotation_invariant {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v) (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) : Submission.BoseGases.g0 v h =ᵐ[MeasureTheory.volume] fun x => Submission.BoseGases.g0 v h (A x) := by
  have hspec := Classical.choose_spec h
  -- the weak equation, in terms of `w₀ = Classical.choose h`
  have key : ∀ φ : ℝ³ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, φ x * Submission.BoseGases.g0 v h x
        = -2 * ∫ x, Classical.choose h x * (Laplacian.laplacian φ) x :=
    fun φ hφ hφc => integral_g0_mul_test h φ hφ hφc
  -- integration against the radial `w₀` is rotation invariant
  have hrot : ∀ (B : ℝ³ ≃ₗᵢ[ℝ] ℝ³) (F : ℝ³ → ℝ),
      ∫ x, Classical.choose h x * F (B x) = ∫ x, Classical.choose h x * F x :=
    fun B F => integral_radial_comp_isometry hspec.1 B F
  -- the distributional identity: `g₀` and `g₀ ∘ A` have the same moments
  have hfin : ∀ φ : ℝ³ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, φ x * Submission.BoseGases.g0 v h (A x)
        = ∫ x, φ x * Submission.BoseGases.g0 v h x := by
    intro φ hφ hφc
    have hφ2 : ContDiff ℝ 2 φ :=
      hφ.of_le (WithTop.coe_le_coe.mpr le_top : (2 : ℕ∞ω) ≤ ∞)
    -- change of variables `x ↦ A x`
    have h1 := (A.measurePreserving).integral_comp' (f := A.toMeasurableEquiv)
      (fun y => φ (A.symm y) * Submission.BoseGases.g0 v h y)
    simp only [LinearIsometryEquiv.coe_toMeasurableEquiv,
      LinearIsometryEquiv.symm_apply_apply] at h1
    rw [h1]
    -- the weak equation applied to the test function `φ ∘ A.symm`
    have hψc : ContDiff ℝ ∞ (fun y : ℝ³ => φ (A.symm y)) := by
      have h := hφ.comp (A.symm.contDiff (𝕜 := ℝ) (n := ∞))
      simpa only [Function.comp_def] using h
    have hψs : HasCompactSupport (fun y : ℝ³ => φ (A.symm y)) := by
      have h := hφc.comp_homeomorph A.symm.toHomeomorph
      simpa only [LinearIsometryEquiv.coe_toHomeomorph, Function.comp_def] using h
    have h2 : ∫ y, φ (A.symm y) * Submission.BoseGases.g0 v h y
        = -2 * ∫ y, Classical.choose h y
            * (Laplacian.laplacian (fun y : ℝ³ => φ (A.symm y))) y :=
      key (fun y : ℝ³ => φ (A.symm y)) hψc hψs
    rw [h2]
    -- the Laplacian is invariant under `A.symm`
    have hlap : (Laplacian.laplacian (fun y : ℝ³ => φ (A.symm y)))
        = fun y => (Laplacian.laplacian φ) (A.symm y) :=
      laplacian_comp_isometry A.symm φ hφ2
    simp only [hlap]
    -- undo the change of variables under the integral against the radial `w₀`
    rw [hrot A.symm (Laplacian.laplacian φ)]
    -- the weak equation for `φ`
    rw [key φ hφ hφc]
  have hg0int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  have hAint : MeasureTheory.Integrable
      (fun x : ℝ³ => Submission.BoseGases.g0 v h (A x)) := by
    have h := (A.measurePreserving).integrable_comp_of_integrable hg0int
    simpa [Function.comp_def] using h
  have hkey : ∀ g : ℝ³ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, g x • (fun x : ℝ³ => Submission.BoseGases.g0 v h (A x)) x
        = ∫ x, g x • Submission.BoseGases.g0 v h x := by
    intro g hg hgc
    simpa [smul_eq_mul] using hfin g hg hgc
  have hmain := ae_eq_of_integral_contDiff_smul_eq
    (f := fun x : ℝ³ => Submission.BoseGases.g0 v h (A x))
    (f' := Submission.BoseGases.g0 v h) (μ := MeasureTheory.volume)
    hAint.locallyIntegrable hg0int.locallyIntegrable hkey
  filter_upwards [hmain] with x hx
  exact hx.symm

end Work.SmallBoxA0
