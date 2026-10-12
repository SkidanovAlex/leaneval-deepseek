import ChallengeDeps
import Submission.Work.BoseFixR.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

open MeasureTheory

/-- **The mass of `W₁ = wScaled ℓ (g₀ v h)` is strictly positive.**

`W₁` is nonnegative a.e. (`g₀ ≥ 0` a.e., `convScale ≥ 0`) and integrable in the
dilute regime (`|wScaled| ≤ 2|g₀|` because `(χ⋆χ)(·/ℓ) ≥ 1/2` on `ball 0 R`);
its support contains the support of `g₀` (on `supp g₀` the renormalisation
factor `convScale ℓ` is `≥ 1/2`, hence nonzero), whose measure is positive
because `∫ g₀ = 8π·a v > 0`.  Conclude with the integral/support criterion for
nonnegative integrable functions. -/
theorem W1fun_mass_pos (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    {R ℓ : ℝ} (hR : 0 < R) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) (hℓ : 0 < ℓ) :
    0 < ∫ y : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h ℓ y := by
  -- the mass of `g₀` is `8π·a v > 0`
  have hg0i : Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  have hg0nn : 0 ≤ᵐ[volume] Submission.BoseGases.g0 v h :=
    Submission.BoseGases.g0_nonneg_ae hR hv hvrad hv_supp h
  have hg0mass : 0 < ∫ z, Submission.BoseGases.g0 v h z := by
    rw [Submission.BoseGases.g0_integral hR hv_supp h]
    exact mul_pos (by positivity) hav
  -- hence `g₀` has support of positive measure
  have hsuppg : 0 < volume (Function.support (Submission.BoseGases.g0 v h)) :=
    (MeasureTheory.integral_pos_iff_support_of_nonneg_ae hg0nn hg0i).mp hg0mass
  -- on the support of `g₀` the renormalisation factor is `≥ 1/2 > 0`
  have hsub : Function.support (Submission.BoseGases.g0 v h)
      ⊆ Function.support (Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h)) := by
    intro z hz
    rw [Function.mem_support] at hz ⊢
    have hzR : ‖z‖ ≤ R := by
      by_contra hcon
      exact hz (Submission.BoseGases.g0_zero_of_norm_ge hv_supp (le_of_lt (not_le.mp hcon)) h)
    have hc : (1 : ℝ) / 2 ≤ Submission.BoseGases.convScale ℓ z :=
      Submission.BoseGases.convScale_ge_half_ball hℓ hR.le hRℓ hzR
    have hcne : Submission.BoseGases.convScale ℓ z ≠ 0 := by linarith
    exact div_ne_zero hz hcne
  have hsuppW : 0 < volume
      (Function.support (Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h))) :=
    lt_of_lt_of_le hsuppg (measure_mono hsub)
  -- `W₁` is nonnegative a.e. and integrable, so the criterion applies
  have hWnn : 0 ≤ᵐ[volume] Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.wScaled_g0_nonneg_ae hR hv hvrad hv_supp h
  have hWi : Integrable (Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h)) :=
    Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ
  have hpos := (MeasureTheory.integral_pos_iff_support_of_nonneg_ae hWnn hWi).mpr hsuppW
  simpa only [Work.BoseFixR.W1fun] using hpos

end Work.BoseBogFS
