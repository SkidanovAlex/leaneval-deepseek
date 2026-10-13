/-
# `Work.FTS.StrongPersist.L3Rhs.L3RhsFKadd` — additivity of the angular moment `FK`

`Work.Construction.FK F z = ∫_θ F(z,θ) K(θ) dθ` is an integral, so it is additive in the
profile: for `F = F_* + g` (`Work.Construction.Ftot`), `FK (F_*+g) z = FK F_* z + FK g z`.

Linearity of the Bochner integral needs *integrability of both summands* (the integral of a
non-integrable function is the junk value `0`, and is not additive).  Here the datum is
`H6Adm α f`, i.e.

* `SmoothOpen f` — `f` is `C^∞` on the **open** quadrant `(0,∞) × (0,π/2)`, and
* `HkMem α 6 f` — the weighted derivatives of `f` are honestly integrable.

At a fixed `z > 0` this gives, on the angular interval `Iθ = [0,π/2]`:

* the slice `θ ↦ f z θ` is a.e. strongly measurable (continuity on the open quadrant; the two
  endpoints are null — this is `Work.Spaces.aesm_slice_of_continuousOn_Qd`, and *no* continuity
  of the slice at `θ = 0, π/2` is available or needed);
* `(f z θ)^2 ≤ HkIntegrand α 6 f z θ` a.e., because on the open interval
  `w z ≥ 1` and `sin(2θ)^{η/2} ≤ 1` make the `i = 0` term of the `D_z`-sum pair of the
  integrand dominate `(f z θ)^2` (`Work.Spaces.sq_le_HkIntegrand_z`).  Hence `θ ↦ (f z θ)²` is
  integrable on `Iθ` by `Integrable.mono'`.

The `K`-weighted slice `θ ↦ K(θ)·f z θ` is then integrable as well, since
`|K θ · f z θ| ≤ (K θ² + f z θ²)/2` and `K` is continuous (hence bounded) on the compact `Iθ`.
The `F_*`-slice is continuous on the compact `Iθ` (the only singularity of
`Γ(θ) = (sinθcos²θ)^{α/3}` is at the endpoints, where the positive exponent makes `Γ`
continuous), so `∫ (F_* + f)·K = ∫ F_*·K + ∫ f·K` by `MeasureTheory.integral_add`.

Resting on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Rhs

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Elementary pointwise tools -/

/-- AM–GM: `|a·b| ≤ (a² + b²)/2`. -/
private lemma abs_mul_le_half_sq (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : 2 * |a| * |b| ≤ |a| ^ 2 + |b| ^ 2 := by nlinarith [sq_nonneg (|a| - |b|)]
  calc |a * b| = |a| * |b| := abs_mul a b
    _ ≤ (|a| ^ 2 + |b| ^ 2) / 2 := by linarith
    _ = (a ^ 2 + b ^ 2) / 2 := by rw [sq_abs a, sq_abs b]

/-- `a² ≤ (a·c)²` for `1 ≤ c`. -/
private lemma sq_le_sq_mul_of_one_le {a c : ℝ} (hc : 1 ≤ c) : a ^ 2 ≤ (a * c) ^ 2 := by
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  calc a ^ 2 = (|a| * 1) ^ 2 := by rw [mul_one, sq_abs]
    _ ≤ (|a| * c) ^ 2 := pow_le_pow_left₀ (mul_nonneg (abs_nonneg a) zero_le_one)
        (mul_le_mul_of_nonneg_left hc (abs_nonneg a)) 2
    _ = (a * c) ^ 2 := by rw [mul_pow, mul_pow, sq_abs]

/-! ## Integrability of the angular slices -/

/-- The angular slice `θ ↦ f s θ` of a function `C^∞` on the open quadrant is a.e. strongly
measurable for `volume.restrict Iθ` and `s > 0`: its restriction to `(0,π/2)` is continuous,
and the two endpoints are null. -/
private theorem aesm_slice_of_smoothOpen {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) {s : ℝ} (hs : 0 < s) :
    AEStronglyMeasurable (fun θ : ℝ => f s θ) (volume.restrict Work.Spaces.Iθ) := by
  have h1 : AEStronglyMeasurable (fun θ : ℝ => f s θ)
      (volume.restrict (Set.Ioo 0 (π / 2))) :=
    (hsm.curry_θ hs).continuousOn.aestronglyMeasurable measurableSet_Ioo
  have hcongr : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo 0 (π / 2)) := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := π / 2)).symm
  rw [hcongr]
  exact h1

/-- For `s > 0` the square slice `θ ↦ (f s θ)²` of an `ℋ^k`-datum with interior smoothness is
integrable on `Iθ`.  Only the `i = 0` term of the `D_z`-part of `HkIntegrand` is used, and only
on the open interval (where `sin(2θ) > 0`); the two endpoints are null. -/
private theorem integrableOn_sq_slice {α : ℝ} {f : ℝ → ℝ → ℝ} {k : ℕ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f)
    {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun θ : ℝ => (f s θ) ^ 2) Work.Spaces.Iθ := by
  refine (hmem.1 s (le_of_lt hs)).mono' ((aesm_slice_of_smoothOpen hsm hs).pow 2) ?_
  -- replace `volume.restrict Iθ` by `volume.restrict (0,π/2)`, where `sin(2θ) > 0`
  have hcongr : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo 0 (π / 2)) := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := π / 2)).symm
  rw [hcongr]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsle : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one hs0.le (Real.sin_le_one _)
      (by have := Work.Spaces.eta_pos; linarith)
  have hspos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hs0 _
  have hw1 : 1 ≤ Work.Spaces.w s := by
    rw [Work.Spaces.w, le_div_iff₀ (pow_pos hs 2)]
    nlinarith
  have hA : 1 ≤ Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    (le_div_iff₀ hspos).mpr (by rw [one_mul]; exact le_trans hsle hw1)
  have h1 : (f s θ) ^ 2
      ≤ (f s θ * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
    sq_le_sq_mul_of_one_le hA
  have h2 : (Work.Spaces.DzIter 0 f s θ
        * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Work.Spaces.HkIntegrand α k f s θ :=
    Work.Spaces.sq_le_HkIntegrand_z α k f s θ 0 (Nat.zero_le k)
  simpa only [Work.Spaces.DzIter_zero] using le_trans h1 h2

/-- For `s > 0` the `K`-weighted slice `θ ↦ f s θ · K θ` is integrable on `Iθ`, from
`SmoothOpen f` and `HkMem α k f`: `K` is bounded on the compact `Iθ`, and the square slice is
integrable. -/
private theorem integrableOn_K_mul_slice {α : ℝ} {f : ℝ → ℝ → ℝ} {k : ℕ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f)
    {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun θ : ℝ => f s θ * Work.Spaces.K θ) Work.Spaces.Iθ := by
  have hsq := integrableOn_sq_slice hsm hmem hs
  have hKcont : Continuous Work.Spaces.K := by
    have h : Work.Spaces.K = fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2 := by
      funext θ; rfl
    rw [h]
    exact (continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)
  have hKsq : IntegrableOn (fun θ : ℝ => (Work.Spaces.K θ) ^ 2) Work.Spaces.Iθ :=
    ContinuousOn.integrableOn_compact isCompact_Icc (hKcont.continuousOn.pow 2)
  have hmaj : Integrable (fun θ => ((f s θ) ^ 2 + (Work.Spaces.K θ) ^ 2) / 2)
      (volume.restrict Work.Spaces.Iθ) := (hsq.add hKsq).div_const 2
  refine hmaj.mono' ?_ ?_
  · exact (aesm_slice_of_smoothOpen hsm hs).mul (hKcont.aestronglyMeasurable.restrict)
  · filter_upwards with θ
    rw [Real.norm_eq_abs]
    exact abs_mul_le_half_sq (f s θ) (Work.Spaces.K θ)

/-- The `F_*`-slice `θ ↦ F_*(α) z θ · K θ` is integrable on `Iθ` for every `z` and `α > 0`:
it is continuous on the compact `Iθ`. -/
private theorem integrableOn_slice_Fstar_mul_K (α : ℝ) (hα : 0 < α) (s : ℝ) :
    IntegrableOn (fun θ => Work.Construction.Fstar α s θ * Work.Spaces.K θ)
      Work.Spaces.Iθ := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  have hGam : ContinuousOn (fun θ => Work.Spaces.Gam α θ) Work.Spaces.Iθ := by
    unfold Work.Spaces.Gam
    intro θ _
    exact (Real.continuousAt_rpow_const _ _ (Or.inr (by positivity))).comp_continuousWithinAt
      (by fun_prop)
  have hF : ContinuousOn (fun θ => Work.Construction.Fstar α s θ) Work.Spaces.Iθ := by
    simp only [Work.Construction.Fstar]
    exact ((continuousOn_const.mul (hGam.div_const (Work.Spaces.c α))).mul continuousOn_const)
  have hK : ContinuousOn (fun θ => Work.Spaces.K θ) Work.Spaces.Iθ := by
    unfold Work.Spaces.K; fun_prop
  exact hF.mul hK

/-! ## The main theorem -/

theorem L3RhsFKadd : ∀ α ∈ Set.Ioc 0 1, ∀ (f : Work.FTS.Galerkin.Fn),
    Work.FTS.StrongPersist.H6Adm α f → ∀ z : ℝ, 0 < z →
    Work.Construction.FK (Work.Construction.Ftot α f) z
      = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK f z := by
  intro α hα f hadm z hz
  obtain ⟨hsm, hmem⟩ := hadm.reg
  have hFint : IntegrableOn
      (fun θ => Work.Construction.Fstar α z θ * Work.Spaces.K θ) Work.Spaces.Iθ :=
    integrableOn_slice_Fstar_mul_K α hα.1 z
  have hfint : IntegrableOn (fun θ => f z θ * Work.Spaces.K θ) Work.Spaces.Iθ :=
    integrableOn_K_mul_slice hsm hmem hz
  have key : (∫ θ in Work.Spaces.Iθ,
        (Work.Construction.Fstar α z θ + f z θ) * Work.Spaces.K θ)
      = (∫ θ in Work.Spaces.Iθ, Work.Construction.Fstar α z θ * Work.Spaces.K θ)
        + ∫ θ in Work.Spaces.Iθ, f z θ * Work.Spaces.K θ := by
    have hpt : (fun θ => (Work.Construction.Fstar α z θ + f z θ) * Work.Spaces.K θ)
        = fun θ => Work.Construction.Fstar α z θ * Work.Spaces.K θ
            + f z θ * Work.Spaces.K θ := by
      funext θ; ring
    rw [hpt]
    exact MeasureTheory.integral_add hFint hfint
  simpa only [Work.Construction.FK, Work.Construction.Ftot] using key

end Work.FTS.StrongPersist.L3Rhs
