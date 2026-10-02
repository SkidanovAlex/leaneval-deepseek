import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.QC.integral_lineDeriv_mul_eq_complex
import Submission.Work.MRMT.QC.locallyIntegrableOn_dz_of_lipschitzOnWith
import Submission.Work.MRMT.QC.beltramiOf_ae_bound_and_dilatation

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Locally Lipschitz homeomorphisms with dilatation `< 1` are quasiconformal

A homeomorphism `g` on an open set `U` which is Lipschitz on `U` and whose pointwise complex
dilatation `dzbar g / dz g` is bounded by some `k < 1` almost everywhere on `U` is quasiconformal
(`Work.MRMT.IsQCOn`) with dilatation `beltramiOf g`.

The only non-trivial point is the `W^{1,2}_{loc}` clause of `IsQCOn`: by Rademacher's theorem a
Lipschitz map is differentiable almost everywhere, and its a.e. pointwise derivative is its weak
(distributional) derivative.  We prove the distributional Wirtinger identities by extending `g` to
a globally Lipschitz map `G` (`LipschitzOnWith.extend_finite_dimension`), applying the
integration-by-parts formula for line derivatives of Lipschitz functions
(`Work.MRMT.QC.integral_lineDeriv_mul_eq_complex`), and transferring the integrands from `G` back
to `g` using the fact that they only see the values of `g` on `U` (the test functions are
supported in `U`).
-/

noncomputable section

open MeasureTheory Complex Function Filter
open scoped Distributions Topology

namespace Work.MRMT.QC
-- ============ integrability tools ============


/-- A function supported in a compact set, a.e. strongly measurable on it and bounded on it,
is integrable. -/
theorem integrable_of_isCompact_of_bound {f : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K)
    (hsupp : Function.support f ⊆ K) (hmeas : AEStronglyMeasurable f (volume.restrict K))
    (C : ℝ) (hb : ∀ᵐ z ∂(volume.restrict K), ‖f z‖ ≤ C) : Integrable f volume :=
  (integrableOn_iff_integrable_of_support_subset hsupp).mp
    (IntegrableOn.of_bound hK.measure_lt_top hmeas C hb)

theorem norm_dz_le (g : ℂ → ℂ) (z : ℂ) : ‖dz g z‖ ≤ ‖fderiv ℝ g z‖ := by
  have h1 : ‖(fderiv ℝ g z) 1‖ ≤ ‖fderiv ℝ g z‖ := by
    simpa using ContinuousLinearMap.le_opNorm (fderiv ℝ g z) (1 : ℂ)
  have h2 : ‖(fderiv ℝ g z) Complex.I‖ ≤ ‖fderiv ℝ g z‖ := by
    simpa [Complex.norm_I] using ContinuousLinearMap.le_opNorm (fderiv ℝ g z) Complex.I
  have hC : ‖fderiv ℝ g z 1 - Complex.I * fderiv ℝ g z Complex.I‖ ≤ 2 * ‖fderiv ℝ g z‖ := by
    calc ‖fderiv ℝ g z 1 - Complex.I * fderiv ℝ g z Complex.I‖
        ≤ ‖fderiv ℝ g z 1‖ + ‖Complex.I * fderiv ℝ g z Complex.I‖ := norm_sub_le _ _
      _ = ‖fderiv ℝ g z 1‖ + ‖fderiv ℝ g z Complex.I‖ := by rw [norm_mul, Complex.norm_I, one_mul]
      _ ≤ 2 * ‖fderiv ℝ g z‖ := by linarith
  rw [dz, div_eq_mul_inv, norm_mul, norm_inv, show ‖(2 : ℂ)‖ = 2 by norm_num, inv_eq_one_div]
  linarith

theorem norm_dzbar_le (g : ℂ → ℂ) (z : ℂ) : ‖dzbar g z‖ ≤ ‖fderiv ℝ g z‖ := by
  have h1 : ‖(fderiv ℝ g z) 1‖ ≤ ‖fderiv ℝ g z‖ := by
    simpa using ContinuousLinearMap.le_opNorm (fderiv ℝ g z) (1 : ℂ)
  have h2 : ‖(fderiv ℝ g z) Complex.I‖ ≤ ‖fderiv ℝ g z‖ := by
    simpa [Complex.norm_I] using ContinuousLinearMap.le_opNorm (fderiv ℝ g z) Complex.I
  have hC : ‖fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I‖ ≤ 2 * ‖fderiv ℝ g z‖ := by
    calc ‖fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I‖
        ≤ ‖fderiv ℝ g z 1‖ + ‖Complex.I * fderiv ℝ g z Complex.I‖ := norm_add_le _ _
      _ = ‖fderiv ℝ g z 1‖ + ‖fderiv ℝ g z Complex.I‖ := by rw [norm_mul, Complex.norm_I, one_mul]
      _ ≤ 2 * ‖fderiv ℝ g z‖ := by linarith
  rw [dzbar, div_eq_mul_inv, norm_mul, norm_inv, show ‖(2 : ℂ)‖ = 2 by norm_num, inv_eq_one_div]
  linarith

theorem continuous_dz_of_contDiff' {f : ℂ → ℂ} {n : WithTop ℕ∞} (hf : ContDiff ℝ n f) (hn : n ≠ 0) :
    Continuous (dz f) := by
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv hn
  have h : Continuous fun z => ((fderiv ℝ f z) 1 - Complex.I * (fderiv ℝ f z) Complex.I) / 2 :=
    ((hfd.clm_apply continuous_const).sub
      (continuous_const.mul (hfd.clm_apply continuous_const))).div_const 2
  change Continuous fun z => ((fderiv ℝ f z) 1 - Complex.I * (fderiv ℝ f z) Complex.I) / 2
  exact h

theorem continuous_dzbar_of_contDiff' {f : ℂ → ℂ} {n : WithTop ℕ∞} (hf : ContDiff ℝ n f)
    (hn : n ≠ 0) : Continuous (dzbar f) := by
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv hn
  have h : Continuous fun z => ((fderiv ℝ f z) 1 + Complex.I * (fderiv ℝ f z) Complex.I) / 2 :=
    ((hfd.clm_apply continuous_const).add
      (continuous_const.mul (hfd.clm_apply continuous_const))).div_const 2
  change Continuous fun z => ((fderiv ℝ f z) 1 + Complex.I * (fderiv ℝ f z) Complex.I) / 2
  exact h

theorem support_mul_test_subset {f₁ f₂ : ℂ → ℂ} {K : Set ℂ} (h : Function.support f₂ ⊆ K) :
    Function.support (fun z => f₁ z * f₂ z) ⊆ K := by
  rw [Function.support_mul]
  exact Set.inter_subset_right.trans h

theorem support_dz_subset (f : ℂ → ℂ) : Function.support (dz f) ⊆ tsupport f := by
  intro z hz
  by_contra h
  apply hz
  have h0 : fderiv ℝ f z = 0 := by
    rw [Filter.EventuallyEq.fderiv_eq (notMem_tsupport_iff_eventuallyEq.mp h)]
    simp
  rw [dz, h0]
  simp

theorem support_dzbar_subset (f : ℂ → ℂ) : Function.support (dzbar f) ⊆ tsupport f := by
  intro z hz
  by_contra h
  apply hz
  have h0 : fderiv ℝ f z = 0 := by
    rw [Filter.EventuallyEq.fderiv_eq (notMem_tsupport_iff_eventuallyEq.mp h)]
    simp
  rw [dzbar, h0]
  simp

/-- `(∂_v g) * ψ` is integrable. -/
theorem integrable_fderiv_mul_test {g : ℂ → ℂ} {U : Set ℂ} {K : NNReal} (hU : IsOpen U)
    (hg : LipschitzOnWith K g U) (ψ : 𝓓(⊤, ℂ)) (hψ : tsupport (ψ : ℂ → ℂ) ⊆ U) (v : ℂ) :
    Integrable (fun z => fderiv ℝ g z v * ψ z) := by
  have hK : IsCompact (tsupport (ψ : ℂ → ℂ)) := ψ.hasCompactSupport
  obtain ⟨Cψ₀, hCψ₀⟩ := hK.exists_bound_of_continuousOn ψ.continuous.continuousOn
  obtain ⟨Cψ, hCψ, hCψnn⟩ : ∃ C : ℝ, (∀ z ∈ tsupport (ψ : ℂ → ℂ), ‖ψ z‖ ≤ C) ∧ 0 ≤ C :=
    ⟨max Cψ₀ 0, fun z hz => (hCψ₀ z hz).trans (le_max_left _ _), le_max_right _ _⟩
  refine integrable_of_isCompact_of_bound hK ?_ ?_ ((K : ℝ) * ‖v‖ * Cψ) ?_
  · exact support_mul_test_subset (subset_tsupport _)
  · exact ((measurable_fderiv_apply_const ℝ g v).aestronglyMeasurable.restrict).mul
      ((ψ.continuous.aestronglyMeasurable).restrict)
  · filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    have h1 : ‖fderiv ℝ g z‖ ≤ (K : ℝ) :=
      norm_fderiv_le_of_lipschitzOn ℝ (hU.mem_nhds (hψ hz)) hg
    have hv : ‖(fderiv ℝ g z) v‖ ≤ ‖fderiv ℝ g z‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    have hψz : ‖ψ z‖ ≤ Cψ := hCψ z hz
    rw [norm_mul]
    calc ‖(fderiv ℝ g z) v‖ * ‖ψ z‖ ≤ (‖fderiv ℝ g z‖ * ‖v‖) * Cψ :=
          mul_le_mul hv hψz (norm_nonneg _) (by positivity)
      _ ≤ ((K : ℝ) * ‖v‖) * Cψ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (norm_nonneg v)) hCψnn

/-- `(dz g) * ψ` and `(dzbar g) * ψ` are integrable. -/
theorem integrable_dz_mul_test {g : ℂ → ℂ} {U : Set ℂ} {K : NNReal} (hU : IsOpen U)
    (hg : LipschitzOnWith K g U) (ψ : 𝓓(⊤, ℂ)) (hψ : tsupport (ψ : ℂ → ℂ) ⊆ U) :
    Integrable (fun z => dz g z * ψ z) ∧ Integrable (fun z => dzbar g z * ψ z) := by
  have hK : IsCompact (tsupport (ψ : ℂ → ℂ)) := ψ.hasCompactSupport
  obtain ⟨Cψ₀, hCψ₀⟩ := hK.exists_bound_of_continuousOn ψ.continuous.continuousOn
  obtain ⟨Cψ, hCψ, hCψnn⟩ : ∃ C : ℝ, (∀ z ∈ tsupport (ψ : ℂ → ℂ), ‖ψ z‖ ≤ C) ∧ 0 ≤ C :=
    ⟨max Cψ₀ 0, fun z hz => (hCψ₀ z hz).trans (le_max_left _ _), le_max_right _ _⟩
  have hmeas : Measurable (fun z => dz g z) := by
    have h1 : Measurable fun z => fderiv ℝ g z 1 := measurable_fderiv_apply_const ℝ g 1
    have h2 : Measurable fun z => fderiv ℝ g z Complex.I := measurable_fderiv_apply_const ℝ g Complex.I
    have heq : (fun z => dz g z)
        = fun z => ((fderiv ℝ g z) 1 - Complex.I * (fderiv ℝ g z) Complex.I) * (2 : ℂ)⁻¹ := by
      funext z; rw [dz, div_eq_mul_inv]
    rw [heq]
    exact (h1.sub (measurable_const.mul h2)).mul_const ((2 : ℂ)⁻¹)
  have hmeas' : Measurable (fun z => dzbar g z) := by
    have h1 : Measurable fun z => fderiv ℝ g z 1 := measurable_fderiv_apply_const ℝ g 1
    have h2 : Measurable fun z => fderiv ℝ g z Complex.I := measurable_fderiv_apply_const ℝ g Complex.I
    have heq : (fun z => dzbar g z)
        = fun z => ((fderiv ℝ g z) 1 + Complex.I * (fderiv ℝ g z) Complex.I) * (2 : ℂ)⁻¹ := by
      funext z; rw [dzbar, div_eq_mul_inv]
    rw [heq]
    exact (h1.add (measurable_const.mul h2)).mul_const ((2 : ℂ)⁻¹)
  constructor
  · refine integrable_of_isCompact_of_bound hK ?_ ?_ ((K : ℝ) * Cψ) ?_
    · exact support_mul_test_subset (subset_tsupport _)
    · exact (hmeas.aestronglyMeasurable.restrict).mul (ψ.continuous.aestronglyMeasurable.restrict)
    · filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
      have h1 : ‖fderiv ℝ g z‖ ≤ (K : ℝ) :=
        norm_fderiv_le_of_lipschitzOn ℝ (hU.mem_nhds (hψ hz)) hg
      have h2 : ‖dz g z‖ ≤ (K : ℝ) := (norm_dz_le g z).trans h1
      rw [norm_mul]
      exact mul_le_mul h2 (hCψ z hz) (norm_nonneg _) (by positivity)
  · refine integrable_of_isCompact_of_bound hK ?_ ?_ ((K : ℝ) * Cψ) ?_
    · exact support_mul_test_subset (subset_tsupport _)
    · exact (hmeas'.aestronglyMeasurable.restrict).mul (ψ.continuous.aestronglyMeasurable.restrict)
    · filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
      have h1 : ‖fderiv ℝ g z‖ ≤ (K : ℝ) :=
        norm_fderiv_le_of_lipschitzOn ℝ (hU.mem_nhds (hψ hz)) hg
      have h2 : ‖dzbar g z‖ ≤ (K : ℝ) := (norm_dzbar_le g z).trans h1
      rw [norm_mul]
      exact mul_le_mul h2 (hCψ z hz) (norm_nonneg _) (by positivity)

/-- `g * (dz ψ)` and `g * (dzbar ψ)` are integrable. -/
theorem integrable_g_mul_dz_test {g : ℂ → ℂ} {U : Set ℂ} {K : NNReal} (hU : IsOpen U)
    (hg : LipschitzOnWith K g U) (hc : ContinuousOn g U) (ψ : 𝓓(⊤, ℂ))
    (hψ : tsupport (ψ : ℂ → ℂ) ⊆ U) :
    Integrable (fun z => g z * dz (ψ : ℂ → ℂ) z) ∧
      Integrable (fun z => g z * dzbar (ψ : ℂ → ℂ) z) := by
  have hK : IsCompact (tsupport (ψ : ℂ → ℂ)) := ψ.hasCompactSupport
  obtain ⟨Cg₀, hCg₀⟩ := hK.exists_bound_of_continuousOn (hc.mono hψ)
  obtain ⟨Cg, hCg, hCgnn⟩ : ∃ C : ℝ, (∀ z ∈ tsupport (ψ : ℂ → ℂ), ‖g z‖ ≤ C) ∧ 0 ≤ C :=
    ⟨max Cg₀ 0, fun z hz => (hCg₀ z hz).trans (le_max_left _ _), le_max_right _ _⟩
  obtain ⟨Cd, hCd⟩ := hK.exists_bound_of_continuousOn
    (continuous_dz_of_contDiff' ψ.contDiff (by simp)).continuousOn
  obtain ⟨Cdb, hCdb⟩ := hK.exists_bound_of_continuousOn
    (continuous_dzbar_of_contDiff' ψ.contDiff (by simp)).continuousOn
  have hmeasg : AEStronglyMeasurable g (volume.restrict (tsupport (ψ : ℂ → ℂ))) := by
    have h : AEStronglyMeasurable g ((volume.restrict U).restrict (tsupport (ψ : ℂ → ℂ))) :=
      (hc.aestronglyMeasurable (μ := volume) hU.measurableSet).restrict
        (s := tsupport (ψ : ℂ → ℂ))
    rwa [Measure.restrict_restrict_of_subset hψ] at h
  constructor
  · refine integrable_of_isCompact_of_bound hK ?_ ?_ (Cg * Cd) ?_
    · exact support_mul_test_subset (f₂ := dz (ψ : ℂ → ℂ)) (support_dz_subset _)
    · exact hmeasg.mul ((continuous_dz_of_contDiff' ψ.contDiff (by simp)).aestronglyMeasurable.restrict)
    · filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
      rw [norm_mul]
      exact mul_le_mul (hCg z hz) (hCd z hz) (norm_nonneg _) hCgnn
  · refine integrable_of_isCompact_of_bound hK ?_ ?_ (Cg * Cdb) ?_
    · exact support_mul_test_subset (f₂ := dzbar (ψ : ℂ → ℂ)) (support_dzbar_subset _)
    · exact hmeasg.mul ((continuous_dzbar_of_contDiff' ψ.contDiff (by simp)).aestronglyMeasurable.restrict)
    · filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
      rw [norm_mul]
      exact mul_le_mul (hCg z hz) (hCdb z hz) (norm_nonneg _) hCgnn



/-- A globally Lipschitz extension of a function Lipschitz on a set. -/
theorem exists_lipschitzWith_eqOn_of_lipschitzOnWith {g : ℂ → ℂ} {U : Set ℂ} {K : NNReal}
    (hg : LipschitzOnWith K g U) :
    ∃ C : NNReal, ∃ G : ℂ → ℂ, LipschitzWith C G ∧ Set.EqOn g G U := by
  obtain ⟨G, hG, hEq⟩ := hg.extend_finite_dimension
  exact ⟨_, G, hG, hEq⟩

/-- Integration by parts for a globally Lipschitz `G` against a test function, in the form
`∫ (∂_v G) ψ = - ∫ (∂_v ψ) G`. -/
theorem integral_fderiv_mul_eq_neg_of_lipschitzWith {G : ℂ → ℂ} {C : NNReal}
    (hG : LipschitzWith C G) (ψ : 𝓓(⊤, ℂ)) (v : ℂ) :
    ∫ z, fderiv ℝ G z v * ψ z = - ∫ z, fderiv ℝ (ψ : ℂ → ℂ) z v * G z := by
  obtain ⟨D, hD⟩ : ∃ D : NNReal, LipschitzWith D (ψ : ℂ → ℂ) :=
    ContDiff.lipschitzWith_of_hasCompactSupport ψ.hasCompactSupport ψ.contDiff (by simp)
  have hψd : Differentiable ℝ (ψ : ℂ → ℂ) := ψ.contDiff.differentiable (by simp)
  have hmain := integral_lineDeriv_mul_eq_complex (μ := (volume : Measure ℂ)) hG hD ψ.hasCompactSupport v
  have h1 : ∫ z, lineDeriv ℝ G z v * ψ z = ∫ z, fderiv ℝ G z v * ψ z := by
    apply integral_congr_ae
    filter_upwards [hG.ae_differentiableAt] with z hz
    rw [hz.lineDeriv_eq_fderiv]
  have h2 : ∫ z, lineDeriv ℝ (ψ : ℂ → ℂ) z (-v) * G z
      = - ∫ z, fderiv ℝ (ψ : ℂ → ℂ) z v * G z := by
    have hpt : (fun z => lineDeriv ℝ (ψ : ℂ → ℂ) z (-v) * G z)
        = fun z => - (fderiv ℝ (ψ : ℂ → ℂ) z v * G z) := by
      funext z
      rw [(hψd z).lineDeriv_eq_fderiv, map_neg, neg_mul]
    rw [hpt, integral_neg]
  rw [h1, h2] at hmain
  exact hmain

/-- Transfer of the integration-by-parts integrands from `G` to `g`, which agrees with `G`
on the (open) set `U` containing the support of the test function. -/
theorem integral_fderiv_mul_eq_of_eqOn {g G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hEq : Set.EqOn g G U) (ψ : 𝓓(⊤, ℂ)) (hψ : tsupport (ψ : ℂ → ℂ) ⊆ U) (v : ℂ) :
    (∫ z, fderiv ℝ g z v * ψ z = ∫ z, fderiv ℝ G z v * ψ z) ∧
      (∫ z, fderiv ℝ (ψ : ℂ → ℂ) z v * g z = ∫ z, fderiv ℝ (ψ : ℂ → ℂ) z v * G z) := by
  constructor
  · apply integral_congr_ae
    filter_upwards with z
    by_cases hz : z ∈ U
    · rw [(hEq.eventuallyEq_of_mem (hU.mem_nhds hz)).fderiv_eq]
    · have hz' : (ψ : ℂ → ℂ) z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hψ h)
      rw [hz', mul_zero, mul_zero]
  · apply integral_congr_ae
    filter_upwards with z
    by_cases hz : z ∈ U
    · rw [hEq hz]
    · have hz' : z ∉ tsupport (ψ : ℂ → ℂ) := fun h => hz (hψ h)
      have hf0 : fderiv ℝ (ψ : ℂ → ℂ) z = 0 := by
        rw [Filter.EventuallyEq.fderiv_eq (notMem_tsupport_iff_eventuallyEq.mp hz')]
        simp
      simp [hf0]



theorem support_fderiv_subset (f : ℂ → ℂ) (v : ℂ) :
    Function.support (fun z => fderiv ℝ f z v) ⊆ tsupport f := by
  intro z hz
  by_contra h
  apply hz
  have h0 : fderiv ℝ f z = 0 := by
    rw [Filter.EventuallyEq.fderiv_eq (notMem_tsupport_iff_eventuallyEq.mp h)]
    simp
  show (fderiv ℝ f z) v = 0
  rw [h0]
  simp

theorem support_mul_subset_left' {f₁ f₂ : ℂ → ℂ} {K : Set ℂ} (h : Function.support f₁ ⊆ K) :
    Function.support (fun z => f₁ z * f₂ z) ⊆ K :=
  (support_mul_subset_left f₁ f₂).trans h

/-- `(∂_v ψ) * g` is integrable, for `ψ` a test function and `g` Lipschitz and continuous on `U`. -/
theorem integrable_fderiv_test_mul {g : ℂ → ℂ} {U : Set ℂ} {K : NNReal} (hU : IsOpen U)
    (hg : LipschitzOnWith K g U) (hc : ContinuousOn g U) (ψ : 𝓓(⊤, ℂ))
    (hψ : tsupport (ψ : ℂ → ℂ) ⊆ U) (v : ℂ) :
    Integrable (fun z => fderiv ℝ (ψ : ℂ → ℂ) z v * g z) := by
  have hK : IsCompact (tsupport (ψ : ℂ → ℂ)) := ψ.hasCompactSupport
  obtain ⟨Cg₀, hCg₀⟩ := hK.exists_bound_of_continuousOn (hc.mono hψ)
  obtain ⟨Cg, hCg, _⟩ : ∃ C : ℝ, (∀ z ∈ tsupport (ψ : ℂ → ℂ), ‖g z‖ ≤ C) ∧ 0 ≤ C :=
    ⟨max Cg₀ 0, fun z hz => (hCg₀ z hz).trans (le_max_left _ _), le_max_right _ _⟩
  obtain ⟨Cd, hCd⟩ := hK.exists_bound_of_continuousOn
    ((ψ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn
  have hmeasg : AEStronglyMeasurable g (volume.restrict (tsupport (ψ : ℂ → ℂ))) := by
    have h : AEStronglyMeasurable g ((volume.restrict U).restrict (tsupport (ψ : ℂ → ℂ))) :=
      (hc.aestronglyMeasurable (μ := volume) hU.measurableSet).restrict
        (s := tsupport (ψ : ℂ → ℂ))
    rwa [Measure.restrict_restrict_of_subset hψ] at h
  refine integrable_of_isCompact_of_bound hK ?_ ?_ (Cd * Cg) ?_
  · exact support_mul_subset_left' (f₁ := fun z => fderiv ℝ (ψ : ℂ → ℂ) z v)
      (f₂ := g) (support_fderiv_subset _ v)
  · exact (((measurable_fderiv_apply_const ℝ (ψ : ℂ → ℂ) v).aestronglyMeasurable).restrict).mul hmeasg
  · filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    rw [norm_mul]
    exact mul_le_mul (hCd z hz) (hCg z hz) (norm_nonneg _)
      (le_trans (norm_nonneg _) (hCd z hz))

/-- The Wirtinger `∂`-integration-by-parts identity on `U`. -/
theorem integral_dz_eq_neg {g : ℂ → ℂ} {U : Set ℂ} {K : NNReal} {G : ℂ → ℂ} {C : NNReal}
    (hU : IsOpen U) (hg : LipschitzOnWith K g U) (hc : ContinuousOn g U)
    (hG : LipschitzWith C G) (hEq : Set.EqOn g G U)
    (ψ : 𝓓(⊤, ℂ)) (hψ : tsupport (ψ : ℂ → ℂ) ⊆ U) :
    ∫ z, g z * dz (ψ : ℂ → ℂ) z = - ∫ z, dz g z * ψ z := by
  have hdir : ∀ v : ℂ, ∫ z, fderiv ℝ g z v * ψ z = - ∫ z, fderiv ℝ (ψ : ℂ → ℂ) z v * g z := by
    intro v
    have hcore := integral_fderiv_mul_eq_neg_of_lipschitzWith hG ψ v
    have htr := integral_fderiv_mul_eq_of_eqOn hU hEq ψ hψ v
    rw [htr.1, hcore, htr.2]
  have h1 := hdir 1
  have hI := hdir Complex.I
  have hi1 : Integrable (fun z => fderiv ℝ g z 1 * ψ z) := integrable_fderiv_mul_test hU hg ψ hψ 1
  have hiI : Integrable (fun z => fderiv ℝ g z Complex.I * ψ z) :=
    integrable_fderiv_mul_test hU hg ψ hψ Complex.I
  have hj1 : Integrable (fun z => fderiv ℝ (ψ : ℂ → ℂ) z 1 * g z) :=
    integrable_fderiv_test_mul hU hg hc ψ hψ 1
  have hjI : Integrable (fun z => fderiv ℝ (ψ : ℂ → ℂ) z Complex.I * g z) :=
    integrable_fderiv_test_mul hU hg hc ψ hψ Complex.I
  have key : ∫ z, dz g z * ψ z = - ∫ z, dz (ψ : ℂ → ℂ) z * g z := by
    have hL : ∫ z, dz g z * ψ z
        = ((∫ z, fderiv ℝ g z 1 * ψ z) - Complex.I * (∫ z, fderiv ℝ g z Complex.I * ψ z))
            / 2 := by
      have hpt : (fun z => dz g z * ψ z)
          = fun z => ((fderiv ℝ g z 1 * ψ z - Complex.I * (fderiv ℝ g z Complex.I * ψ z))
              * (2 : ℂ)⁻¹) := by
        funext z
        rw [dz, div_eq_mul_inv]
        ring
      rw [hpt, integral_mul_const, integral_sub hi1 (hiI.const_mul Complex.I), integral_const_mul,
        div_eq_mul_inv]
    have hL' : ∫ z, dz (ψ : ℂ → ℂ) z * g z
        = ((∫ z, fderiv ℝ (ψ : ℂ → ℂ) z 1 * g z)
            - Complex.I * (∫ z, fderiv ℝ (ψ : ℂ → ℂ) z Complex.I * g z)) / 2 := by
      have hpt : (fun z => dz (ψ : ℂ → ℂ) z * g z)
          = fun z => ((fderiv ℝ (ψ : ℂ → ℂ) z 1 * g z
              - Complex.I * (fderiv ℝ (ψ : ℂ → ℂ) z Complex.I * g z)) * (2 : ℂ)⁻¹) := by
        funext z
        rw [dz, div_eq_mul_inv]
        ring
      rw [hpt, integral_mul_const, integral_sub hj1 (hjI.const_mul Complex.I), integral_const_mul,
        div_eq_mul_inv]
    rw [hL, hL', h1, hI]
    ring
  have hcomm : (fun z => g z * dz (ψ : ℂ → ℂ) z) = fun z => dz (ψ : ℂ → ℂ) z * g z :=
    funext fun z => mul_comm _ _
  rw [hcomm, key, neg_neg]

/-- The Wirtinger `∂̄`-integration-by-parts identity on `U`. -/
theorem integral_dzbar_eq_neg {g : ℂ → ℂ} {U : Set ℂ} {K : NNReal} {G : ℂ → ℂ} {C : NNReal}
    (hU : IsOpen U) (hg : LipschitzOnWith K g U) (hc : ContinuousOn g U)
    (hG : LipschitzWith C G) (hEq : Set.EqOn g G U)
    (ψ : 𝓓(⊤, ℂ)) (hψ : tsupport (ψ : ℂ → ℂ) ⊆ U) :
    ∫ z, g z * dzbar (ψ : ℂ → ℂ) z = - ∫ z, dzbar g z * ψ z := by
  have hdir : ∀ v : ℂ, ∫ z, fderiv ℝ g z v * ψ z = - ∫ z, fderiv ℝ (ψ : ℂ → ℂ) z v * g z := by
    intro v
    have hcore := integral_fderiv_mul_eq_neg_of_lipschitzWith hG ψ v
    have htr := integral_fderiv_mul_eq_of_eqOn hU hEq ψ hψ v
    rw [htr.1, hcore, htr.2]
  have h1 := hdir 1
  have hI := hdir Complex.I
  have hi1 : Integrable (fun z => fderiv ℝ g z 1 * ψ z) := integrable_fderiv_mul_test hU hg ψ hψ 1
  have hiI : Integrable (fun z => fderiv ℝ g z Complex.I * ψ z) :=
    integrable_fderiv_mul_test hU hg ψ hψ Complex.I
  have hj1 : Integrable (fun z => fderiv ℝ (ψ : ℂ → ℂ) z 1 * g z) :=
    integrable_fderiv_test_mul hU hg hc ψ hψ 1
  have hjI : Integrable (fun z => fderiv ℝ (ψ : ℂ → ℂ) z Complex.I * g z) :=
    integrable_fderiv_test_mul hU hg hc ψ hψ Complex.I
  have key : ∫ z, dzbar g z * ψ z = - ∫ z, dzbar (ψ : ℂ → ℂ) z * g z := by
    have hL : ∫ z, dzbar g z * ψ z
        = ((∫ z, fderiv ℝ g z 1 * ψ z) + Complex.I * (∫ z, fderiv ℝ g z Complex.I * ψ z))
            / 2 := by
      have hpt : (fun z => dzbar g z * ψ z)
          = fun z => ((fderiv ℝ g z 1 * ψ z + Complex.I * (fderiv ℝ g z Complex.I * ψ z))
              * (2 : ℂ)⁻¹) := by
        funext z
        rw [dzbar, div_eq_mul_inv]
        ring
      rw [hpt, integral_mul_const, integral_add hi1 (hiI.const_mul Complex.I), integral_const_mul,
        div_eq_mul_inv]
    have hL' : ∫ z, dzbar (ψ : ℂ → ℂ) z * g z
        = ((∫ z, fderiv ℝ (ψ : ℂ → ℂ) z 1 * g z)
            + Complex.I * (∫ z, fderiv ℝ (ψ : ℂ → ℂ) z Complex.I * g z)) / 2 := by
      have hpt : (fun z => dzbar (ψ : ℂ → ℂ) z * g z)
          = fun z => ((fderiv ℝ (ψ : ℂ → ℂ) z 1 * g z
              + Complex.I * (fderiv ℝ (ψ : ℂ → ℂ) z Complex.I * g z)) * (2 : ℂ)⁻¹) := by
        funext z
        rw [dzbar, div_eq_mul_inv]
        ring
      rw [hpt, integral_mul_const, integral_add hj1 (hjI.const_mul Complex.I), integral_const_mul,
        div_eq_mul_inv]
    rw [hL, hL', h1, hI]
    ring
  have hcomm : (fun z => g z * dzbar (ψ : ℂ → ℂ) z) = fun z => dzbar (ψ : ℂ → ℂ) z * g z :=
    funext fun z => mul_comm _ _
  rw [hcomm, key, neg_neg]


/-- A map which is Lipschitz on an open set is locally square integrable there, and locally
integrable there.  (Only the values of `g` on `U` are used; no measurability of `g` outside `U`
is needed or implied.) -/
theorem memL2LocOn_of_lipschitzOnWith_of_isOpen {g : ℂ → ℂ} {U : Set ℂ} {K : NNReal}
    (hU : IsOpen U) (hg : LipschitzOnWith K g U) :
    MemL2LocOn g U ∧ LocallyIntegrableOn g U volume := by
  have hc : ContinuousOn g U := hg.continuousOn
  constructor
  · intro Kc hKc
    have hfin : volume (Kc ∩ U) < ⊤ :=
      lt_of_le_of_lt (measure_mono Set.inter_subset_left) hKc.measure_lt_top
    have hmeas : AEStronglyMeasurable (fun z => ‖g z‖ ^ 2) (volume.restrict (Kc ∩ U)) := by
      have h1 : AEStronglyMeasurable g ((volume.restrict U).restrict Kc) :=
        (hc.aestronglyMeasurable (μ := volume) hU.measurableSet).restrict (s := Kc)
      rw [Measure.restrict_restrict hKc.measurableSet] at h1
      exact h1.norm.pow 2
    by_cases hne : (Kc ∩ U).Nonempty
    · obtain ⟨z₀, hz₀⟩ := hne
      obtain ⟨C₀, hC₀⟩ := Metric.isBounded_iff.mp hKc.isBounded
      refine IntegrableOn.of_bound hfin hmeas ((‖g z₀‖ + (K : ℝ) * max C₀ 0) ^ 2) ?_
      filter_upwards [ae_restrict_mem (hKc.measurableSet.inter hU.measurableSet)] with z hz
      have hzK : z ∈ Kc := hz.1
      have hzU : z ∈ U := hz.2
      have hd : dist (g z) (g z₀) ≤ (K : ℝ) * max C₀ 0 := by
        refine (hg.dist_le_mul z hzU z₀ hz₀.2).trans ?_
        exact mul_le_mul_of_nonneg_left ((hC₀ hzK hz₀.1).trans (le_max_left _ _)) (by positivity)
      have h1 : ‖g z‖ ≤ ‖g z₀‖ + (K : ℝ) * max C₀ 0 := by
        rw [dist_eq_norm] at hd
        calc ‖g z‖ = ‖(g z - g z₀) + g z₀‖ := by rw [show (g z - g z₀) + g z₀ = g z by abel]
          _ ≤ ‖g z - g z₀‖ + ‖g z₀‖ := norm_add_le _ _
          _ ≤ ‖g z₀‖ + (K : ℝ) * max C₀ 0 := by linarith
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      refine IntegrableOn.of_bound (by rw [hne]; simp) (by rw [hne]; simp) 0 ?_
      rw [hne]
      simp
  · intro x hx
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
    have hε2 : (0 : ℝ) < ε / 2 := by linarith
    refine ⟨Metric.ball x (ε / 2) ∩ U, ?_, ?_⟩
    · rw [Metric.mem_nhdsWithin_iff]
      exact ⟨ε / 2, hε2, fun y hy => hy⟩
    · have hfin : volume (Metric.ball x (ε / 2) ∩ U) < ⊤ :=
        lt_of_le_of_lt
          (measure_mono (Set.inter_subset_left.trans Metric.ball_subset_closedBall))
          (measure_closedBall_lt_top (μ := volume) (x := x) (r := ε / 2))
      have hmeas : AEStronglyMeasurable g (volume.restrict (Metric.ball x (ε / 2) ∩ U)) := by
        have h1 : AEStronglyMeasurable g
            ((volume.restrict U).restrict (Metric.ball x (ε / 2) ∩ U)) :=
          (hc.aestronglyMeasurable (μ := volume) hU.measurableSet).restrict
            (s := Metric.ball x (ε / 2) ∩ U)
        rwa [Measure.restrict_restrict_of_subset Set.inter_subset_right] at h1
      refine IntegrableOn.of_bound hfin hmeas (‖g x‖ + (K : ℝ) * (ε / 2)) ?_
      filter_upwards [ae_restrict_mem
        ((Metric.isOpen_ball.measurableSet).inter hU.measurableSet)] with z hz
      have hzU : z ∈ U := hz.2
      have hd : ‖g z - g x‖ ≤ (K : ℝ) * (ε / 2) := by
        rw [← dist_eq_norm]
        exact (hg.dist_le_mul z hzU x hx).trans
          (mul_le_mul_of_nonneg_left (le_of_lt (Metric.mem_ball.mp hz.1)) (by positivity))
      calc ‖g z‖ = ‖(g z - g x) + g x‖ := by rw [show (g z - g x) + g x = g z by abel]
        _ ≤ ‖g z - g x‖ + ‖g x‖ := norm_add_le _ _
        _ ≤ ‖g x‖ + (K : ℝ) * (ε / 2) := by linarith

/-- **M5**: a locally Lipschitz homeomorphism whose dilatation is a.e. bounded by `k < 1`
is quasiconformal. -/
theorem isQCOn_of_lipschitz {g : ℂ → ℂ} {U : Set ℂ} {k K : ℝ}
    (hU : IsOpen U) (hhomeo : IsHomeomorphOn g U) (hlip : LipschitzOnWith (Real.toNNReal K) g U)
    (hk : 0 ≤ k) (hk1 : k < 1)
    (hdil : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      z ∈ U → ‖dzbar g z‖ ≤ k * ‖dz g z‖) :
    IsQCOn g U (beltramiOf g) := by
  obtain ⟨C, G, hG, hEq⟩ := exists_lipschitzWith_eqOn_of_lipschitzOnWith hlip
  have hc : ContinuousOn g U := hhomeo.1
  obtain ⟨hgL2, hgli⟩ := memL2LocOn_of_lipschitzOnWith_of_isOpen hU hlip
  obtain ⟨⟨hdzli, hdzL2⟩, ⟨hdzbli, hdzbL2⟩⟩ := locallyIntegrableOn_dz_of_lipschitzOnWith hU hlip
  obtain ⟨hbnd, hdilat⟩ := beltramiOf_ae_bound_and_dilatation hk hk1 hdil
  refine ⟨hU, hhomeo, ?_, hbnd, hdilat⟩
  refine ⟨hgL2, dz g, dzbar g, ?_, ?_, hdzL2, hdzbL2, Filter.EventuallyEq.rfl,
    Filter.EventuallyEq.rfl⟩
  · refine ⟨hgli, hdzli, fun φ hφ => ⟨?_, ?_, ?_⟩⟩
    · exact (integrable_g_mul_dz_test hU hlip hc φ hφ).1
    · exact (integrable_dz_mul_test hU hlip φ hφ).1
    · exact integral_dz_eq_neg hU hlip hc hG hEq φ hφ
  · refine ⟨hgli, hdzbli, fun φ hφ => ⟨?_, ?_, ?_⟩⟩
    · exact (integrable_g_mul_dz_test hU hlip hc φ hφ).2
    · exact (integrable_dz_mul_test hU hlip φ hφ).2
    · exact integral_dzbar_eq_neg hU hlip hc hG hEq φ hφ


end Work.MRMT.QC
