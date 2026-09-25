import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusSqfunDefs
import Submission.Work.BourgainPlan.Maximal.annulusKernel_size

/-!
# `annulusK b m ∈ L¹ ∩ L²` with `𝓕 (annulusK b m) = b m`

The annulus kernel `annulusK b m = 𝓕⁻ (b m)` of an annulus-symbol family is the inverse Fourier
transform of a smooth compactly supported symbol, hence is a Schwartz function; here we need only
the three facts recorded in the target statement: `annulusK b m ∈ L¹`, `annulusK b m ∈ L²`, and
Fourier inversion `𝓕 (annulusK b m) = b m`.

Everything is read off the kernel-size estimate `annulusKernel_size` (with `N = 2`):

  `‖𝓕⁻ (b m) z‖ ≤ C · 2^{-m} · (1 + 2^{-m}|z|)^{-2}`   for all `z`,

together with the elementary comparison `(1 + a|z|)^{-2} ≤ (min 1 a)^{-2} (1 + |z|)^{-2}` (`a > 0`),
which converts the frequency-scale weight `2^{-m}|z|` into the fixed weight `|z|`.  The resulting
majorant `K (1 + |z|)^{-2}` is in `L¹` and in `L²` by `integrable_one_add_norm`.

The `L¹` integrability of `𝓕 (b m)` needed for Fourier inversion comes from the elementary identity
`𝓕 f ξ = 𝓕⁻ f (-ξ)` applied to the same bound: `b m` being smooth with compact support, its Fourier
transform decays at infinity like every power.
-/

namespace Work.BourgainPlan.Maximal

open MeasureTheory Filter
open scoped ENNReal Topology FourierTransform

/-- The Fourier transform of an integrable function is continuous. -/
private lemma annulusK_continuous_fourier {f : ℝ → ℂ} (hf : Integrable f volume) :
    Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous (L := innerₗ ℝ) Real.continuous_fourierChar
    continuous_inner hf

/-- The inverse Fourier transform of an integrable function is continuous. -/
private lemma annulusK_continuous_fourierInv {f : ℝ → ℂ} (hf : Integrable f volume) :
    Continuous (𝓕⁻ f) := by
  rw [Real.fourierInv_eq_fourier_comp_neg]
  exact annulusK_continuous_fourier hf.comp_neg

/-- `z ↦ (1 + |z|)^{-r}` is integrable on `ℝ` for every `r > 1`. -/
private lemma annulusK_integrable_one_add_abs {r : ℝ} (hr : (1 : ℝ) < r) :
    Integrable (fun z : ℝ => (1 + |z|) ^ (-r)) volume := by
  have h : ((Module.finrank ℝ ℝ : ℕ) : ℝ) < r := by
    simp only [Module.finrank_self, Nat.cast_one]; exact hr
  simpa [Real.norm_eq_abs] using
    (integrable_one_add_norm (E := ℝ) (μ := (volume : Measure ℝ)) (r := r) h)

/-- The exponent-two negative power as an inverse square. -/
private lemma annulusK_rpow_inv_sq {x : ℝ} (hx : 0 ≤ x) : x ^ (-(2 : ℝ)) = x⁻¹ ^ 2 := by
  rw [Real.rpow_neg hx]; norm_num

/-- Comparison of the frequency-scale weight with the fixed weight: for `a > 0`,
`(1 + a|z|)^{-2} ≤ (min 1 a)^{-2} (1 + |z|)^{-2}`. -/
private lemma annulusK_rpow_compare {a z : ℝ} (ha : 0 < a) :
    (1 + a * |z|) ^ (-(2 : ℝ)) ≤ ((min 1 a)⁻¹ ^ 2) * (1 + |z|) ^ (-(2 : ℝ)) := by
  have hc : 0 < min 1 a := lt_min one_pos ha
  have h1 : min 1 a * (1 + |z|) ≤ 1 + a * |z| := by
    rcases lt_or_ge a 1 with h | h
    · rw [min_eq_right h.le]; nlinarith [abs_nonneg z]
    · rw [min_eq_left h]; nlinarith [abs_nonneg z]
  have hstep : (1 + a * |z|) ^ (-(2 : ℝ)) ≤ (min 1 a * (1 + |z|)) ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
  have hsplit : (min 1 a * (1 + |z|)) ^ (-(2 : ℝ))
      = (min 1 a)⁻¹ ^ 2 * (1 + |z|) ^ (-(2 : ℝ)) := by
    rw [Real.mul_rpow (le_of_lt hc) (by positivity), annulusK_rpow_inv_sq (le_of_lt hc)]
  exact le_trans hstep hsplit.le

theorem annulusK_memLp (b : ℤ → ℝ → ℂ)
    (hb : Work.BourgainPlan.Maximal.AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) (m : ℤ) :
    MeasureTheory.MemLp (Work.BourgainPlan.Maximal.annulusK b m) 1 MeasureTheory.volume ∧
      MeasureTheory.MemLp (Work.BourgainPlan.Maximal.annulusK b m) 2 MeasureTheory.volume ∧
      FourierTransform.fourier (Work.BourgainPlan.Maximal.annulusK b m) = b m := by
  obtain ⟨C, hCpos, hC⟩ := annulusKernel_size b hb hsmooth 2
  set a : ℝ := (2 : ℝ) ^ (-m) with ha
  have hapos : 0 < a := by rw [ha]; positivity
  set K : ℝ := C * a * ((min 1 a)⁻¹ ^ 2) with hK
  have hKnn : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg (mul_nonneg hCpos.le hapos.le) (sq_nonneg _)
  set G : ℝ → ℝ := fun z => K * (1 + |z|) ^ (-(2 : ℝ)) with hG
  have hGnn : ∀ z, 0 ≤ G z := fun z => by
    rw [hG]; exact mul_nonneg hKnn (Real.rpow_nonneg (by positivity) _)
  have hbint : Integrable (b m) volume :=
    (hsmooth m).continuous.integrable_of_hasCompactSupport (annulusK_hasCompactSupport b hb m)
  have hInvcont : Continuous (𝓕⁻ (b m)) := annulusK_continuous_fourierInv hbint
  -- the pointwise decay bound
  have hboundInv : ∀ z : ℝ, ‖𝓕⁻ (b m) z‖ ≤ G z := by
    intro z
    have h := hC m z
    rw [← ha] at h
    have hcmp := annulusK_rpow_compare (a := a) (z := z) hapos
    have hcmp' : C * a * (1 + a * |z|) ^ (-(2 : ℝ)) ≤ G z := by
      rw [hG, hK]
      calc C * a * (1 + a * |z|) ^ (-(2 : ℝ))
          ≤ C * a * (((min 1 a)⁻¹ ^ 2) * (1 + |z|) ^ (-(2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hcmp (mul_nonneg hCpos.le hapos.le)
        _ = C * a * (min 1 a)⁻¹ ^ 2 * (1 + |z|) ^ (-(2 : ℝ)) := by ring
    exact le_trans h hcmp'
  -- the majorant is in `L¹` and in `L²`
  have hGint : Integrable G volume := by
    rw [hG]
    exact (annulusK_integrable_one_add_abs (by norm_num : (1 : ℝ) < 2)).const_mul K
  have hGmem1 : MemLp G 1 volume := memLp_one_iff_integrable.mpr hGint
  have hGcont : Continuous G := by
    rw [hG]
    have heq : ∀ z : ℝ, (1 + |z|) ^ (-(2 : ℝ)) = ((1 + |z|) ^ 2)⁻¹ := fun z => by
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + |z|)]
      norm_num
    simp only [heq]
    refine continuous_const.mul (Continuous.inv₀ ?_ ?_)
    · exact (continuous_const.add continuous_abs).pow 2
    · intro z
      show ((1 : ℝ) + |z|) ^ 2 ≠ 0
      positivity
  have hGmem2 : MemLp G 2 volume := by
    rw [memLp_two_iff_integrable_sq hGcont.aestronglyMeasurable]
    have h4 : Integrable (fun z : ℝ => K ^ 2 * (1 + |z|) ^ (-(4 : ℝ))) volume :=
      (annulusK_integrable_one_add_abs (by norm_num : (1 : ℝ) < 4)).const_mul (K ^ 2)
    refine h4.congr (Eventually.of_forall fun z => ?_)
    rw [hG]
    simp only [mul_pow]
    congr 1
    rw [← Real.rpow_natCast ((1 + |z|) ^ (-(2 : ℝ))) 2, ← Real.rpow_mul (by positivity)]
    norm_num
  -- `annulusK b m ∈ L¹ ∩ L²`
  have hKmem1 : MemLp (annulusK b m) 1 volume :=
    MemLp.of_le hGmem1 hInvcont.aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_of_nonneg (hGnn z)]; exact hboundInv z)
  have hKmem2 : MemLp (annulusK b m) 2 volume :=
    MemLp.of_le hGmem2 hInvcont.aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_of_nonneg (hGnn z)]; exact hboundInv z)
  -- `𝓕 (b m)` is integrable (same decay, through `𝓕 b m ξ = 𝓕⁻ b m (-ξ)`)
  have hFcont : Continuous (𝓕 (b m)) := annulusK_continuous_fourier hbint
  have hFbound : ∀ ξ : ℝ, ‖𝓕 (b m) ξ‖ ≤ G ξ := by
    intro ξ
    have h := hboundInv (-ξ)
    rw [Real.fourierInv_eq_fourier_neg (b m) (-ξ)] at h
    have hGneg : G (-ξ) = G ξ := by rw [hG]; simp
    rw [hGneg] at h
    simpa using h
  have hFint : Integrable (𝓕 (b m)) volume :=
    hGint.mono' hFcont.aestronglyMeasurable (Eventually.of_forall hFbound)
  have hinv : 𝓕 (𝓕⁻ (b m)) = b m :=
    (hsmooth m).continuous.fourier_fourierInv_eq hbint hFint
  exact ⟨hKmem1, hKmem2, by simpa only [annulusK] using hinv⟩

end Work.BourgainPlan.Maximal
