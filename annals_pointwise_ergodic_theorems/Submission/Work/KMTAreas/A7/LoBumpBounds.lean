/-
# The `L¹` mass bounds for the bumps `φ_N`, `φ̃_N` (the `LoBumpBounds` interface)

For the §5/§6 model approximation one needs, uniformly in the continuous scales `k` and for
`m ≤ 2`, the `L¹` mass of the `m`-th derivative of the two bumps

`φ_N(ξ) = η(2^{Log N - k}ξ) - η(2^{Log N-k+1}ξ)`,   `φ̃_N(ξ) = η(2^{d(Log N-k)}ξ) - η(2^{d(Log N-k)+d}ξ)`

(`Work.KMTAreas.A7.varphiN`, `Work.KMTAreas.A7.varphitildeN`, with `η = Work.KMTContract.kmtEta`
the fixed `C²`-cutoff).  The paper's estimate is

`∫ ‖φ_N^{(m)}‖ ≲ (2^{Log N}/2^k)^{m-1}`,  `∫ ‖φ̃_N^{(m)}‖ ≲ (2^{d(Log N-k)})^{m-1}`,

with constants independent of `N`, `k` and (in the second case) of the degree `d ≥ 0`.

Both bumps are *differences of dilations* of `η`: `ξ ↦ η(cξ)` and `ξ ↦ η(2^d c ξ)`.  The proof
below is the elementary Jacobian computation for such a dilation.  For a measurable `f` and
`c > 0` the substitution `ξ ↦ cξ` gives

`∫⁻ ξ, ‖f(cξ)‖ = c⁻¹ ∫⁻ ξ, ‖f ξ‖`   (`lintegral_norm_comp_mul_left_lo`),

and for the `m`-th derivative, `(f(c·))^{(m)} = c^m (f^{(m)})(c·)` gives

`∫⁻ ξ, ‖(f(c·))^{(m)}(ξ)‖ = c^{m-1} ∫⁻ ξ, ‖f^{(m)}(ξ)‖`   (`lintegral_norm_deriv_rescale_lo`).

The base bound `∫⁻ ξ, ‖η^{(m)}(ξ)‖ ≤ Cη` (`m ≤ 2`) is obtained from the ordinary integral via
`ofReal_integral_eq_lintegral_ofReal` and the compact support of `η`.  All of this is
`∫⁻`-valued (ENNReal), matching the `ENNReal.ofReal` form in which the estimates are consumed.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.varphiN_mass_bounds

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## The elementary rescalings of the `∫⁻`-norm -/

/-- The norm of a real number seen as a complex number. -/
private lemma norm_ofReal_eq_abs_lo (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal]
  simpa [pow_two] using Real.sqrt_sq_eq_abs r

/-- **The substitution rule for the `∫⁻`-norm under a dilation.**  For `c > 0` and measurable `f`,
`∫⁻ ξ, ‖f (c ξ)‖ = c⁻¹ ∫⁻ ξ, ‖f ξ‖`. -/
private lemma lintegral_norm_comp_mul_left_lo (f : ℝ → ℂ) (hf : Measurable f) {c : ℝ}
    (hc : 0 < c) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal ‖f (c * ξ)‖)
      = ENNReal.ofReal c⁻¹ * ∫⁻ ξ : ℝ, ENNReal.ofReal ‖f ξ‖ := by
  have hmap : Measure.map (fun x : ℝ => c * x) volume = ENNReal.ofReal c⁻¹ • volume := by
    rw [Real.map_volume_mul_left (ne_of_gt hc), abs_of_pos (inv_pos.mpr hc)]
  have hmeas : Measurable (fun x : ℝ => c * x) := measurable_const_mul c
  have h1 : (∫⁻ ξ : ℝ, ENNReal.ofReal ‖f ξ‖
        ∂Measure.map (fun x : ℝ => c * x) volume)
      = ∫⁻ ξ : ℝ, ENNReal.ofReal ‖f (c * ξ)‖ := by
    rw [MeasureTheory.lintegral_map (hf.norm.ennreal_ofReal) hmeas]
  rw [← h1, hmap, MeasureTheory.lintegral_smul_measure, smul_eq_mul]

/-- **The chain rule for a dilation**, in the form needed below: the `m`-th derivative of
`ξ ↦ f (c ξ)` is `c^m` times the `m`-th derivative of `f` at `c ξ`. -/
private lemma iteratedDeriv_comp_mul_left_eq_lo (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (c : ℝ)
    (m : ℕ) (hm : m ≤ 2) :
    iteratedDeriv m (fun ξ : ℝ => f (c * ξ))
      = fun ξ : ℝ => (c : ℂ) ^ m * iteratedDeriv m f (c * ξ) := by
  rw [iteratedDeriv_comp_const_smul (𝕜 := ℝ) (F := ℂ) (hf.of_le (by exact_mod_cast hm)) c]
  funext x
  rw [Complex.real_smul, Complex.ofReal_pow]

/-- **The rescaling identity for the `∫⁻`-mass of the `m`-th derivative:**
`∫⁻ ξ, ‖(f(c·))^{(m)}(ξ)‖ = c^{m-1} ∫⁻ ξ, ‖f^{(m)}(ξ)‖` for `c > 0` and `m ≤ 2`. -/
private lemma lintegral_norm_deriv_rescale_lo (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) {c : ℝ}
    (hc : 0 < c) (m : ℕ) (hm : m ≤ 2) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m (fun ξ : ℝ => f (c * ξ)) ξ‖)
      = ENNReal.ofReal (c ^ ((m : ℝ) - 1))
          * (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m f ξ‖) := by
  rw [iteratedDeriv_comp_mul_left_eq_lo f hf c m hm]
  have hcont : Continuous (iteratedDeriv m f) :=
    hf.continuous_iteratedDeriv m (by exact_mod_cast hm)
  have hmeas : Measurable (fun ξ : ℝ => ENNReal.ofReal ‖iteratedDeriv m f ξ‖) :=
    hcont.norm.measurable.ennreal_ofReal
  have hmeas2 : Measurable (fun ξ : ℝ => ENNReal.ofReal ‖iteratedDeriv m f (c * ξ)‖) :=
    hmeas.comp (measurable_const_mul c)
  have hnorm : ∀ ξ : ℝ, ‖(c : ℂ) ^ m * iteratedDeriv m f (c * ξ)‖
      = c ^ m * ‖iteratedDeriv m f (c * ξ)‖ := by
    intro ξ
    rw [norm_mul, norm_pow, norm_ofReal_eq_abs_lo, abs_of_pos hc]
  rw [show (fun ξ : ℝ => ENNReal.ofReal ‖(c : ℂ) ^ m * iteratedDeriv m f (c * ξ)‖)
      = fun ξ : ℝ => ENNReal.ofReal (c ^ m) * ENNReal.ofReal ‖iteratedDeriv m f (c * ξ)‖ from by
    funext ξ
    rw [hnorm ξ, ENNReal.ofReal_mul (pow_nonneg hc.le m)]]
  rw [MeasureTheory.lintegral_const_mul'' _ hmeas2.aemeasurable,
    lintegral_norm_comp_mul_left_lo (iteratedDeriv m f) hcont.measurable hc]
  have hprod : ENNReal.ofReal (c ^ m) * ENNReal.ofReal c⁻¹
      = ENNReal.ofReal (c ^ ((m : ℝ) - 1)) := by
    rw [← ENNReal.ofReal_mul (pow_nonneg hc.le m)]
    congr 1
    rw [← Real.rpow_natCast c m, ← Real.rpow_neg_one c, ← Real.rpow_add hc]
    congr 1
  rw [← mul_assoc, hprod]

/-! ## The mass of the derivatives of the cutoff `η` -/

/-- **The base bound**: the `∫⁻`-mass of the `m`-th derivative of the cutoff `η` is bounded by a
constant, uniformly in `m ≤ 2`. -/
private theorem lintegral_kmtEta_deriv_le_lo :
    ∃ Cη : ℝ, 0 < Cη ∧ ∀ (m : ℕ), m ≤ 2 →
      (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m Work.KMTContract.kmtEta ξ‖)
        ≤ ENNReal.ofReal Cη := by
  have hInt : ∀ j : ℕ, j ≤ 2 →
      Integrable (fun ξ : ℝ => ‖iteratedDeriv j Work.KMTContract.kmtEta ξ‖) := by
    intro j hj
    interval_cases j
    · exact (integrable_kmtEta_varphiN).norm
    · have hcs : HasCompactSupport (fun ξ : ℝ => iteratedDeriv 1 Work.KMTContract.kmtEta ξ) := by
        rw [iteratedDeriv_one]
        exact (hasCompactSupport_kmtEta_varphiN).deriv
      have hcont : Continuous (fun ξ : ℝ => iteratedDeriv 1 Work.KMTContract.kmtEta ξ) := by
        rw [iteratedDeriv_one]
        exact (contDiff_kmtEta 2).continuous_deriv (by norm_num)
      exact (hcont.integrable_of_hasCompactSupport hcs).norm
    · exact integrable_iteratedDeriv_two_kmtEta_varphiN
  refine ⟨(∫ ξ : ℝ, ‖Work.KMTContract.kmtEta ξ‖)
      + (∫ ξ : ℝ, ‖iteratedDeriv 1 Work.KMTContract.kmtEta ξ‖)
      + (∫ ξ : ℝ, ‖iteratedDeriv 2 Work.KMTContract.kmtEta ξ‖) + 1, by positivity, ?_⟩
  intro m hm
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hInt m hm)
    (Filter.Eventually.of_forall (fun x => norm_nonneg _))]
  refine ENNReal.ofReal_le_ofReal ?_
  have h0 : (0:ℝ) ≤ ∫ ξ : ℝ, ‖Work.KMTContract.kmtEta ξ‖ :=
    integral_nonneg (fun x => norm_nonneg _)
  have h1 : (0:ℝ) ≤ ∫ ξ : ℝ, ‖iteratedDeriv 1 Work.KMTContract.kmtEta ξ‖ :=
    integral_nonneg (fun x => norm_nonneg _)
  have h2 : (0:ℝ) ≤ ∫ ξ : ℝ, ‖iteratedDeriv 2 Work.KMTContract.kmtEta ξ‖ :=
    integral_nonneg (fun x => norm_nonneg _)
  interval_cases m
  · rw [iteratedDeriv_zero]; linarith
  · linarith
  · linarith

/-! ## The bounds for a dilation and for a difference of two dilations -/

/-- A single dilation `ξ ↦ g (cξ)` gains the factor `c^{m-1}` in the `∫⁻`-mass of the `m`-th
derivative. -/
private lemma lintegral_deriv_dilation_le_lo (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) {c Cg : ℝ}
    (hc : 0 < c) (hCg : 0 < Cg)
    (hgmass : ∀ m : ℕ, m ≤ 2 →
      (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m g ξ‖) ≤ ENNReal.ofReal Cg) :
    ∀ m : ℕ, m ≤ 2 →
      (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m (fun ξ : ℝ => g (c * ξ)) ξ‖)
        ≤ ENNReal.ofReal (c ^ ((m : ℝ) - 1) * Cg) := by
  intro m hm
  rw [lintegral_norm_deriv_rescale_lo g hg hc m hm]
  calc ENNReal.ofReal (c ^ ((m : ℝ) - 1)) * (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m g ξ‖)
      ≤ ENNReal.ofReal (c ^ ((m : ℝ) - 1)) * ENNReal.ofReal Cg :=
        mul_le_mul_right (hgmass m hm) _
    _ = ENNReal.ofReal (c ^ ((m : ℝ) - 1) * Cg) := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _)]

/-- A difference of two dilations `ξ ↦ g(c₁ξ) - g(c₂ξ)` is bounded by the sum of the two
dilation constants. -/
private lemma lintegral_deriv_dilation_sub_le_lo (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g)
    {c₁ c₂ Cg : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hCg : 0 < Cg)
    (hgmass : ∀ m : ℕ, m ≤ 2 →
      (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m g ξ‖) ≤ ENNReal.ofReal Cg) :
    ∀ m : ℕ, m ≤ 2 →
      (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m (fun ξ : ℝ => g (c₁ * ξ) - g (c₂ * ξ)) ξ‖)
        ≤ ENNReal.ofReal ((c₁ ^ ((m : ℝ) - 1) + c₂ ^ ((m : ℝ) - 1)) * Cg) := by
  intro m hm
  have hm' : (m : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hm
  have h1 : ContDiff ℝ 2 (fun ξ : ℝ => g (c₁ * ξ)) := hg.comp (by fun_prop)
  have h2 : ContDiff ℝ 2 (fun ξ : ℝ => g (c₂ * ξ)) := hg.comp (by fun_prop)
  have hsub : ∀ ξ : ℝ, iteratedDeriv m (fun ξ : ℝ => g (c₁ * ξ) - g (c₂ * ξ)) ξ
      = iteratedDeriv m (fun ξ : ℝ => g (c₁ * ξ)) ξ
        - iteratedDeriv m (fun ξ : ℝ => g (c₂ * ξ)) ξ := by
    intro ξ
    rw [show (fun ξ : ℝ => g (c₁ * ξ) - g (c₂ * ξ))
        = (fun ξ : ℝ => g (c₁ * ξ)) - (fun ξ : ℝ => g (c₂ * ξ)) from rfl]
    exact iteratedDeriv_sub ((h1.of_le hm').contDiffAt) ((h2.of_le hm').contDiffAt)
  have hm1 : AEMeasurable
      (fun ξ : ℝ => ENNReal.ofReal ‖iteratedDeriv m (fun ξ : ℝ => g (c₁ * ξ)) ξ‖) volume :=
    (((h1.continuous_iteratedDeriv m (by exact_mod_cast hm)).norm).measurable.ennreal_ofReal).aemeasurable
  have hr1 : (0 : ℝ) ≤ c₁ ^ ((m : ℝ) - 1) := Real.rpow_nonneg (le_of_lt hc₁) _
  have hr2 : (0 : ℝ) ≤ c₂ ^ ((m : ℝ) - 1) := Real.rpow_nonneg (le_of_lt hc₂) _
  calc (∫⁻ ξ : ℝ, ENNReal.ofReal
          ‖iteratedDeriv m (fun ξ : ℝ => g (c₁ * ξ) - g (c₂ * ξ)) ξ‖)
      = ∫⁻ ξ : ℝ, ENNReal.ofReal
          ‖iteratedDeriv m (fun ξ : ℝ => g (c₁ * ξ)) ξ
            - iteratedDeriv m (fun ξ : ℝ => g (c₂ * ξ)) ξ‖ := by
        refine lintegral_congr (fun ξ => ?_)
        rw [hsub ξ]
    _ ≤ ∫⁻ ξ : ℝ, ENNReal.ofReal
          (‖iteratedDeriv m (fun ξ : ℝ => g (c₁ * ξ)) ξ‖
            + ‖iteratedDeriv m (fun ξ : ℝ => g (c₂ * ξ)) ξ‖) := by
        refine lintegral_mono (fun ξ => ?_)
        exact ENNReal.ofReal_le_ofReal (norm_sub_le _ _)
    _ = ∫⁻ ξ : ℝ, (ENNReal.ofReal ‖iteratedDeriv m (fun ξ : ℝ => g (c₁ * ξ)) ξ‖
            + ENNReal.ofReal ‖iteratedDeriv m (fun ξ : ℝ => g (c₂ * ξ)) ξ‖) := by
        refine lintegral_congr (fun ξ => ?_)
        rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    _ = (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m (fun ξ : ℝ => g (c₁ * ξ)) ξ‖)
          + (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m (fun ξ : ℝ => g (c₂ * ξ)) ξ‖) :=
        MeasureTheory.lintegral_add_left' hm1 _
    _ = ENNReal.ofReal (c₁ ^ ((m : ℝ) - 1)) * (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m g ξ‖)
          + ENNReal.ofReal (c₂ ^ ((m : ℝ) - 1))
            * (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m g ξ‖) := by
        rw [lintegral_norm_deriv_rescale_lo g hg hc₁ m hm,
          lintegral_norm_deriv_rescale_lo g hg hc₂ m hm]
    _ ≤ ENNReal.ofReal (c₁ ^ ((m : ℝ) - 1)) * ENNReal.ofReal Cg
          + ENNReal.ofReal (c₂ ^ ((m : ℝ) - 1)) * ENNReal.ofReal Cg := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_right (hgmass m hm) _
        · exact mul_le_mul_right (hgmass m hm) _
    _ = ENNReal.ofReal (c₁ ^ ((m : ℝ) - 1) * Cg)
          + ENNReal.ofReal (c₂ ^ ((m : ℝ) - 1) * Cg) := by
        rw [ENNReal.ofReal_mul hr1, ENNReal.ofReal_mul hr2]
    _ = ENNReal.ofReal (c₁ ^ ((m : ℝ) - 1) * Cg + c₂ ^ ((m : ℝ) - 1) * Cg) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    _ = ENNReal.ofReal ((c₁ ^ ((m : ℝ) - 1) + c₂ ^ ((m : ℝ) - 1)) * Cg) := by
        congr 1; ring

/-! ## Elementary `2`-power arithmetic -/

/-- `2^{m-1} ≤ 2` for `m ≤ 2`. -/
private lemma rpow_sub_one_le_two_lo {m : ℕ} (hm : m ≤ 2) :
    (2 : ℝ) ^ ((m : ℝ) - 1) ≤ 2 := by
  have h1 : ((m : ℝ) - 1) ≤ 1 := by
    have : (m : ℝ) ≤ 2 := by exact_mod_cast hm
    linarith
  calc (2 : ℝ) ^ ((m : ℝ) - 1) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    _ = 2 := Real.rpow_one 2

/-- `2^{Log N} / 2^k = 2^{Log N - k}`. -/
private lemma thN_div_eq_lo (N k : ℕ) :
    (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ) / (2 : ℝ) ^ k
      = (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) := by
  rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]

/-- `(2^d)^{Log N} / 2^{dk} = 2^{d(Log N - k)}`. -/
private lemma psN_eq_lo (d N k : ℕ) :
    ((2 : ℝ) ^ d) ^ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ) / (2 : ℝ) ^ (d * k)
      = (2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) := by
  have hnum : ((2 : ℝ) ^ d) ^ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)
      = (2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) := by
    rw [← Real.rpow_natCast (2 : ℝ) d, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hden : (2 : ℝ) ^ (d * k) = (2 : ℝ) ^ (((k : ℕ) : ℝ) * ((d : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast (2 : ℝ) (d * k)]
    congr 1
    push_cast
    ring
  rw [hnum, hden, ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-! ## The target -/

theorem LoBumpBounds (P : Polynomial ℤ) :
    ∃ Cφ Cψ : ℝ, 0 < Cφ ∧ 0 < Cψ ∧
      (∀ (N k m : ℕ), m ≤ 2 →
        (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m (Work.KMTAreas.A7.varphiN N k) ξ‖)
          ≤ ENNReal.ofReal (Cφ * (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ))
              / (2 : ℝ) ^ k) ^ ((m : ℝ) - 1))) ∧
      (∀ (N k m : ℕ), m ≤ 2 →
        (∫⁻ ξ : ℝ, ENNReal.ofReal
            ‖iteratedDeriv m (Work.KMTAreas.A7.varphitildeN P.natDegree N k) ξ‖)
          ≤ ENNReal.ofReal (Cψ * ((((2 : ℝ) ^ P.natDegree)
                ^ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) / (2 : ℝ) ^ (P.natDegree * k))
              ^ ((m : ℝ) - 1))) := by
  obtain ⟨Cη, hCη, hη⟩ := lintegral_kmtEta_deriv_le_lo
  refine ⟨3 * Cη, (1 + (2 : ℝ) ^ P.natDegree) * Cη, by positivity, by positivity, ?_, ?_⟩
  · intro N k m hm
    have hrpow : (2 : ℝ) ^ ((m : ℝ) - 1) ≤ 2 := rpow_sub_one_le_two_lo hm
    by_cases hk : k = 0
    · subst hk
      have hc : 0 < (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have hEq : varphiN N 0 = fun ξ : ℝ =>
          Work.KMTContract.kmtEta
            (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) * ξ) := by
        funext ξ
        unfold varphiN
        rw [if_pos rfl]
      rw [hEq]
      have hmain := lintegral_deriv_dilation_le_lo Work.KMTContract.kmtEta (contDiff_kmtEta 2)
        hc hCη hη m hm
      refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [pow_zero, div_one]
      have hA : (0 : ℝ)
          ≤ ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) ^ ((m : ℝ) - 1) :=
        Real.rpow_nonneg hc.le _
      nlinarith [hCη, hA]
    · have hc0 : 0 < (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have hca : 0 < (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have hEq : varphiN N k = fun ξ : ℝ =>
          Work.KMTContract.kmtEta
              (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * ξ)
            - Work.KMTContract.kmtEta
              (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * ξ) := by
        funext ξ
        unfold varphiN
        rw [if_neg hk]
      rw [hEq]
      have hmain := lintegral_deriv_dilation_sub_le_lo Work.KMTContract.kmtEta (contDiff_kmtEta 2)
        hc0 hca hCη hη m hm
      refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
      set X : ℝ := (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) with hX
      have hXpos : 0 < X := by rw [hX]; exact hc0
      have hca_eq : (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1) = 2 * X := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one, ← hX]
        ring
      have hbase : (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ) / (2 : ℝ) ^ k = X := by
        rw [thN_div_eq_lo N k, ← hX]
      rw [hca_eq, hbase, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hXpos.le]
      set A : ℝ := X ^ ((m : ℝ) - 1) with hA
      have hA0 : 0 ≤ A := by rw [hA]; exact Real.rpow_nonneg hXpos.le _
      have h2 : (2 : ℝ) ^ ((m : ℝ) - 1) * A ≤ 2 * A :=
        mul_le_mul_of_nonneg_right hrpow hA0
      nlinarith [hCη, hA0, h2]
  · intro N k m hm
    by_cases hk : k = 0
    · subst hk
      have hc : 0 < (2 : ℝ) ^ ((P.natDegree : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have hEq : varphitildeN P.natDegree N 0 = fun ξ : ℝ =>
          Work.KMTContract.kmtEta
            (((2 : ℝ) ^ ((P.natDegree : ℝ) * (Work.Analysis.EndVar.logN N : ℝ))) * ξ) := by
        funext ξ
        unfold varphitildeN
        rw [if_pos rfl]
      rw [hEq]
      have hmain := lintegral_deriv_dilation_le_lo Work.KMTContract.kmtEta (contDiff_kmtEta 2)
        hc hCη hη m hm
      refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
      have hbase0 : ((2 : ℝ) ^ P.natDegree) ^ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)
          = (2 : ℝ) ^ ((P.natDegree : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) := by
        rw [← Real.rpow_natCast (2 : ℝ) P.natDegree,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [Nat.mul_zero, pow_zero, div_one, hbase0]
      have hA : (0 : ℝ)
          ≤ ((2 : ℝ) ^ ((P.natDegree : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)))
              ^ ((m : ℝ) - 1) := Real.rpow_nonneg hc.le _
      have hp1 : (1 : ℝ) ≤ (2 : ℝ) ^ P.natDegree :=
        one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      have h2 : (0 : ℝ) ≤ ((2 : ℝ) ^ P.natDegree)
          * (((2 : ℝ) ^ ((P.natDegree : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)))
              ^ ((m : ℝ) - 1)) * Cη :=
        mul_nonneg (mul_nonneg (by linarith [hp1]) hA) hCη.le
      nlinarith [h2]
    · have hc0 : 0 < (2 : ℝ) ^ ((P.natDegree : ℝ)
          * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have hca : 0 < (2 : ℝ) ^ ((P.natDegree : ℝ)
          * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have hEq : varphitildeN P.natDegree N k = fun ξ : ℝ =>
          Work.KMTContract.kmtEta
              (((2 : ℝ) ^ ((P.natDegree : ℝ)
                * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)))) * ξ)
            - Work.KMTContract.kmtEta
              (((2 : ℝ) ^ ((P.natDegree : ℝ)
                * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1))) * ξ) := by
        funext ξ
        unfold varphitildeN
        rw [if_neg hk]
      rw [hEq]
      have hmain := lintegral_deriv_dilation_sub_le_lo Work.KMTContract.kmtEta (contDiff_kmtEta 2)
        hc0 hca hCη hη m hm
      refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
      set X : ℝ := (2 : ℝ) ^ ((P.natDegree : ℝ)
        * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) with hX
      have hXpos : 0 < X := by rw [hX]; exact hc0
      have hca_exp : (P.natDegree : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)
          = (P.natDegree : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))
            + (P.natDegree : ℝ) := by ring
      have hca_eq : (2 : ℝ) ^ ((P.natDegree : ℝ)
            * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1))
          = ((2 : ℝ) ^ P.natDegree) * X := by
        rw [hca_exp, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          Real.rpow_natCast (2 : ℝ) P.natDegree, ← hX]
        ring
      have hbase : ((2 : ℝ) ^ P.natDegree) ^ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)
            / (2 : ℝ) ^ (P.natDegree * k) = X := by
        rw [psN_eq_lo P.natDegree N k, ← hX]
      rw [hca_eq, hbase, Real.mul_rpow (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ P.natDegree)
        hXpos.le]
      set B : ℝ := ((2 : ℝ) ^ P.natDegree) ^ ((m : ℝ) - 1) with hB
      set A : ℝ := X ^ ((m : ℝ) - 1) with hA
      have hA0 : 0 ≤ A := by rw [hA]; exact Real.rpow_nonneg hXpos.le _
      have hB_le : B ≤ (2 : ℝ) ^ P.natDegree := by
        rw [hB]
        have hexp : ((2 : ℝ) ^ P.natDegree) ^ ((m : ℝ) - 1)
            = (2 : ℝ) ^ (((P.natDegree : ℕ) : ℝ) * ((m : ℝ) - 1)) := by
          rw [← Real.rpow_natCast (2 : ℝ) P.natDegree,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        rw [hexp, ← Real.rpow_natCast (2 : ℝ) P.natDegree]
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
        have hm1 : ((m : ℝ) - 1) ≤ 1 := by
          have : (m : ℝ) ≤ 2 := by exact_mod_cast hm
          linarith
        have hd0 : (0 : ℝ) ≤ (P.natDegree : ℝ) := Nat.cast_nonneg P.natDegree
        nlinarith [hd0, hm1]
      have hstep : B * A ≤ ((2 : ℝ) ^ P.natDegree) * A :=
        mul_le_mul_of_nonneg_right hB_le hA0
      have hp1 : (1 : ℝ) ≤ (2 : ℝ) ^ P.natDegree :=
        one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      nlinarith [hCη, hA0, hstep, hp1]

end

end Work.KMTAreas.A7
