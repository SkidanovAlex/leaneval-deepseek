import Mathlib
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.region_II_defs
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.region_II_resonant
import Submission.Work.GM.Affine.region_II_resonant_high
import Submission.Work.GM.Affine.gSum_fourier
import Submission.Work.GM.Affine.region_II_resonant_C3
import Submission.Work.GM.Affine.regionII_winmass_aux
import Submission.Work.GM.Affine.far_C3_copy

/-!
# GM §9, region II: the reduction `(9.6')` with the scale hypothesis `M₃ ≤ C₃ Mbig`

This file states the region-II reduction of GM §9 (Lemma 9.2) in the form needed by
`regionII_core`: the third scale is only assumed to satisfy `M₃ ≤ C₃ Mbig` (with `C₃ ≥ 1` a fixed
input constant) rather than `M₃ ≤ Mbig`.

`ĝ = ĝ_res + ĝ_far` (`ghat_eq_res_add_far`), so with `‖a+b‖² ≤ 2‖a‖² + 2‖b‖²` the reduction is
assembled here from the two *half*-statements:

* `RegionIIResC3` — the resonant half (`ghatRes`), proved in `region_II_resonant_C3.lean`;
* `RegionIIFarC3` — the far half (`ghatFar`), proved in `region_II_far_C3.lean`.

The only work in *this* file is the assembly (`regionII_to_winmass_of_halves`), plus the
elementary integration bookkeeping.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.GM.Affine

noncomputable section

/-! ## The three Prop-valued forms of the region-II reduction -/

/-- The **resonant** half of the region-II reduction (`M₃ ≤ C₃ Mbig`). -/
def RegionIIResC3 (C₀ K T₀ C₃ : ℝ) (c : ℕ → ℝ → ℝ) (δ : ℝ) : Prop :=
  ∃ C' : ℝ, 0 < C' ∧
    ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
      ∀ Λ : ℝ, 0 < Λ →
      (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
        ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
      Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
      ∀ Mbig M₁ M₂ M₃ : ℝ,
      1 ≤ Mbig → Mbig ≤ T ^ 4 → 1 ≤ M₃ → M₃ ≤ C₃ * Mbig →
      0 < M₁ → M₁ ≤ Mbig → 0 < M₂ → M₂ ≤ Mbig →
      (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6))
          \ (Set.Icc (-(T ^ (min δ 1 / 2) * M₁ / M₃)) (T ^ (min δ 1 / 2) * M₁ / M₃)),
          ‖ghatRes K M₁ M₂ M₃ f ξ‖ ^ 2) ≤
        C' * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃

/-- The **far** half of the region-II reduction (`M₃ ≤ C₃ Mbig`). -/
def RegionIIFarC3 (C₀ K T₀ C₃ : ℝ) (c : ℕ → ℝ → ℝ) (δ : ℝ) : Prop :=
  ∃ C' : ℝ, 0 < C' ∧
    ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
      ∀ Λ : ℝ, 0 < Λ →
      (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
        ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
      Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
      ∀ Mbig M₁ M₂ M₃ : ℝ,
      1 ≤ Mbig → Mbig ≤ T ^ 4 → 1 ≤ M₃ → M₃ ≤ C₃ * Mbig →
      0 < M₁ → M₁ ≤ Mbig → 0 < M₂ → M₂ ≤ Mbig →
      (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6))
          \ (Set.Icc (-(T ^ (min δ 1 / 2) * M₁ / M₃)) (T ^ (min δ 1 / 2) * M₁ / M₃)),
          ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2) ≤
        C' * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃

/-- The full region-II reduction (`M₃ ≤ C₃ Mbig`) — the target statement. -/
def RegionIIC3 (C₀ K T₀ C₃ : ℝ) (c : ℕ → ℝ → ℝ) (δ : ℝ) : Prop :=
  ∃ C' : ℝ, 0 < C' ∧
    ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
      ∀ Λ : ℝ, 0 < Λ →
      (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
        ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
      Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
      ∀ Mbig M₁ M₂ M₃ : ℝ,
      1 ≤ Mbig → Mbig ≤ T ^ 4 → 1 ≤ M₃ → M₃ ≤ C₃ * Mbig →
      0 < M₁ → M₁ ≤ Mbig → 0 < M₂ → M₂ ≤ Mbig →
      (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6))
          \ (Set.Icc (-(T ^ (min δ 1 / 2) * M₁ / M₃)) (T ^ (min δ 1 / 2) * M₁ / M₃)),
          ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2) ≤
        C' * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃

/-! ## The assembly -/

theorem regionII_to_winmass_of_halves {C₀ K T₀ C₃ : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K)
    (hT₀ : 1 ≤ T₀) (hC₃ : 1 ≤ C₃) {c : ℕ → ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hres : RegionIIResC3 C₀ K T₀ C₃ c δ) (hfar : RegionIIFarC3 C₀ K T₀ C₃ c δ) :
    RegionIIC3 C₀ K T₀ C₃ c δ := by
  obtain ⟨C₁, hC₁pos, hres'⟩ := hres
  obtain ⟨C₂, hC₂pos, hfar'⟩ := hfar
  refine ⟨4 * max C₁ C₂ + 1, by positivity, ?_⟩
  intro T hT f hf hfnn hsupp Λ hΛ hdec hcompat Mbig M₁ M₂ M₃
    hMb1 hMbT hM₃1 hM₃M hM₁0 hM₁M hM₂0 hM₂M
  have hT1 : (1 : ℝ) ≤ T := le_trans hT₀ hT
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT1
  have hM₃0 : (0 : ℝ) < M₃ := lt_of_lt_of_le zero_lt_one hM₃1
  have hcs : HasCompactSupport f := hcs_of_SuppHyp hsupp
  set a : ℝ := T ^ (min δ 1 / 2) * M₁ / M₃ with ha
  set A : Set ℝ := Set.Icc (-(T ^ 6)) (T ^ 6) \ Set.Icc (-a) a with hA
  have hAmeas : MeasurableSet A := by
    rw [hA]; exact measurableSet_Icc.diff measurableSet_Icc
  have hAsub : A ⊆ Set.Icc (-(T ^ 6)) (T ^ 6) := by
    intro ξ hξ; rw [hA] at hξ; exact hξ.1
  have hAfin : volume A < ⊤ :=
    lt_of_le_of_lt (measure_mono hAsub) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
  have hWnn : 0 ≤ WinMass f M₂ M₃ := WinMass_nonneg f M₂ M₃
  have hMMnn : (0 : ℝ) ≤ M₁ + M₃ := by linarith [hM₁0.le, hM₃0.le]
  have hTδnn : (0 : ℝ) ≤ T ^ δ := Real.rpow_nonneg hTpos.le δ
  have hXnn : (0 : ℝ) ≤ T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := by positivity
  -- the two halves
  have hresb := hres' T hT f hf hfnn hsupp Λ hΛ hdec hcompat Mbig M₁ M₂ M₃
    hMb1 hMbT hM₃1 hM₃M hM₁0 hM₁M hM₂0 hM₂M
  have hfarb := hfar' T hT f hf hfnn hsupp Λ hΛ hdec hcompat Mbig M₁ M₂ M₃
    hMb1 hMbT hM₃1 hM₃M hM₁0 hM₁M hM₂0 hM₂M
  -- rewrite the integral region through `a`
  have hresA : (∫ ξ in A, ‖ghatRes K M₁ M₂ M₃ f ξ‖ ^ 2)
      ≤ C₁ * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := by
    rw [hA, ha]; exact hresb
  have hfarA : (∫ ξ in A, ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2)
      ≤ C₂ * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := by
    rw [hA, ha]; exact hfarb
  -- integrability
  obtain ⟨V, hVpos, hV⟩ := exists_psi1hat_bound_high K hK
  have hVnn : 0 ≤ V := hVpos.le
  have hResb : ∀ ξ : ℝ, ‖ghatRes K M₁ M₂ M₃ f ξ‖
      ≤ 8 * ((4 * M₂ ^ 2 * (∫ u, f u)) * (M₃ * (V * (4 / M₃ + 3)))) :=
    fun ξ => norm_ghatRes_le hV hVnn hM₁0 hM₂0 hM₃0 hfnn ξ
  have hGb : ∀ ξ : ℝ, ‖ghat K M₁ M₂ M₃ f ξ‖ ≤ ∫ u, gSum K M₁ M₂ M₃ f u :=
    fun ξ => norm_ghat_le_integral_gSum hfnn ξ
  have hIntRes : IntegrableOn (fun ξ : ℝ => ‖ghatRes K M₁ M₂ M₃ f ξ‖ ^ 2) A :=
    IntegrableOn.of_bound hAfin ((measurable_ghatRes hf hcs).norm.pow_const 2).aestronglyMeasurable
      _ (Filter.Eventually.of_forall (fun ξ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hResb ξ) 2))
  have hGcont : Continuous (fun ξ : ℝ => ghat K M₁ M₂ M₃ f ξ) :=
    continuous_ghat_of_SuppHyp hK hM₁0 hM₂0 hM₃0 hf hcs
  have hFarmeas : Measurable (ghatFar K M₁ M₂ M₃ f) := by
    have h : (ghatFar K M₁ M₂ M₃ f)
        = fun ξ : ℝ => ghat K M₁ M₂ M₃ f ξ - ghatRes K M₁ M₂ M₃ f ξ := by
      funext ξ; simp [ghatFar]
    rw [h]; exact hGcont.measurable.sub (measurable_ghatRes hf hcs)
  have hFarb : ∀ ξ : ℝ, ‖ghatFar K M₁ M₂ M₃ f ξ‖
      ≤ (∫ u, gSum K M₁ M₂ M₃ f u)
        + 8 * ((4 * M₂ ^ 2 * (∫ u, f u)) * (M₃ * (V * (4 / M₃ + 3)))) := by
    intro ξ
    have hdf : ghatFar K M₁ M₂ M₃ f ξ = ghat K M₁ M₂ M₃ f ξ - ghatRes K M₁ M₂ M₃ f ξ := by
      simp [ghatFar]
    rw [hdf]
    exact (norm_sub_le _ _).trans (add_le_add (hGb ξ) (hResb ξ))
  have hIntFar : IntegrableOn (fun ξ : ℝ => ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2) A :=
    IntegrableOn.of_bound hAfin ((hFarmeas.norm).pow_const 2).aestronglyMeasurable
      _ (Filter.Eventually.of_forall (fun ξ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hFarb ξ) 2))
  have hIntG : IntegrableOn (fun ξ : ℝ => ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2) A :=
    IntegrableOn.of_bound hAfin ((hGcont.measurable.norm).pow_const 2).aestronglyMeasurable
      _ (Filter.Eventually.of_forall (fun ξ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hGb ξ) 2))
  -- the pointwise inequality and its integral
  have hpt : ∀ ξ : ℝ, ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2
      ≤ 2 * ‖ghatRes K M₁ M₂ M₃ f ξ‖ ^ 2 + 2 * ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2 := by
    intro ξ
    rw [ghat_eq_res_add_far K M₁ M₂ M₃ f ξ]
    have h1 : ‖ghatRes K M₁ M₂ M₃ f ξ + ghatFar K M₁ M₂ M₃ f ξ‖
        ≤ ‖ghatRes K M₁ M₂ M₃ f ξ‖ + ‖ghatFar K M₁ M₂ M₃ f ξ‖ := norm_add_le _ _
    have h2 : ‖ghatRes K M₁ M₂ M₃ f ξ + ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2
        ≤ (‖ghatRes K M₁ M₂ M₃ f ξ‖ + ‖ghatFar K M₁ M₂ M₃ f ξ‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : (‖ghatRes K M₁ M₂ M₃ f ξ‖ + ‖ghatFar K M₁ M₂ M₃ f ξ‖) ^ 2
        ≤ 2 * ‖ghatRes K M₁ M₂ M₃ f ξ‖ ^ 2 + 2 * ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2 := by
      nlinarith [sq_nonneg (‖ghatRes K M₁ M₂ M₃ f ξ‖ - ‖ghatFar K M₁ M₂ M₃ f ξ‖)]
    exact le_trans h2 h3
  have hmono : (∫ ξ in A, ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
      ≤ ∫ ξ in A, (2 * ‖ghatRes K M₁ M₂ M₃ f ξ‖ ^ 2 + 2 * ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2) :=
    MeasureTheory.setIntegral_mono_of_nonneg (fun ξ _ => sq_nonneg _)
      (fun ξ _ => hpt ξ) ((hIntRes.const_mul 2).add (hIntFar.const_mul 2))
  have hsplit : (∫ ξ in A,
        (2 * ‖ghatRes K M₁ M₂ M₃ f ξ‖ ^ 2 + 2 * ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2))
      = 2 * (∫ ξ in A, ‖ghatRes K M₁ M₂ M₃ f ξ‖ ^ 2)
        + 2 * (∫ ξ in A, ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2) := by
    rw [integral_add (hIntRes.const_mul 2) (hIntFar.const_mul 2),
      integral_const_mul, integral_const_mul]
  -- arithmetic
  have harith : 2 * (C₁ * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃)
      + 2 * (C₂ * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃)
      ≤ (4 * max C₁ C₂ + 1) * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := by
    have hle : 2 * (C₁ * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃)
        + 2 * (C₂ * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃)
        = (2 * (C₁ + C₂)) * (T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃) := by ring
    rw [hle]
    have h2 : 2 * (C₁ + C₂) ≤ 4 * max C₁ C₂ + 1 := by
      have h3 : 2 * C₁ ≤ 2 * max C₁ C₂ := by linarith [le_max_left C₁ C₂]
      have h4 : 2 * C₂ ≤ 2 * max C₁ C₂ := by linarith [le_max_right C₁ C₂]
      linarith
    have hX : (0 : ℝ) ≤ T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := hXnn
    calc (2 * (C₁ + C₂)) * (T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃)
        ≤ (4 * max C₁ C₂ + 1) * (T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃) :=
          mul_le_mul_of_nonneg_right h2 hX
      _ = (4 * max C₁ C₂ + 1) * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := by ring
  calc (∫ ξ in A, ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
      ≤ 2 * (∫ ξ in A, ‖ghatRes K M₁ M₂ M₃ f ξ‖ ^ 2)
        + 2 * (∫ ξ in A, ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2) := by
        rw [← hsplit]; exact hmono
    _ ≤ 2 * (C₁ * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃)
        + 2 * (C₂ * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hresA (by norm_num))
          (mul_le_mul_of_nonneg_left hfarA (by norm_num))
    _ ≤ (4 * max C₁ C₂ + 1) * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := harith

/-- The resonant half holds with the explicit statement of `region_II_resonant_C3`. -/
theorem RegionIIResC3_true {C₀ K T₀ C₃ : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K) (hT₀ : 1 ≤ T₀)
    (hC₃ : 1 ≤ C₃) (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    RegionIIResC3 C₀ K T₀ C₃ c δ :=
  region_II_resonant_C3 hC₀ hK hT₀ hC₃ c δ hδ

/-! ## The target -/

theorem regionII_to_winmass {C₀ K T₀ C₃ : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K) (hT₀ : 1 ≤ T₀)
    (hC₃ : 1 ≤ C₃) (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∀ Mbig M₁ M₂ M₃ : ℝ,
        1 ≤ Mbig → Mbig ≤ T ^ 4 → 1 ≤ M₃ → M₃ ≤ C₃ * Mbig →
        0 < M₁ → M₁ ≤ Mbig → 0 < M₂ → M₂ ≤ Mbig →
        (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6))
            \ (Set.Icc (-(T ^ (min δ 1 / 2) * M₁ / M₃)) (T ^ (min δ 1 / 2) * M₁ / M₃)),
            ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2) ≤
          C' * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ :=
  regionII_to_winmass_of_halves hC₀ hK hT₀ hC₃ hδ
    (RegionIIResC3_true hC₀ hK hT₀ hC₃ c δ hδ)
    (region_II_far_C3_c hC₀ hK hT₀ hC₃ c δ hδ)

end

end Work.GM.Affine
