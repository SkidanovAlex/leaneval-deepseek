import Mathlib
import Submission.Work.GM.Affine.far_est_M3_le_Mbig_v2
import Submission.Work.GM.Affine.regionII_winmass_aux
import Submission.Work.GM.Affine.region_II_resonant_C3
import Submission.Work.GM.Affine.far_low_xi_est

/-!
# GM §9, region II: the reduction `(9.6')` in the honest `supf` form

This file proves `Work.GM.Affine.regionII_to_winmass_sup_c`, the region-II reduction of GM §9 with

* the *honest* Fourier-decay hypothesis `supf f ≤ Λ` (the bare `Λ`-form is false for narrow
  needles, see `NOTES_T1_BOUND_defect.md` and `NOTES_region_II_far_C3_verdict.md`), and
* the relaxed third scale `M₃ ≤ C₃ Mbig` (`C₃ ≥ 1` a fixed input constant).

The statement is assembled from two halves, exactly as in `regionII_to_winmass`:

* the **resonant** half — already available, and even in the stronger `Λ`-form, by
  `Work.GM.Affine.region_II_resonant_C3`;
* the **far** half — `Work.GM.Affine.regionII_far_C3_sup_c`, proved here.

The far half is reduced to the sharp `M₃ ≤ Mbig` estimate
`Work.GM.Affine.far_est_M3_le_Mbig_v2` by the `T → a T`, `a = C₃^{1/4}` rescaling: with
`T' = a T` one has `M₃ ≤ C₃ T⁴ = T'⁴`, so all scale hypotheses of the sharp estimate hold, and
`(T')^δ = a^δ T^δ` is absorbed into `C'`.  The rescaling loses the annulus
`T^η M₁/M₃ < |ξ| ≤ a^η T^η M₁/M₃` (`η = min δ 1 / 2`), which is covered by the proved
low-frequency estimate `Work.GM.Affine.far_low_xi_est` (it applies precisely when `T⁴ < M₃`,
the only case in which the rescaling is needed).
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.GM.Affine

noncomputable section

/-! ## Elementary scaling facts -/

/-- For `T, D ≥ 1`, `ε ≥ 0`, `a ≥ 0` and `j : ℕ`: `T^ε a^j ≤ (TD)^ε (aD)^j`. -/
lemma rpow_mul_pow_le_mul_c {T D ε a : ℝ} (hT : 1 ≤ T) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (ha : 0 ≤ a) (j : ℕ) :
    T ^ ε * a ^ j ≤ (T * D) ^ ε * (a * D) ^ j := by
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT
  have hD0 : (0 : ℝ) ≤ D := le_trans zero_le_one hD
  have hD1 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have h1 : (T * D) ^ ε = T ^ ε * D ^ ε := Real.mul_rpow hT0 hD0
  have h2 : (a * D) ^ j = a ^ j * D ^ j := mul_pow a D j
  have h3 : (1 : ℝ) ≤ D ^ ε * D ^ j := by
    rw [← Real.rpow_natCast D j, ← Real.rpow_add hD1 ε (j : ℝ)]
    exact Real.one_le_rpow hD (by positivity)
  rw [h1, h2]
  calc T ^ ε * a ^ j = T ^ ε * a ^ j * 1 := (mul_one _).symm
    _ ≤ T ^ ε * a ^ j * (D ^ ε * D ^ j) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = T ^ ε * D ^ ε * (a ^ j * D ^ j) := by ring

/-- The `T`-decay hypothesis transfers to `T * D` for `D ≥ 1`, with the *same* constant `c`.
Non-negativity of `c j ε * Λ` is forced by the hypothesis itself (the left-hand side of the
decay estimate is a norm). -/
lemma decay_scale_up_c {T D : ℝ} (hT : 1 ≤ T) (hD : 1 ≤ D) {c : ℕ → ℝ → ℝ} {Λ : ℝ} {g : ℝ → ℂ}
    (h : ∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 → ‖g ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) :
    ∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
      ‖g ξ‖ ≤ c j ε * (T * D) ^ ε * ((T * D) / |ξ|) ^ j * Λ := by
  intro j ε hε ξ hξ
  have hcΛ : 0 ≤ c j ε * Λ := by
    have h0 := h j ε hε 1 one_ne_zero
    have h1 : 0 ≤ c j ε * T ^ ε * (T / |(1 : ℝ)|) ^ j * Λ := le_trans (norm_nonneg _) h0
    have h2 : c j ε * T ^ ε * (T / |(1 : ℝ)|) ^ j * Λ
        = (T ^ ε * (T / |(1 : ℝ)|) ^ j) * (c j ε * Λ) := by ring
    have h3 : 0 < T ^ ε * (T / |(1 : ℝ)|) ^ j := by
      rw [abs_one, div_one]; positivity
    rw [h2] at h1
    exact nonneg_of_mul_nonneg_right h1 h3
  have hle := rpow_mul_pow_le_mul_c (T := T) (D := D) (ε := ε) (a := T / |ξ|) hT hD
    (le_of_lt hε) (by positivity) j
  have heq : (T * D) / |ξ| = (T / |ξ|) * D := by ring
  rw [heq]
  calc ‖g ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ := h j ε hε ξ hξ
    _ = (c j ε * Λ) * (T ^ ε * (T / |ξ|) ^ j) := by ring
    _ ≤ (c j ε * Λ) * ((T * D) ^ ε * ((T / |ξ|) * D) ^ j) := mul_le_mul_of_nonneg_left hle hcΛ
    _ = c j ε * (T * D) ^ ε * ((T / |ξ|) * D) ^ j * Λ := by ring

/-- Set algebra for the rescaling: the annulus `A_T = {T^η M₁/M₃ < |ξ| ≤ T⁶}` is contained in
the enlarged annulus `A_{Ta} = {(Ta)^η M₁/M₃ < |ξ| ≤ (Ta)⁶}` (for `a ≥ 1`) together with the
"inner" annulus `{a^η T^η M₁/M₃ < |ξ| ≤ T^η M₁/M₃}`. -/
lemma annulus_subset_scale_c {T a M₁ M₃ η : ℝ} (hT : 0 < T) (ha : 1 ≤ a) (hM₃ : 0 < M₃) :
    (Set.Icc (-(T ^ 6)) (T ^ 6) \ Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃))
      ⊆ (Set.Icc (-((T * a) ^ 6)) ((T * a) ^ 6)
            \ Set.Icc (-((T * a) ^ η * M₁ / M₃)) ((T * a) ^ η * M₁ / M₃))
        ∪ (Set.Icc (-(a ^ η * T ^ η * M₁ / M₃)) (a ^ η * T ^ η * M₁ / M₃)
            \ Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃)) := by
  intro ξ hξ
  have hξ' : (-(T ^ 6) ≤ ξ ∧ ξ ≤ T ^ 6)
      ∧ ¬ (-(T ^ η * M₁ / M₃) ≤ ξ ∧ ξ ≤ T ^ η * M₁ / M₃) := by
    simpa only [Set.mem_diff, Set.mem_Icc] using hξ
  obtain ⟨⟨h1, h2⟩, h3⟩ := hξ'
  have ha0 : (0 : ℝ) ≤ a := le_trans zero_le_one ha
  have hTa : T ≤ T * a := by
    calc T = T * 1 := (mul_one T).symm
      _ ≤ T * a := mul_le_mul_of_nonneg_left ha hT.le
  have hT6 : T ^ (6 : ℕ) ≤ (T * a) ^ (6 : ℕ) := pow_le_pow_left₀ hT.le hTa 6
  have hrw : (T * a) ^ η * M₁ / M₃ = a ^ η * T ^ η * M₁ / M₃ := by
    rw [Real.mul_rpow hT.le ha0]; ring
  by_cases hq : ξ ∈ Set.Icc (-((T * a) ^ η * M₁ / M₃)) ((T * a) ^ η * M₁ / M₃)
  · right
    have hqabs : |ξ| ≤ (T * a) ^ η * M₁ / M₃ := by
      rw [Set.mem_Icc] at hq; exact abs_le.mpr hq
    rw [hrw] at hqabs
    rw [Set.mem_diff, Set.mem_Icc, Set.mem_Icc]
    exact ⟨abs_le.mp hqabs, h3⟩
  · left
    rw [Set.mem_diff, Set.mem_Icc, Set.mem_Icc]
    exact ⟨⟨by linarith, by linarith⟩, hq⟩

/-! ## The far half with `M₃ ≤ C₃ Mbig` -/

/-- **GM §9, region II, far part, relaxed third scale.**  `Work.GM.Affine.far_est_M3_le_Mbig_v2`
with `M₃ ≤ C₃ Mbig` in place of `M₃ ≤ Mbig`. -/
theorem regionII_far_C3_sup_c {C₀ K T₀ C₃ : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K) (hT₀ : 1 ≤ T₀)
    (hC₃ : 1 ≤ C₃) (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        supf f ≤ Λ →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∀ Mbig M₁ M₂ M₃ : ℝ,
        1 ≤ Mbig → Mbig ≤ T ^ 4 → 1 ≤ M₃ → M₃ ≤ C₃ * Mbig →
        0 < M₁ → M₁ ≤ Mbig → 0 < M₂ → M₂ ≤ Mbig →
        (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6))
            \ (Set.Icc (-(T ^ (min δ 1 / 2) * M₁ / M₃)) (T ^ (min δ 1 / 2) * M₁ / M₃)),
            ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2) ≤
          C' * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := by
  obtain ⟨Cfar, hCfarpos, hfar⟩ :=
    far_est_M3_le_Mbig_v2 (C₀ := C₀) (K := K) (T₀ := T₀) hC₀ hK hT₀ c δ hδ
  set a : ℝ := C₃ ^ ((1 : ℝ) / 4) with hadef
  have ha1 : 1 ≤ a := by rw [hadef]; exact Real.one_le_rpow hC₃ (by norm_num)
  have hapos : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  obtain ⟨Clow, hClowpos, hlow⟩ :=
    far_low_xi_est (C₀ := C₀) (K := K) (T₀ := T₀) (a := a) hC₀ hK hT₀ ha1 c δ hδ
  have haδ1 : 1 ≤ a ^ δ := Real.one_le_rpow ha1 hδ.le
  refine ⟨Cfar * a ^ δ + Clow + 1, by positivity, ?_⟩
  intro T hT f hf hfnn hsupp Λ hΛ hdec hsupf hΛb Mbig M₁ M₂ M₃
    hMb1 hMbT hM₃1 hM₃M hM₁0 hM₁M hM₂0 hM₂M
  have hT1 : (1 : ℝ) ≤ T := le_trans hT₀ hT
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT1
  have hC₃pos : (0 : ℝ) < C₃ := lt_of_lt_of_le zero_lt_one hC₃
  have hM₃pos : (0 : ℝ) < M₃ := lt_of_lt_of_le zero_lt_one hM₃1
  have hAnn : (0 : ℝ) ≤ M₁ + M₃ := by linarith
  have hWnn : 0 ≤ WinMass f M₂ M₃ := WinMass_nonneg f M₂ M₃
  have hTδnn : 0 ≤ T ^ δ := Real.rpow_nonneg hTpos.le δ
  have hXnn : 0 ≤ T ^ δ * ((M₁ + M₃) * WinMass f M₂ M₃) :=
    mul_nonneg hTδnn (mul_nonneg hAnn hWnn)
  have hcs : HasCompactSupport f := hcs_of_SuppHyp hsupp
  -- a uniform bound on `‖ghatFar‖`, hence `IntegrableOn` on every set of finite measure
  obtain ⟨V, hVpos, hV⟩ := exists_psi1hat_bound_high K hK
  have hVnn : 0 ≤ V := hVpos.le
  have hResb : ∀ ξ : ℝ, ‖ghatRes K M₁ M₂ M₃ f ξ‖
      ≤ 8 * ((4 * M₂ ^ 2 * (∫ u, f u)) * (M₃ * (V * (4 / M₃ + 3)))) :=
    fun ξ => norm_ghatRes_le hV hVnn hM₁0 hM₂0 hM₃pos hfnn ξ
  have hGb : ∀ ξ : ℝ, ‖ghat K M₁ M₂ M₃ f ξ‖ ≤ ∫ u, gSum K M₁ M₂ M₃ f u :=
    fun ξ => norm_ghat_le_integral_gSum hfnn ξ
  have hFarb : ∀ ξ : ℝ, ‖ghatFar K M₁ M₂ M₃ f ξ‖
      ≤ (∫ u, gSum K M₁ M₂ M₃ f u)
        + 8 * ((4 * M₂ ^ 2 * (∫ u, f u)) * (M₃ * (V * (4 / M₃ + 3)))) := by
    intro ξ
    have hdf : ghatFar K M₁ M₂ M₃ f ξ = ghat K M₁ M₂ M₃ f ξ - ghatRes K M₁ M₂ M₃ f ξ := by
      simp [ghatFar]
    rw [hdf]
    exact (norm_sub_le _ _).trans (add_le_add (hGb ξ) (hResb ξ))
  have hGcont : Continuous (fun ξ : ℝ => ghat K M₁ M₂ M₃ f ξ) :=
    continuous_ghat_of_SuppHyp hK hM₁0 hM₂0 hM₃pos hf hcs
  have hFarmeas : Measurable (ghatFar K M₁ M₂ M₃ f) := by
    have h : (ghatFar K M₁ M₂ M₃ f)
        = fun ξ : ℝ => ghat K M₁ M₂ M₃ f ξ - ghatRes K M₁ M₂ M₃ f ξ := by
      funext ξ; simp [ghatFar]
    rw [h]; exact hGcont.measurable.sub (measurable_ghatRes hf hcs)
  have hIntFar : ∀ S : Set ℝ, volume S < ⊤ →
      IntegrableOn (fun ξ : ℝ => ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2) S := by
    intro S hS
    refine IntegrableOn.of_bound hS ((hFarmeas.norm).pow_const 2).aestronglyMeasurable
      (((∫ u, gSum K M₁ M₂ M₃ f u)
        + 8 * ((4 * M₂ ^ 2 * (∫ u, f u)) * (M₃ * (V * (4 / M₃ + 3))))) ^ 2) ?_
    exact Filter.Eventually.of_forall (fun ξ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hFarb ξ) 2)
  have hvol : ∀ D : ℝ, volume (Set.Icc (-D) D) < ⊤ := by
    intro D; rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  set A : Set ℝ := (Set.Icc (-(T ^ 6)) (T ^ 6))
      \ (Set.Icc (-(T ^ (min δ 1 / 2) * M₁ / M₃)) (T ^ (min δ 1 / 2) * M₁ / M₃)) with hAdef
  by_cases hcase : M₃ ≤ T ^ 4
  · -- Case 1: `M₃ ≤ T⁴` — apply the sharp estimate directly with `Mbig := max Mbig M₃`
    have hfar' := hfar T hT f hf hfnn hsupp Λ hΛ hdec hsupf hΛb (max Mbig M₃) M₁ M₂ M₃
      (le_trans hMb1 (le_max_left _ _)) hM₃1 hM₁0 (le_trans hM₁M (le_max_left _ _)) hM₂0
      (le_trans hM₂M (le_max_left _ _)) (le_max_right _ _) (max_le hMbT hcase)
    rw [hAdef]
    refine hfar'.trans ?_
    have hle : Cfar ≤ Cfar * a ^ δ + Clow + 1 := by nlinarith [haδ1, hCfarpos, hClowpos]
    calc Cfar * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃
        = Cfar * (T ^ δ * ((M₁ + M₃) * WinMass f M₂ M₃)) := by ring
      _ ≤ (Cfar * a ^ δ + Clow + 1) * (T ^ δ * ((M₁ + M₃) * WinMass f M₂ M₃)) :=
          mul_le_mul_of_nonneg_right hle hXnn
      _ = (Cfar * a ^ δ + Clow + 1) * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := by ring
  · -- Case 2: `T⁴ < M₃` — rescale `T → T' = T a` and pay with `far_low_xi_est`
    have hT4M₃ : T ^ 4 < M₃ := lt_of_not_ge hcase
    set T' : ℝ := T * a with hT'def
    have hTT' : T ≤ T' := by
      rw [hT'def]
      calc T = T * 1 := (mul_one T).symm
        _ ≤ T * a := mul_le_mul_of_nonneg_left ha1 hTpos.le
    have hT'1 : 1 ≤ T' := le_trans hT1 hTT'
    have hT'pos : 0 < T' := lt_of_lt_of_le zero_lt_one hT'1
    have hT'₀ : T₀ ≤ T' := le_trans hT hTT'
    have ha4 : a ^ (4 : ℕ) = C₃ := by
      rw [hadef, ← Real.rpow_natCast (C₃ ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul hC₃pos.le]
      have h2 : ((1 : ℝ) / 4) * ((4 : ℕ) : ℝ) = 1 := by norm_num
      rw [h2, Real.rpow_one]
    have hT'4 : (T') ^ (4 : ℕ) = C₃ * T ^ 4 := by
      rw [hT'def, mul_pow, ha4]; ring
    have hMb'T' : max Mbig M₃ ≤ (T') ^ (4 : ℕ) := by
      rw [max_le_iff, hT'4]
      refine ⟨?_, ?_⟩
      · calc Mbig ≤ T ^ 4 := hMbT
          _ ≤ C₃ * T ^ 4 := by nlinarith [hC₃pos, pow_pos hTpos 4]
      · calc M₃ ≤ C₃ * Mbig := hM₃M
          _ ≤ C₃ * T ^ 4 := mul_le_mul_of_nonneg_left hMbT hC₃pos.le
    -- the decay hypothesis at `T' = T a`
    have hdec' : ∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
        ‖Fhat f ξ‖ ≤ c j ε * (T') ^ ε * (T' / |ξ|) ^ j * Λ := by
      have h := decay_scale_up_c (T := T) (D := a) (c := c) (Λ := Λ) (g := Fhat f) hT1 ha1 hdec
      rw [hT'def]
      exact h
    have hΛb' : Λ ≤ 16 * c 2 1 * (T') ^ 3 * ∫ u, f u := by
      have hcK : 0 < c 2 1 * ∫ u, f u := by
        have h1 : 0 < 16 * c 2 1 * T ^ 3 * (∫ u, f u) := lt_of_lt_of_le hΛ hΛb
        have h2 : 0 < T ^ 3 := by positivity
        nlinarith [h1, h2]
      have hT3 : T ^ 3 ≤ (T') ^ 3 := pow_le_pow_left₀ hTpos.le hTT' 3
      have hfac : 0 ≤ 16 * (c 2 1 * ∫ u, f u) := by linarith
      have hstep := mul_le_mul_of_nonneg_left hT3 hfac
      have hA' : 16 * c 2 1 * T ^ 3 * (∫ u, f u) = 16 * (c 2 1 * ∫ u, f u) * T ^ 3 := by ring
      have hB' : 16 * c 2 1 * (T') ^ 3 * (∫ u, f u)
          = 16 * (c 2 1 * ∫ u, f u) * (T') ^ 3 := by ring
      calc Λ ≤ 16 * c 2 1 * T ^ 3 * (∫ u, f u) := hΛb
        _ = 16 * (c 2 1 * ∫ u, f u) * T ^ 3 := hA'
        _ ≤ 16 * (c 2 1 * ∫ u, f u) * (T') ^ 3 := hstep
        _ = 16 * c 2 1 * (T') ^ 3 * (∫ u, f u) := hB'.symm
    have hfar' := hfar T' hT'₀ f hf hfnn hsupp Λ hΛ hdec' hsupf hΛb' (max Mbig M₃) M₁ M₂ M₃
      (le_trans hMb1 (le_max_left _ _)) hM₃1 hM₁0 (le_trans hM₁M (le_max_left _ _)) hM₂0
      (le_trans hM₂M (le_max_left _ _)) (le_max_right _ _) hMb'T'
    have hlow' := hlow T hT f hf hfnn hsupp Λ hΛ hdec hΛb M₁ M₂ M₃ hM₁0
      (le_trans hM₁M hMbT) hM₂0 (le_trans hM₂M hMbT) hM₃1 hT4M₃
    -- the three sets
    set A' : Set ℝ := (Set.Icc (-((T') ^ 6)) ((T') ^ 6))
        \ (Set.Icc (-((T') ^ (min δ 1 / 2) * M₁ / M₃)) ((T') ^ (min δ 1 / 2) * M₁ / M₃))
      with hA'def
    set B : Set ℝ := (Set.Icc (-(a ^ (min δ 1 / 2) * T ^ (min δ 1 / 2) * M₁ / M₃))
          (a ^ (min δ 1 / 2) * T ^ (min δ 1 / 2) * M₁ / M₃))
        \ (Set.Icc (-(T ^ (min δ 1 / 2) * M₁ / M₃)) (T ^ (min δ 1 / 2) * M₁ / M₃))
      with hBdef
    set g : ℝ → ℝ := fun ξ => ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2 with hgdef
    have hsub : A ⊆ A' ∪ B := by
      rw [hAdef, hA'def, hBdef, hT'def]
      intro ξ hξ
      exact annulus_subset_scale_c (T := T) (a := a) (M₁ := M₁) (M₃ := M₃)
        (η := min δ 1 / 2) hTpos ha1 hM₃pos hξ
    have hdisj : Disjoint A' B := by
      rw [Set.disjoint_left, hA'def, hBdef]
      intro ξ h1 h2
      simp only [Set.mem_diff, Set.mem_Icc] at h1 h2
      have harg : T' ^ (min δ 1 / 2) * M₁ / M₃
          = a ^ (min δ 1 / 2) * T ^ (min δ 1 / 2) * M₁ / M₃ := by
        rw [hT'def, Real.mul_rpow hTpos.le (le_trans zero_le_one ha1)]
        ring
      rw [harg] at h1
      exact h1.2 h2.1
    -- integrability
    have hAfin : volume A < ⊤ :=
      lt_of_le_of_lt (measure_mono (fun ξ hξ => by
        rw [hAdef] at hξ; exact hξ.1)) (hvol (T ^ 6))
    have hA'fin : volume A' < ⊤ :=
      lt_of_le_of_lt (measure_mono (fun ξ hξ => by
        rw [hA'def] at hξ; exact hξ.1)) (hvol ((T') ^ 6))
    have hBfin : volume B < ⊤ :=
      lt_of_le_of_lt (measure_mono (fun ξ hξ => by
        rw [hBdef] at hξ; exact hξ.1)) (hvol (a ^ (min δ 1 / 2) * T ^ (min δ 1 / 2) * M₁ / M₃))
    have hIntA : IntegrableOn g A := hIntFar A hAfin
    have hIntA' : IntegrableOn g A' := hIntFar A' hA'fin
    have hIntB : IntegrableOn g B := hIntFar B hBfin
    have hIntU : IntegrableOn g (A' ∪ B) := hIntFar (A' ∪ B) (by
      refine lt_of_le_of_lt (measure_union_le A' B) ?_
      rw [ENNReal.add_lt_top]
      exact ⟨hA'fin, hBfin⟩)
    have hBmeas : MeasurableSet B := by
      rw [hBdef]; exact measurableSet_Icc.diff measurableSet_Icc
    -- bounds for the two pieces
    have hA'bound : ∫ ξ in A', g ξ ≤ Cfar * a ^ δ * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := by
      have h := hfar'
      rw [hA'def] at h
      have heq : (T') ^ δ = a ^ δ * T ^ δ := by
        rw [hT'def, Real.mul_rpow hTpos.le (le_trans zero_le_one ha1), mul_comm (T ^ δ) (a ^ δ)]
      have heq2 : Cfar * (T') ^ δ * (M₁ + M₃) * WinMass f M₂ M₃
          = Cfar * a ^ δ * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := by
        rw [heq]; ring
      calc ∫ ξ in A', g ξ = ∫ ξ in A', ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2 := rfl
        _ ≤ Cfar * (T') ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := h
        _ = Cfar * a ^ δ * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := heq2
    have hBbound : ∫ ξ in B, g ξ ≤ Clow * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := by
      have h := hlow'
      rw [hBdef] at h
      calc ∫ ξ in B, g ξ = ∫ ξ in B, ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2 := rfl
        _ ≤ Clow * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := h
    -- assemble
    have hstep1 : ∫ ξ in A, g ξ ≤ ∫ ξ in A' ∪ B, g ξ :=
      setIntegral_mono_set hIntU (Filter.Eventually.of_forall (fun ξ => sq_nonneg _))
        (Filter.Eventually.of_forall hsub)
    have hstep2 : ∫ ξ in A' ∪ B, g ξ = (∫ ξ in A', g ξ) + (∫ ξ in B, g ξ) :=
      setIntegral_union hdisj hBmeas hIntA' hIntB
    have hstep3 : (∫ ξ in A', g ξ) + (∫ ξ in B, g ξ)
        ≤ (Cfar * a ^ δ + Clow + 1) * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := by
      have hsum := add_le_add hA'bound hBbound
      have heq : Cfar * a ^ δ * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃
            + Clow * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃
          = (Cfar * a ^ δ + Clow) * (T ^ δ * ((M₁ + M₃) * WinMass f M₂ M₃)) := by ring
      have hcoef : Cfar * a ^ δ + Clow ≤ Cfar * a ^ δ + Clow + 1 := by linarith
      calc (∫ ξ in A', g ξ) + (∫ ξ in B, g ξ)
          ≤ Cfar * a ^ δ * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃
            + Clow * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := hsum
        _ = (Cfar * a ^ δ + Clow) * (T ^ δ * ((M₁ + M₃) * WinMass f M₂ M₃)) := heq
        _ ≤ (Cfar * a ^ δ + Clow + 1) * (T ^ δ * ((M₁ + M₃) * WinMass f M₂ M₃)) :=
            mul_le_mul_of_nonneg_right hcoef hXnn
        _ = (Cfar * a ^ δ + Clow + 1) * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := by ring
    calc ∫ ξ in A, g ξ ≤ ∫ ξ in A' ∪ B, g ξ := hstep1
      _ = (∫ ξ in A', g ξ) + (∫ ξ in B, g ξ) := hstep2
      _ ≤ (Cfar * a ^ δ + Clow + 1) * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := hstep3

/-! ## The target -/

theorem regionII_to_winmass_sup_c {C₀ K T₀ C₃ : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K)
    (hT₀ : 1 ≤ T₀) (hC₃ : 1 ≤ C₃) (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        supf f ≤ Λ →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∀ Mbig M₁ M₂ M₃ : ℝ,
        1 ≤ Mbig → Mbig ≤ T ^ 4 → 1 ≤ M₃ → M₃ ≤ C₃ * Mbig →
        0 < M₁ → M₁ ≤ Mbig → 0 < M₂ → M₂ ≤ Mbig →
        (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6))
            \ (Set.Icc (-(T ^ (min δ 1 / 2) * M₁ / M₃)) (T ^ (min δ 1 / 2) * M₁ / M₃)),
            ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2) ≤
          C' * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := by
  obtain ⟨C₁, hC₁pos, hres'⟩ := region_II_resonant_C3 hC₀ hK hT₀ hC₃ c δ hδ
  obtain ⟨C₂, hC₂pos, hfar'⟩ := regionII_far_C3_sup_c hC₀ hK hT₀ hC₃ c δ hδ
  refine ⟨4 * max C₁ C₂ + 1, by positivity, ?_⟩
  intro T hT f hf hfnn hsupp Λ hΛ hdec hsupf hcompat Mbig M₁ M₂ M₃
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
  have hXnn : (0 : ℝ) ≤ T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ :=
    mul_nonneg (mul_nonneg hTδnn hMMnn) hWnn
  -- the two halves
  have hresb := hres' T hT f hf hfnn hsupp Λ hΛ hdec hcompat Mbig M₁ M₂ M₃
    hMb1 hMbT hM₃1 hM₃M hM₁0 hM₁M hM₂0 hM₂M
  have hfarb := hfar' T hT f hf hfnn hsupp Λ hΛ hdec hsupf hcompat Mbig M₁ M₂ M₃
    hMb1 hMbT hM₃1 hM₃M hM₁0 hM₁M hM₂0 hM₂M
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
end

end Work.GM.Affine
