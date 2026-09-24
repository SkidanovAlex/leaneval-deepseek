import Mathlib
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.region_II_resonant
import Submission.Work.GM.Affine.region_II_resonant_high
import Submission.Work.GM.Affine.region_II_resonant_low
import Submission.Work.GM.Affine.region_II_resonant_low_C3

/-!
# GM §9, region II: the resonant part of `ĝ`, with the `C₃`-scaled bound on `M₃`

`region_II_resonant` bounds the integral of the resonant part `ghatRes` of the Poisson
expansion of `ĝ` over region II by `C' T^δ (M₁+M₃) WinMass`, under the hypothesis `M₃ ≤ Mbig`
(with `Mbig ≤ T^4`).

Here the same is done under the weaker hypothesis `M₃ ≤ C₃ * Mbig` (with `C₃ ≥ 1`), which is
what the finer decomposition of region II needs.  The *high* part `|ξ| > 4M₁/M₃` is unaffected
(`region_II_resonant_high` needs no bound on `M₃` at all: the pair count
`≪ T^δ (1 + M₁/M₃)` already contains the `M₃`-dependence).  Only the *low* part
`|ξ| ≤ 4M₁/M₃` has to be redone with the relaxed hypothesis: there the argument bounds the
region's `‖Bsum‖²`-mass by `|R1 M₁| M₃ V² WinMass` and the nonemptiness of the region forces
`T^η < 4`, so that both `M₁ ≤ T^4` and `M₃ ≤ C₃ T^4` are bounded by the absolute constant
`C₃ 4^{4/η}` (`η = min δ 1 / 2`), which is absorbed into `C'`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.GM.Affine

noncomputable section

theorem region_II_resonant_C3 {C₀ K T₀ C₃ : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K) (hT₀ : 1 ≤ T₀)
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
            ‖ghatRes K M₁ M₂ M₃ f ξ‖ ^ 2) ≤
          C' * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := by
  obtain ⟨Ch, hChpos, hhigh⟩ := region_II_resonant_high hK δ hδ c
  obtain ⟨Cl, hClpos, hlow⟩ := region_II_resonant_low_C3 hK δ hδ C₃ hC₃ c
  obtain ⟨V, hVpos, hV0⟩ := psi1hat_decay K hK 0
  have hV : ∀ y : ℝ, ‖psi1hat K y‖ ≤ V := fun y => by simpa using hV0 y
  refine ⟨(Ch + Cl) + 1, by positivity, ?_⟩
  intro T hT f hf hfnn hsupp Λ hΛ hdec hcompat Mbig M₁ M₂ M₃
    hMb1 hMbT hM₃1 hM₃C hM₁ hM₁M hM₂ hM₂M
  have hT1 : (1 : ℝ) ≤ T := le_trans hT₀ hT
  have hcs : HasCompactSupport f := by
    refine HasCompactSupport.intro (K := Set.Icc (1 / C₀) C₀) isCompact_Icc ?_
    intro x hx
    by_contra h
    exact hx (hsupp x h)
  set a : ℝ := T ^ (min δ 1 / 2) * M₁ / M₃ with ha
  set b : ℝ := 4 * M₁ / M₃ with hb
  set h : ℝ → ℝ := fun ξ => ‖ghatRes K M₁ M₂ M₃ f ξ‖ ^ 2 with hdef
  have hhnn : ∀ ξ, 0 ≤ h ξ := fun ξ => sq_nonneg _
  have hWnn : 0 ≤ WinMass f M₂ M₃ :=
    tsum_nonneg (fun ℓ => integral_nonneg (fun τ => sq_nonneg _))
  have hMMnn : 0 ≤ M₁ + M₃ := by linarith [hM₁.le, hM₃1]
  have hmeas : Measurable (fun ξ : ℝ => ghatRes K M₁ M₂ M₃ f ξ) :=
    measurable_ghatRes hf hcs
  set B : ℝ := 8 * ((4 * M₂ ^ 2 * (∫ u, f u)) * (M₃ * (V * (4 / M₃ + 3)))) with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    have h1 : (0:ℝ) ≤ ∫ u, f u := integral_nonneg hfnn
    have h2 : 0 < 4 / M₃ + 3 := by positivity
    positivity
  have hbdd : ∀ ξ, h ξ ≤ B ^ 2 := by
    intro ξ
    rw [hdef]
    rw [hBdef]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_ghatRes_le hV hVpos.le hM₁ hM₂ (lt_of_lt_of_le zero_lt_one hM₃1) hfnn ξ) 2
  -- the covering of region II by the two parts
  have hmem : ∀ (c x : ℝ), x ∈ Set.Icc (-c) c ↔ |x| ≤ c := by
    intro c x; rw [Set.mem_Icc, abs_le]
  have hsub : (Set.Icc (-(T ^ 6)) (T ^ 6)) \ (Set.Icc (-a) a)
      ⊆ ((Set.Icc (-(T ^ 6)) (T ^ 6)) \ (Set.Icc (-b) b)) ∪
        (((Set.Icc (-(T ^ 6)) (T ^ 6)) ∩ (Set.Icc (-b) b)) \ (Set.Icc (-a) a)) := by
    intro ξ hξ
    rw [Set.mem_diff] at hξ
    obtain ⟨hξ1, hξ2⟩ := hξ
    rw [hmem a ξ] at hξ2
    rw [Set.mem_union]
    by_cases hb' : b < |ξ|
    · left
      refine ⟨hξ1, fun hcontra => ?_⟩
      exact absurd ((hmem b ξ).mp hcontra) (not_le.mpr hb')
    · right
      push_neg at hb'
      refine ⟨⟨hξ1, (hmem b ξ).mpr hb'⟩, fun hcontra => hξ2 ((hmem a ξ).mp hcontra)⟩
  have hchain : (∫⁻ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6)) \ (Set.Icc (-a) a),
        ENNReal.ofReal (h ξ)) ≤
      (∫⁻ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6)) \ (Set.Icc (-b) b), ENNReal.ofReal (h ξ)) +
      (∫⁻ ξ in ((Set.Icc (-(T ^ 6)) (T ^ 6)) ∩ (Set.Icc (-b) b)) \ (Set.Icc (-a) a),
        ENNReal.ofReal (h ξ)) := by
    refine (lintegral_mono_set hsub).trans ?_
    exact lintegral_union_le _ _ _
  have hfin1 : (∫⁻ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6)) \ (Set.Icc (-b) b), ENNReal.ofReal (h ξ))
      ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono (fun ξ => ENNReal.ofReal_le_ofReal (hbdd ξ)))
    rw [lintegral_const]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    rw [Measure.restrict_apply_univ]
    exact ne_of_lt (lt_of_le_of_lt (measure_mono (fun ξ hξ => hξ.1))
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top))
  have hfin2 : (∫⁻ ξ in ((Set.Icc (-(T ^ 6)) (T ^ 6)) ∩ (Set.Icc (-b) b)) \ (Set.Icc (-a) a),
        ENNReal.ofReal (h ξ)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono (fun ξ => ENNReal.ofReal_le_ofReal (hbdd ξ)))
    rw [lintegral_const]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    rw [Measure.restrict_apply_univ]
    exact ne_of_lt (lt_of_le_of_lt (measure_mono (fun ξ hξ => hξ.1.1))
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top))
  have hsplit : (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6)) \ (Set.Icc (-a) a), h ξ) ≤
      (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6)) \ (Set.Icc (-b) b), h ξ) +
      (∫ ξ in ((Set.Icc (-(T ^ 6)) (T ^ 6)) ∩ (Set.Icc (-b) b)) \ (Set.Icc (-a) a), h ξ) := by
    have e1 : (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6)) \ (Set.Icc (-a) a), h ξ)
        = (∫⁻ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6)) \ (Set.Icc (-a) a),
            ENNReal.ofReal (h ξ)).toReal :=
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hhnn)
        (hmeas.norm.pow_const 2).aestronglyMeasurable
    have e2 : (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6)) \ (Set.Icc (-b) b), h ξ)
        = (∫⁻ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6)) \ (Set.Icc (-b) b),
            ENNReal.ofReal (h ξ)).toReal :=
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hhnn)
        (hmeas.norm.pow_const 2).aestronglyMeasurable
    have e3 : (∫ ξ in ((Set.Icc (-(T ^ 6)) (T ^ 6)) ∩ (Set.Icc (-b) b)) \ (Set.Icc (-a) a), h ξ)
        = (∫⁻ ξ in ((Set.Icc (-(T ^ 6)) (T ^ 6)) ∩ (Set.Icc (-b) b)) \ (Set.Icc (-a) a),
            ENNReal.ofReal (h ξ)).toReal :=
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hhnn)
        (hmeas.norm.pow_const 2).aestronglyMeasurable
    rw [e1, e2, e3]
    refine (ENNReal.toReal_mono ?_ hchain).trans ENNReal.toReal_add_le
    intro htop
    rcases ENNReal.add_eq_top.mp htop with h' | h'
    · exact hfin1 h'
    · exact hfin2 h'
  have hhi := hhigh T Λ hT1 hΛ M₁ M₂ M₃ hM₃1 hM₁ hM₂ f hf hcs hdec
  have hlo := hlow T Λ hT1 hΛ Mbig M₁ M₂ M₃ hMb1 hM₃1 hM₁ hM₁M hM₂ hM₂M hM₃C hMbT
    f hf hcs hdec
  have hTd : (1 : ℝ) ≤ T ^ δ := Real.one_le_rpow hT1 hδ.le
  have hkey : Cl * (M₁ + M₃) * WinMass f M₂ M₃ ≤ Cl * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := by
    have h2 : Cl * (M₁ + M₃) ≤ Cl * T ^ δ * (M₁ + M₃) := by
      have h3 : Cl ≤ Cl * T ^ δ := by
        have := mul_le_mul_of_nonneg_left hTd hClpos.le
        rwa [mul_one] at this
      exact mul_le_mul_of_nonneg_right h3 hMMnn
    exact mul_le_mul_of_nonneg_right h2 hWnn
  have htnn : 0 ≤ T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ :=
    mul_nonneg (mul_nonneg (le_trans zero_le_one hTd) hMMnn) hWnn
  calc (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6)) \ (Set.Icc (-a) a), h ξ)
      ≤ (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6)) \ (Set.Icc (-b) b), h ξ) +
        (∫ ξ in ((Set.Icc (-(T ^ 6)) (T ^ 6)) ∩ (Set.Icc (-b) b)) \ (Set.Icc (-a) a), h ξ) :=
        hsplit
    _ ≤ Ch * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ +
        Cl * (M₁ + M₃) * WinMass f M₂ M₃ := add_le_add hhi hlo
    _ ≤ ((Ch + Cl) + 1) * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := by
        nlinarith [hkey, htnn, hChpos, hClpos, hWnn, hMMnn]

end

end Work.GM.Affine
