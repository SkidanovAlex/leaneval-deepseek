import Mathlib
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.card_mul_pairs_le
import Submission.Work.GM.Affine.psi1hat_decay
import Submission.Work.GM.Affine.region_I_bound
import Submission.Work.GM.Affine.cauchy_base
import Submission.Work.GM.Affine.supf_le_of_decay
import Submission.Work.GM.Affine.smoothed_properties
import Submission.Work.GM.Affine.window_integral_Bsum
import Submission.Work.GM.Affine.tsum_resonance_eq_finsum
import Submission.Work.GM.Affine.finset_sum_window_le_WinMass
import Submission.Work.GM.Affine.resonant_count_good
import Submission.Work.GM.Affine.region_II_resonant_high
import Submission.Work.GM.Affine.region_II_resonant_low

/-!
# GM §9, region II: the resonant (near-diagonal) part of `ĝ`

`region_II_resonant` bounds the integral, over region II `T^η M₁/M₃ < |ξ| ≤ T⁶`
(`η = min δ 1 / 2`), of the *resonant* part `ghatRes` of the Poisson expansion of `ĝ`
(only the pairs `(m₁,ℓ)` with `|ℓ - ξ/m₁| ≤ 2/M₃`) by `C' T^δ (M₁+M₃) WinMass f M₂ M₃`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.GM.Affine

noncomputable section

/-! ### The resonance weight -/

/-- The resonance weight `T(x) = Σ'_ℓ [|ℓ - x| ≤ 2/M₃] ψ̂₁(K, M₃(ℓ - x))` appearing in `ghatRes`. -/
def Twt (K M₃ x : ℝ) : ℂ :=
  ∑' ℓ : ℤ, if |(ℓ : ℝ) - x| ≤ 2 / M₃ then psi1hat K (M₃ * ((ℓ : ℝ) - x)) else 0

/-- `ghatRes` is the `m₁`-sum of `Bsum` times `M₃` times the resonance weight. -/
lemma ghatRes_eq_Twt (K M₁ M₂ M₃ : ℝ) (f : ℝ → ℝ) (ξ : ℝ) :
    ghatRes K M₁ M₂ M₃ f ξ =
      ∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
        ((M₃ : ℂ) * Twt K M₃ (ξ / (m₁ : ℝ))) := rfl

/-- `psi1hat` is continuous (Fourier transform of an `L¹` function). -/
lemma continuous_psi1hat (K : ℝ) : Continuous (psi1hat K) := by
  have hint : Integrable (fun t : ℝ => ((psi1 K t : ℝ) : ℂ)) volume :=
    (psi1_ofReal_contDiff K).continuous.integrable_of_hasCompactSupport
      (psi1_ofReal_hasCompactSupport K)
  unfold psi1hat
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hint

lemma measurable_Twt (K M₃ : ℝ) : Measurable (Twt K M₃) := by
  unfold Twt
  refine Measurable.tsum (fun ℓ => ?_)
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_le (measurable_const.sub measurable_id).abs measurable_const
  · exact ((continuous_psi1hat K).comp
      (continuous_const.mul (continuous_const.sub continuous_id))).measurable

/-- The resonant integers for `x` are contained in the interval `[⌊x-2/M₃⌋, ⌈x+2/M₃⌉]`. -/
lemma Twt_eq_finsum (K M₃ x : ℝ) (hM₃ : 0 < M₃) :
    Twt K M₃ x = ∑ ℓ ∈ Finset.Icc ⌊x - 2 / M₃⌋ ⌈x + 2 / M₃⌉,
      (if |(ℓ : ℝ) - x| ≤ 2 / M₃ then psi1hat K (M₃ * ((ℓ : ℝ) - x)) else 0) := by
  unfold Twt
  refine tsum_eq_sum (fun ℓ hℓ => ?_)
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hℓ
  have h2 : (0:ℝ) < 2 / M₃ := by positivity
  rw [if_neg]
  rcases hℓ with h | h
  · have h1 : ((ℓ : ℤ) : ℝ) < x - 2 / M₃ := by
      have hc : ((ℓ : ℤ) : ℝ) < ((⌊x - 2 / M₃⌋ : ℤ) : ℝ) := by exact_mod_cast h
      have hf := Int.floor_le (x - 2 / M₃); linarith
    rw [abs_of_neg (by linarith : ((ℓ : ℤ) : ℝ) - x < 0)]
    linarith
  · have h1 : x + 2 / M₃ < ((ℓ : ℤ) : ℝ) := by
      have hc : ((⌈x + 2 / M₃⌉ : ℤ) : ℝ) < ((ℓ : ℤ) : ℝ) := by exact_mod_cast h
      have hf := Int.le_ceil (x + 2 / M₃); linarith
    rw [abs_of_pos (by linarith : 0 < ((ℓ : ℤ) : ℝ) - x)]
    linarith

/-- Cardinality of the resonant index set: at most `4/M₃ + 3` integers. -/
lemma card_resonant_le (M₃ x : ℝ) (hM₃ : 0 < M₃) :
    ((Finset.Icc ⌊x - 2 / M₃⌋ ⌈x + 2 / M₃⌉).card : ℝ) ≤ 4 / M₃ + 3 := by
  set n : ℤ := ⌈x + 2 / M₃⌉ + 1 - ⌊x - 2 / M₃⌋ with hn
  rw [Int.card_Icc]
  rcases le_or_gt ⌊x - 2 / M₃⌋ ⌈x + 2 / M₃⌉ with h | h
  · have hnn : (0 : ℤ) ≤ n := by rw [hn]; omega
    have hgoal : (((n.toNat : ℕ)) : ℝ) = (n : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hnn)
    rw [hgoal]
    have hb : ((⌈x + 2 / M₃⌉ : ℤ) : ℝ) < x + 2 / M₃ + 1 := Int.ceil_lt_add_one _
    have ha : x - 2 / M₃ - 1 < ((⌊x - 2 / M₃⌋ : ℤ) : ℝ) := Int.sub_one_lt_floor _
    rw [hn]; push_cast
    have hsum : ((⌈x + 2 / M₃⌉ : ℤ) : ℝ) + 1 - ((⌊x - 2 / M₃⌋ : ℤ) : ℝ)
        < 2 * (2 / M₃) + 3 := by linarith [hb, ha]
    have heq : (2:ℝ) * (2 / M₃) + 3 = 4 / M₃ + 3 := by ring
    linarith [hsum, heq]
  · have hnp : n ≤ 0 := by rw [hn]; omega
    have hgoal : (n.toNat : ℕ) = 0 := Int.toNat_of_nonpos hnp
    rw [hgoal]
    push_cast
    have : 0 < 4 / M₃ + 3 := by positivity
    linarith

/-- Bound on the resonance weight: `‖T(x)‖ ≤ V (4/M₃ + 3)`. -/
lemma norm_Twt_le {K M₃ V : ℝ} (hV : ∀ y : ℝ, ‖psi1hat K y‖ ≤ V) (hVnn : 0 ≤ V)
    (hM₃ : 0 < M₃) (x : ℝ) : ‖Twt K M₃ x‖ ≤ V * (4 / M₃ + 3) := by
  rw [Twt_eq_finsum K M₃ x hM₃]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ ℓ ∈ Finset.Icc ⌊x - 2 / M₃⌋ ⌈x + 2 / M₃⌉,
        ‖(if |(ℓ : ℝ) - x| ≤ 2 / M₃ then psi1hat K (M₃ * ((ℓ : ℝ) - x)) else 0)‖
      ≤ ∑ _ℓ ∈ Finset.Icc ⌊x - 2 / M₃⌋ ⌈x + 2 / M₃⌉, V := by
        apply Finset.sum_le_sum; intro ℓ _
        by_cases hc : |(ℓ : ℝ) - x| ≤ 2 / M₃
        · rw [if_pos hc]; exact hV _
        · rw [if_neg hc, norm_zero]; exact hVnn
    _ = V * ((Finset.Icc ⌊x - 2 / M₃⌋ ⌈x + 2 / M₃⌉).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ V * (4 / M₃ + 3) :=
        mul_le_mul_of_nonneg_left (card_resonant_le M₃ x hM₃) hVnn

/-! ### A global bound for `ghatRes` -/

lemma norm_Bsum_le {M₂ : ℝ} (hM₂ : 0 < M₂) {f : ℝ → ℝ} (hfnn : ∀ u, 0 ≤ f u) (y : ℝ) :
    ‖Bsum f M₂ y‖ ≤ 4 * M₂ ^ 2 * (∫ u, f u) := by
  have hF : ∀ z : ℝ, ‖Fhat f z‖ ≤ ∫ u, f u := by
    intro z
    unfold Fhat
    rw [Real.fourier_eq (fun u : ℝ => (f u : ℂ)) z]
    refine (VectorFourier.norm_fourierIntegral_le_integral_norm (e := 𝐞) (μ := volume)
      (L := innerₗ ℝ) (f := fun u : ℝ => (f u : ℂ)) (w := z)).trans ?_
    refine le_of_eq ?_
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    change ‖(((f u : ℝ)) : ℂ)‖ = f u
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hfnn u)]
  unfold Bsum
  refine (norm_sum_le _ _).trans ?_
  calc ∑ m₂ ∈ R2 M₂, ‖(((m₂ : ℝ)) : ℂ) * Fhat f ((m₂ : ℝ) * y)‖
      = ∑ m₂ ∈ R2 M₂, ((m₂ : ℝ)) * ‖Fhat f ((m₂ : ℝ) * y)‖ := by
        refine Finset.sum_congr rfl (fun m₂ hm₂ => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (R2_pos hM₂ hm₂)]
    _ ≤ ∑ m₂ ∈ R2 M₂, ((m₂ : ℝ)) * (∫ u, f u) := by
        apply Finset.sum_le_sum; intro m₂ hm₂
        exact mul_le_mul_of_nonneg_left (hF _) (R2_pos hM₂ hm₂).le
    _ = (∑ m₂ ∈ R2 M₂, ((m₂ : ℝ))) * (∫ u, f u) := by rw [Finset.sum_mul]
    _ ≤ (4 * M₂ ^ 2) * (∫ u, f u) :=
        mul_le_mul_of_nonneg_right (sum_R2_le M₂ hM₂) (integral_nonneg hfnn)

/-- Global pointwise bound for `ghatRes`. -/
lemma norm_ghatRes_le {K M₁ M₂ M₃ V : ℝ} (hV : ∀ y : ℝ, ‖psi1hat K y‖ ≤ V) (hVnn : 0 ≤ V)
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃) {f : ℝ → ℝ} (hfnn : ∀ u, 0 ≤ f u)
    (ξ : ℝ) :
    ‖ghatRes K M₁ M₂ M₃ f ξ‖ ≤
      8 * ((4 * M₂ ^ 2 * (∫ u, f u)) * (M₃ * (V * (4 / M₃ + 3)))) := by
  have hXnn : (0 : ℝ) ≤ (4 * M₂ ^ 2 * (∫ u, f u)) * (M₃ * (V * (4 / M₃ + 3))) := by
    have h1 : (0:ℝ) ≤ ∫ u, f u := integral_nonneg hfnn
    have h2 : 0 < 4 / M₃ + 3 := by positivity
    positivity
  rw [ghatRes_eq_Twt]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ m₁ : ℤ,
      ‖((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
        ((M₃ : ℂ) * Twt K M₃ (ξ / (m₁ : ℝ)))‖
      ≤ (1 / |(m₁ : ℝ)|) * ((4 * M₂ ^ 2 * (∫ u, f u)) * (M₃ * (V * (4 / M₃ + 3)))) := by
    intro m₁
    have h1 : ‖((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹‖ = 1 / |(m₁ : ℝ)| := by
      simp [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_abs]
    have h4 : ‖((M₃ : ℝ) : ℂ)‖ = M₃ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM₃]
    simp only [norm_mul, h1, h4]
    have hT := norm_Twt_le hV hVnn hM₃ (ξ / (m₁ : ℝ))
    have hB := norm_Bsum_le hM₂ hfnn (ξ / (m₁ : ℝ))
    have hc1 : (0 : ℝ) ≤ 1 / |(m₁ : ℝ)| := by positivity
    have hK2 : (0 : ℝ) ≤ 4 * M₂ ^ 2 * (∫ u, f u) := by
      have : (0:ℝ) ≤ ∫ u, f u := integral_nonneg hfnn
      positivity
    have e1 : 1 / |(m₁ : ℝ)| * ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖
        ≤ 1 / |(m₁ : ℝ)| * (4 * M₂ ^ 2 * (∫ u, f u)) :=
      mul_le_mul_of_nonneg_left hB hc1
    have e2 : M₃ * ‖Twt K M₃ (ξ / (m₁ : ℝ))‖ ≤ M₃ * (V * (4 / M₃ + 3)) :=
      mul_le_mul_of_nonneg_left hT hM₃.le
    calc 1 / |(m₁ : ℝ)| * ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ * (M₃ * ‖Twt K M₃ (ξ / (m₁ : ℝ))‖)
        ≤ (1 / |(m₁ : ℝ)| * (4 * M₂ ^ 2 * (∫ u, f u))) * (M₃ * (V * (4 / M₃ + 3))) :=
          mul_le_mul e1 e2 (mul_nonneg hM₃.le (norm_nonneg _)) (mul_nonneg hc1 hK2)
      _ = (1 / |(m₁ : ℝ)|) * ((4 * M₂ ^ 2 * (∫ u, f u)) * (M₃ * (V * (4 / M₃ + 3)))) := by ring
  calc ∑ m₁ ∈ R1 M₁, ‖((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
        ((M₃ : ℂ) * Twt K M₃ (ξ / (m₁ : ℝ)))‖
      ≤ ∑ m₁ ∈ R1 M₁, (1 / |(m₁ : ℝ)|) *
          ((4 * M₂ ^ 2 * (∫ u, f u)) * (M₃ * (V * (4 / M₃ + 3)))) :=
        Finset.sum_le_sum (fun m₁ _ => hterm m₁)
    _ = (∑ m₁ ∈ R1 M₁, 1 / |(m₁ : ℝ)|) *
          ((4 * M₂ ^ 2 * (∫ u, f u)) * (M₃ * (V * (4 / M₃ + 3)))) := by
        rw [Finset.sum_mul]
    _ ≤ 8 * ((4 * M₂ ^ 2 * (∫ u, f u)) * (M₃ * (V * (4 / M₃ + 3)))) :=
        mul_le_mul_of_nonneg_right (sum_inv_abs_R1_le M₁ hM₁) hXnn

/-- `Bsum f M₂` is continuous for continuous compactly supported `f`. -/
lemma continuous_Bsum {M₂ : ℝ} {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    Continuous (fun u => Bsum f M₂ u) := by
  unfold Bsum
  refine continuous_finsetSum _ (fun m₂ _ => ?_)
  have h1 : Continuous (fun u : ℝ => ((m₂ : ℝ) : ℂ) * Fhat f ((m₂ : ℝ) * u)) := by
    refine Continuous.mul continuous_const ?_
    exact (continuous_fhat hf hcs).comp (continuous_const.mul continuous_id)
  exact h1

/-- `ghatRes` is measurable. -/
lemma measurable_ghatRes {K M₁ M₂ M₃ : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) : Measurable (ghatRes K M₁ M₂ M₃ f) := by
  rw [funext (fun ξ => ghatRes_eq_Twt K M₁ M₂ M₃ f ξ)]
  refine Finset.measurable_sum _ (fun m₁ _ => ?_)
  refine Measurable.mul (Measurable.mul measurable_const ?_) ?_
  · exact (continuous_Bsum hf hcs).measurable.comp (measurable_id.div_const _)
  · refine Measurable.mul measurable_const ?_
    exact (measurable_Twt K M₃).comp (measurable_id.div_const _)

theorem region_II_resonant {C₀ K T₀ : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K) (hT₀ : 1 ≤ T₀)
    (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∀ Mbig M₁ M₂ M₃ : ℝ,
        1 ≤ Mbig → 1 ≤ M₃ → 0 < M₁ → M₁ ≤ Mbig → 0 < M₂ → M₂ ≤ Mbig → M₃ ≤ Mbig →
        Mbig ≤ T ^ 4 →
        (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6))
            \ (Set.Icc (-(T ^ (min δ 1 / 2) * M₁ / M₃)) (T ^ (min δ 1 / 2) * M₁ / M₃)),
            ‖ghatRes K M₁ M₂ M₃ f ξ‖ ^ 2) ≤
          C' * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := by
  obtain ⟨Ch, hChpos, hhigh⟩ := region_II_resonant_high hK δ hδ c
  obtain ⟨Cl, hClpos, hlow⟩ := region_II_resonant_low hK δ hδ c
  obtain ⟨V, hVpos, hV0⟩ := psi1hat_decay K hK 0
  have hV : ∀ y : ℝ, ‖psi1hat K y‖ ≤ V := fun y => by simpa using hV0 y
  refine ⟨(Ch + Cl) + 1, by positivity, ?_⟩
  intro T hT f hf hfnn hsupp Λ hΛ hdec hcompat Mbig M₁ M₂ M₃
    hMb1 hM₃1 hM₁ hM₁M hM₂ hM₂M hM₃M hMbT
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
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_ghatRes_le hV hVpos.le hM₁ hM₂ (lt_of_lt_of_le zero_lt_one hM₃1) hfnn ξ) 2
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
  have hlo := hlow T Λ hT1 hΛ Mbig M₁ M₂ M₃ hMb1 hM₃1 hM₁ hM₁M hM₂ hM₂M hM₃M hMbT f hf hcs hdec
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
