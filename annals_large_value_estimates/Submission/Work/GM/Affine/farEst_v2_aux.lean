import Mathlib
import Submission.Work.GM.Affine.FarMass_defs
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.region_II_defs
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.ghatFar_eq_sum_Wfar
import Submission.Work.GM.Affine.bsum_far_le_winmass
import Submission.Work.GM.Affine.card_mul_pairs_le
import Submission.Work.GM.Affine.window_integral_Bsum
import Submission.Work.GM.Affine.farHprof_defs
import Submission.Work.GM.Affine.farHprof_helpers
import Submission.Work.GM.Affine.tail_part_bound
import Submission.Work.GM.Affine.ghatFar_split_win_tail
import Submission.Work.GM.Affine.farTauWin_aux
import Submission.Work.GM.Affine.WinMass_ge_hprof
import Submission.Work.GM.Affine.WindowFar_sharp_v2
import Submission.Work.GM.Affine.far_wsum_lattice_bound

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.GM.Affine

noncomputable section

/-- With the threshold `B = 2` the window weight `Wwin` vanishes identically (the `ℓ`-range
`2/M₃ < |ℓ - y| ≤ 2/M₃` is empty). -/
lemma Wwin_two_eq_zero (K M₃ y : ℝ) : Wwin K M₃ 2 y = 0 := by
  unfold Wwin
  have h0 : ∀ ℓ : ℤ,
      (if 2 / M₃ < |(ℓ : ℝ) - y| ∧ |(ℓ : ℝ) - y| ≤ 2 / M₃ then
        psi1hat K (M₃ * ((ℓ : ℝ) - y)) else 0 : ℂ) = 0 := by
    intro ℓ
    rw [if_neg (fun hc => absurd hc.2 (not_le.mpr hc.1))]
  have h : (∑' ℓ : ℤ,
      (if 2 / M₃ < |(ℓ : ℝ) - y| ∧ |(ℓ : ℝ) - y| ≤ 2 / M₃ then
        psi1hat K (M₃ * ((ℓ : ℝ) - y)) else 0 : ℂ)) = 0 := by
    rw [tsum_congr h0, tsum_zero]
  rw [h, mul_zero]

lemma Wtail_two_eq_Wfar (K M₃ y : ℝ) : Wtail K M₃ 2 y = Wfar K M₃ y := by
  unfold Wtail Wfar
  congr 1
  refine tsum_congr (fun ℓ => ?_)
  by_cases h : 2 / M₃ < |(ℓ : ℝ) - y|
  · rw [if_pos ⟨h, h⟩, if_pos h]
  · rw [if_neg (fun hc => h hc.2), if_neg h]

/-- `Wwin` is a measurable function of its last argument. -/
lemma measurable_Wwin (K M₃ B : ℝ) : Measurable (fun y : ℝ => Wwin K M₃ B y) := by
  unfold Wwin
  refine Measurable.mul measurable_const ?_
  refine Measurable.tsum fun ℓ => ?_
  refine Measurable.ite ?_ ?_ measurable_const
  · have hg : Measurable (fun y : ℝ => |((ℓ : ℝ) - y)|) := by fun_prop
    exact (measurableSet_lt measurable_const hg).inter (measurableSet_le hg measurable_const)
  · apply Continuous.measurable
    exact (psi1hat_continuous K).comp
      (continuous_const.mul (continuous_const.sub continuous_id))

/-- `Wtail` is a measurable function of its last argument. -/
lemma measurable_Wtail (K M₃ B : ℝ) : Measurable (fun y : ℝ => Wtail K M₃ B y) := by
  unfold Wtail
  refine Measurable.mul measurable_const ?_
  refine Measurable.tsum fun ℓ => ?_
  refine Measurable.ite ?_ ?_ measurable_const
  · have hg : Measurable (fun y : ℝ => |((ℓ : ℝ) - y)|) := by fun_prop
    exact (measurableSet_lt measurable_const hg).inter (measurableSet_lt measurable_const hg)
  · apply Continuous.measurable
    exact (psi1hat_continuous K).comp
      (continuous_const.mul (continuous_const.sub continuous_id))

/-- The two `m₁`-sums of `Bsum` against `Wwin`/`Wtail` are measurable. -/
theorem measurable_win_tail_sums (K M₁ M₂ M₃ B : ℝ) (f : ℝ → ℝ) :
    Measurable (fun ξ : ℝ => ∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ *
        Bsum f M₂ (ξ / (m₁ : ℝ)) * Wwin K M₃ B (ξ / (m₁ : ℝ)))
    ∧ Measurable (fun ξ : ℝ => ∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ *
        Bsum f M₂ (ξ / (m₁ : ℝ)) * Wtail K M₃ B (ξ / (m₁ : ℝ))) := by
  constructor
  · refine Finset.measurable_sum _ fun m₁ _ => ?_
    exact (measurable_const.mul
      ((measurable_Bsum f M₂).comp (measurable_id.div measurable_const))).mul
      ((measurable_Wwin K M₃ B).comp (measurable_id.div measurable_const))
  · refine Finset.measurable_sum _ fun m₁ _ => ?_
    exact (measurable_const.mul
      ((measurable_Bsum f M₂).comp (measurable_id.div measurable_const))).mul
      ((measurable_Wtail K M₃ B).comp (measurable_id.div measurable_const))


/-! ## Elementary helpers (copies of the corresponding lemmas of `far_part_assembly`, which
cannot be imported here because its import closure clashes with ours) -/

lemma norm_Fhat_le_integral' (f : ℝ → ℝ) (y : ℝ) :
    ‖Fhat f y‖ ≤ ∫ u, ‖f u‖ := by
  rw [Fhat, Real.fourier_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  simp

lemma norm_Bsum_le_sum' (M₂ u : ℝ) (f : ℝ → ℝ) :
    ‖Bsum f M₂ u‖ ≤ (∑ m₂ ∈ R2 M₂, (m₂ : ℝ)) * (∫ v, ‖f v‖) := by
  rw [Bsum]
  calc ‖∑ m₂ ∈ R2 M₂, ((m₂ : ℝ) : ℂ) * Fhat f ((m₂ : ℝ) * u)‖
      ≤ ∑ m₂ ∈ R2 M₂, ‖((m₂ : ℝ) : ℂ) * Fhat f ((m₂ : ℝ) * u)‖ := norm_sum_le _ _
    _ = ∑ m₂ ∈ R2 M₂, (m₂ : ℝ) * ‖Fhat f ((m₂ : ℝ) * u)‖ := by
        refine Finset.sum_congr rfl (fun m₂ hm₂ => ?_)
        have hm1 : (1 : ℤ) ≤ m₂ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm₂).1).1
        have hm1R : (1 : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast hm1
        rw [norm_mul, show ‖((m₂ : ℝ) : ℂ)‖ = |(m₂ : ℝ)| from by simp,
          abs_of_nonneg (by linarith)]
    _ ≤ ∑ m₂ ∈ R2 M₂, (m₂ : ℝ) * (∫ v, ‖f v‖) :=
        Finset.sum_le_sum (fun m₂ hm₂ => by
          have hm1 : (1 : ℤ) ≤ m₂ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm₂).1).1
          have hm1R : (1 : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast hm1
          exact mul_le_mul_of_nonneg_left (norm_Fhat_le_integral' f _) (by linarith))
    _ = (∑ m₂ ∈ R2 M₂, (m₂ : ℝ)) * (∫ v, ‖f v‖) := by rw [Finset.sum_mul]

lemma norm_weight_sum_le {T M₁ M₂ M₃ Cw Bb : ℝ} {f : ℝ → ℝ}
    (hM₁ : 0 < M₁) (hM₃ : 1 ≤ M₃) (hCw : 0 ≤ Cw)
    (hBb : 0 ≤ Bb) (hBsub : ∀ u : ℝ, ‖Bsum f M₂ u‖ ≤ Bb)
    {Wt : ℝ → ℂ} (hWb : ∀ y : ℝ, ‖Wt y‖ ≤ Cw * M₃ * (1 + |y|) ^ 2)
    {ξ : ℝ} (hξ : |ξ| ≤ T ^ 6) :
    ‖∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
        Wt (ξ / (m₁ : ℝ))‖
      ≤ (∑ m₁ ∈ R1 M₁, |(m₁ : ℝ)|⁻¹) * (Bb * (Cw * M₃ * (1 + T ^ 6 / M₁) ^ 2)) := by
  have hM₃pos : 0 < M₃ := lt_of_lt_of_le zero_lt_one hM₃
  calc ‖∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
        Wt (ξ / (m₁ : ℝ))‖
      ≤ ∑ m₁ ∈ R1 M₁, ‖((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
          Wt (ξ / (m₁ : ℝ))‖ := norm_sum_le _ _
    _ = ∑ m₁ ∈ R1 M₁, |(m₁ : ℝ)|⁻¹ * ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ * ‖Wt (ξ / (m₁ : ℝ))‖ := by
        refine Finset.sum_congr rfl (fun m₁ _ => ?_)
        rw [norm_mul, norm_mul, norm_inv]; simp
    _ ≤ ∑ m₁ ∈ R1 M₁, |(m₁ : ℝ)|⁻¹ * Bb * (Cw * M₃ * (1 + T ^ 6 / M₁) ^ 2) := by
        refine Finset.sum_le_sum (fun m₁ hm₁ => ?_)
        have hMm : M₁ < |(m₁ : ℝ)| := (Finset.mem_filter.mp hm₁).2
        have hq : |ξ / (m₁ : ℝ)| ≤ T ^ 6 / M₁ := by
          rw [abs_div]
          have h2 : |ξ| / |(m₁ : ℝ)| ≤ |ξ| / M₁ :=
            div_le_div_of_nonneg_left (abs_nonneg ξ) hM₁ hMm.le
          have h3 : |ξ| / M₁ ≤ T ^ 6 / M₁ := div_le_div_of_nonneg_right hξ hM₁.le
          linarith
        have h3 : ‖Wt (ξ / (m₁ : ℝ))‖ ≤ Cw * M₃ * (1 + T ^ 6 / M₁) ^ 2 := by
          refine le_trans (hWb _) ?_
          have h1 : (1 + |ξ / (m₁ : ℝ)|) ^ 2 ≤ (1 + T ^ 6 / M₁) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (by linarith) 2
          exact mul_le_mul_of_nonneg_left h1 (mul_nonneg hCw hM₃pos.le)
        have h4 : ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ ≤ Bb := hBsub _
        have h5 : 0 ≤ |(m₁ : ℝ)|⁻¹ := inv_nonneg.mpr (abs_nonneg _)
        exact mul_le_mul (mul_le_mul_of_nonneg_left h4 h5) h3 (norm_nonneg _) (mul_nonneg h5 hBb)
    _ = (∑ m₁ ∈ R1 M₁, |(m₁ : ℝ)|⁻¹) * (Bb * (Cw * M₃ * (1 + T ^ 6 / M₁) ^ 2)) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]; ring

lemma integrableOn_sq_of_bound {A : Set ℝ} {g : ℝ → ℂ} {C : ℝ}
    (hA : MeasurableSet A) (hfin : volume A < ⊤) (hm : Measurable g)
    (hb : ∀ ξ ∈ A, ‖g ξ‖ ≤ C) :
    IntegrableOn (fun ξ : ℝ => ‖g ξ‖ ^ 2) A := by
  refine IntegrableOn.of_bound hfin ((hm.norm.pow_const 2)).aestronglyMeasurable (C ^ 2) ?_
  rw [MeasureTheory.ae_restrict_iff' hA]
  refine Filter.Eventually.of_forall (fun ξ hξ => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hb ξ hξ) 2

lemma far_glue {K M₁ M₂ M₃ : ℝ} {f : ℝ → ℝ} {G₁ G₂ : ℝ → ℂ} {A : Set ℝ} {X Y : ℝ}
    (hsplit : ∀ ξ : ℝ, ghatFar K M₁ M₂ M₃ f ξ = G₁ ξ + G₂ ξ)
    (hms₁ : Measurable G₁) (hms₂ : Measurable G₂) (hA : MeasurableSet A)
    (hint₁ : IntegrableOn (fun ξ : ℝ => ‖G₁ ξ‖ ^ 2) A)
    (hint₂ : IntegrableOn (fun ξ : ℝ => ‖G₂ ξ‖ ^ 2) A)
    (h1 : ∫ ξ in A, ‖G₁ ξ‖ ^ 2 ≤ X) (h2 : ∫ ξ in A, ‖G₂ ξ‖ ^ 2 ≤ Y) :
    ∫ ξ in A, ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2 ≤ 2 * X + 2 * Y := by
  have hpt : ∀ ξ : ℝ, ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2 ≤ 2 * ‖G₁ ξ‖ ^ 2 + 2 * ‖G₂ ξ‖ ^ 2 := by
    intro ξ
    rw [hsplit ξ]
    have hle : ‖G₁ ξ + G₂ ξ‖ ≤ ‖G₁ ξ‖ + ‖G₂ ξ‖ := norm_add_le _ _
    nlinarith [hle, norm_nonneg (G₁ ξ), norm_nonneg (G₂ ξ), norm_nonneg (G₁ ξ + G₂ ξ),
      sq_nonneg (‖G₁ ξ‖ - ‖G₂ ξ‖)]
  have hmeas : AEStronglyMeasurable (fun ξ : ℝ => ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2)
      (volume.restrict A) := by
    have heq : (fun ξ : ℝ => ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2)
        = fun ξ : ℝ => ‖G₁ ξ + G₂ ξ‖ ^ 2 := by
      funext ξ; rw [hsplit ξ]
    rw [heq]
    exact ((hms₁.add hms₂).norm.pow_const 2).aestronglyMeasurable
  have hdom : Integrable (fun ξ : ℝ => 2 * ‖G₁ ξ‖ ^ 2 + 2 * ‖G₂ ξ‖ ^ 2) (volume.restrict A) :=
    (hint₁.const_mul 2).add (hint₂.const_mul 2)
  have hintg : Integrable (fun ξ : ℝ => ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2) (volume.restrict A) :=
    hdom.mono' hmeas (Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hpt ξ)
  have hmono : ∫ ξ in A, ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2
      ≤ ∫ ξ in A, (2 * ‖G₁ ξ‖ ^ 2 + 2 * ‖G₂ ξ‖ ^ 2) :=
    setIntegral_mono_on hintg hdom hA (fun ξ _ => hpt ξ)
  have hsum : ∫ ξ in A, (2 * ‖G₁ ξ‖ ^ 2 + 2 * ‖G₂ ξ‖ ^ 2)
      = 2 * (∫ ξ in A, ‖G₁ ξ‖ ^ 2) + 2 * (∫ ξ in A, ‖G₂ ξ‖ ^ 2) := by
    rw [integral_add (hint₁.const_mul 2) (hint₂.const_mul 2), integral_const_mul,
      integral_const_mul]
  linarith [hmono, hsum, h1, h2]

/-- **The target.**  See the module docstring for the accounting. -/
theorem farEst_v2_aux {C₀ K T₀ : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K) (hT₀ : 1 ≤ T₀)
    (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        supf f ≤ Λ →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∀ Mbig M₁ M₂ M₃ : ℝ,
        1 ≤ Mbig → 1 ≤ M₃ → 0 < M₁ → M₁ ≤ Mbig → 0 < M₂ → M₂ ≤ Mbig → M₃ ≤ Mbig →
        Mbig ≤ T ^ 4 →
        (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6))
            \ (Set.Icc (-(T ^ (min δ 1 / 2) * M₁ / M₃)) (T ^ (min δ 1 / 2) * M₁ / M₃)),
            ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2) ≤
          C' * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := by
  -- ==================== the two analytic inputs ====================
  obtain ⟨cwin, hcwinpos, hwin⟩ := WinMass_ge_hprof (C₀ := C₀) (K := K) hC₀ hK
  -- ==================== constants ====================
  set δ' : ℝ := min δ 1 with hδ'def
  have hδ'pos : 0 < δ' := lt_min hδ one_pos
  have hδ'le : δ' ≤ δ := min_le_left _ _
  have hδ'le1 : δ' ≤ 1 := min_le_right _ _
  set ε₀ : ℝ := δ' / 32 with hε₀def
  have hε₀pos : 0 < ε₀ := by rw [hε₀def]; linarith
  have hε₀δ : ε₀ * (1 + ε₀) + 6 * ε₀ ≤ δ := by
    rw [hε₀def]
    nlinarith [hδ'pos, hδ'le, hδ'le1]
  set η : ℝ := δ' / 2 with hηdef
  have hηpos : 0 < η := by rw [hηdef]; linarith
  have hηeq : η = min δ 1 / 2 := by rw [hηdef, hδ'def]
  have hε₀η : ε₀ < η := by rw [hε₀def, hηdef]; linarith
  have hηε : 0 < η - ε₀ := by linarith
  set N : ℕ := ⌈4 / ε₀⌉₊ + 2 with hNdef
  have hN3 : 3 ≤ N := by
    rw [hNdef]
    have h1 : 1 ≤ ⌈4 / ε₀⌉₊ := Nat.ceil_pos.mpr (by positivity)
    omega
  have hN4 : 4 ≤ ε₀ * (((N : ℕ) : ℝ) - 1) := by
    rw [hNdef]
    push_cast
    have hle : 4 / ε₀ ≤ ((⌈4 / ε₀⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h := mul_le_mul_of_nonneg_left hle hε₀pos.le
    rw [mul_div_cancel₀ (4 : ℝ) hε₀pos.ne'] at h
    linarith
  obtain ⟨Ctail, hCtailpos, htail⟩ := tail_part_bound (K := K) hK N hN3
  obtain ⟨Cwinsharp, hCwinsharppos, hwinsharp⟩ :=
    WindowFar_sharp_v2 (C₀ := C₀) (K := K) hC₀ hK ε₀ hε₀pos
  obtain ⟨Cwf, hCwfpos, hCwf⟩ := far_wsum_lattice_bound K hK
  set Tthr : ℝ := max T₀ (max (2 ^ (1 / ε₀)) (2 ^ (1 / (η - ε₀)))) with hTthrdef
  have hTthr₁ : 1 ≤ Tthr := le_trans hT₀ (le_max_left _ _)
  have hTthr₂ : (2 : ℝ) ^ (1 / ε₀) ≤ Tthr := le_trans (le_max_left _ _) (le_max_right _ _)
  have hTthr₃ : (2 : ℝ) ^ (1 / (η - ε₀)) ≤ Tthr := le_trans (le_max_right _ _) (le_max_right _ _)
  set C' : ℝ := max (2 * (Ctail / cwin) * Tthr ^ 8)
    (2 * Cwinsharp + 2 * (Ctail / cwin)) + 1 with hC'def
  have hC'pos : 0 < C' := by
    rw [hC'def]
    have hmax : (0 : ℝ) ≤ max (2 * (Ctail / cwin) * Tthr ^ 8)
        (2 * Cwinsharp + 2 * (Ctail / cwin)) := le_max_of_le_left (by positivity)
    linarith
  refine ⟨C', hC'pos, ?_⟩
  -- ==================== the main argument ====================
  intro T hT f hf hfnn hSupp Λ hΛ hdec hsupf hΛb Mbig M₁ M₂ M₃
    hMb1 hM₃1 hM₁ hM₁M hM₂ hM₂M hM₃M hMbT
  have hT1 : (1 : ℝ) ≤ T := le_trans hT₀ hT
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hM₃pos : 0 < M₃ := lt_of_lt_of_le zero_lt_one hM₃1
  have hcs : HasCompactSupport f := hasCompactSupport_of_suppHyp_far hSupp
  have hTδ1 : (1 : ℝ) ≤ T ^ δ := Real.one_le_rpow hT1 hδ.le
  have hWnn : (0 : ℝ) ≤ WinMass f M₂ M₃ :=
    tsum_nonneg (fun ℓ => integral_nonneg (fun τ => sq_nonneg _))
  have hAnn : (0 : ℝ) ≤ M₁ + M₃ := by linarith
  -- the input (★★), in the form needed
  have hwin' : (∫ s, (Hsum M₂ f s) ^ 2) ≤ (1 / cwin) * WinMass f M₂ M₃ := by
    have h0 := hwin M₂ M₃ hM₂ hM₃1 f hf hfnn hSupp
    have heq : (∫ u, (Hprof f M₂ u) ^ 2) = ∫ s, (Hsum M₂ f s) ^ 2 := rfl
    rw [← heq]
    have hdiv : (1 / cwin) * WinMass f M₂ M₃ = WinMass f M₂ M₃ / cwin := by ring
    rw [hdiv, le_div_iff₀ hcwinpos, mul_comm]
    exact h0
  -- the region of integration
  set A : Set ℝ := (Set.Icc (-(T ^ 6)) (T ^ 6))
      \ (Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃)) with hAdef
  have hAmeas : MeasurableSet A := by rw [hAdef]; exact measurableSet_Icc.diff measurableSet_Icc
  have hAfin : volume A < ⊤ := by
    have hsub : A ⊆ Set.Icc (-(T ^ 6)) (T ^ 6) := by
      rw [hAdef]; exact Set.diff_subset
    refine lt_of_le_of_lt (measure_mono hsub) ?_
    rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  have hAξ : ∀ ξ ∈ A, |ξ| ≤ T ^ 6 := by
    intro ξ hξ
    rw [hAdef] at hξ
    have h1 : ξ ∈ Set.Icc (-(T ^ 6)) (T ^ 6) := hξ.1
    rw [Set.mem_Icc] at h1
    rw [abs_le]
    exact ⟨h1.1, h1.2⟩
  by_cases hcase : T ≤ Tthr
  · -- ==================== Case A: B = 2 (small T) ====================
    have hsplit : ∀ ξ : ℝ, ghatFar K M₁ M₂ M₃ f ξ =
        (∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
            Wtail K M₃ 2 (ξ / (m₁ : ℝ))) + 0 := by
      intro ξ
      rw [ghatFar_split_win_tail (B := 2) hK hM₁ hM₂ hM₃pos hf hcs ξ, add_zero]
      have hzero : (∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
          Wwin K M₃ 2 (ξ / (m₁ : ℝ))) = 0 :=
        Finset.sum_eq_zero (fun m₁ _ => by rw [Wwin_two_eq_zero]; ring)
      rw [hzero, zero_add]
    have hms₁ : Measurable (fun ξ : ℝ => ∑ m₁ ∈ R1 M₁,
        ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
          Wtail K M₃ 2 (ξ / (m₁ : ℝ))) := (measurable_win_tail_sums K M₁ M₂ M₃ 2 f).2
    have hBb : (0 : ℝ) ≤ (∑ m₂ ∈ R2 M₂, (m₂ : ℝ)) * (∫ v, ‖f v‖) := by
      have h1 : (0 : ℝ) ≤ ∑ m₂ ∈ R2 M₂, (m₂ : ℝ) := by
        refine Finset.sum_nonneg (fun m₂ hm₂ => ?_)
        have h2 : (1 : ℤ) ≤ m₂ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm₂).1).1
        exact_mod_cast (by omega : (0 : ℤ) ≤ m₂)
      exact mul_nonneg h1 (integral_nonneg (fun v => norm_nonneg _))
    have hbnd : ∀ ξ ∈ A, ‖∑ m₁ ∈ R1 M₁,
        ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
          Wtail K M₃ 2 (ξ / (m₁ : ℝ))‖
        ≤ (∑ m₁ ∈ R1 M₁, |(m₁ : ℝ)|⁻¹) * (((∑ m₂ ∈ R2 M₂, (m₂ : ℝ)) * (∫ v, ‖f v‖)) *
            (Cwf * M₃ * (1 + T ^ 6 / M₁) ^ 2)) := by
      intro ξ hξ
      exact norm_weight_sum_le hM₁ hM₃1 hCwfpos.le hBb
        (fun u => norm_Bsum_le_sum' M₂ u f)
        (fun y => (hCwf M₃ 2 y hM₃1 (by norm_num)).2.1) (hAξ ξ hξ)
    have hint₁ : IntegrableOn (fun ξ : ℝ => ‖∑ m₁ ∈ R1 M₁,
        ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
          Wtail K M₃ 2 (ξ / (m₁ : ℝ))‖ ^ 2) A :=
      integrableOn_sq_of_bound hAmeas hAfin hms₁ hbnd
    have hint₂ : IntegrableOn (fun ξ : ℝ => ‖(0 : ℂ)‖ ^ 2) A :=
      integrableOn_sq_of_bound (C := 0) hAmeas hAfin measurable_const
        (fun ξ _ => by simp)
    have h1 : ∫ ξ in A, ‖∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
        Wtail K M₃ 2 (ξ / (m₁ : ℝ))‖ ^ 2
        ≤ Ctail * (M₁ * M₃ ^ 2 / 2 ^ (2 * (N - 1))) * ∫ s, (Hsum M₂ f s) ^ 2 := by
      have h := htail T η 2 M₁ M₂ M₃ hT1 hηpos (by norm_num) hM₁ hM₂ hM₃1 f hf hcs hfnn
      rwa [← hAdef] at h
    have h2 : ∫ ξ in A, ‖(0 : ℂ)‖ ^ 2 ≤ 0 := by simp
    have hglue := far_glue hsplit hms₁ measurable_const hAmeas hint₁ hint₂ h1 h2
    simp only [mul_zero, add_zero] at hglue
    -- arithmetic
    have hM₃T : M₃ ^ 2 ≤ Tthr ^ 8 := by
      have h1 : M₃ ≤ Tthr ^ 4 := le_trans hM₃M (le_trans hMbT (pow_le_pow_left₀ hTpos.le hcase 4))
      calc M₃ ^ 2 ≤ (Tthr ^ 4) ^ 2 := pow_le_pow_left₀ hM₃pos.le h1 2
        _ = Tthr ^ 8 := by ring
    have hTthr4 : (0 : ℝ) ≤ Tthr ^ 8 := by positivity
    have hkey : M₁ * M₃ ^ 2 / 2 ^ (2 * (N - 1)) ≤ (M₁ + M₃) * Tthr ^ 8 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ (2 * (N - 1)))]
      have h2 : (1 : ℝ) ≤ 2 ^ (2 * (N - 1)) := one_le_pow₀ (by norm_num)
      have h3 : M₁ * M₃ ^ 2 ≤ (M₁ + M₃) * Tthr ^ 8 := by
        have h4 : M₃ ^ 2 ≤ Tthr ^ 8 := hM₃T
        nlinarith [hM₁.le, h4, hM₃pos.le, hTthr4, hAnn]
      nlinarith [h3, h2, mul_nonneg hAnn hTthr4, hM₁.le, hM₃pos.le]
    have hI : (0 : ℝ) ≤ ∫ s, (Hsum M₂ f s) ^ 2 := integral_nonneg (fun s => sq_nonneg _)
    have hPnn : (0 : ℝ) ≤ (M₁ + M₃) * WinMass f M₂ M₃ := mul_nonneg hAnn hWnn
    have hA1 : 2 * (Ctail * (M₁ * M₃ ^ 2 / 2 ^ (2 * (N - 1))) * ∫ s, (Hsum M₂ f s) ^ 2)
        ≤ (2 * Ctail * Tthr ^ 8 / cwin) * ((M₁ + M₃) * WinMass f M₂ M₃) := by
      have hXY : Ctail * (M₁ * M₃ ^ 2 / 2 ^ (2 * (N - 1))) * ∫ s, (Hsum M₂ f s) ^ 2
          ≤ (Ctail * Tthr ^ 8 / cwin) * ((M₁ + M₃) * WinMass f M₂ M₃) := by
        have h5 := mul_le_mul (mul_le_mul_of_nonneg_left hkey hCtailpos.le) hwin' hI
          (by positivity : (0 : ℝ) ≤ Ctail * ((M₁ + M₃) * Tthr ^ 8))
        have h6 : Ctail * ((M₁ + M₃) * Tthr ^ 8) * ((1 / cwin) * WinMass f M₂ M₃)
            = (Ctail * Tthr ^ 8 / cwin) * ((M₁ + M₃) * WinMass f M₂ M₃) := by ring
        linarith [h5, h6.le, h6.ge]
      have h7 := mul_le_mul_of_nonneg_left hXY (by norm_num : (0 : ℝ) ≤ 2)
      have h8 : 2 * ((Ctail * Tthr ^ 8 / cwin) * ((M₁ + M₃) * WinMass f M₂ M₃))
          = (2 * Ctail * Tthr ^ 8 / cwin) * ((M₁ + M₃) * WinMass f M₂ M₃) := by ring
      linarith [h7, h8.le, h8.ge]
    have hA2 : (2 * Ctail * Tthr ^ 8 / cwin) ≤ C' := by
      rw [hC'def]
      have hEq : 2 * Ctail * Tthr ^ 8 / cwin = 2 * (Ctail / cwin) * Tthr ^ 8 := by ring
      linarith [le_max_left (2 * (Ctail / cwin) * Tthr ^ 8) (2 * Cwinsharp + 2 * (Ctail / cwin)),
        hEq.le, hEq.ge]
    calc ∫ ξ in A, ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2
        ≤ 2 * (Ctail * (M₁ * M₃ ^ 2 / 2 ^ (2 * (N - 1))) * ∫ s, (Hsum M₂ f s) ^ 2) := hglue
      _ ≤ (2 * Ctail * Tthr ^ 8 / cwin) * ((M₁ + M₃) * WinMass f M₂ M₃) := hA1
      _ ≤ C' * ((M₁ + M₃) * WinMass f M₂ M₃) := mul_le_mul_of_nonneg_right hA2 hPnn
      _ ≤ C' * ((M₁ + M₃) * WinMass f M₂ M₃) * T ^ δ := by
          simpa using mul_le_mul_of_nonneg_left hTδ1 (mul_nonneg hC'pos.le hPnn)
      _ = C' * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := by ring
  · -- ==================== Case B: B = T^ε₀ (large T) ====================
    have hTthrT : Tthr < T := lt_of_not_ge hcase
    set B : ℝ := T ^ ε₀ with hBdef
    have hB2 : (2 : ℝ) ≤ B := by
      rw [hBdef]
      have h2 : (2 : ℝ) ^ (1 / ε₀) < T := lt_of_le_of_lt hTthr₂ hTthrT
      have hpos : (0 : ℝ) ≤ 2 ^ (1 / ε₀) := le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
      have h3 := Real.rpow_lt_rpow hpos h2 hε₀pos
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) (1 / ε₀) ε₀,
        one_div_mul_cancel hε₀pos.ne', Real.rpow_one] at h3
      exact le_of_lt h3
    have hBpos : 0 < B := Real.rpow_pos_of_pos hTpos _
    have h2B : 2 * B ≤ T ^ η := by
      have h2 : (2 : ℝ) < T ^ (η - ε₀) := by
        have h3 : (2 : ℝ) ^ (1 / (η - ε₀)) < T := lt_of_le_of_lt hTthr₃ hTthrT
        have hpos : (0 : ℝ) ≤ 2 ^ (1 / (η - ε₀)) :=
          le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
        have h4 := Real.rpow_lt_rpow hpos h3 hηε
        rwa [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) (1 / (η - ε₀)) (η - ε₀),
          one_div_mul_cancel hηε.ne', Real.rpow_one] at h4
      have h5 := mul_lt_mul_of_pos_right h2 (Real.rpow_pos_of_pos hTpos ε₀)
      rw [← Real.rpow_add hTpos] at h5
      have h6 : η - ε₀ + ε₀ = η := by ring
      rw [h6] at h5
      linarith [h5]
    have hBδ : B ^ (1 + ε₀) * T ^ (6 * ε₀) ≤ T ^ δ := by
      have h1 : B ^ (1 + ε₀) = T ^ (ε₀ * (1 + ε₀)) := by
        rw [hBdef, Real.rpow_mul hTpos.le ε₀ (1 + ε₀)]
      rw [h1, ← Real.rpow_add hTpos (ε₀ * (1 + ε₀)) (6 * ε₀)]
      refine Real.rpow_le_rpow_of_exponent_le hT1 ?_
      linarith [hε₀δ]
    -- the split and the glue
    have hsplit : ∀ ξ : ℝ, ghatFar K M₁ M₂ M₃ f ξ =
        (∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
            Wwin K M₃ B (ξ / (m₁ : ℝ)))
          + (∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
            Wtail K M₃ B (ξ / (m₁ : ℝ))) :=
      fun ξ => ghatFar_split_win_tail (B := B) hK hM₁ hM₂ hM₃pos hf hcs ξ
    have hms₁ : Measurable (fun ξ : ℝ => ∑ m₁ ∈ R1 M₁,
        ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
          Wwin K M₃ B (ξ / (m₁ : ℝ))) := (measurable_win_tail_sums K M₁ M₂ M₃ B f).1
    have hms₂ : Measurable (fun ξ : ℝ => ∑ m₁ ∈ R1 M₁,
        ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
          Wtail K M₃ B (ξ / (m₁ : ℝ))) := (measurable_win_tail_sums K M₁ M₂ M₃ B f).2
    have hBb : (0 : ℝ) ≤ (∑ m₂ ∈ R2 M₂, (m₂ : ℝ)) * (∫ v, ‖f v‖) := by
      have h1 : (0 : ℝ) ≤ ∑ m₂ ∈ R2 M₂, (m₂ : ℝ) := by
        refine Finset.sum_nonneg (fun m₂ hm₂ => ?_)
        have h2 : (1 : ℤ) ≤ m₂ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm₂).1).1
        exact_mod_cast (by omega : (0 : ℤ) ≤ m₂)
      exact mul_nonneg h1 (integral_nonneg (fun v => norm_nonneg _))
    have hbnd₁ : ∀ ξ ∈ A, ‖∑ m₁ ∈ R1 M₁,
        ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
          Wwin K M₃ B (ξ / (m₁ : ℝ))‖
        ≤ (∑ m₁ ∈ R1 M₁, |(m₁ : ℝ)|⁻¹) * (((∑ m₂ ∈ R2 M₂, (m₂ : ℝ)) * (∫ v, ‖f v‖)) *
            (Cwf * M₃ * (1 + T ^ 6 / M₁) ^ 2)) := by
      intro ξ hξ
      exact norm_weight_sum_le hM₁ hM₃1 hCwfpos.le hBb
        (fun u => norm_Bsum_le_sum' M₂ u f)
        (fun y => (hCwf M₃ B y hM₃1 hB2).1) (hAξ ξ hξ)
    have hbnd₂ : ∀ ξ ∈ A, ‖∑ m₁ ∈ R1 M₁,
        ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
          Wtail K M₃ B (ξ / (m₁ : ℝ))‖
        ≤ (∑ m₁ ∈ R1 M₁, |(m₁ : ℝ)|⁻¹) * (((∑ m₂ ∈ R2 M₂, (m₂ : ℝ)) * (∫ v, ‖f v‖)) *
            (Cwf * M₃ * (1 + T ^ 6 / M₁) ^ 2)) := by
      intro ξ hξ
      exact norm_weight_sum_le hM₁ hM₃1 hCwfpos.le hBb
        (fun u => norm_Bsum_le_sum' M₂ u f)
        (fun y => (hCwf M₃ B y hM₃1 hB2).2.1) (hAξ ξ hξ)
    have hint₁ : IntegrableOn (fun ξ : ℝ => ‖∑ m₁ ∈ R1 M₁,
        ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
          Wwin K M₃ B (ξ / (m₁ : ℝ))‖ ^ 2) A :=
      integrableOn_sq_of_bound hAmeas hAfin hms₁ hbnd₁
    have hint₂ : IntegrableOn (fun ξ : ℝ => ‖∑ m₁ ∈ R1 M₁,
        ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
          Wtail K M₃ B (ξ / (m₁ : ℝ))‖ ^ 2) A :=
      integrableOn_sq_of_bound hAmeas hAfin hms₂ hbnd₂
    have h1 : ∫ ξ in A, ‖∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
        Wwin K M₃ B (ξ / (m₁ : ℝ))‖ ^ 2
        ≤ Cwinsharp * B ^ (1 + ε₀) * T ^ (6 * ε₀) * (M₁ + M₃) * WinMass f M₂ M₃ := by
      have h := hwinsharp T η B M₁ M₂ M₃ hT1 hηpos hB2 h2B hM₁ hM₂ hM₃1 f hf hfnn hSupp
      rwa [← hAdef] at h
    have h2 : ∫ ξ in A, ‖∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
        Wtail K M₃ B (ξ / (m₁ : ℝ))‖ ^ 2
        ≤ Ctail * (M₁ * M₃ ^ 2 / B ^ (2 * (N - 1))) * ∫ s, (Hsum M₂ f s) ^ 2 := by
      have h := htail T η B M₁ M₂ M₃ hT1 hηpos hB2 hM₁ hM₂ hM₃1 f hf hcs hfnn
      rwa [← hAdef] at h
    have hglue := far_glue hsplit hms₁ hms₂ hAmeas hint₁ hint₂ h1 h2
    -- arithmetic
    have hM₃T : M₃ ^ 2 ≤ T ^ 8 := by
      have h1 : M₃ ≤ T ^ 4 := le_trans hM₃M hMbT
      nlinarith [h1, hM₃pos]
    have hB8 : T ^ 8 ≤ B ^ (2 * (N - 1)) := by
      have hN1 : (1 : ℕ) ≤ N := by omega
      have hcast : ((2 * (N - 1) : ℕ) : ℝ) = 2 * (((N : ℕ) : ℝ) - 1) := by
        rw [Nat.cast_mul]
        have h1 : (((N - 1 : ℕ)) : ℝ) = ((N : ℕ) : ℝ) - 1 := by
          rw [Nat.cast_sub hN1, Nat.cast_one]
        rw [h1]; ring
      rw [hBdef, ← Real.rpow_natCast (T ^ ε₀) (2 * (N - 1)), hcast,
        ← Real.rpow_mul hTpos.le, ← Real.rpow_natCast T 8]
      refine Real.rpow_le_rpow_of_exponent_le hT1 ?_
      calc (8 : ℝ) = 2 * 4 := by norm_num
        _ ≤ 2 * (ε₀ * (((N : ℕ) : ℝ) - 1)) := mul_le_mul_of_nonneg_left hN4 (by norm_num)
        _ = ε₀ * (2 * (((N : ℕ) : ℝ) - 1)) := by ring
    have hI : (0 : ℝ) ≤ ∫ s, (Hsum M₂ f s) ^ 2 := integral_nonneg (fun s => sq_nonneg _)
    have hPnn : (0 : ℝ) ≤ (M₁ + M₃) * WinMass f M₂ M₃ := mul_nonneg hAnn hWnn
    have hQnn : (0 : ℝ) ≤ T ^ δ * ((M₁ + M₃) * WinMass f M₂ M₃) := by positivity
    have htailarith : Ctail * (M₁ * M₃ ^ 2 / B ^ (2 * (N - 1))) * ∫ s, (Hsum M₂ f s) ^ 2
        ≤ (Ctail / cwin) * ((M₁ + M₃) * WinMass f M₂ M₃) := by
      have h1 : M₁ * M₃ ^ 2 / B ^ (2 * (N - 1)) ≤ M₁ + M₃ := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < B ^ (2 * (N - 1)))]
        have h4 : M₁ * T ^ 8 ≤ M₁ * B ^ (2 * (N - 1)) := mul_le_mul_of_nonneg_left hB8 hM₁.le
        have h5 : M₁ * B ^ (2 * (N - 1)) ≤ (M₁ + M₃) * B ^ (2 * (N - 1)) :=
          mul_le_mul_of_nonneg_right (by linarith : M₁ ≤ M₁ + M₃) (by positivity)
        nlinarith [hM₃T, h4, h5, hM₁.le]
      have h6 := mul_le_mul (mul_le_mul_of_nonneg_left h1 hCtailpos.le) hwin' hI
        (by positivity : (0 : ℝ) ≤ Ctail * (M₁ + M₃))
      have h7 : Ctail * (M₁ + M₃) * ((1 / cwin) * WinMass f M₂ M₃)
          = (Ctail / cwin) * ((M₁ + M₃) * WinMass f M₂ M₃) := by ring
      linarith [h6, h7.le, h7.ge]
    have hwinarith : Cwinsharp * B ^ (1 + ε₀) * T ^ (6 * ε₀) * (M₁ + M₃) * WinMass f M₂ M₃
        ≤ Cwinsharp * (T ^ δ * ((M₁ + M₃) * WinMass f M₂ M₃)) := by
      have h3 : B ^ (1 + ε₀) * T ^ (6 * ε₀) ≤ T ^ δ := hBδ
      have h4 := mul_le_mul_of_nonneg_right h3 hPnn
      have h5 := mul_le_mul_of_nonneg_left h4 hCwinsharppos.le
      have h6 : Cwinsharp * ((B ^ (1 + ε₀) * T ^ (6 * ε₀)) * ((M₁ + M₃) * WinMass f M₂ M₃))
          = Cwinsharp * B ^ (1 + ε₀) * T ^ (6 * ε₀) * (M₁ + M₃) * WinMass f M₂ M₃ := by ring
      linarith [h5, h6.le, h6.ge]
    have hb : 2 * Cwinsharp + 2 * (Ctail / cwin) ≤ C' := by
      rw [hC'def]
      linarith [le_max_right (2 * (Ctail / cwin) * Tthr ^ 8) (2 * Cwinsharp + 2 * (Ctail / cwin))]
    have htail2 : (Ctail / cwin) * ((M₁ + M₃) * WinMass f M₂ M₃)
        ≤ (Ctail / cwin) * (T ^ δ * ((M₁ + M₃) * WinMass f M₂ M₃)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc (M₁ + M₃) * WinMass f M₂ M₃ = ((M₁ + M₃) * WinMass f M₂ M₃) * 1 := by ring
        _ ≤ ((M₁ + M₃) * WinMass f M₂ M₃) * T ^ δ := mul_le_mul_of_nonneg_left hTδ1 hPnn
        _ = T ^ δ * ((M₁ + M₃) * WinMass f M₂ M₃) := by ring
    calc ∫ ξ in A, ‖ghatFar K M₁ M₂ M₃ f ξ‖ ^ 2
        ≤ 2 * (Cwinsharp * B ^ (1 + ε₀) * T ^ (6 * ε₀) * (M₁ + M₃) * WinMass f M₂ M₃)
          + 2 * (Ctail * (M₁ * M₃ ^ 2 / B ^ (2 * (N - 1))) * ∫ s, (Hsum M₂ f s) ^ 2) := hglue
      _ ≤ 2 * (Cwinsharp * (T ^ δ * ((M₁ + M₃) * WinMass f M₂ M₃)))
          + 2 * ((Ctail / cwin) * ((M₁ + M₃) * WinMass f M₂ M₃)) :=
          add_le_add (mul_le_mul_of_nonneg_left hwinarith (by norm_num))
            (mul_le_mul_of_nonneg_left htailarith (by norm_num))
      _ ≤ 2 * (Cwinsharp * (T ^ δ * ((M₁ + M₃) * WinMass f M₂ M₃)))
          + 2 * ((Ctail / cwin) * (T ^ δ * ((M₁ + M₃) * WinMass f M₂ M₃))) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left htail2 (by norm_num))
      _ = (2 * Cwinsharp + 2 * (Ctail / cwin)) * (T ^ δ * ((M₁ + M₃) * WinMass f M₂ M₃)) := by
          ring
      _ ≤ C' * (T ^ δ * ((M₁ + M₃) * WinMass f M₂ M₃)) := mul_le_mul_of_nonneg_right hb hQnn
      _ = C' * T ^ δ * (M₁ + M₃) * WinMass f M₂ M₃ := by ring

end

end Work.GM.Affine
