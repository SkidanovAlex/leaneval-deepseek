import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.support_width_ge_of_decay
import Submission.Work.GM.Affine.supf_le_of_decay_three
import Submission.Work.GM.Affine.supf_le_of_decay
import Submission.Work.GM.Affine.supf_decay_general
import Submission.Work.GM.Affine.f_sq_le_smoothed_sq_crux
import Submission.Work.GM.Affine.local_mass_comparison
import Submission.Work.GM.Affine.supf_le_integral_norm_fhat
import Submission.Work.GM.Affine.assembly_aux

/-!
# `supf f ≤ C T^{1+δ} ∫ f` from the scaled decay hypothesis of GM §9

The test function `f` of GM §9 (non-negative, supported in `[1/C₀, C₀]`) is assumed to satisfy
the Fourier decay condition *with an auxiliary scale* `Λ`,

  `‖Fhat f ξ‖ ≤ c j ε · T^ε · (T/|ξ|)^j · Λ`   for all `j ∈ ℕ`, `ε > 0`, `ξ ≠ 0`,

together with the *compatibility* `Λ ≤ 16 c 2 1 T³ ∫ f` (this is GM's remark that the decay
scale is controlled by the mass of `f`).

Under these hypotheses the supremum of `f` is bounded by `C T^{1+δ} ∫ f` (as opposed to the
crude bound `supf f ≤ 16 c 2 1 T³ ∫ f` obtained from `j = 2` alone).

## Proof

Let `M = supf f`, `V = ∫ f` and `D = c j ε T^ε T^j Λ`, so that `‖Fhat f ξ‖ ≤ D/|ξ|^j`.

* Fourier inversion gives `M ≤ ∫ ξ, ‖Fhat f ξ‖` (`supf_le_integral_norm_fhat`).
* Splitting the integral at `|ξ| = r` (the tail using the decay at `j`, the middle using
  `‖Fhat f ξ‖ ≤ V`) gives, for every `r > 0`,
  `M ≤ 2 r V + 2 D/((j-1) r^{j-1})`.
* Taking `r = Y T^{(j+3+ε)/j}` with `Y = (|c j ε|+1)(|16 c 2 1|+1)`, one has
  `r^j ≥ (c j ε · 16 c 2 1) T^{j+3+ε} ≥ D/V` (using the compatibility), so the tail term is at
  most `2 V r/(j-1) ≤ 2 V r`, and `M ≤ 4 V r ≤ 4 Y V T^{1+(3+ε)/j}`.
* Choosing `ε = 1/2` and `j ≥ 7/(2δ)` makes `(3+ε)/j ≤ δ`, so `T^{1+(3+ε)/j} ≤ T^{1+δ}`,
  and the constant `C = 4Y+1` is independent of `T`, `f`, `Λ`.

The cases `V = 0` (then the compatibility contradicts `Λ > 0`) and `D = 0` (`M ≤ 2 r V` for all
`r > 0`, hence `M = 0`) are degenerate.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.GM.Affine

noncomputable section

/-! ## Auxiliary measure-theoretic facts -/

private lemma ae_ne_zero_real_afn : ∀ᵐ ξ : ℝ ∂(volume : Measure ℝ), ξ ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  have h : {x : ℝ | ¬ (x ≠ 0)} = {0} := by ext x; simp
  rw [h]; exact measure_singleton 0

private lemma integral_Ioi_div_pow_afn (D : ℝ) {j : ℕ} (hj : 2 ≤ j) {r : ℝ} (hr : 0 < r) :
    ∫ x in Set.Ioi r, D / x ^ j = D / (((j : ℝ) - 1) * r ^ (j - 1)) := by
  have hjR : (1 : ℝ) < (j : ℝ) := by
    have : (1 : ℕ) < j := by omega
    exact_mod_cast this
  have ha : (-(j : ℝ)) < -1 := by linarith
  have hcast : (((j - 1 : ℕ)) : ℝ) = (j : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ j)]; norm_num
  have hjn : (((j - 1 : ℕ)) : ℝ) ≠ 0 := by rw [hcast]; linarith
  have hrne : r ≠ 0 := ne_of_gt hr
  have hrp : r ^ (j - 1) ≠ 0 := pow_ne_zero _ hrne
  rw [← hcast]
  have h : (fun x : ℝ => D / x ^ j) = fun x => D * x ^ (-(j : ℝ)) := by
    funext x
    rw [div_eq_mul_inv, Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
  rw [h, integral_const_mul, integral_Ioi_rpow_of_lt ha hr]
  rw [show -(j : ℝ) + 1 = -(((j - 1 : ℕ)) : ℝ) by rw [hcast]; ring]
  rw [Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
  field_simp

private lemma integrableOn_Ioi_div_pow_afn (D : ℝ) {j : ℕ} (hj : 2 ≤ j) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => D / x ^ j) (Set.Ioi r) := by
  have hjR : (1 : ℝ) < (j : ℝ) := by
    have : (1 : ℕ) < j := by omega
    exact_mod_cast this
  have ha : (-(j : ℝ)) < -1 := by linarith
  have h1 : IntegrableOn (fun x : ℝ => D * x ^ (-(j : ℝ))) (Set.Ioi r) :=
    (integrableOn_Ioi_rpow_of_lt ha hr).const_mul D
  refine h1.congr_fun ?_ measurableSet_Ioi
  intro x _
  show D * x ^ (-(j : ℝ)) = D / x ^ j
  rw [div_eq_mul_inv, Real.rpow_neg_natCast, zpow_neg, zpow_natCast]

/-- Tail-splitting estimate with a `j`-th power decay: if `g x ≤ A` everywhere and
`g x ≤ D/x^j` for `x ≠ 0`, then `∫ g ≤ 2 r A + 2 D/((j-1) r^{j-1})`. -/
private lemma integral_le_split_pow_afn {g : ℝ → ℝ} {A D : ℝ} {j : ℕ} (hj : 2 ≤ j) {r : ℝ}
    (hr : 0 < r) (hg : Integrable g) (h1 : ∀ x, g x ≤ A)
    (h2 : ∀ x, x ≠ 0 → g x ≤ D / |x| ^ j) :
    ∫ x, g x ≤ 2 * r * A + 2 * (D / (((j : ℝ) - 1) * r ^ (j - 1))) := by
  have hIntB : IntegrableOn (fun x : ℝ => D / x ^ j) (Set.Ioi r) :=
    integrableOn_Ioi_div_pow_afn D hj hr
  have htail : ∫ x in Set.Ioi r, D / x ^ j = D / (((j : ℝ) - 1) * r ^ (j - 1)) :=
    integral_Ioi_div_pow_afn D hj hr
  have hsplit : ∫ x, g x = (∫ x in Set.Iic r, g x) + (∫ x in Set.Ioi r, g x) := by
    rw [← integral_add_compl (μ := volume) (f := g) (s := Set.Iic r) measurableSet_Iic hg,
      Set.compl_Iic]
  have hunion : Set.Iic r = Set.Iic (-r) ∪ Set.Ioc (-r) r := by
    ext x; constructor
    · intro hx
      rcases le_or_gt x (-r) with h | h
      · exact Or.inl (Set.mem_Iic.mpr h)
      · exact Or.inr ⟨h, Set.mem_Iic.mp hx⟩
    · rintro (h | h)
      · exact Set.mem_Iic.mpr (le_trans (Set.mem_Iic.mp h) (by linarith))
      · exact Set.mem_Iic.mpr h.2
  have hIic_split : ∫ x in Set.Iic r, g x
      = (∫ x in Set.Iic (-r), g x) + (∫ x in Set.Ioc (-r) r, g x) := by
    rw [← setIntegral_union (s := Set.Iic (-r)) (t := Set.Ioc (-r) r)
      (by rw [Set.disjoint_left]; rintro x hx ⟨hx1, _⟩
          exact absurd (Set.mem_Iic.mp hx) (not_le.mpr hx1))
      measurableSet_Ioc hg.integrableOn hg.integrableOn, hunion]
  have hIoi : ∫ x in Set.Ioi r, g x ≤ D / (((j : ℝ) - 1) * r ^ (j - 1)) := by
    rw [← htail]
    refine setIntegral_mono_on hg.integrableOn hIntB measurableSet_Ioi (fun x hx => ?_)
    have hx0 : 0 < x := lt_trans hr (Set.mem_Ioi.mp hx)
    have h := h2 x (ne_of_gt hx0)
    rwa [abs_of_pos hx0] at h
  have hIic : ∫ x in Set.Iic (-r), g x ≤ D / (((j : ℝ) - 1) * r ^ (j - 1)) := by
    rw [← integral_comp_neg_Ioi r g, ← htail]
    refine setIntegral_mono_on hg.comp_neg.integrableOn hIntB measurableSet_Ioi (fun x hx => ?_)
    have hx0 : 0 < x := lt_trans hr (Set.mem_Ioi.mp hx)
    have h := h2 (-x) (neg_ne_zero.mpr (ne_of_gt hx0))
    rw [abs_neg] at h
    rwa [abs_of_pos hx0] at h
  have hIoc : ∫ x in Set.Ioc (-r) r, g x ≤ 2 * r * A := by
    calc ∫ x in Set.Ioc (-r) r, g x ≤ ∫ x in Set.Ioc (-r) r, A :=
          setIntegral_mono_on hg.integrableOn
            (integrableOn_const (C := A) (by simp [Real.volume_Ioc])) measurableSet_Ioc
            (fun x _ => h1 x)
      _ = 2 * r * A := by
          rw [setIntegral_const, Measure.real_def, Real.volume_Ioc,
            ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
          ring
  calc ∫ x, g x = (∫ x in Set.Iic r, g x) + (∫ x in Set.Ioi r, g x) := hsplit
    _ = ((∫ x in Set.Iic (-r), g x) + (∫ x in Set.Ioc (-r) r, g x))
          + (∫ x in Set.Ioi r, g x) := by rw [hIic_split]
    _ ≤ (D / (((j : ℝ) - 1) * r ^ (j - 1)) + 2 * r * A)
          + D / (((j : ℝ) - 1) * r ^ (j - 1)) := add_le_add (add_le_add hIic hIoc) hIoi
    _ = 2 * r * A + 2 * (D / (((j : ℝ) - 1) * r ^ (j - 1))) := by ring

/-- Integrability of `Fhat f` from the `j`-th power decay (`j ≥ 2`) and the trivial bound
`‖Fhat f ξ‖ ≤ ∫ f`. -/
private lemma integrable_fhat_of_pow_bound {f : ℝ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) (hnn : ∀ u, 0 ≤ f u) {j : ℕ} (hj : 2 ≤ j) {K : ℝ}
    (hK : 0 ≤ K) (hb : ∀ ξ : ℝ, ξ ≠ 0 → ‖Fhat f ξ‖ ≤ K / |ξ| ^ j) :
    Integrable (Fhat f) := by
  have hV : 0 ≤ ∫ u, f u := integral_nonneg hnn
  have hcont : Continuous (Fhat f) := continuous_fhat hf hcs
  have hg : Integrable (fun ξ : ℝ => 2 * ((∫ u, f u) + K) * (1 + ξ ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  refine Integrable.mono' hg hcont.aestronglyMeasurable ?_
  filter_upwards [ae_ne_zero_real_afn] with ξ hξ
  rcases le_or_gt |ξ| 1 with h | h
  · have hsq : ξ ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg ξ]
    have h1 := norm_fhat_le_integral hnn ξ
    calc ‖Fhat f ξ‖ ≤ ∫ u, f u := h1
      _ ≤ 2 * ((∫ u, f u) + K) * (1 + ξ ^ 2)⁻¹ := by
          rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
          nlinarith [hV, hK, hsq]
  · have hξ1 : (1 : ℝ) ≤ |ξ| := le_of_lt h
    have hsq1 : (1 : ℝ) ≤ ξ ^ 2 := by rw [← sq_abs]; exact one_le_pow₀ hξ1
    have hstep : K / |ξ| ^ j ≤ K / ξ ^ 2 := by
      refine div_le_div_of_nonneg_left hK (by rw [← sq_abs]; exact pow_pos (abs_pos.mpr hξ) 2) ?_
      rw [← sq_abs]
      exact pow_le_pow_right₀ hξ1 hj
    have h2 := hb ξ hξ
    calc ‖Fhat f ξ‖ ≤ K / |ξ| ^ j := h2
      _ ≤ K / ξ ^ 2 := hstep
      _ ≤ 2 * ((∫ u, f u) + K) * (1 + ξ ^ 2)⁻¹ := by
          rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hsq1, hK, hV]

/-! ## The main estimate -/

theorem supf_le_T_mul_integral {C₀ : ℝ} (hC₀ : 1 ≤ C₀) (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ T : ℝ, 1 ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        supf f ≤ C * T ^ (1 + δ) * ∫ u, f u := by
  set ε : ℝ := 1 / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; norm_num
  set j : ℕ := max 2 (Nat.ceil (7 / (2 * δ))) with hjdef
  have hj2 : 2 ≤ j := le_max_left 2 _
  have hjpos : (0 : ℝ) < (j : ℝ) := by
    have : 0 < j := by omega
    exact_mod_cast this
  have hnum : (3 + ε) / (j : ℝ) ≤ δ := by
    have h2δ : (0 : ℝ) < 2 * δ := by linarith
    have hle : 7 / (2 * δ) ≤ (j : ℝ) := by
      have h1 : 7 / (2 * δ) ≤ ((Nat.ceil (7 / (2 * δ))) : ℝ) := Nat.le_ceil _
      have h2 : ((Nat.ceil (7 / (2 * δ))) : ℝ) ≤ (j : ℝ) := by
        rw [hjdef]; exact_mod_cast le_max_right 2 _
      linarith
    have h3 : (7 : ℝ) / 2 ≤ δ * (j : ℝ) := by
      have := (div_le_iff₀ h2δ).mp hle
      linarith
    have heq : (3 + ε) / (j : ℝ) = ((7 : ℝ) / 2) / (j : ℝ) := by
      rw [hεdef]; norm_num
    rw [heq, div_le_iff₀ hjpos]
    linarith
  set Y : ℝ := (|c j ε| + 1) * (|16 * c 2 1| + 1) with hYdef
  have hYpos : 0 < Y := by
    rw [hYdef]
    have h1 : (0:ℝ) < |c j ε| + 1 := by linarith [abs_nonneg (c j ε)]
    have h2 : (0:ℝ) < |16 * c 2 1| + 1 := by linarith [abs_nonneg (16 * c 2 1)]
    exact mul_pos h1 h2
  have hY1 : 1 ≤ Y := by
    rw [hYdef]
    have h1 : (1:ℝ) ≤ |c j ε| + 1 := by linarith [abs_nonneg (c j ε)]
    have h2 : (1:ℝ) ≤ |16 * c 2 1| + 1 := by linarith [abs_nonneg (16 * c 2 1)]
    nlinarith
  refine ⟨4 * Y + 1, by linarith, ?_⟩
  intro T hT f hf hnn hsupp Λ hΛpos hdec hcompat
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hcs : HasCompactSupport f := hasCompactSupport_of_suppHyp hC₀ hsupp
  set M : ℝ := supf f with hMdef
  set V : ℝ := ∫ u, f u with hVdef
  have hVnn : 0 ≤ V := integral_nonneg hnn
  have hMnn : 0 ≤ M := supf_nonneg hf hcs hnn
  set K : ℝ := c j ε * T ^ ε * T ^ j * Λ with hKdef
  have hKnn : 0 ≤ K := by
    have h := hdec j ε hεpos 1 one_ne_zero
    have h' : ‖Fhat f 1‖ ≤ K := by
      rw [hKdef]; simpa [abs_one, div_one] using h
    linarith [norm_nonneg (Fhat f 1)]
  have hbA : ∀ ξ : ℝ, ‖Fhat f ξ‖ ≤ V := by
    intro ξ
    rw [hVdef]
    exact norm_fhat_le_integral hnn ξ
  have hbD : ∀ ξ : ℝ, ξ ≠ 0 → ‖Fhat f ξ‖ ≤ K / |ξ| ^ j := by
    intro ξ hξ
    have h := hdec j ε hεpos ξ hξ
    rw [div_pow] at h
    calc ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T ^ j / |ξ| ^ j) * Λ := h
      _ = K / |ξ| ^ j := by rw [hKdef]; ring
  have hint : Integrable (Fhat f) := integrable_fhat_of_pow_bound hf hcs hnn hj2 hKnn hbD
  have hMinv : M ≤ ∫ ξ, ‖Fhat f ξ‖ := by
    have h := supf_le_integral_norm_fhat hf hcs hnn hint
    rw [hMdef]; exact h
  have hsplit : ∀ r : ℝ, 0 < r → M ≤ 2 * r * V + 2 * (K / (((j : ℝ) - 1) * r ^ (j - 1))) := by
    intro r hr
    have h := integral_le_split_pow_afn (g := fun ξ : ℝ => ‖Fhat f ξ‖) hj2 hr hint.norm hbA hbD
    linarith [hMinv, h]
  by_cases hV0 : V = 0
  · -- the compatibility contradicts `Λ > 0`
    exfalso
    have h0 : Λ ≤ 0 := by
      have h := hcompat
      rw [hV0] at h
      simpa using h
    linarith
  · have hVpos : 0 < V := lt_of_le_of_ne hVnn (Ne.symm hV0)
    by_cases hK0 : K = 0
    · -- `D = 0`: then `M ≤ 2 r V` for every `r > 0`, hence `M = 0`
      have hMle : M ≤ 0 := by
        apply le_of_forall_pos_le_add
        intro η hη
        have hr : 0 < η / (2 * (V + 1)) := by
          apply div_pos hη
          linarith
        have h := hsplit _ hr
        rw [hK0] at h
        simp only [zero_div, mul_zero, add_zero] at h
        have h2 : 2 * (η / (2 * (V + 1))) * V ≤ η := by
          have hV1 : (0:ℝ) < V + 1 := by linarith
          rw [show 2 * (η / (2 * (V + 1))) * V = η * V / (V + 1) by field_simp]
          rw [div_le_iff₀ hV1]
          nlinarith [hVnn, hη]
        linarith
      have hgnn : 0 ≤ (4 * Y + 1) * T ^ (1 + δ) * V := by
        have h1 : (0:ℝ) < 4 * Y + 1 := by linarith
        have h2 : (0:ℝ) ≤ T ^ (1 + δ) := Real.rpow_nonneg hTpos.le _
        exact mul_nonneg (mul_nonneg h1.le h2) hVnn
      linarith
    · have hKpos : 0 < K := lt_of_le_of_ne hKnn (Ne.symm hK0)
      have hc21pos : 0 < c 2 1 := by
        have h16T3V : 0 < 16 * T ^ 3 * V :=
          mul_pos (mul_pos (by norm_num) (pow_pos hTpos 3)) hVpos
        have hprod : 0 < 16 * c 2 1 * T ^ 3 * V := by linarith [hcompat, hΛpos]
        have heq : 16 * c 2 1 * T ^ 3 * V = (16 * T ^ 3 * V) * (c 2 1) := by ring
        exact pos_of_mul_pos_right (heq ▸ hprod) h16T3V.le
      have hcJe : 0 < c j ε := by
        have hfac : 0 < T ^ ε * T ^ j * Λ :=
          mul_pos (mul_pos (Real.rpow_pos_of_pos hTpos ε) (pow_pos hTpos j)) hΛpos
        have heq : K = (c j ε) * (T ^ ε * T ^ j * Λ) := by rw [hKdef]; ring
        exact pos_of_mul_pos_left (heq ▸ hKpos) hfac.le
      have hcoefnn : 0 ≤ c j ε * T ^ ε * T ^ j :=
        mul_nonneg (mul_nonneg hcJe.le (Real.rpow_pos_of_pos hTpos ε).le) (pow_pos hTpos j).le
      -- `K ≤ (c j ε · 16 c 2 1 · T^{j+3+ε}) V`
      have hKle : K ≤ (c j ε * 16 * (c 2 1) * T ^ (j + 3 + ε)) * V := by
        have hcoef : c j ε * T ^ ε * T ^ j * Λ
            ≤ c j ε * T ^ ε * T ^ j * (16 * c 2 1 * T ^ 3 * V) :=
          mul_le_mul_of_nonneg_left hcompat hcoefnn
        have hTpow : T ^ ε * T ^ j * T ^ 3 = T ^ (j + 3 + ε) := by
          rw [← Real.rpow_natCast T j, ← Real.rpow_natCast T 3]
          rw [← Real.rpow_add hTpos, ← Real.rpow_add hTpos]
          congr 1
          ring
        calc K = c j ε * T ^ ε * T ^ j * Λ := hKdef
          _ ≤ c j ε * T ^ ε * T ^ j * (16 * c 2 1 * T ^ 3 * V) := hcoef
          _ = (c j ε * 16 * (c 2 1) * T ^ (j + 3 + ε)) * V := by
              rw [show c j ε * T ^ ε * T ^ j * (16 * c 2 1 * T ^ 3 * V)
                    = (c j ε * 16 * c 2 1) * (T ^ ε * T ^ j * T ^ 3) * V by ring, hTpow]
      have hle1 : c j ε * 16 * (c 2 1) ≤ Y := by
        rw [hYdef]
        have h1 : c j ε ≤ |c j ε| + 1 := by linarith [le_abs_self (c j ε)]
        have h2 : 16 * (c 2 1) ≤ |16 * c 2 1| + 1 := by linarith [le_abs_self (16 * c 2 1)]
        have h2nn : 0 ≤ 16 * (c 2 1) := by linarith
        calc c j ε * 16 * (c 2 1) = (c j ε) * (16 * (c 2 1)) := by ring
          _ ≤ (|c j ε| + 1) * (|16 * c 2 1| + 1) :=
              mul_le_mul h1 h2 h2nn (by linarith [abs_nonneg (c j ε)])
      set e : ℝ := ((j : ℝ) + 3 + ε) / (j : ℝ) with hedef
      set r : ℝ := Y * T ^ e with hrdef
      have hrpos : 0 < r := by
        rw [hrdef]
        exact mul_pos hYpos (Real.rpow_pos_of_pos hTpos e)
      have hej : e * (j : ℝ) = (j : ℝ) + 3 + ε := by
        rw [hedef, div_mul_cancel₀ _ (ne_of_gt hjpos)]
      have hrpow : r ^ j = Y ^ j * T ^ (j + 3 + ε) := by
        have hTe : (T ^ e) ^ j = T ^ (j + 3 + ε) := by
          rw [← Real.rpow_natCast (T ^ e) j, ← Real.rpow_mul hTpos.le, hej]
        rw [hrdef, mul_pow, hTe]
      have hrj : K / V ≤ r ^ j := by
        rw [div_le_iff₀ hVpos]
        calc K ≤ (c j ε * 16 * (c 2 1) * T ^ (j + 3 + ε)) * V := hKle
          _ ≤ (Y ^ j * T ^ (j + 3 + ε)) * V := by
              have hTnn : 0 ≤ T ^ (j + 3 + ε) := Real.rpow_nonneg hTpos.le _
              have hYj : Y ≤ Y ^ j := le_self_pow₀ hY1 (by omega)
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (le_trans hle1 hYj) hTnn) hVnn
          _ = r ^ j * V := by rw [hrpow]
      have htail : 2 * (K / (((j : ℝ) - 1) * r ^ (j - 1))) ≤ 2 * V * r := by
        have hp1 : (1:ℝ) ≤ (j : ℝ) - 1 := by
          have : (2:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj2
          linarith
        have hppos : 0 < (j : ℝ) - 1 := by linarith
        have hden : 0 < ((j : ℝ) - 1) * r ^ (j - 1) :=
          mul_pos hppos (pow_pos hrpos _)
        have hKV : K ≤ r ^ j * V := (div_le_iff₀ hVpos).mp hrj
        have hmain : K / (((j : ℝ) - 1) * r ^ (j - 1)) ≤ V * r := by
          rw [div_le_iff₀ hden]
          have hrpow' : r * r ^ (j - 1) = r ^ j := by
            rw [← pow_succ']
            congr 1
            omega
          rw [show V * r * (((j : ℝ) - 1) * r ^ (j - 1))
                = ((j : ℝ) - 1) * V * (r * r ^ (j - 1)) by ring, hrpow']
          nlinarith [hKV, hp1, hVnn, pow_nonneg hrpos.le j]
        linarith
      have hmain : M ≤ 4 * r * V := by
        have h := hsplit r hrpos
        nlinarith [h, htail]
      have hTe : T ^ e ≤ T ^ (1 + δ) := by
        have he_le : e ≤ 1 + δ := by
          have h3e : 3 + ε ≤ δ * (j : ℝ) := (div_le_iff₀ hjpos).mp hnum
          rw [hedef, div_le_iff₀ hjpos]
          nlinarith [h3e]
        exact Real.rpow_le_rpow_of_exponent_le hT he_le
      have hfinal : 4 * r * V ≤ (4 * Y + 1) * T ^ (1 + δ) * V := by
        have h1 : 4 * Y * T ^ e * V ≤ 4 * Y * T ^ (1 + δ) * V :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTe (by linarith)) hVnn
        have h2 : 4 * Y * T ^ (1 + δ) * V ≤ (4 * Y + 1) * T ^ (1 + δ) * V :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by linarith : 4 * Y ≤ 4 * Y + 1)
              (Real.rpow_nonneg hTpos.le _)) hVnn
        calc 4 * r * V = 4 * Y * T ^ e * V := by rw [hrdef]; ring
          _ ≤ 4 * Y * T ^ (1 + δ) * V := h1
          _ ≤ (4 * Y + 1) * T ^ (1 + δ) * V := h2
      linarith [hmain, hfinal]

end

end Work.GM.Affine
