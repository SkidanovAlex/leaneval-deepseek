import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.supf_le_integral_norm_fhat

/-!
# `supf f ≤ 4 (4c(j,ε)/(j-1))^{1/(j-1)} T^{(ε+j)/(j-1)} ∫ f`   (GM §9)

General-`j` version of the crude consequence of the Fourier decay hypothesis of GM §9.

With `M = supf f`, `A = ∫ f`, `D = c j ε · T^ε · T^j · M` we have
* `‖Fhat f ξ‖ ≤ A` for all `ξ` and `‖Fhat f ξ‖ ≤ D/|ξ|^j` for `ξ ≠ 0`;
* Fourier inversion gives `M ≤ ∫ ξ, ‖Fhat f ξ‖`;
* splitting the integral at `|ξ| = r` gives `M ≤ 2rA + 2D/((j-1) r^{j-1})`;
* choosing `r = (4D/((j-1)M))^{1/(j-1)}` balances the two terms and yields the claim.

The case `T < 0` is degenerate: `Real.rpow` of a negative base is
`exp (log|x| · y) cos (yπ)`, so `T^{1/2} = 0` and the decay hypothesis at `(j, ε) = (2, 1/2)`
forces `f ≡ 0`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-! ## Auxiliary analytic facts about `Fhat f` -/

private lemma ae_ne_zero_real : ∀ᵐ ξ : ℝ ∂(volume : Measure ℝ), ξ ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  have h : {x : ℝ | ¬ (x ≠ 0)} = {0} := by ext x; simp
  rw [h]; exact measure_singleton 0

private lemma norm_fhat_le_integral {f : ℝ → ℝ} (hnn : ∀ u, 0 ≤ f u) (ξ : ℝ) :
    ‖Fhat f ξ‖ ≤ ∫ u, f u := by
  calc ‖Fhat f ξ‖ = ‖∫ v, Real.fourierChar (-inner ℝ v ξ) • (f v : ℂ)‖ := by
        rw [Fhat, Real.fourier_eq]
    _ ≤ ∫ v, ‖Real.fourierChar (-inner ℝ v ξ) • (f v : ℂ)‖ := norm_integral_le_integral_norm _
    _ = ∫ v, ‖(f v : ℂ)‖ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        simp
    _ = ∫ v, f v := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        simp [Real.norm_of_nonneg (hnn v)]

private lemma continuous_fhat {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    Continuous (Fhat f) := by
  rw [show Fhat f = VectorFourier.fourierIntegral Real.fourierChar (volume : Measure ℝ)
      (innerₗ ℝ) (fun u : ℝ => (f u : ℂ)) from rfl]
  exact VectorFourier.fourierIntegral_continuous (μ := (volume : Measure ℝ)) (L := innerₗ ℝ)
    (f := fun u : ℝ => (f u : ℂ)) Real.continuous_fourierChar (by fun_prop)
    ((hf.integrable_of_hasCompactSupport hcs).ofReal)

private lemma norm_fhat_le_decay_sq {c : ℕ → ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ} (hdec : DecayHyp c T f)
    {ε : ℝ} (hε : 0 < ε) (ξ : ℝ) (hξ : ξ ≠ 0) :
    ‖Fhat f ξ‖ ≤ c 2 ε * T ^ ε * T ^ 2 * supf f / ξ ^ 2 := by
  have h := hdec 2 ε hε ξ hξ
  rw [div_pow] at h
  calc ‖Fhat f ξ‖ ≤ c 2 ε * T ^ ε * (T ^ 2 / |ξ| ^ 2) * supf f := h
    _ = c 2 ε * T ^ ε * T ^ 2 * supf f / ξ ^ 2 := by rw [sq_abs]; ring

private lemma integrable_fhat_of_decay {c : ℕ → ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) (hnn : ∀ u, 0 ≤ f u) (hdec : DecayHyp c T f) {ε : ℝ}
    (hε : 0 < ε) (hB : 0 ≤ c 2 ε * T ^ ε * T ^ 2 * supf f) :
    Integrable (Fhat f) := by
  have hA : 0 ≤ ∫ u, f u := integral_nonneg hnn
  have hcont : Continuous (Fhat f) := continuous_fhat hf hcs
  have hg : Integrable (fun ξ : ℝ =>
      (2 * (∫ u, f u) + 2 * (c 2 ε * T ^ ε * T ^ 2 * supf f)) * (1 + ξ ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  refine Integrable.mono' hg hcont.aestronglyMeasurable ?_
  filter_upwards [ae_ne_zero_real] with ξ hξ
  have h1 := norm_fhat_le_integral hnn ξ
  have h2 := norm_fhat_le_decay_sq hdec hε ξ hξ
  rcases le_or_gt |ξ| 1 with h | h
  · have hsq : ξ ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg ξ]
    calc ‖Fhat f ξ‖ ≤ ∫ u, f u := h1
      _ ≤ (2 * (∫ u, f u) + 2 * (c 2 ε * T ^ ε * T ^ 2 * supf f)) * (1 + ξ ^ 2)⁻¹ := by
          rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
          nlinarith [hA, hB, hsq]
  · have hsq : 1 ≤ ξ ^ 2 := by rw [← sq_abs]; nlinarith [abs_pos.mpr hξ]
    calc ‖Fhat f ξ‖ ≤ c 2 ε * T ^ ε * T ^ 2 * supf f / ξ ^ 2 := h2
      _ ≤ (2 * (∫ u, f u) + 2 * (c 2 ε * T ^ ε * T ^ 2 * supf f)) * (1 + ξ ^ 2)⁻¹ := by
          rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hA, hB, hsq]

/-! ## The tail integral of `|x|^{-j}` -/

private lemma integral_Ioi_div_pow (D : ℝ) {j : ℕ} (hj : 2 ≤ j) {r : ℝ} (hr : 0 < r) :
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

private lemma integrableOn_Ioi_div_pow (D : ℝ) {j : ℕ} (hj : 2 ≤ j) {r : ℝ} (hr : 0 < r) :
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

/-! ## The splitting estimate -/

private lemma integral_le_split_pow {g : ℝ → ℝ} {A D : ℝ} {j : ℕ} (hj : 2 ≤ j) {r : ℝ}
    (hr : 0 < r) (hg : Integrable g) (h1 : ∀ x, g x ≤ A)
    (h2 : ∀ x, x ≠ 0 → g x ≤ D / |x| ^ j) :
    ∫ x, g x ≤ 2 * r * A + 2 * (D / (((j : ℝ) - 1) * r ^ (j - 1))) := by
  have hIntB : IntegrableOn (fun x : ℝ => D / x ^ j) (Set.Ioi r) :=
    integrableOn_Ioi_div_pow D hj hr
  have htail : ∫ x in Set.Ioi r, D / x ^ j = D / (((j : ℝ) - 1) * r ^ (j - 1)) :=
    integral_Ioi_div_pow D hj hr
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

/-! ## The main estimate -/

theorem supf_decay_general {c : ℕ → ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) (hnn : ∀ u, 0 ≤ f u) (hdec : DecayHyp c T f) {j : ℕ}
    (hj : 2 ≤ j) {ε : ℝ} (hε : 0 < ε) (hc : 0 ≤ c j ε) :
    supf f ≤ 4 * (4 * c j ε / ((j : ℝ) - 1)) ^ (1 / ((j : ℝ) - 1))
      * T ^ ((ε + (j : ℝ)) / ((j : ℝ) - 1)) * ∫ u, f u := by
  set M : ℝ := supf f with hMdef
  set A : ℝ := ∫ u, f u with hAdef
  have hA : 0 ≤ A := integral_nonneg hnn
  have hMnn : 0 ≤ M := supf_nonneg hf hcs hnn
  have hjR : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hp : 0 < (j : ℝ) - 1 := by linarith
  by_cases hT : T < 0
  · -- degenerate case: the decay hypothesis forces `f ≡ 0`
    have hξ0 : ∀ ξ, ξ ≠ 0 → Fhat f ξ = 0 := by
      intro ξ hξ
      have h := hdec 2 (1 / 2) (by norm_num) ξ hξ
      have hT2 : T ^ ((1 : ℝ) / 2) = 0 := by
        rw [Real.rpow_def_of_neg hT]
        rw [show ((1 : ℝ) / 2) * Real.pi = Real.pi / 2 by ring, Real.cos_pi_div_two,
          mul_zero]
      have h' : ‖Fhat f ξ‖ ≤ 0 := by
        have hh := h
        rw [hT2] at hh
        simpa only [mul_zero, zero_mul] using hh
      exact norm_eq_zero.mp (le_antisymm h' (norm_nonneg _))
    have hae : Fhat f =ᵐ[volume] 0 := by
      show ∀ᵐ x ∂volume, Fhat f x = 0
      rw [MeasureTheory.ae_iff]
      refine measure_mono_null ?_ (measure_singleton 0)
      intro x hx
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff] at hx ⊢
      by_contra hx0
      exact hx (hξ0 x hx0)
    have hint : Integrable (Fhat f) :=
      Integrable.congr (integrable_zero ℝ ℂ volume) hae.symm
    have hInt0 : ∫ ξ, ‖Fhat f ξ‖ = 0 := by
      have h : (fun ξ => ‖Fhat f ξ‖) =ᵐ[volume] (fun _ : ℝ => (0 : ℝ)) := by
        filter_upwards [hae] with ξ hξ
        rw [hξ]; simp
      rw [integral_congr_ae h]; simp
    have hMinv : M ≤ ∫ ξ, ‖Fhat f ξ‖ := by
      have h := supf_le_integral_norm_fhat hf hcs hnn hint
      rw [← hMdef] at h
      exact h
    have hMle : M ≤ 0 := by linarith [hMinv, hInt0]
    have hM0 : M = 0 := le_antisymm hMle hMnn
    have hf0 : ∀ u, f u = 0 := by
      intro u
      have h1 : f u ≤ M := hMdef.symm ▸ le_supf hf hcs u
      exact le_antisymm (hM0 ▸ h1) (hnn u)
    have hA0 : A = 0 := by rw [hAdef]; simp [hf0]
    rw [hA0, mul_zero]
    exact hMle
  · have hT0 : 0 ≤ T := le_of_not_gt hT
    -- integrability of `Fhat f`
    have hD2nn : 0 ≤ c 2 ε * T ^ ε * T ^ 2 * M := by
      have h := hdec 2 ε hε 1 one_ne_zero
      have h' : ‖Fhat f 1‖ ≤ c 2 ε * T ^ ε * T ^ 2 * M := by
        simpa [hMdef, abs_one, div_one] using h
      linarith [norm_nonneg (Fhat f 1)]
    have hint : Integrable (Fhat f) :=
      integrable_fhat_of_decay hf hcs hnn hdec hε (by simpa [hMdef] using hD2nn)
    have hMinv : M ≤ ∫ ξ, ‖Fhat f ξ‖ := by
      have h := supf_le_integral_norm_fhat hf hcs hnn hint
      rw [← hMdef] at h
      exact h
    set D : ℝ := c j ε * T ^ ε * T ^ j * M with hDdef
    have hbA : ∀ ξ, ‖Fhat f ξ‖ ≤ A := fun ξ => norm_fhat_le_integral hnn ξ
    have hbD : ∀ ξ, ξ ≠ 0 → ‖Fhat f ξ‖ ≤ D / |ξ| ^ j := by
      intro ξ hξ
      have h := hdec j ε hε ξ hξ
      rw [div_pow] at h
      calc ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T ^ j / |ξ| ^ j) * supf f := h
        _ = D / |ξ| ^ j := by
            rw [hDdef, hMdef, div_eq_mul_inv, div_eq_mul_inv]
            ring
    have hsplit : ∀ r > 0, M ≤ 2 * r * A + 2 * (D / (((j : ℝ) - 1) * r ^ (j - 1))) := by
      intro r hr
      have h := integral_le_split_pow (g := fun ξ => ‖Fhat f ξ‖) hj hr hint.norm hbA hbD
      linarith [hMinv, h]
    by_cases hD0 : D = 0
    · have hMle : M ≤ 0 := by
        apply le_of_forall_pos_le_add
        intro δ hδ
        have hr : 0 < δ / (2 * (A + 1)) := by positivity
        have h := hsplit (δ / (2 * (A + 1))) hr
        rw [hD0] at h
        simp only [zero_div, mul_zero, add_zero] at h
        have h2 : 2 * (δ / (2 * (A + 1))) * A ≤ δ := by
          have hA1 : (0 : ℝ) < A + 1 := by linarith
          rw [show 2 * (δ / (2 * (A + 1))) * A = δ * A / (A + 1) by field_simp]
          rw [div_le_iff₀ hA1]
          nlinarith [hA, hδ]
        linarith
      have hM0 : M = 0 := le_antisymm hMle hMnn
      have hf0 : ∀ u, f u = 0 := by
        intro u
        have h1 : f u ≤ M := hMdef.symm ▸ le_supf hf hcs u
        exact le_antisymm (hM0 ▸ h1) (hnn u)
      have hA0 : A = 0 := by rw [hAdef]; simp [hf0]
      rw [hA0, mul_zero]
      exact hMle
    · have hDnn : 0 ≤ D := by
        have h := hdec j ε hε 1 one_ne_zero
        have h' : ‖Fhat f 1‖ ≤ D := by
          simpa [hDdef, hMdef, abs_one, div_one] using h
        linarith [norm_nonneg (Fhat f 1)]
      have hDpos : 0 < D := lt_of_le_of_ne hDnn (Ne.symm hD0)
      have hD_eq : D = (c j ε * T ^ ε * T ^ j) * M := by rw [hDdef]
      have hMpos : 0 < M := by
        rcases eq_or_lt_of_le hMnn with h | h
        · exfalso
          have : D = 0 := by rw [hD_eq, ← h, mul_zero]
          exact hD0 this
        · exact h
      have hKpos : 0 < c j ε * T ^ ε * T ^ j :=
        pos_of_mul_pos_left (hD_eq ▸ hDpos) (le_of_lt hMpos)
      have hTjpos : 0 < T ^ j := by
        have ha : 0 ≤ c j ε * T ^ ε := mul_nonneg hc (Real.rpow_nonneg hT0 ε)
        exact pos_of_mul_pos_right hKpos ha
      have hTne : T ≠ 0 := by
        intro h0
        have : (0 : ℝ) ^ j = 0 := zero_pow (by omega : j ≠ 0)
        rw [h0, this] at hTjpos
        exact lt_irrefl 0 hTjpos
      have hTpos : 0 < T := lt_of_le_of_ne hT0 (Ne.symm hTne)
      set p : ℝ := (j : ℝ) - 1 with hpdef
      have hppos : 0 < p := by rw [hpdef]; linarith
      have hXpos : 0 < 4 * (c j ε * T ^ ε * T ^ j) / p := by positivity
      set r : ℝ := (4 * (c j ε * T ^ ε * T ^ j) / p) ^ (1 / p) with hrdef
      have hr : 0 < r := by rw [hrdef]; exact Real.rpow_pos_of_pos hXpos _
      have hcast : (((j - 1 : ℕ)) : ℝ) = p := by
        rw [hpdef, Nat.cast_sub (by omega : 1 ≤ j)]; norm_num
      have hrpow : r ^ (j - 1) = 4 * (c j ε * T ^ ε * T ^ j) / p := by
        rw [hrdef, ← Real.rpow_natCast _ (j - 1), hcast]
        rw [← Real.rpow_mul (le_of_lt hXpos) (1 / p) p]
        rw [show (1 / p) * p = 1 by field_simp]
        rw [Real.rpow_one]
      have hb := hsplit r hr
      have hden : p * r ^ (j - 1) = 4 * (c j ε * T ^ ε * T ^ j) := by
        rw [hrpow, ← mul_div_assoc,
          mul_div_cancel_left₀ (4 * (c j ε * T ^ ε * T ^ j)) (ne_of_gt hppos)]
      have hsimp : 2 * (D / (p * r ^ (j - 1))) = M / 2 := by
        have hXne : c j ε * T ^ ε * T ^ j ≠ 0 := ne_of_gt hKpos
        have h1 : c j ε * T ^ ε * T ^ j * M / (4 * (c j ε * T ^ ε * T ^ j)) = M / 4 := by
          rw [mul_comm 4 (c j ε * T ^ ε * T ^ j)]
          exact mul_div_mul_left M 4 hXne
        rw [hden, hDdef, h1]
        ring
      have hmain : M ≤ 4 * r * A := by linarith [hb, hsimp]
      have hfac : r = (4 * c j ε / p) ^ (1 / p) * T ^ ((ε + (j : ℝ)) / p) := by
        rw [hrdef]
        have hQ : 4 * (c j ε * T ^ ε * T ^ j) / p = (4 * c j ε / p) * (T ^ ε * T ^ j) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]; ring
        rw [hQ]
        rw [Real.mul_rpow (by positivity) (by positivity)]
        congr 1
        rw [show T ^ j = T ^ ((j : ℝ)) from (Real.rpow_natCast T j).symm]
        rw [← Real.rpow_add hTpos]
        rw [← Real.rpow_mul (le_of_lt hTpos)]
        congr 1
        ring
      rw [hfac] at hmain
      calc M ≤ 4 * ((4 * c j ε / p) ^ (1 / p) * T ^ ((ε + (j : ℝ)) / p)) * A := hmain
        _ = 4 * (4 * c j ε / p) ^ (1 / p) * T ^ ((ε + (j : ℝ)) / p) * A := by ring

end

end Work.GM.Affine
