import Mathlib
import Submission.Work.GM.Affine.setup

/-!
# `supf f ≤ 16 c(2,ε) T^ε T² ∫ f` (GM §9)

GM §9 (proof of Lemma 9.2) uses the crude consequence of the Fourier-decay hypothesis

  `f(u) ⪅ T²`,  hence  `∫ f(u) du ⪆ 1/T²`

of the test function `f` (see the sentence "Crudely, the rapid decay of `f̂` implies that
`f(u) ⪅ T²`, so `∫ f(u)du ⪆ 1/T²`" in the paper).  The present file proves the precise form

  `supf f ≤ 16 * c 2 ε * T^ε * T^2 * ∫ f`,

i.e. `∫ f ≳ sup f / (T^ε T²)`, with an explicit dependence on the decay constant `c 2 ε`.

## Proof

Write `M = supf f`, `A = ∫ f`, `B = c 2 ε * T^ε * T² * M`.

1. `‖Fhat f ξ‖ ≤ A` for every `ξ` (the Fourier transform is bounded by the `L¹` norm), and, by
   `DecayHyp` with `j = 2`, `‖Fhat f ξ‖ ≤ B/ξ²` for `ξ ≠ 0`.  Hence `Fhat f` is integrable.
2. Fourier inversion at a point `x` where `f` attains its supremum gives
   `M = f x ≤ ∫ ξ, ‖Fhat f ξ‖`.
3. For every `r > 0` splitting the integral at `±r` gives
   `M ≤ ∫ ‖Fhat f ξ‖ ≤ (B/r) + 2rA + (B/r) = 2rA + 2B/r`
   (the middle piece `|ξ| ≤ r` contributes `2rA`, the two tails `B/r` each).
4. If `B = 0` then `M ≤ 2rA` for all `r > 0`, so `M = 0`, and (as `f ≥ 0` and continuous)
   `A = 0`, whence the claim.  Otherwise `K := c 2 ε * T^ε * T² > 0` (as `B = K·M` and `M > 0`)
   and choosing `r = 4K` in (3) gives `M ≤ 8K A + M/2`, i.e. `M ≤ 16 K A`.
5. If `M = 0` then `f ≡ 0`, so `A = 0` and both sides vanish.

The hypothesis `hc : 0 ≤ c 2 ε` is not used: the degenerate sign cases are also handled by the
argument above.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-! ### Elementary auxiliary estimates -/

/-- `(volume : Measure ℝ) {0} = 0`: the point `0` is negligible. -/
private lemma hae_ne_zero_real : ∀ᵐ ξ : ℝ ∂(volume : Measure ℝ), ξ ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  have h : {x : ℝ | ¬ (x ≠ 0)} = {0} := by ext x; simp
  rw [h]; exact measure_singleton 0

/-- `∫_{x > r} B/x² = B/r` for `r > 0`. -/
private lemma integral_Ioi_div_sq (B : ℝ) {r : ℝ} (hr : 0 < r) :
    ∫ x in Set.Ioi r, B / x ^ 2 = B / r := by
  have h : (fun x : ℝ => B / x ^ 2) = fun x => B * x ^ (-2 : ℝ) := by
    funext x
    rw [div_eq_mul_inv, show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
  rw [h, integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hr]
  rw [show (-2 : ℝ) + 1 = -((1 : ℕ) : ℝ) by norm_num, Real.rpow_neg_natCast, zpow_neg,
    zpow_natCast]
  field_simp
  ring

/-- `x ↦ B/x²` is integrable on `(r, ∞)` for `r > 0`. -/
private lemma integrableOn_Ioi_div_sq (B : ℝ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => B / x ^ 2) (Set.Ioi r) := by
  have h1 : IntegrableOn (fun x : ℝ => B * x ^ (-2 : ℝ)) (Set.Ioi r) :=
    (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num : (-2 : ℝ) < -1) hr).const_mul B
  refine IntegrableOn.congr_fun h1 ?_ measurableSet_Ioi
  intro x _
  show B * x ^ (-2 : ℝ) = B / x ^ 2
  rw [div_eq_mul_inv, show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg_natCast,
    zpow_neg, zpow_natCast]

/-- Tail-splitting estimate: if `g x ≤ A` everywhere, `g x ≤ B/x²` for `x ≠ 0`, and `g` is
integrable, then `∫ g ≤ 2rA + 2B/r` for every `r > 0`. -/
private lemma integral_le_two_r_aux {g : ℝ → ℝ} {A B r : ℝ} (hr : 0 < r)
    (hg : Integrable g) (h1 : ∀ x, g x ≤ A) (h2 : ∀ x, x ≠ 0 → g x ≤ B / x ^ 2) :
    ∫ x, g x ≤ 2 * r * A + 2 * B / r := by
  have hIntB : IntegrableOn (fun x : ℝ => B / x ^ 2) (Set.Ioi r) := integrableOn_Ioi_div_sq B hr
  have htail : ∫ x in Set.Ioi r, B / x ^ 2 = B / r := integral_Ioi_div_sq B hr
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
  have hIoi : ∫ x in Set.Ioi r, g x ≤ B / r := by
    rw [← htail]
    refine setIntegral_mono_on hg.integrableOn hIntB measurableSet_Ioi (fun x hx => ?_)
    exact h2 x (ne_of_gt (lt_trans hr (Set.mem_Ioi.mp hx)))
  have hIic : ∫ x in Set.Iic (-r), g x ≤ B / r := by
    rw [← integral_comp_neg_Ioi r g, ← htail]
    refine setIntegral_mono_on hg.comp_neg.integrableOn hIntB measurableSet_Ioi (fun x hx => ?_)
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans hr (Set.mem_Ioi.mp hx))
    calc g (-x) ≤ B / (-x) ^ 2 := h2 (-x) (neg_ne_zero.mpr hx0)
      _ = B / x ^ 2 := by ring
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
    _ ≤ (B / r + 2 * r * A) + B / r := add_le_add (add_le_add hIic hIoc) hIoi
    _ = 2 * r * A + 2 * B / r := by ring

/-! ### The Fourier transform of `f`: continuity, size and integrability -/

/-- `Fhat f` is continuous (as the Fourier transform of an integrable function). -/
lemma continuous_fhat {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    Continuous (Fhat f) := by
  rw [show Fhat f = VectorFourier.fourierIntegral Real.fourierChar (volume : Measure ℝ)
      (innerₗ ℝ) (fun u : ℝ => (f u : ℂ)) from rfl]
  exact VectorFourier.fourierIntegral_continuous (μ := (volume : Measure ℝ)) (L := innerₗ ℝ)
    (f := fun u : ℝ => (f u : ℂ)) Real.continuous_fourierChar (by fun_prop)
    ((hf.integrable_of_hasCompactSupport hcs).ofReal)

/-- The trivial bound `‖Fhat f ξ‖ ≤ ∫ f` for `f ≥ 0`. -/
lemma norm_fhat_le_integral {f : ℝ → ℝ} (hnn : ∀ u, 0 ≤ f u) (ξ : ℝ) :
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

/-- The Fourier-decay bound of GM §9 with `j = 2`. -/
lemma norm_fhat_le_decay {c : ℕ → ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ} (hdec : DecayHyp c T f)
    {ε : ℝ} (hε : 0 < ε) (ξ : ℝ) (hξ : ξ ≠ 0) :
    ‖Fhat f ξ‖ ≤ c 2 ε * T ^ ε * T ^ 2 * supf f / ξ ^ 2 := by
  have h := hdec 2 ε hε ξ hξ
  rw [div_pow] at h
  calc ‖Fhat f ξ‖ ≤ c 2 ε * T ^ ε * (T ^ 2 / |ξ| ^ 2) * supf f := h
    _ = c 2 ε * T ^ ε * T ^ 2 * supf f / ξ ^ 2 := by rw [sq_abs]; ring

/-- Under the two pointwise bounds above (and `0 ≤ B`), the Fourier transform is integrable:
both bounds are dominated by a multiple of `(1 + ξ²)⁻¹`. -/
lemma integrable_fhat_of_bounds {c : ℕ → ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) (hnn : ∀ u, 0 ≤ f u) (hdec : DecayHyp c T f) {ε : ℝ}
    (hε : 0 < ε) (hB : 0 ≤ c 2 ε * T ^ ε * T ^ 2 * supf f) :
    Integrable (Fhat f) := by
  have hA : 0 ≤ ∫ u, f u := integral_nonneg hnn
  have hcont : Continuous (Fhat f) := continuous_fhat hf hcs
  have hg : Integrable (fun ξ : ℝ =>
      (2 * (∫ u, f u) + 2 * (c 2 ε * T ^ ε * T ^ 2 * supf f)) * (1 + ξ ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  refine Integrable.mono' hg hcont.aestronglyMeasurable ?_
  filter_upwards [hae_ne_zero_real] with ξ hξ
  have h1 := norm_fhat_le_integral hnn ξ
  have h2 := norm_fhat_le_decay hdec hε ξ hξ
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

/-- **Fourier inversion**: the supremum of `f` is bounded by the `L¹` norm of `Fhat f`. -/
private lemma supf_le_integral_norm_fhat_aux {f : ℝ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) (hnn : ∀ u, 0 ≤ f u) (hint : Integrable (Fhat f)) :
    supf f ≤ ∫ ξ, ‖Fhat f ξ‖ := by
  obtain ⟨x, hx⟩ := exists_eq_supf hf hcs
  have hcont : Continuous (fun u : ℝ => (f u : ℂ)) := Complex.continuous_ofReal.comp hf
  have hg : Integrable (fun u : ℝ => (f u : ℂ)) :=
    (hf.integrable_of_hasCompactSupport hcs).ofReal
  have hFint : Integrable (𝓕 (fun u : ℝ => (f u : ℂ))) := hint
  have hinv := Continuous.fourierInv_fourier_eq hcont hg hFint
  have hxinv : (f x : ℂ) = ∫ ξ, (𝐞 (inner ℝ ξ x)) • Fhat f ξ := by
    have h1 : 𝓕⁻ (𝓕 (fun u : ℝ => (f u : ℂ))) x = (f x : ℂ) := congrFun hinv x
    rw [← h1, Real.fourierInv_eq]
    simp only [Fhat]
  calc supf f = f x := hx.symm
    _ = ‖(f x : ℂ)‖ := by
        rw [show ‖(f x : ℂ)‖ = |f x| from RCLike.norm_ofReal (f x),
          abs_of_nonneg (hnn x)]
    _ = ‖∫ ξ, (𝐞 (inner ℝ ξ x)) • Fhat f ξ‖ := by rw [hxinv]
    _ ≤ ∫ ξ, ‖(𝐞 (inner ℝ ξ x)) • Fhat f ξ‖ := norm_integral_le_integral_norm _
    _ = ∫ ξ, ‖Fhat f ξ‖ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
        exact Circle.norm_smul (𝐞 (inner ℝ ξ x)) (Fhat f ξ)

/-! ### The main estimate -/

theorem supf_le_of_decay {c : ℕ → ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) (hnn : ∀ u, 0 ≤ f u) (hdec : DecayHyp c T f) {ε : ℝ}
    (hε : 0 < ε) (hc : 0 ≤ c 2 ε) :
    supf f ≤ 16 * (c 2 ε) * T ^ ε * T ^ 2 * ∫ u, f u := by
  have hM : 0 ≤ supf f := supf_nonneg hf hcs hnn
  by_cases hM0 : supf f = 0
  · -- `supf f = 0` forces `f ≡ 0`, hence `∫ f = 0`
    have hf0 : ∀ u, f u = 0 := fun u => le_antisymm (hM0 ▸ le_supf hf hcs u) (hnn u)
    have hA0 : ∫ u, f u = 0 := by simp [hf0]
    rw [hM0, hA0]; simp
  · have hMpos : 0 < supf f := lt_of_le_of_ne hM (Ne.symm hM0)
    -- `B := c 2 ε * T^ε * T² * supf f` is non-negative: otherwise the decay bound at `ξ = 1`
    -- would give `‖Fhat f 1‖ < 0`
    have hBnn : 0 ≤ c 2 ε * T ^ ε * T ^ 2 * supf f := by
      by_contra h
      push Not at h
      have h1 := norm_fhat_le_decay hdec hε 1 one_ne_zero
      have h1' : ‖Fhat f 1‖ ≤ c 2 ε * T ^ ε * T ^ 2 * supf f := by simpa using h1
      exact absurd (lt_of_le_of_lt h1' h) (not_lt_of_ge (norm_nonneg _))
    have hInt : Integrable (Fhat f) := integrable_fhat_of_bounds hf hcs hnn hdec hε hBnn
    -- the two-sided tail estimate
    have hmain : ∀ r > 0,
        supf f ≤ 2 * r * (∫ u, f u) + 2 * (c 2 ε * T ^ ε * T ^ 2 * supf f) / r := by
      intro r hr
      have h1 : supf f ≤ ∫ ξ, ‖Fhat f ξ‖ :=
        supf_le_integral_norm_fhat_aux hf hcs hnn hInt
      have h2 : ∫ ξ, ‖Fhat f ξ‖
          ≤ 2 * r * (∫ u, f u) + 2 * (c 2 ε * T ^ ε * T ^ 2 * supf f) / r :=
        integral_le_two_r_aux hr hInt.norm (fun x => norm_fhat_le_integral hnn x)
          (fun x hx => norm_fhat_le_decay hdec hε x hx)
      linarith
    have hKnn : 0 ≤ c 2 ε * T ^ ε * T ^ 2 := (mul_nonneg_iff_of_pos_right hMpos).mp hBnn
    by_cases hK0 : c 2 ε * T ^ ε * T ^ 2 = 0
    · -- `B = 0`: then `supf f ≤ 2rA` for every `r > 0`, so `supf f = 0` and `A = 0`
      exfalso
      have hle : supf f ≤ 0 := by
        apply le_of_forall_pos_le_add
        intro δ hδ
        have hA0 : 0 ≤ ∫ u, f u := integral_nonneg hnn
        have hr : 0 < δ / (2 * ((∫ u, f u) + 1)) := by
          apply div_pos hδ
          linarith
        have h := hmain _ hr
        have hzero : 2 * (c 2 ε * T ^ ε * T ^ 2 * supf f) / (δ / (2 * ((∫ u, f u) + 1))) = 0 := by
          rw [hK0]; simp
        rw [hzero, add_zero] at h
        have hstep : 2 * (δ / (2 * ((∫ u, f u) + 1))) * (∫ u, f u) ≤ δ := by
          have heq : 2 * (δ / (2 * ((∫ u, f u) + 1))) * (∫ u, f u)
              = δ * (∫ u, f u) / ((∫ u, f u) + 1) := by field_simp
          rw [heq, div_le_iff₀ (by linarith : (0 : ℝ) < (∫ u, f u) + 1)]
          nlinarith [hA0, hδ]
        linarith
      linarith
    · -- `K := c 2 ε * T^ε * T² > 0`: take `r = 4K`
      have hKpos : 0 < c 2 ε * T ^ ε * T ^ 2 := lt_of_le_of_ne hKnn (Ne.symm hK0)
      have h4 := hmain (4 * (c 2 ε * T ^ ε * T ^ 2)) (by positivity)
      have hEq : 2 * (4 * (c 2 ε * T ^ ε * T ^ 2)) * (∫ u, f u)
            + 2 * (c 2 ε * T ^ ε * T ^ 2 * supf f) / (4 * (c 2 ε * T ^ ε * T ^ 2))
          = 8 * (c 2 ε * T ^ ε * T ^ 2) * (∫ u, f u) + supf f / 2 := by
        rw [show 2 * (c 2 ε * T ^ ε * T ^ 2 * supf f) / (4 * (c 2 ε * T ^ ε * T ^ 2))
              = supf f / 2 from by
          rw [div_eq_iff (by positivity : (4 : ℝ) * (c 2 ε * T ^ ε * T ^ 2) ≠ 0)]
          ring]
        ring
      rw [hEq] at h4
      nlinarith [h4]

end

end Work.GM.Affine
