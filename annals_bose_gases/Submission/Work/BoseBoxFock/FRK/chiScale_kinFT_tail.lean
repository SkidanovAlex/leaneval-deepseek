import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseK15.ChiReg_corpus
import Submission.Work.BoseRowsFS.LatRiemann.radialDecay4
import Submission.Work.SmallBoxBridge.Resolve.kinFT_eq_fourier
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.FRK.chiScale_kinFT_tail`

The `L¹` tail of the `p`-convention Fourier transform of the scaled cubic bump

    `∫_{‖q‖ ≥ R} ‖kinFT (chiScale ℓ) q‖ dq ≤ C (1 + ℓR)⁻³`   (`ℓ > 0`, `R ≥ 0`),

with a constant `C` uniform in `ℓ, R`.

## Why this is the right shape

`chiScale ℓ z = χ(ℓ⁻¹ • z)` (`Submission.BoseGases.chiScale`), so the substitution `y = ℓ z`
gives the exact scaling law

    `kinFT (chiScale ℓ) q = ℓ³ · χ̂(ℓ • q)`,   `χ̂ := kinFT χ`   (`chiScaleC_kinFT_eq`),

and then `u = ℓ q` turns the tail integral into `∫_{‖u‖ ≥ ℓR} ‖χ̂ u‖ du`, which depends on
`(ℓ, R)` only through the product `ℓR`.  Since `χ` is `C^∞` with compact support, `χ̂` is a
Schwartz function, so it decays faster than any polynomial; the choice of decay order `6`
(`chiC_kinFT_decay`) is exactly what integrates to the sharp `(1+L)⁻³` tail
(`chiC_kinFT_tail_le`), via the one-dimensional primitive `∫_L^∞ (1+r)⁻⁴ dr = 1/(3(1+L)³)`
(copied from `Work.BoseRowsFS.LatRiemann.radialDecay4`) and the polar-coordinate identity
`Submission.BoseGases.integral_fun_norm_r3`.

## Layout

* `chiC_kinFT_decay` — order-`6` pointwise decay of `χ̂ = kinFT χ` (Schwartz-class route:
  pack `χ` as a `SchwartzMap`, use `SchwartzMap.decay` on its Fourier transform).
* the `private` lemmas — the one-dimensional tail computation on `(1+r)^{-4}`.
* `chiC_kinFT_tail_le`, `chiC_kinFT_tail` — the `(1+L)^{-3}` tail bound for `χ̂`.
* `chiScaleC_kinFT_eq` — the exact scaling law.
* `chiScale_kinFT_tail` — the target.
-/

noncomputable section

open MeasureTheory Filter
open scoped FourierTransform SchwartzMap Real Topology Pointwise

namespace Work.BoseBoxFock.FRK

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The complexified cubic bump of the corpus: `χ` viewed as a `ℂ`-valued function. -/
noncomputable def chiC : E3 → ℂ := fun z => ((Submission.BoseGases.chi z : ℝ) : ℂ)

/-! ## 0. Two elementary scalar facts -/

/-- `(1 + t)^N ≤ 2^N (1 + t^N)` for `t ≥ 0`. -/
private lemma one_add_pow_le_two_pow_mul (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (1 + t) ^ N ≤ 2 ^ N * (1 + t ^ N) := by
  rcases le_total t 1 with h | h
  · have h2 : (1 + t) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    have h3 : (1 : ℝ) ≤ 1 + t ^ N := le_add_of_nonneg_right (pow_nonneg ht N)
    calc (1 + t) ^ N ≤ 2 ^ N := h2
      _ = 2 ^ N * 1 := (mul_one _).symm
      _ ≤ 2 ^ N * (1 + t ^ N) := by gcongr
  · have h2 : (1 + t) ^ N ≤ (2 * t) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    have h5 : t ^ N ≤ 1 + t ^ N := le_add_of_nonneg_left (by norm_num)
    calc (1 + t) ^ N ≤ (2 * t) ^ N := h2
      _ = 2 ^ N * t ^ N := mul_pow 2 t N
      _ ≤ 2 ^ N * (1 + t ^ N) := by gcongr

/-- `1/x³ = x^(-3 : ℤ)`: the natural-power form of a negative integer power. -/
private lemma one_div_pow_three_eq_zpow (x : ℝ) : 1 / x ^ 3 = x ^ (-3 : ℤ) := by
  have h1 : x ^ (-(3 : ℤ)) = 1 / x ^ 3 := by
    rw [zpow_neg, inv_eq_one_div]
    congr 1
  have h2 : (-(3 : ℤ)) = (-3 : ℤ) := by norm_num
  rw [← h2]
  exact h1.symm

/-! ## 1. Order-`6` decay of the fixed bump `χ̂ = kinFT χ` -/

/-- **Rapid decay of `χ̂ = kinFT χ`.**  There is `K ≥ 0` with
`‖kinFT χ p‖ ≤ K (1 + ‖p‖)⁻⁶` for every `p`.

The bump `χ` is `C^∞` with compact support, hence a Schwartz function; its Fourier transform
is again Schwartz, which decays faster than any polynomial.  Concretely, with `H := 𝓕 χ`
(a Schwartz map), `SchwartzMap.decay H 6 0` and `SchwartzMap.decay H 0 0` give
`‖x‖⁶‖H x‖ ≤ C₆` and `‖H x‖ ≤ C₀`, and `(1 + ‖x‖)⁶ ≤ 2⁶(1 + ‖x‖⁶)` then yields
`‖H x‖ ≤ 64(C₀ + C₆)/(1 + ‖x‖)⁶`.  Passing to the `kinFT` convention
(`kinFT_eq_fourier`: `kinFT χ p = 𝓕 χ ((2π)⁻¹ • p)`) costs a factor `(2π)⁶`. -/
theorem chiC_kinFT_decay :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : E3, ‖Submission.BoseGases.kinFT chiC p‖ ≤ K / (1 + ‖p‖) ^ 6 := by
  have hcs : HasCompactSupport chiC :=
    Submission.BoseGases.chi_hasCompactSupport.comp_left (by simp)
  have hdiff : ContDiff ℝ (⊤ : ℕ∞) chiC :=
    Complex.ofRealCLM.contDiff.comp Submission.BoseGases.chi_contDiff
  let G : 𝓢(E3, ℂ) := hcs.toSchwartzMap hdiff
  have hGcoe : ⇑G = chiC := funext (fun z => HasCompactSupport.toSchwartzMap_toFun hcs hdiff z)
  let H : 𝓢(E3, ℂ) := SchwartzMap.fourierTransformCLM ℂ G
  have hHcoe : ⇑H = 𝓕 (chiC) := by
    show ⇑(SchwartzMap.fourierTransformCLM ℂ G) = 𝓕 chiC
    rw [← hGcoe]
    exact SchwartzMap.fourier_coe G
  obtain ⟨C6, _hC6pos, hC6⟩ := SchwartzMap.decay H 6 0
  obtain ⟨C0, _hC0pos, hC0⟩ := SchwartzMap.decay H 0 0
  have hC6' : ∀ ξ : E3, ‖ξ‖ ^ 6 * ‖H ξ‖ ≤ C6 := by
    intro ξ; simpa only [norm_iteratedFDeriv_zero] using hC6 ξ
  have hC0' : ∀ ξ : E3, ‖H ξ‖ ≤ C0 := by
    intro ξ; simpa only [norm_iteratedFDeriv_zero, pow_zero, one_mul] using hC0 ξ
  refine ⟨(64 * (C0 + C6)) * (2 * π) ^ 6, by positivity, fun p => ?_⟩
  have hbound : ∀ ξ : E3, ‖H ξ‖ ≤ (64 * (C0 + C6)) / (1 + ‖ξ‖) ^ 6 := by
    intro ξ
    have key : (1 + ‖ξ‖) ^ 6 * ‖H ξ‖ ≤ 64 * (C0 + C6) := by
      have hA := one_add_pow_le_two_pow_mul 6 (norm_nonneg ξ)
      have hnn : (0 : ℝ) ≤ ‖H ξ‖ := norm_nonneg _
      have step : (1 + ‖ξ‖) ^ 6 * ‖H ξ‖ ≤ (2 ^ 6 * (1 + ‖ξ‖ ^ 6)) * ‖H ξ‖ :=
        mul_le_mul_of_nonneg_right hA hnn
      have step2 : (2 ^ 6 * (1 + ‖ξ‖ ^ 6)) * ‖H ξ‖ = 64 * (‖H ξ‖ + ‖ξ‖ ^ 6 * ‖H ξ‖) := by
        norm_num; ring
      have h1 := hC0' ξ
      have h2 := hC6' ξ
      linarith [step, step2]
    rw [le_div_iff₀ (by positivity)]
    linarith [key]
  have hnorm : ‖(2 * π)⁻¹ • p‖ = (2 * π)⁻¹ * ‖p‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have hpi : (1 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_three]
  have h1 : 1 + ‖p‖ ≤ 2 * π * (1 + (2 * π)⁻¹ * ‖p‖) := by
    have hmul : 2 * π * (2 * π)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
    have hpp : (0 : ℝ) ≤ ‖p‖ := norm_nonneg p
    nlinarith [hpi, hpp, hmul]
  have h2 : (1 + ‖p‖) ^ 6 ≤ (2 * π) ^ 6 * (1 + (2 * π)⁻¹ * ‖p‖) ^ 6 := by
    have h' := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + ‖p‖) h1 6
    rwa [mul_pow] at h'
  calc ‖Submission.BoseGases.kinFT chiC p‖
      = ‖𝓕 chiC ((2 * π)⁻¹ • p)‖ := by rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
    _ = ‖H ((2 * π)⁻¹ • p)‖ := by rw [← hHcoe]
    _ ≤ (64 * (C0 + C6)) / (1 + ‖(2 * π)⁻¹ • p‖) ^ 6 := hbound _
    _ ≤ (64 * (C0 + C6)) * (2 * π) ^ 6 / (1 + ‖p‖) ^ 6 := by
        rw [hnorm, div_le_div_iff₀ (by positivity) (by positivity)]
        conv_rhs => rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 64 * (C0 + C6) by positivity)

/-! ## 2. The one-dimensional tail of `(1 + r)^{-4}` on `(0, ∞)`

These four lemmas are the (one-dimensional) computation behind the sharp rate: the primitive
of `(1+r)^{-4}` is `-(1/3)(1+r)^{-3}`, so the tail from `L ≥ 0` is `1/(3(1+L)³)`.
-/

private lemma inv_one_add_pow_eq_rpow_neg (n : ℕ) (r : ℝ) (hr : 0 ≤ 1 + r) :
    ((1 + r) ^ n)⁻¹ = (1 + r) ^ (-(n : ℝ)) := by
  have h4 : (1 + r) ^ ((n : ℝ)) = (1 + r) ^ n := Real.rpow_natCast (1 + r) n
  rw [← h4, ← Real.rpow_neg hr (n : ℝ)]

private lemma integrableOn_Ioi_inv_one_add_pow_four (c : ℝ) (hc : -1 < c) :
    IntegrableOn (fun r : ℝ => ((1 + r) ^ 4)⁻¹) (Set.Ioi c) := by
  have h1 : IntegrableOn (fun r : ℝ => (1 + r) ^ (-4 : ℝ)) (Set.Ioi c) := by
    have h' := integrableOn_add_rpow_Ioi_of_lt (a := (-4 : ℝ)) (c := c) (m := (1 : ℝ))
      (by norm_num) (by linarith)
    simpa [add_comm] using h'
  refine h1.congr_fun ?_ measurableSet_Ioi
  intro r hr
  exact (inv_one_add_pow_eq_rpow_neg 4 r (by have := Set.mem_Ioi.mp hr; linarith)).symm

private lemma integral_Ioi_inv_one_add_pow_four (c : ℝ) (hc : 0 ≤ c) :
    (∫ r in Set.Ioi c, ((1 + r) ^ 4)⁻¹) = 1 / (3 * (1 + c) ^ 3) := by
  have hderiv : ∀ x ∈ Set.Ici c,
      HasDerivAt (fun r : ℝ => -(1 / 3) * (1 + r) ^ (-3 : ℝ)) ((1 + x) ^ (-4 : ℝ)) x := by
    intro x hx
    have hx0 : 1 + x ≠ 0 := by have := Set.mem_Ici.mp hx; linarith
    have hbase : HasDerivAt (fun r : ℝ => (1 + r)) 1 x := by
      simpa using (hasDerivAt_id x).const_add (1 : ℝ)
    have h1 : HasDerivAt (fun r : ℝ => (1 + r) ^ (-3 : ℝ))
        ((-3 : ℝ) * (1 + x) ^ (-4 : ℝ)) x := by
      have hh := hbase.rpow_const (p := (-3 : ℝ)) (Or.inl hx0)
      simpa [show (-3 : ℝ) - 1 = (-4 : ℝ) by norm_num, one_mul] using hh
    have h3 := h1.const_mul (-(1 / 3))
    have key : (-(1 / 3) : ℝ) * ((-3 : ℝ) * (1 + x) ^ (-4 : ℝ)) = (1 + x) ^ (-4 : ℝ) := by
      ring
    rw [key] at h3
    exact h3
  have hint : IntegrableOn (fun r : ℝ => (1 + r) ^ (-4 : ℝ)) (Set.Ioi c) := by
    have h' := integrableOn_add_rpow_Ioi_of_lt (a := (-4 : ℝ)) (c := c) (m := (1 : ℝ))
      (by norm_num) (by linarith)
    simpa [add_comm] using h'
  have htend : Tendsto (fun r : ℝ => (1 + r) ^ (-3 : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (y := (3 : ℝ)) (by norm_num)).comp
      (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)
  have hf : Tendsto (fun r : ℝ => -(1 / 3) * (1 + r) ^ (-3 : ℝ)) atTop (𝓝 0) := by
    have h := htend.const_mul (-(1 / 3))
    rw [mul_zero] at h
    exact h
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' (a := c) hderiv hint hf
  have hconv : (∫ r in Set.Ioi c, (1 + r) ^ (-4 : ℝ)) = ∫ r in Set.Ioi c, ((1 + r) ^ 4)⁻¹ := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro r hr
    exact (inv_one_add_pow_eq_rpow_neg 4 r (by have := Set.mem_Ioi.mp hr; linarith)).symm
  rw [← hconv, hftc]
  have h3 : (1 + c) ^ (-3 : ℝ) = ((1 + c) ^ 3)⁻¹ := by
    rw [Real.rpow_neg (by linarith)]
    simp
  rw [h3]
  rw [show (0 : ℝ) - -(1 / 3) * ((1 + c) ^ 3)⁻¹ = 1 / (3 * (1 + c) ^ 3) by
    have hc3 : (1 + c) ^ 3 ≠ 0 := by positivity
    field_simp
    ring]

/-- `∫_{r > 0} 1_{L ≤ r}(1+r)^{-4} dr = 1/(3(1+L)³)` for `L ≥ 0`. -/
private lemma setIntegral_Ioi_zero_indicator_Ici (c : ℝ) (hc : 0 ≤ c) :
    (∫ r in Set.Ioi (0 : ℝ), (Set.Ici c).indicator (fun r : ℝ => ((1 + r) ^ 4)⁻¹) r)
      = 1 / (3 * (1 + c) ^ 3) := by
  rw [setIntegral_indicator measurableSet_Ici]
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · rw [← hc0]
    have hset : Set.Ioi (0 : ℝ) ∩ Set.Ici 0 = Set.Ioi 0 := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
      constructor
      · intro h; exact h.1
      · intro h; exact ⟨h, le_of_lt h⟩
    rw [hset]
    exact integral_Ioi_inv_one_add_pow_four 0 le_rfl
  · have hset : Set.Ioi (0 : ℝ) ∩ Set.Ici c = Set.Ici c := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
      constructor
      · intro h; exact h.2
      · intro h; exact ⟨lt_of_lt_of_le hcpos h, h⟩
    rw [hset, setIntegral_congr_set Ioi_ae_eq_Ici.symm]
    exact integral_Ioi_inv_one_add_pow_four c hc

/-- The truncated `(1+r)^{-4}` is integrable on `(0, ∞)`. -/
private lemma integrableOn_Ioi_trunc_inv_one_add_pow_four (L : ℝ) :
    IntegrableOn (fun r : ℝ => if L ≤ r then ((1 + r) ^ 4)⁻¹ else 0) (Set.Ioi 0) := by
  have hbase : IntegrableOn (fun r : ℝ => ((1 + r) ^ 4)⁻¹) (Set.Ioi 0) :=
    integrableOn_Ioi_inv_one_add_pow_four 0 (by norm_num)
  refine Integrable.mono' hbase ?_ ?_
  · exact (Measurable.ite measurableSet_Ici (by fun_prop) measurable_const).aestronglyMeasurable
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hr0 : (0 : ℝ) < r := hr
    have hf0 : 0 ≤ ((1 + r) ^ 4)⁻¹ := by positivity
    by_cases h : L ≤ r
    · rw [if_pos h, Real.norm_of_nonneg hf0]
    · rw [if_neg h, norm_zero]
      exact hf0

/-! ## 3. The tail bound for the fixed bump `χ̂` -/

/-- **The `(1+L)^{-3}` tail bound for `χ̂ = kinFT χ`**, with the constant `K` of the
pointwise decay made explicit.

The chain is: dominate `‖χ̂ p‖` by `K(1+‖p‖)^{-6}`; reduce the tail integral to the radial
one `4π ∫_{r>0} r² 1_{L≤r}(1+r)^{-6} dr` (`integral_fun_norm_r3`); use
`r²(1+r)^{-6} ≤ (1+r)^{-4}` on `r > 0`, whose tail is `1/(3(1+L)³)`. -/
lemma chiC_kinFT_tail_le (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ p : E3, ‖Submission.BoseGases.kinFT chiC p‖ ≤ K / (1 + ‖p‖) ^ 6) :
    ∀ L : ℝ, 0 ≤ L →
      ∫ p in {p : E3 | L ≤ ‖p‖}, ‖Submission.BoseGases.kinFT chiC p‖
        ≤ (K * (4 * π / 3)) / (1 + L) ^ 3 := by
  intro L hL
  have hsmeas : MeasurableSet {p : E3 | L ≤ ‖p‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  -- integrability of the `p`-space majorant, via polar coordinates
  have h1d : IntegrableOn (fun r : ℝ => r ^ 2 * (1 / (1 + r) ^ 6)) (Set.Ioi 0) := by
    refine Integrable.mono' (integrableOn_Ioi_inv_one_add_pow_four 0 (by norm_num)) ?_ ?_
    · exact (by fun_prop : Measurable (fun r : ℝ => r ^ 2 * (1 / (1 + r) ^ 6))).aestronglyMeasurable
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with r hr
      have hr0 : (0 : ℝ) < r := hr
      have hnn : 0 ≤ ((1 + r) ^ 6)⁻¹ := by positivity
      have h2 : r ^ 2 ≤ (1 + r) ^ 2 := by nlinarith [sq_nonneg (1 + r), hr0]
      rw [one_div, Real.norm_of_nonneg (by positivity)]
      calc r ^ 2 * ((1 + r) ^ 6)⁻¹ ≤ (1 + r) ^ 2 * ((1 + r) ^ 6)⁻¹ :=
            mul_le_mul_of_nonneg_right h2 hnn
        _ = ((1 + r) ^ 4)⁻¹ := by field_simp
  have hdiv : Integrable (fun p : E3 => 1 / (1 + ‖p‖) ^ 6) :=
    (Submission.BoseGases.integrable_radial_r3 (f := fun r : ℝ => 1 / (1 + r) ^ 6)).mpr h1d
  have hpt : ∀ p : E3, ‖Submission.BoseGases.kinFT chiC p‖ ≤ K * (1 / (1 + ‖p‖) ^ 6) := by
    intro p; rw [← div_eq_mul_one_div]; exact hK p
  have hstep1 : ∫ p in {p : E3 | L ≤ ‖p‖}, ‖Submission.BoseGases.kinFT chiC p‖
      ≤ ∫ p in {p : E3 | L ≤ ‖p‖}, K * (1 / (1 + ‖p‖) ^ 6) := by
    refine setIntegral_mono_of_nonneg (fun p _ => norm_nonneg _) (fun p _ => hpt p) ?_
    exact (hdiv.const_mul K).integrableOn
  have hstep3 : ∫ p in {p : E3 | L ≤ ‖p‖}, 1 / (1 + ‖p‖) ^ 6
      = 4 * π * ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * (if L ≤ r then 1 / (1 + r) ^ 6 else 0) := by
    rw [← integral_indicator hsmeas]
    have hfun : (fun p : E3 =>
        {p : E3 | L ≤ ‖p‖}.indicator (fun p : E3 => 1 / (1 + ‖p‖) ^ 6) p)
        = fun p : E3 => (fun r : ℝ => if L ≤ r then 1 / (1 + r) ^ 6 else 0) ‖p‖ := by
      funext p
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    rw [hfun, Submission.BoseGases.integral_fun_norm_r3
      (g := fun r : ℝ => if L ≤ r then 1 / (1 + r) ^ 6 else 0)]
  have hstep4 : (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * (if L ≤ r then 1 / (1 + r) ^ 6 else 0))
      ≤ ∫ r in Set.Ioi (0 : ℝ), (if L ≤ r then ((1 + r) ^ 4)⁻¹ else 0) := by
    refine setIntegral_mono_of_nonneg (fun r _ => ?_) (fun r hr => ?_)
      (integrableOn_Ioi_trunc_inv_one_add_pow_four L)
    · by_cases h : L ≤ r
      · rw [if_pos h]; positivity
      · rw [if_neg h, mul_zero]
    · have hr0 : (0 : ℝ) < r := hr
      by_cases h : L ≤ r
      · rw [if_pos h, if_pos h]
        have h2 : r ^ 2 ≤ (1 + r) ^ 2 := by nlinarith [sq_nonneg (1 + r), hr0]
        have hnn : 0 ≤ ((1 + r) ^ 6)⁻¹ := by positivity
        rw [one_div]
        calc r ^ 2 * ((1 + r) ^ 6)⁻¹ ≤ (1 + r) ^ 2 * ((1 + r) ^ 6)⁻¹ :=
              mul_le_mul_of_nonneg_right h2 hnn
          _ = ((1 + r) ^ 4)⁻¹ := by field_simp
      · rw [if_neg h, if_neg h, mul_zero]
  have hstep5 : (∫ r in Set.Ioi (0 : ℝ), (if L ≤ r then ((1 + r) ^ 4)⁻¹ else 0))
      = 1 / (3 * (1 + L) ^ 3) := by
    have hfun : (fun r : ℝ => if L ≤ r then ((1 + r) ^ 4)⁻¹ else 0)
        = (Set.Ici L).indicator (fun r : ℝ => ((1 + r) ^ 4)⁻¹) := by
      funext r
      by_cases h : L ≤ r <;> simp [h, Set.indicator_of_mem, Set.indicator_of_notMem]
    rw [hfun, setIntegral_Ioi_zero_indicator_Ici L hL]
  calc ∫ p in {p : E3 | L ≤ ‖p‖}, ‖Submission.BoseGases.kinFT chiC p‖
      ≤ ∫ p in {p : E3 | L ≤ ‖p‖}, K * (1 / (1 + ‖p‖) ^ 6) := hstep1
    _ = K * ∫ p in {p : E3 | L ≤ ‖p‖}, 1 / (1 + ‖p‖) ^ 6 := integral_const_mul K _
    _ = K * (4 * π * ∫ r in Set.Ioi (0 : ℝ),
            r ^ 2 * (if L ≤ r then 1 / (1 + r) ^ 6 else 0)) := by rw [hstep3]
    _ ≤ K * (4 * π * ∫ r in Set.Ioi (0 : ℝ),
            (if L ≤ r then ((1 + r) ^ 4)⁻¹ else 0)) := by
          apply mul_le_mul_of_nonneg_left _ hK0
          exact mul_le_mul_of_nonneg_left hstep4 (by positivity)
    _ = K * (4 * π * (1 / (3 * (1 + L) ^ 3))) := by rw [hstep5]
    _ = K * (4 * π / 3) / (1 + L) ^ 3 := by
          have hkey : (4 : ℝ) * π * (1 / (3 * (1 + L) ^ 3)) = 4 * π / 3 / (1 + L) ^ 3 := by
            field_simp
          rw [hkey, ← mul_div_assoc]

/-- **The tail bound for the fixed bump `χ̂`**: there is `C ≥ 0` with
`∫_{‖p‖ ≥ L} ‖χ̂ p‖ ≤ C (1 + L)^{-3}` for every `L ≥ 0`. -/
theorem chiC_kinFT_tail : ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L →
    ∫ p in {p : E3 | L ≤ ‖p‖}, ‖Submission.BoseGases.kinFT chiC p‖ ≤ C / (1 + L) ^ 3 := by
  obtain ⟨K, hK0, hK⟩ := chiC_kinFT_decay
  exact ⟨K * (4 * π / 3), by positivity, chiC_kinFT_tail_le K hK0 hK⟩

/-! ## 4. The scaling law -/

/-- **The exact scaling law**: for `ℓ > 0`,
`kinFT (chiScale ℓ) q = ℓ³ · χ̂(ℓ • q)` with `χ̂ = kinFT χ`.

Substituting `y = ℓ z` (i.e. `y = (ℓ⁻¹)⁻¹ • z`, the `integral_comp_inv_smul_of_nonneg` change
of variables, whose Jacobian is `ℓ³` in dimension `3`) and using
`⟪ℓ q, ℓ⁻¹ y⟫ = ⟪q, y⟫`. -/
lemma chiScaleC_kinFT_eq {ℓ : ℝ} (hℓ : 0 < ℓ) (q : E3) :
    Submission.BoseGases.kinFT
        (fun z : E3 => ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)) q
      = ((ℓ ^ 3 : ℝ) : ℂ) * Submission.BoseGases.kinFT chiC (ℓ • q) := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hfr : Module.finrank ℝ E3 = 3 := by simp
  set F : E3 → ℂ := fun z => Complex.exp (-(Complex.I * ((inner ℝ (ℓ • q) z : ℝ) : ℂ))) *
      ((Submission.BoseGases.chi z : ℝ) : ℂ) with hF
  have key : ∀ y : E3,
      Complex.exp (-(Complex.I * ((inner ℝ q y : ℝ) : ℂ))) *
          ((Submission.BoseGases.chi ((ℓ⁻¹) • y) : ℝ) : ℂ)
        = F ((ℓ⁻¹) • y) := by
    intro y
    have hinner : inner ℝ (ℓ • q) ((ℓ⁻¹) • y) = inner ℝ q y := by
      rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hℓne, one_mul]
    rw [hF]
    simp only
    rw [hinner]
  have hkin : (∫ z : E3, F z) = Submission.BoseGases.kinFT chiC (ℓ • q) := by
    rw [hF]
    rfl
  calc Submission.BoseGases.kinFT
        (fun z : E3 => ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)) q
      = ∫ y : E3, Complex.exp (-(Complex.I * ((inner ℝ q y : ℝ) : ℂ))) *
          ((Submission.BoseGases.chi ((ℓ⁻¹) • y) : ℝ) : ℂ) := rfl
    _ = ∫ y : E3, F ((ℓ⁻¹) • y) := by
          apply integral_congr_ae
          filter_upwards with y
          exact key y
    _ = (ℓ ^ (Module.finrank ℝ E3)) • (∫ z : E3, F z) :=
          Measure.integral_comp_inv_smul_of_nonneg (μ := volume) F hℓ.le
    _ = ((ℓ ^ 3 : ℝ) : ℂ) * Submission.BoseGases.kinFT chiC (ℓ • q) := by
          rw [hfr, Complex.real_smul, hkin]

/-! ## 5. The target -/

theorem chiScale_kinFT_tail : ∃ C : ℝ, 0 ≤ C ∧ ∀ {ℓ R : ℝ}, 0 < ℓ → 0 ≤ R →
    MeasureTheory.integral
        (MeasureTheory.volume.restrict {q : EuclideanSpace ℝ (Fin 3) | R ≤ ‖q‖})
        (fun q : EuclideanSpace ℝ (Fin 3) =>
          ‖Submission.BoseGases.kinFT
            (fun z : EuclideanSpace ℝ (Fin 3) => (Submission.BoseGases.chiScale ℓ z : ℂ)) q‖)
      ≤ C * (1 + ℓ * R) ^ (-3 : ℤ) := by
  obtain ⟨C, hC0, hC⟩ := chiC_kinFT_tail
  refine ⟨C, hC0, fun {ℓ R} hℓ hR => ?_⟩
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hfr : Module.finrank ℝ E3 = 3 := by simp
  -- the pointwise norm identity
  have hnormC : ‖((ℓ ^ 3 : ℝ) : ℂ)‖ = ℓ ^ 3 := by
    have h1 : ‖((ℓ ^ 3 : ℝ) : ℂ)‖ = |ℓ ^ 3| := RCLike.norm_ofReal (ℓ ^ 3)
    rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ℓ ^ 3)] at h1
  have hpt : ∀ q : E3, ‖Submission.BoseGases.kinFT
        (fun z : E3 => ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)) q‖
      = ℓ ^ 3 * ‖Submission.BoseGases.kinFT chiC (ℓ • q)‖ := by
    intro q
    rw [chiScaleC_kinFT_eq hℓ q, norm_mul, hnormC]
  -- the rescaled tail region
  have hset : ℓ • ({q : E3 | R ≤ ‖q‖} : Set E3) = {p : E3 | ℓ * R ≤ ‖p‖} := by
    ext p
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨q, hq, rfl⟩
      simp only [Set.mem_ofPred_eq] at hq ⊢
      rw [norm_smul, Real.norm_of_nonneg hℓ.le]
      exact mul_le_mul_of_nonneg_left hq hℓ.le
    · intro hp
      simp only [Set.mem_ofPred_eq] at hp ⊢
      refine ⟨ℓ⁻¹ • p, ?_, ?_⟩
      · rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        have h2 := mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ ℓ⁻¹)
        rwa [← mul_assoc, inv_mul_cancel₀ hℓne, one_mul] at h2
      · rw [smul_smul, mul_inv_cancel₀ hℓne, one_smul]
  have hmain : (∫ q in {q : E3 | R ≤ ‖q‖}, ‖Submission.BoseGases.kinFT
        (fun z : E3 => ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)) q‖)
      = ∫ p in {p : E3 | ℓ * R ≤ ‖p‖}, ‖Submission.BoseGases.kinFT chiC p‖ := by
    calc ∫ q in {q : E3 | R ≤ ‖q‖}, ‖Submission.BoseGases.kinFT
          (fun z : E3 => ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)) q‖
        = ∫ q in {q : E3 | R ≤ ‖q‖}, ℓ ^ 3 * ‖Submission.BoseGases.kinFT chiC (ℓ • q)‖ := by
            apply setIntegral_congr_fun
              (isClosed_le continuous_const continuous_norm).measurableSet
            intro q _
            exact hpt q
      _ = ℓ ^ 3 * ∫ q in {q : E3 | R ≤ ‖q‖},
            ‖Submission.BoseGases.kinFT chiC (ℓ • q)‖ := integral_const_mul _ _
      _ = ℓ ^ 3 * ((ℓ ^ 3)⁻¹ * ∫ p in {p : E3 | ℓ * R ≤ ‖p‖},
            ‖Submission.BoseGases.kinFT chiC p‖) := by
            rw [Measure.setIntegral_comp_smul_of_pos (μ := volume)
                  (f := fun p : E3 => ‖Submission.BoseGases.kinFT chiC p‖)
                  (s := {q : E3 | R ≤ ‖q‖}) hℓ, hset, hfr, smul_eq_mul]
      _ = ∫ p in {p : E3 | ℓ * R ≤ ‖p‖}, ‖Submission.BoseGases.kinFT chiC p‖ := by
            rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 3 hℓne), one_mul]
  calc MeasureTheory.integral (MeasureTheory.volume.restrict {q : E3 | R ≤ ‖q‖})
        (fun q : E3 => ‖Submission.BoseGases.kinFT
          (fun z : E3 => ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)) q‖)
      = ∫ q in {q : E3 | R ≤ ‖q‖}, ‖Submission.BoseGases.kinFT
          (fun z : E3 => ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)) q‖ := rfl
    _ = ∫ p in {p : E3 | ℓ * R ≤ ‖p‖}, ‖Submission.BoseGases.kinFT chiC p‖ := hmain
    _ ≤ C / (1 + ℓ * R) ^ 3 := hC (ℓ * R) (mul_nonneg hℓ.le hR)
    _ = C * (1 + ℓ * R) ^ (-3 : ℤ) := by
          rw [div_eq_mul_inv, ← one_div_pow_three_eq_zpow, inv_eq_one_div]

end Work.BoseBoxFock.FRK
