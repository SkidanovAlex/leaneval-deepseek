import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiTailDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.wLoc_fibre_kernelCompare`

The comparison of the fibre `w1Fibre ℓ (wLoc ℓ g 0)` of the localised kernel at the cell
`u = 0` with the *constant* profile `chat (wScaled ℓ g) 0 · χ_ℓ(x)²`.

For an even `g`, integrable and supported in `ball 0 R` with `R ≤ ℓ·chiR0`:

* pointwise in `x`,
  `|Ĝ(0)·χ_ℓ(x)² − w1Fibre ℓ (wLoc ℓ g 0) x| ≤ C (R/ℓ)² ∫|wScaled ℓ g|`;
* and the `acube ℓ`-average of the fibre differs from `Ĝ(0)` by the same amount.

Both are consequences of two *second order* facts about `χ`:
`lem:Convolution` (`Submission.BoseGases.convolution_approx`, the Taylor remainder of the bump
with the linear term killed by evenness of `g`) for the pointwise statement, and
`∫_{acube²} wPair = ℓ³∫g` (`wPair_double_full_integral`) together with the quadratic deviation of
`χ⋆χ` from `1` (`conv3chi_second_order_bound`) for the average.
-/

noncomputable section

open MeasureTheory Metric
open scoped Topology Real

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Elementary facts about the localised kernel -/

/-- At the translation parameter `u = 0` the localisation kernel is the χ-renormalised pair
kernel. -/
lemma wLocKC_wLoc_zero_eq_wPair (ℓ : ℝ) (h : E3 → ℝ) (x y : E3) :
    Submission.BoseGases.wLoc ℓ h 0 x y = Submission.BoseGases.wPair ℓ h x y := by
  simp only [Submission.BoseGases.wLoc, Submission.BoseGases.wPair,
    Submission.BoseGases.chiU, Submission.BoseGases.chiScale, sub_zero]

/-- `wScaled` of an even function is even. -/
lemma wLocKC_wScaled_even {h : E3 → ℝ} (hh : ∀ z : E3, h (-z) = h z) (ℓ : ℝ) (z : E3) :
    Submission.BoseGases.wScaled ℓ h (-z) = Submission.BoseGases.wScaled ℓ h z := by
  unfold Submission.BoseGases.wScaled
  rw [hh z, Submission.BoseGases.convScale_symm ℓ z]

/-- `chat W 0 = ∫ W` (the Fourier transform at the origin is the integral). -/
lemma wLocKC_chat_zero_eq_integral (W : E3 → ℝ) :
    Work.BoseFixR.chat W 0 = ∫ z : E3, W z := by
  rw [Work.BoseFixR.chat]
  have h1 : Submission.BoseGases.kinFT (fun y : E3 => ((W y : ℝ) : ℂ)) 0
      = ∫ y : E3, ((W y : ℝ) : ℂ) := by
    simp [Submission.BoseGases.kinFT]
  have h2 : (∫ y : E3, ((W y : ℝ) : ℂ)) = ((∫ y : E3, W y : ℝ) : ℂ) := integral_ofReal
  rw [h1, h2, Complex.ofReal_re]

/-! ## The second order data of `χ` and of `χ ⋆ χ` -/

/-- **Global quadratic deviation of `χ⋆χ` from `1`**: `|(χ⋆χ)(t) − 1| ≤ C‖t‖²` for every `t`.
Local version `conv3chi_second_order_bound`; outside its ball `0 ≤ χ⋆χ ≤ 1` gives `|·| ≤ 2`. -/
lemma wLocKC_conv3chi_dev_quadratic :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : E3,
      |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi t - 1|
        ≤ C * ‖t‖ ^ 2 := by
  obtain ⟨C, hC0, r₁, hr₁, hloc⟩ := Submission.BoseGases.conv3chi_second_order_bound
  refine ⟨max C (2 / r₁ ^ 2), le_trans hC0 (le_max_left C _), fun t => ?_⟩
  by_cases ht : ‖t‖ ≤ r₁
  · calc |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi t - 1|
        ≤ C * ‖t‖ ^ 2 := hloc t ht
      _ ≤ max C (2 / r₁ ^ 2) * ‖t‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (le_max_left C _) (sq_nonneg _)
  · have htr : r₁ < ‖t‖ := lt_of_not_ge ht
    have h1 : Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi t ≤ 1 :=
      Submission.BoseGases.conv3chi_le_one t
    have h2 : 0 ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi t :=
      Submission.BoseGases.conv3chi_nonneg t
    have h3 : |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi t - 1|
        ≤ 2 := by
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    have hsq : r₁ ^ 2 ≤ ‖t‖ ^ 2 := pow_le_pow_left₀ hr₁.le htr.le 2
    have hC2 : 2 / r₁ ^ 2 * r₁ ^ 2 = 2 := by field_simp
    have hkey : 2 ≤ 2 / r₁ ^ 2 * ‖t‖ ^ 2 := by
      have hpos : 0 ≤ 2 / r₁ ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left hsq hpos
      linarith
    calc |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi t - 1|
        ≤ 2 := h3
      _ ≤ 2 / r₁ ^ 2 * ‖t‖ ^ 2 := hkey
      _ ≤ max C (2 / r₁ ^ 2) * ‖t‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (le_max_right C _) (sq_nonneg _)

/-- The scaled self-convolution `convScale ℓ z = (χ⋆χ)(z/ℓ)` deviates from `1` at second order. -/
lemma wLocKC_convScale_dev_le {ℓ : ℝ} (hℓ : 0 < ℓ) {C : ℝ} (_hC : 0 ≤ C)
    (hdev : ∀ t : E3,
      |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi t - 1|
        ≤ C * ‖t‖ ^ 2) (z : E3) :
    |Submission.BoseGases.convScale ℓ z - 1| ≤ C * (‖z‖ / ℓ) ^ 2 := by
  have hn : ‖(ℓ⁻¹) • z‖ = ‖z‖ / ℓ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ), div_eq_inv_mul]
  have h := hdev ((ℓ⁻¹) • z)
  rw [hn] at h
  simpa [Submission.BoseGases.convScale] using h

/-! ## The fibre of the localised kernel as a `χ`-convolution -/

/-- **The fibre identity**: `w1Fibre ℓ (wLoc ℓ h 0) x = χ_ℓ(x)·∫_y W(y)·χ_ℓ(x−y) dy` with
`W = wScaled ℓ h`.  (`wLoc ℓ h 0 = wPair ℓ h` splits off the outer factor `χ_ℓ(x)`; the inner
`acube`-integral of a function supported in `acube` is the full integral; and `y ↦ x − y` is
measure preserving.) -/
lemma wLocKC_fibre_eq {ℓ : ℝ} (hℓ : 0 < ℓ) (h : E3 → ℝ) (x : E3) :
    Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wLoc ℓ h 0) x
      = Submission.BoseGases.chiScale ℓ x *
          ∫ y : E3, Submission.BoseGases.wScaled ℓ h y *
            Submission.BoseGases.chiScale ℓ (x - y) := by
  unfold Submission.BoseGases.w1Fibre
  have hpt : ∀ y : E3, Submission.BoseGases.wLoc ℓ h 0 x y
      = Submission.BoseGases.chiScale ℓ x *
          (Submission.BoseGases.wScaled ℓ h (x - y) * Submission.BoseGases.chiScale ℓ y) := by
    intro y
    simp only [Submission.BoseGases.wLoc, Submission.BoseGases.chiU,
      Submission.BoseGases.chiScale, sub_zero]
    ring
  calc (∫ y in Submission.BoseGases.acube ℓ, Submission.BoseGases.wLoc ℓ h 0 x y)
      = ∫ y in Submission.BoseGases.acube ℓ, Submission.BoseGases.chiScale ℓ x *
          (Submission.BoseGases.wScaled ℓ h (x - y) * Submission.BoseGases.chiScale ℓ y) := by
        apply setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
        intro y _
        exact hpt y
    _ = Submission.BoseGases.chiScale ℓ x *
          (∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wScaled ℓ h (x - y) * Submission.BoseGases.chiScale ℓ y) := by
        rw [MeasureTheory.integral_const_mul]
    _ = Submission.BoseGases.chiScale ℓ x *
          (∫ y : E3,
            Submission.BoseGases.wScaled ℓ h (x - y) * Submission.BoseGases.chiScale ℓ y) := by
        congr 1
        exact Submission.BoseGases.integral_cube_eq_full_of_support (ℓ := ℓ)
          (f := fun y : E3 =>
            Submission.BoseGases.wScaled ℓ h (x - y) * Submission.BoseGases.chiScale ℓ y)
          (by
            intro y hy
            exact Submission.BoseGases.chiScale_mem_acube hℓ (fun hc => hy (by simp [hc])))
    _ = Submission.BoseGases.chiScale ℓ x *
          (∫ y : E3, Submission.BoseGases.wScaled ℓ h y *
            Submission.BoseGases.chiScale ℓ (x - y)) := by
        congr 1
        have hgen := Submission.BoseGases.integral_comp_sub_left
          (g := fun z : E3 =>
            Submission.BoseGases.wScaled ℓ h (x - z) * Submission.BoseGases.chiScale ℓ z) x
        simpa using hgen.symm

/-! ## The main comparison -/

theorem wLoc_fibre_kernelCompare :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ : ℝ},
      0 < R → 0 < ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 →
      (∀ z, g (-z) = g z) →
      tsupport g ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R →
      MeasureTheory.Integrable g →
      (∀ x : EuclideanSpace ℝ (Fin 3),
        |Work.BoseFixR.chat (Submission.BoseGases.wScaled ℓ g) 0 *
            Submission.BoseGases.chiScale ℓ x ^ 2
          - Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wLoc ℓ g 0) x|
          ≤ C * (R / ℓ) ^ 2 *
              ∫ z : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.wScaled ℓ g z|)
      ∧ |(ℓ ^ 3)⁻¹ * (∫ x in Submission.BoseGases.acube ℓ,
              Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wLoc ℓ g 0) x)
            - Work.BoseFixR.chat (Submission.BoseGases.wScaled ℓ g) 0|
          ≤ C * (R / ℓ) ^ 2 *
              ∫ z : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.wScaled ℓ g z| := by
  obtain ⟨Cχ, hCχ0, hχT⟩ := Submission.BoseGases.chi_second_order_bound
  obtain ⟨C₁, hC₁0, hdev⟩ := wLocKC_conv3chi_dev_quadratic
  set C : ℝ := max (Submission.BoseGases.chiSup * Cχ) C₁ with hCdef
  have hCle : Submission.BoseGases.chiSup * Cχ ≤ C := le_max_left _ _
  have hC1le : C₁ ≤ C := le_max_right _ _
  have hC0 : 0 ≤ C :=
    le_trans (mul_nonneg (le_of_lt Submission.BoseGases.chiSup_pos) hCχ0) hCle
  refine ⟨C, hC0, ?_⟩
  intro g R ℓ hR hℓ hRℓ hge hgsupp hgI
  -- ## basic facts about `g` and `W := wScaled ℓ g`
  have hgsupp0 : ∀ z : E3, R ≤ ‖z‖ → g z = 0 := by
    intro z hz
    refine image_eq_zero_of_notMem_tsupport (fun hmem => ?_)
    have h := hgsupp hmem
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h
    linarith
  set W : E3 → ℝ := Submission.BoseGases.wScaled ℓ g with hWdef
  have hWint : MeasureTheory.Integrable W := by
    rw [hWdef]
    exact Submission.BoseGases.wScaled_integrable_ae hℓ hR.le hRℓ hgI hgsupp0
  have hWeven : ∀ z : E3, W (-z) = W z := by
    intro z
    rw [hWdef]
    exact wLocKC_wScaled_even hge ℓ z
  have hWsupp : ∀ z : E3, R ≤ ‖z‖ → W z = 0 := by
    intro z hz
    rw [hWdef]
    simp [Submission.BoseGases.wScaled, hgsupp0 z hz]
  have hWabs_nonneg : 0 ≤ ∫ z : E3, |W z| := integral_nonneg (fun z => abs_nonneg (W z))
  have hG : (∫ z : E3, |W z|) = ∫ z : E3, |Submission.BoseGases.wScaled ℓ g z| := by
    rw [hWdef]
  have hchat : Work.BoseFixR.chat (Submission.BoseGases.wScaled ℓ g) 0 = ∫ z : E3, W z := by
    rw [hWdef]
    exact wLocKC_chat_zero_eq_integral _
  -- ## Part 1: the pointwise comparison
  have hpart1 : ∀ x : E3,
      |Work.BoseFixR.chat (Submission.BoseGases.wScaled ℓ g) 0 *
          Submission.BoseGases.chiScale ℓ x ^ 2
        - Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wLoc ℓ g 0) x|
        ≤ C * (R / ℓ) ^ 2 *
            ∫ z : E3, |Submission.BoseGases.wScaled ℓ g z| := by
    intro x
    -- integrability of the two pieces of the linear split
    have hAint : MeasureTheory.Integrable
        (fun y : E3 => W y * Submission.BoseGases.chiScale ℓ x) :=
      hWint.mul_const _
    have hBint : MeasureTheory.Integrable
        (fun y : E3 => W y * Submission.BoseGases.chiScale ℓ (x - y)) := by
      refine Integrable.mono' (hWint.abs.const_mul Submission.BoseGases.chiSup) ?_ ?_
      · exact hWint.aestronglyMeasurable.mul
          (((Submission.BoseGases.chiScale_continuous ℓ).comp
            (continuous_const.sub continuous_id)).aestronglyMeasurable)
      · refine ae_of_all _ (fun y => ?_)
        calc ‖W y * Submission.BoseGases.chiScale ℓ (x - y)‖
            = |W y| * |Submission.BoseGases.chiScale ℓ (x - y)| := by
              rw [Real.norm_eq_abs, abs_mul]
          _ ≤ |W y| * Submission.BoseGases.chiSup :=
              mul_le_mul_of_nonneg_left (Submission.BoseGases.abs_chiScale_le_chiSup ℓ (x - y))
                (abs_nonneg _)
          _ = Submission.BoseGases.chiSup * |W y| := by ring
    -- `chat 0 · χ_ℓ(x) = ∫_y W(y) χ_ℓ(x)`
    have hconst : Work.BoseFixR.chat (Submission.BoseGases.wScaled ℓ g) 0 *
        Submission.BoseGases.chiScale ℓ x
        = ∫ y : E3, W y * Submission.BoseGases.chiScale ℓ x := by
      rw [hchat, MeasureTheory.integral_mul_const]
    -- the bracket is (minus) the Taylor remainder of `lem:Convolution`
    have hbracket : Work.BoseFixR.chat (Submission.BoseGases.wScaled ℓ g) 0 *
          Submission.BoseGases.chiScale ℓ x
        - (∫ y : E3, W y * Submission.BoseGases.chiScale ℓ (x - y))
        = -(∫ y : E3, W y * (Submission.BoseGases.chiScale ℓ (x - y)
            - Submission.BoseGases.chiScale ℓ x)) := by
      have h2 : (∫ y : E3, (W y * Submission.BoseGases.chiScale ℓ x
            - W y * Submission.BoseGases.chiScale ℓ (x - y)))
          = -∫ y : E3, W y * (Submission.BoseGases.chiScale ℓ (x - y)
              - Submission.BoseGases.chiScale ℓ x) := by
        rw [show (fun y : E3 => W y * Submission.BoseGases.chiScale ℓ x
              - W y * Submission.BoseGases.chiScale ℓ (x - y))
            = (fun y : E3 => -(W y * (Submission.BoseGases.chiScale ℓ (x - y)
                - Submission.BoseGases.chiScale ℓ x))) from
          funext (fun y => by ring)]
        rw [MeasureTheory.integral_neg]
      rw [hconst, ← MeasureTheory.integral_sub hAint hBint, h2]
    have hq := Submission.BoseGases.convolution_approx (f := W) hℓ hχT hWint hWeven hWsupp
      hR.le x
    have hfac : Work.BoseFixR.chat (Submission.BoseGases.wScaled ℓ g) 0 *
          Submission.BoseGases.chiScale ℓ x ^ 2
        - Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wLoc ℓ g 0) x
        = Submission.BoseGases.chiScale ℓ x *
          (Work.BoseFixR.chat (Submission.BoseGases.wScaled ℓ g) 0 *
              Submission.BoseGases.chiScale ℓ x
            - (∫ y : E3, W y * Submission.BoseGases.chiScale ℓ (x - y))) := by
      have hfib : Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wLoc ℓ g 0) x
          = Submission.BoseGases.chiScale ℓ x *
              (∫ y : E3, W y * Submission.BoseGases.chiScale ℓ (x - y)) := by
        rw [hWdef]
        exact wLocKC_fibre_eq hℓ g x
      rw [hfib]
      ring
    rw [hfac, abs_mul]
    calc |Submission.BoseGases.chiScale ℓ x| *
          |Work.BoseFixR.chat (Submission.BoseGases.wScaled ℓ g) 0 *
              Submission.BoseGases.chiScale ℓ x
            - (∫ y : E3, W y * Submission.BoseGases.chiScale ℓ (x - y))|
        = |Submission.BoseGases.chiScale ℓ x| *
          |∫ y : E3, W y * (Submission.BoseGases.chiScale ℓ (x - y)
            - Submission.BoseGases.chiScale ℓ x)| := by
          rw [hbracket, abs_neg]
      _ ≤ Submission.BoseGases.chiSup * (Cχ * (R / ℓ) ^ 2 * ∫ y : E3, |W y|) :=
          mul_le_mul (Submission.BoseGases.abs_chiScale_le_chiSup ℓ x) hq (abs_nonneg _)
            (le_of_lt Submission.BoseGases.chiSup_pos)
      _ = Submission.BoseGases.chiSup * Cχ * (R / ℓ) ^ 2 * ∫ y : E3, |W y| := by ring
      _ ≤ C * (R / ℓ) ^ 2 * ∫ y : E3, |W y| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCle (sq_nonneg _))
            hWabs_nonneg
      _ = C * (R / ℓ) ^ 2 * ∫ z : E3, |Submission.BoseGases.wScaled ℓ g z| := by
          rw [hG]
  -- ## Part 2: the average over the cube
  have hpart2 : |(ℓ ^ 3)⁻¹ * (∫ x in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wLoc ℓ g 0) x)
        - Work.BoseFixR.chat (Submission.BoseGases.wScaled ℓ g) 0|
        ≤ C * (R / ℓ) ^ 2 *
            ∫ z : E3, |Submission.BoseGases.wScaled ℓ g z| := by
    -- the double integral of the localised kernel is `ℓ³∫g`
    have hA : (∫ x in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wLoc ℓ g 0) x)
        = ℓ ^ 3 * ∫ z : E3, g z := by
      have hwUpair : (fun p : E3 × E3 => Submission.BoseGases.wLoc ℓ g 0 p.1 p.2)
          = Submission.BoseGases.wPairU ℓ g := by
        funext p
        rcases p with ⟨a, b⟩
        exact wLocKC_wLoc_zero_eq_wPair ℓ g a b
      have hwiPair : IntegrableOn (Submission.BoseGases.wPairU ℓ g)
          (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) :=
        Submission.BoseGases.integrableOn_wPairU_of hℓ hgI hgsupp0 hR.le hRℓ
      have hwiU : IntegrableOn (fun p : E3 × E3 => Submission.BoseGases.wLoc ℓ g 0 p.1 p.2)
          (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) := by
        rw [hwUpair]
        exact hwiPair
      calc (∫ x in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wLoc ℓ g 0) x)
          = ∫ x in Submission.BoseGases.acube ℓ, ∫ y in Submission.BoseGases.acube ℓ,
              Submission.BoseGases.wLoc ℓ g 0 x y := rfl
        _ = ∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
              Submission.BoseGases.wLoc ℓ g 0 p.1 p.2 :=
              Submission.BoseGases.prod_setIntegral_eq_iter_outer hwiU
        _ = ∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
              Submission.BoseGases.wPairU ℓ g p := by rw [hwUpair]
        _ = ∫ x : E3, ∫ y : E3, Submission.BoseGases.wPair ℓ g x y :=
              Submission.BoseGases.wPairU_cube_integral_eq_full hℓ hwiPair
        _ = ℓ ^ 3 * ∫ z : E3, g z :=
              Submission.BoseGases.wPair_double_full_integral hℓ hgI hgsupp0 hRℓ
    have hT : (ℓ ^ 3)⁻¹ * (∫ x in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wLoc ℓ g 0) x)
        = ∫ z : E3, g z := by
      rw [hA, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ)), one_mul]
    -- `∫g − ∫W = ∫ W (convScale − 1)`
    have hΔ : (∫ z : E3, g z) - (∫ z : E3, W z)
        = ∫ z : E3, W z * (Submission.BoseGases.convScale ℓ z - 1) := by
      rw [← MeasureTheory.integral_sub hgI hWint]
      apply MeasureTheory.integral_congr_ae
      refine ae_of_all _ (fun z => ?_)
      change g z - W z = W z * (Submission.BoseGases.convScale ℓ z - 1)
      by_cases hc : Submission.BoseGases.convScale ℓ z = 0
      · have hWz : W z = 0 := by
          rw [hWdef]
          simp [Submission.BoseGases.wScaled, hc]
        have hgz : g z = 0 := by
          by_contra hgz
          have hzR : ‖z‖ ≤ R := le_of_lt (lt_of_not_ge (fun h => hgz (hgsupp0 z h)))
          have hhalf := Submission.BoseGases.convScale_ge_half_ball hℓ hR.le hRℓ hzR
          rw [hc] at hhalf
          linarith
        rw [hWz, hgz]
        ring
      · have hWz : W z = g z / Submission.BoseGases.convScale ℓ z := by
          rw [hWdef]
          rfl
        rw [hWz]
        field_simp
    have hΔbound : |∫ z : E3, W z * (Submission.BoseGases.convScale ℓ z - 1)|
        ≤ C₁ * (R / ℓ) ^ 2 * ∫ z : E3, |W z| := by
      have hpt : ∀ z : E3, |W z * (Submission.BoseGases.convScale ℓ z - 1)|
          ≤ C₁ * (R / ℓ) ^ 2 * |W z| := by
        intro z
        by_cases hWz : W z = 0
        · simp [hWz]
        · have hzR : ‖z‖ ≤ R := le_of_lt (lt_of_not_ge (fun h => hWz (hWsupp z h)))
          have hdevz := wLocKC_convScale_dev_le hℓ hC₁0 hdev z
          have hle : ‖z‖ / ℓ ≤ R / ℓ := div_le_div_of_nonneg_right hzR hℓ.le
          have hsq : (‖z‖ / ℓ) ^ 2 ≤ (R / ℓ) ^ 2 :=
            pow_le_pow_left₀ (div_nonneg (norm_nonneg _) hℓ.le) hle 2
          calc |W z * (Submission.BoseGases.convScale ℓ z - 1)|
              = |W z| * |Submission.BoseGases.convScale ℓ z - 1| := abs_mul _ _
            _ ≤ |W z| * (C₁ * (‖z‖ / ℓ) ^ 2) :=
                mul_le_mul_of_nonneg_left hdevz (abs_nonneg _)
            _ ≤ |W z| * (C₁ * (R / ℓ) ^ 2) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hC₁0) (abs_nonneg _)
            _ = C₁ * (R / ℓ) ^ 2 * |W z| := by ring
      have hint : MeasureTheory.Integrable
          (fun z : E3 => W z * (Submission.BoseGases.convScale ℓ z - 1)) := by
        refine Integrable.mono' (hWint.abs.const_mul (C₁ * (R / ℓ) ^ 2)) ?_ ?_
        · exact hWint.aestronglyMeasurable.mul
            (((Submission.BoseGases.convScale_continuous ℓ).sub continuous_const).aestronglyMeasurable)
        · refine ae_of_all _ (fun z => ?_)
          simpa [Real.norm_eq_abs] using hpt z
      calc |∫ z : E3, W z * (Submission.BoseGases.convScale ℓ z - 1)|
          ≤ ∫ z : E3, |W z * (Submission.BoseGases.convScale ℓ z - 1)| :=
            MeasureTheory.abs_integral_le_integral_abs
        _ ≤ ∫ z : E3, C₁ * (R / ℓ) ^ 2 * |W z| :=
            MeasureTheory.integral_mono_ae hint.abs (hWint.abs.const_mul _)
              (ae_of_all _ hpt)
        _ = C₁ * (R / ℓ) ^ 2 * ∫ z : E3, |W z| := by
            rw [MeasureTheory.integral_const_mul]
    calc |(ℓ ^ 3)⁻¹ * (∫ x in Submission.BoseGases.acube ℓ,
              Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wLoc ℓ g 0) x)
            - Work.BoseFixR.chat (Submission.BoseGases.wScaled ℓ g) 0|
        = |(∫ z : E3, g z) - (∫ z : E3, W z)| := by rw [hT, hchat]
      _ = |∫ z : E3, W z * (Submission.BoseGases.convScale ℓ z - 1)| := by rw [hΔ]
      _ ≤ C₁ * (R / ℓ) ^ 2 * ∫ z : E3, |W z| := hΔbound
      _ ≤ C * (R / ℓ) ^ 2 * ∫ z : E3, |W z| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1le (sq_nonneg _))
            hWabs_nonneg
      _ = C * (R / ℓ) ^ 2 * ∫ z : E3, |Submission.BoseGases.wScaled ℓ g z| := by
          rw [hG]
  exact ⟨hpart1, hpart2⟩

end Work.BoseBoxFock
