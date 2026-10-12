import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1.BoxFrameAux
import Submission.Work.BoseFixB1.boxTauGen_mode_bound_meas
import Submission.Work.BoseFixB1B.pairMass_pos
import Submission.Work.BoseFixB1S.D1InputsB1
import Submission.Work.BoseFixB1S.boxPairIdSlidingB1
import Submission.Work.BoseFixB1S.chainIntegralQdep
import Submission.Work.BoseFixB1S.pairW_newtonian_sharp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.pairRung.nuPairWNuBounds`

The two uniform kernel bounds for the `dℓ`-localised two-factor kernel of FS's D1 chapter,

    𝒲 = wSmallScaled M (ℓ·d) (g₀) / convScale ℓ
      = g₀ / ( (χ_M⋆χ_M)(·/(ℓd)) · (χ⋆χ)(·/ℓ) )       (ℓ ≥ 16R, ℓd ≥ 16R),

namely FS `eq:WSestimate` (`|𝓕𝒲| ≤ K·a v`) and `eq:I2-integral` / `eq:appw1sliding`
(`(2π)^{-3}∫(pairW 𝒲)²/‖q‖² ≤ K·ĝω(0)`), at the *coarse* dilute regime `16R ≤ ℓ`, `16R ≤ ℓd`.

The corpus's versions of these two bounds (`Work.BoseFixB1S.pairW_wSmallScaled_sup_leB1`,
`Work.BoseFixB1S.slidingNewtonMassSharpB1`) are stated in the finer regime `R ≤ ℓ·chiR0`, in
which both renormalisation denominators are `≥ 1/2` by construction of the radius `chiR0`.  Here
`chiR0` is not available (it is an opaque `Classical.choose`), so the two denominator lower bounds
are produced by hand on the polydisc of radius `1/16` — exactly the regime `16R ≤ ℓ`, `16R ≤ ℓd`:

* `(χ_M⋆χ_M)(t) ≥ smallConvLower M > 0` for `‖t‖ ≤ 1/16` — the corpus's
  `Work.SmallBoxSliding.conv3Small_coord_lower`;
* `(χ⋆χ)(t) ≥ c₀ > 0` for `‖t‖ ≤ 1/16` — `exists_conv3_chi_lower` below, from strict
  positivity of `χ⋆χ` on that compact ball and the extreme value theorem.

With those, `|𝒲| ≤ (1/(c₀·smallConvLower M))·|g₀|` everywhere, which gives

* the `L¹` bound `∫|𝒲| ≤ 8π·a v/(c₀·smallConvLower M)`, hence FS `eq:WSestimate` via
  `|𝓕𝒲| ≤ ‖𝒲‖₁` (`abs_pairW_le_integral_abs`);
* the pointwise comparison `0 ≤ᵐ 𝒲 ≤ (1 + δ)·g₀` with `δ = 1/(c₀·smallConvLower M)`, hence the
  sharp Newtonian mass via `Work.BoseFixB1S.pairW_newtonian_sharp`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B.pairRung

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Strict positivity of the cubic self-convolution on the polydisc of radius `1/16`.**

Both factors of the integrand of `(χ⋆χ)(t) = ∫ y, χ y · χ (t − y)` are strictly positive at
`y = t/2` (there `‖t/2‖ ≤ 1/32 ≤ 1/4`, where the underlying bump `chiBase` equals `1`), so
`Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero` applies. -/
private lemma conv3_chi_pos_of_norm_le (t : E3) (ht : ‖t‖ ≤ 1 / 16) :
    0 < Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi t := by
  have hhalf : ‖(2 : ℝ)⁻¹ • t‖ ≤ 1 / 4 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)]
    calc (2 : ℝ)⁻¹ * ‖t‖ ≤ (2 : ℝ)⁻¹ * (1 / 16) :=
          mul_le_mul_of_nonneg_left ht (by norm_num)
      _ ≤ 1 / 4 := by norm_num
  have hchi0 : 0 < Submission.BoseGases.chi ((2 : ℝ)⁻¹ • t) := by
    have hbase : Submission.BoseGases.chiBase ((2 : ℝ)⁻¹ • t) = 1 :=
      Submission.BoseGases.chiBase_eq_one_of_norm_le hhalf
    have hs : 0 < Real.sqrt Submission.BoseGases.chiNormSq :=
      Real.sqrt_pos.mpr Submission.BoseGases.chiNormSq_pos
    rw [Submission.BoseGases.chi, hbase]
    exact div_pos one_pos hs
  have hmid : t - (2 : ℝ)⁻¹ • t = (2 : ℝ)⁻¹ • t := by
    have hs := sub_smul (1 : ℝ) ((2 : ℝ)⁻¹) t
    rw [one_smul] at hs
    rw [show (1 : ℝ) - (2 : ℝ)⁻¹ = (2 : ℝ)⁻¹ by norm_num] at hs
    exact hs.symm
  have hcont : Continuous
      (fun y : E3 => Submission.BoseGases.chi y * Submission.BoseGases.chi (t - y)) :=
    Submission.BoseGases.chi_continuous.mul
      (Submission.BoseGases.chi_continuous.comp (continuous_const.sub continuous_id))
  have hcs : HasCompactSupport
      (fun y : E3 => Submission.BoseGases.chi y * Submission.BoseGases.chi (t - y)) := by
    refine HasCompactSupport.mono Submission.BoseGases.chi_hasCompactSupport ?_
    intro y hy
    rw [Function.mem_support] at hy ⊢
    intro hc
    exact hy (by rw [hc, zero_mul])
  have hnn : 0 ≤ (fun y : E3 => Submission.BoseGases.chi y *
      Submission.BoseGases.chi (t - y)) :=
    fun y => mul_nonneg (Submission.BoseGases.chi_nonneg y) (Submission.BoseGases.chi_nonneg _)
  have hne : (fun y : E3 => Submission.BoseGases.chi y *
      Submission.BoseGases.chi (t - y)) ((2 : ℝ)⁻¹ • t) ≠ 0 := by
    show Submission.BoseGases.chi ((2 : ℝ)⁻¹ • t)
      * Submission.BoseGases.chi (t - (2 : ℝ)⁻¹ • t) ≠ 0
    rw [hmid]
    exact mul_ne_zero (ne_of_gt hchi0) (ne_of_gt hchi0)
  have hpos := Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (f := fun y : E3 => Submission.BoseGases.chi y * Submission.BoseGases.chi (t - y))
    (x := (2 : ℝ)⁻¹ • t) (μ := MeasureTheory.volume) hcont hcs hnn hne
  show 0 < ∫ y : E3, Submission.BoseGases.chi y * Submission.BoseGases.chi (t - y)
  exact hpos

/-- **A positive lower bound for the cubic self-convolution on the polydisc of radius `1/16`.**

Immediate from `conv3_chi_pos_of_norm_le` and the extreme value theorem applied to the
continuous `χ⋆χ` on the compact `closedBall 0 (1/16)`. -/
private lemma exists_conv3_chi_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ t : E3, ‖t‖ ≤ 1 / 16 →
      c ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi t := by
  have hcont : Continuous
      (fun t : E3 => Submission.BoseGases.conv3 Submission.BoseGases.chi
        Submission.BoseGases.chi t) :=
    Submission.BoseGases.conv_contDiff.continuous
  obtain ⟨x, hx, hmin⟩ :=
    (isCompact_closedBall (0 : E3) (1 / 16)).exists_isMinOn ⟨0, by simp⟩ hcont.continuousOn
  have hx' : ‖x‖ ≤ 1 / 16 := by
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    exact hx
  refine ⟨_, conv3_chi_pos_of_norm_le x hx', ?_⟩
  intro t ht
  refine hmin ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  exact ht

theorem nuPairWNuBounds {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {M : ℕ} (hM : 1 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
        (hRℓ : 16 * R ≤ ℓ) (hRd : 16 * R ≤ ℓ * d),
        (∀ q : EuclideanSpace ℝ (Fin 3),
            |Submission.BoseGases.pairW (fun z => Submission.BoseGases.wSmallScaled M (ℓ * d)
                (Submission.BoseGases.g0 v h) z / Submission.BoseGases.convScale ℓ z) q|
              ≤ K * (_root_.BoseGases.a v))
          ∧ ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3),
              (Submission.BoseGases.pairW (fun z => Submission.BoseGases.wSmallScaled M (ℓ * d)
                  (Submission.BoseGases.g0 v h) z / Submission.BoseGases.convScale ℓ z) q) ^ 2 / ‖q‖ ^ 2
            ≤ K * Work.BoseFixB1B.PairMass h := by
  classical
  obtain ⟨cbig, hcbig_pos, hcbig⟩ := exists_conv3_chi_lower
  set s : ℝ := Work.SmallBoxSliding.smallConvLower M with hsdef
  have hs_pos : 0 < s := by
    rw [hsdef]; exact Work.SmallBoxSliding.smallConvLower_pos M
  have hsc_pos : 0 < s * cbig := mul_pos hs_pos hcbig_pos
  refine ⟨max (8 * Real.pi / (s * cbig)) (2 * (1 + 1 / (s * cbig)) ^ 2), ?_, ?_⟩
  · exact le_max_of_le_left (div_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hsc_pos.le)
  intro ℓ d hℓ hd hRℓ hRd
  have hR16 : R ≤ ℓ * d / 16 := by linarith
  have hR16ℓ : R ≤ ℓ / 16 := by linarith
  -- the kernel
  set W : E3 → ℝ := fun z =>
    Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z
      / Submission.BoseGases.convScale ℓ z with hWdef
  have hWval : ∀ z : E3, W z
      = Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z
        / Submission.BoseGases.convScale ℓ z := fun z => rfl
  -- the `g₀` facts
  have hg0supp : ∀ z : E3, R ≤ ‖z‖ → Submission.BoseGases.g0 v h z = 0 :=
    fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
  have hg0int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  have hg0nn : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure E3),
      0 ≤ Submission.BoseGases.g0 v h z :=
    Submission.BoseGases.g0_nonneg_ae hR hv hvrad hv_supp h
  -- the two denominator lower bounds on `ball 0 R`
  have hconv : ∀ z : E3, ‖z‖ ≤ R → cbig ≤ Submission.BoseGases.convScale ℓ z := by
    intro z hz
    have hnorm : ‖(ℓ)⁻¹ • z‖ ≤ 1 / 16 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ)]
      calc ℓ⁻¹ * ‖z‖ ≤ ℓ⁻¹ * R := mul_le_mul_of_nonneg_left hz (inv_pos.mpr hℓ).le
        _ ≤ ℓ⁻¹ * (ℓ / 16) := mul_le_mul_of_nonneg_left hR16ℓ (inv_pos.mpr hℓ).le
        _ = 1 / 16 := by field_simp
    exact hcbig _ hnorm
  have hconvS : ∀ z : E3, ‖z‖ ≤ R → s ≤ Submission.BoseGases.convScaleSmall M (ℓ * d) z := by
    intro z hz
    have hnorm : ‖(ℓ * d)⁻¹ • z‖ ≤ 1 / 16 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (mul_pos hℓ hd))]
      calc (ℓ * d)⁻¹ * ‖z‖ ≤ (ℓ * d)⁻¹ * R :=
            mul_le_mul_of_nonneg_left hz (inv_pos.mpr (mul_pos hℓ hd)).le
        _ ≤ (ℓ * d)⁻¹ * (ℓ * d / 16) :=
            mul_le_mul_of_nonneg_left hR16 (inv_pos.mpr (mul_pos hℓ hd)).le
        _ = 1 / 16 := by field_simp
    have hcoord : ∀ j : Fin 3, |((ℓ * d)⁻¹ • z).ofLp j| ≤ 1 / 16 :=
      fun j => le_trans (Submission.BoseGases.coord_abs_le_norm _ j) hnorm
    have h := Work.SmallBoxSliding.conv3Small_coord_lower (M := M) hM ((ℓ * d)⁻¹ • z) hcoord
    rw [hsdef]
    exact h
  -- pointwise domination of the kernel by `g₀`
  have hpt : ∀ z : E3, |W z| ≤ (1 / (s * cbig)) * |Submission.BoseGases.g0 v h z| := by
    intro z
    rw [hWval z]
    by_cases hnorm : ‖z‖ ≤ R
    · have hD2 : 0 < Submission.BoseGases.convScale ℓ z := lt_of_lt_of_le hcbig_pos (hconv z hnorm)
      have h1 : |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z|
          ≤ |Submission.BoseGases.g0 v h z| / s := by
        rw [hsdef]
        exact Work.SmallBoxSliding.abs_wSmallScaled_le (M := M) hM (mul_pos hℓ hd)
          hg0supp hR16 z
      rw [div_eq_mul_inv, abs_mul, abs_of_pos (inv_pos.mpr hD2)]
      calc |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z|
            * (Submission.BoseGases.convScale ℓ z)⁻¹
          ≤ (|Submission.BoseGases.g0 v h z| / s) * (Submission.BoseGases.convScale ℓ z)⁻¹ :=
            mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hD2.le)
        _ ≤ (|Submission.BoseGases.g0 v h z| / s) * cbig⁻¹ :=
            mul_le_mul_of_nonneg_left
              ((inv_le_inv₀ hD2 hcbig_pos).mpr (hconv z hnorm))
              (div_nonneg (abs_nonneg _) hs_pos.le)
        _ = (1 / (s * cbig)) * |Submission.BoseGases.g0 v h z| := by
            field_simp
    · have hzR : R ≤ ‖z‖ := le_of_lt (lt_of_not_ge hnorm)
      have hz0 : Submission.BoseGases.g0 v h z = 0 := hg0supp z hzR
      have hw0 : Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z = 0 := by
        rw [Submission.BoseGases.wSmallScaled, hz0, zero_div]
      rw [hw0, zero_div, abs_zero, hz0, abs_zero, mul_zero]
  -- integrability of the kernel
  have hmeas : AEMeasurable W (MeasureTheory.volume : MeasureTheory.Measure E3) := by
    have hc : Continuous (fun x : E3 => (ℓ * d)⁻¹ • x) := by fun_prop
    have h1 : AEMeasurable (Submission.BoseGases.convScaleSmall M (ℓ * d))
        (MeasureTheory.volume : MeasureTheory.Measure E3) :=
      ((Submission.BoseGases.conv3Small_continuous hM).comp hc).aemeasurable
    have h2 : AEMeasurable (Submission.BoseGases.convScale ℓ)
        (MeasureTheory.volume : MeasureTheory.Measure E3) :=
      (Submission.BoseGases.convScale_continuous ℓ).aemeasurable
    have h3 : AEMeasurable (Submission.BoseGases.g0 v h)
        (MeasureTheory.volume : MeasureTheory.Measure E3) :=
      hg0int.aestronglyMeasurable.aemeasurable
    rw [hWdef]
    simp only [Submission.BoseGases.wSmallScaled]
    exact (h3.div h1).div h2
  have hcint : MeasureTheory.Integrable
      (fun z => (1 / (s * cbig)) * |Submission.BoseGases.g0 v h z|) :=
    hg0int.abs.const_mul _
  have hWint : MeasureTheory.Integrable W :=
    MeasureTheory.Integrable.mono' hcint hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hpt)
  -- the `L¹` bound
  have hint : ∫ z : E3, |W z|
      ≤ (1 / (s * cbig)) * ∫ z : E3, |Submission.BoseGases.g0 v h z| := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_mono_ae hWint.abs hcint (Filter.Eventually.of_forall hpt)
  have hg0abs : ∫ z : E3, |Submission.BoseGases.g0 v h z| = 8 * Real.pi * _root_.BoseGases.a v := by
    have hae : (fun z => |Submission.BoseGases.g0 v h z|)
        =ᵐ[MeasureTheory.volume] Submission.BoseGases.g0 v h :=
      hg0nn.mono (fun z hz => abs_of_nonneg hz)
    rw [MeasureTheory.integral_congr_ae hae, Submission.BoseGases.g0_integral hR hv_supp h]
  -- the pointwise sign/domination hypotheses for the Newtonian mass
  have hW0 : 0 ≤ᵐ[MeasureTheory.volume] W := by
    filter_upwards [hg0nn] with z hz
    by_cases hnorm : ‖z‖ ≤ R
    · have hD1 : 0 < Submission.BoseGases.convScaleSmall M (ℓ * d) z :=
        lt_of_lt_of_le hs_pos (hconvS z hnorm)
      have hD2 : 0 < Submission.BoseGases.convScale ℓ z := lt_of_lt_of_le hcbig_pos (hconv z hnorm)
      rw [hWval z]
      rw [show Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z
            = Submission.BoseGases.g0 v h z / Submission.BoseGases.convScaleSmall M (ℓ * d) z
            from rfl, div_div]
      exact div_nonneg hz (mul_nonneg hD1.le hD2.le)
    · have hzR : R ≤ ‖z‖ := le_of_lt (lt_of_not_ge hnorm)
      have hz0 : Submission.BoseGases.g0 v h z = 0 := hg0supp z hzR
      simp [hWval z, Submission.BoseGases.wSmallScaled, hz0]
  have hWsupp : ∀ x : E3, R ≤ ‖x‖ → W x = 0 := by
    intro x hx
    have hx0 : Submission.BoseGases.g0 v h x = 0 := hg0supp x hx
    simp [hWval x, Submission.BoseGases.wSmallScaled, hx0]
  have hWle : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure E3),
      W x ≤ (1 + 1 / (s * cbig)) * Submission.BoseGases.g0 v h x := by
    filter_upwards [hg0nn] with z hz
    have h1 := hpt z
    rw [abs_of_nonneg hz] at h1
    have h2 : (1 / (s * cbig)) * Submission.BoseGases.g0 v h z
        ≤ (1 + 1 / (s * cbig)) * Submission.BoseGases.g0 v h z := by
      have h3 : (1 / (s * cbig)) ≤ 1 + 1 / (s * cbig) := by linarith
      exact mul_le_mul_of_nonneg_right h3 hz
    linarith [le_abs_self (W z), h1, h2]
  -- the Newtonian mass
  have hnewt := Work.BoseFixB1S.pairW_newtonian_sharp (v := v) (R := R)
    (δ := 1 / (s * cbig)) hR (by positivity) hv hvrad hv_supp h hWint hW0 hWsupp hWle
  have hPairMass_pos : 0 < Work.BoseFixB1B.PairMass h :=
    Work.BoseFixB1B.pairMass_pos h hR hv hv1 hvrad hv_supp hav
  constructor
  · intro q
    calc |Submission.BoseGases.pairW W q| ≤ ∫ z : E3, |W z| :=
          Submission.BoseGases.abs_pairW_le_integral_abs q
      _ ≤ (1 / (s * cbig)) * (8 * Real.pi * _root_.BoseGases.a v) := by
          rw [hg0abs] at hint
          exact hint
      _ = (8 * Real.pi / (s * cbig)) * _root_.BoseGases.a v := by ring
      _ ≤ max (8 * Real.pi / (s * cbig)) (2 * (1 + 1 / (s * cbig)) ^ 2) * _root_.BoseGases.a v :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hav.le
  · calc ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3, (Submission.BoseGases.pairW W q) ^ 2 / ‖q‖ ^ 2
        ≤ 2 * (1 + 1 / (s * cbig)) ^ 2 * Submission.BoseGases.g0w0Mass h := hnewt
      _ = 2 * (1 + 1 / (s * cbig)) ^ 2 * Work.BoseFixB1B.PairMass h := by
          rw [← Work.BoseFixB1B.PairMass_eq_g0w0Mass h]
      _ ≤ max (8 * Real.pi / (s * cbig)) (2 * (1 + 1 / (s * cbig)) ^ 2) * Work.BoseFixB1B.PairMass h :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hPairMass_pos.le

end Work.BoseFixB1B.pairRung
