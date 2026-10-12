import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1B.pairRung.nuPairWNuBounds
import Submission.Work.BoseFixB1S.integrable_wSmallScaled_div_convScale
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.nuPairWNuIntegrable`

The `q`-side kernel data of the `dℓ`-localised two-factor kernel

    𝒲 = wSmallScaled M (ℓ·d) (g₀) / convScale ℓ
      = g₀ / ( (χ_M⋆χ_M)(·/(ℓd)) · (χ⋆χ)(·/ℓ) ),

uniformly over the sliding parameters `ℓ, d` in the *coarse* dilute regime
`16R ≤ ℓ`, `16R ≤ ℓd`, consist of three rows:

* the sup bound `|𝓕𝒲| ≤ K·a v` (FS `eq:WSestimate`),
* the **integrability** of `q ↦ (pairW 𝒲 q)²/‖q‖²`,
* the Newtonian mass bound `(2π)⁻³∫(pairW 𝒲 q)²/‖q‖² ≤ K·ĝω(0)` (FS `eq:I2-integral`).

The first and third rows are exactly the conclusion of
`Work.BoseFixB1B.pairRung.nuPairWNuBounds` (proved), whose mass constant there is
`Work.BoseFixB1B.PairMass h` — definitionally `Submission.BoseGases.g0w0Mass h`.  This module
supplies the missing middle row and assembles the three.

The integrability route is the Coulomb one, exactly as in `Work.MGroupInput.newtonianSharp`:

* `Work.BoseFixB1S.wLocScaled_abs_le_16R` below dominates the kernel pointwise by
  `c·|g₀|` with `c = 1/(smallConvLower M · c₀)`, where `c₀ > 0` is a lower bound for `χ⋆χ`
  on the ball of radius `1/16` (`exists_conv3_chi_lower`) and `smallConvLower M` is the
  corpus's lower bound for `χ_M⋆χ_M` on the polydisc of radius `1/16`
  (`Work.SmallBoxSliding.conv3Small_coord_lower`).  The two regime hypotheses
  `16R ≤ ℓ`, `16R ≤ ℓd` give exactly the two normalisations `‖z/ℓ‖ ≤ 1/16`,
  `‖z/(ℓd)‖ ≤ 1/16` on `ball 0 R`, where `g₀` is supported;
* hence `𝒲 ∈ L¹` (`Work.BoseFixB1S.integrable_wSmallScaled_div_convScale`), `𝒲 ≥ 0` a.e. and
  `𝒲 ≤ (1+c)·g₀` a.e.;
* the `g₀`-Coulomb double integral is finite
  (`Work.MGroupInput.newtonianSharp_g0_coulPot_integrable` +
  `Work.MGroupInput.newtonianSharp_integrable_double_coulPot`), and passes to `𝒲` by the sharp
  comparison (`Work.MGroupInput.newtonianSharp_integrable_double_of_sharp`);
* the Coulomb inequality in lintegral form (`Submission.BoseGases.integrable_pairW_sq_div`)
  then converts the position-space finiteness into the momentum-side integrability.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-- **Strict positivity of the cubic self-convolution on the ball of radius `1/16`.**

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

/-- **A positive lower bound for the cubic self-convolution on the ball of radius `1/16`.**

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

/-- **The `dℓ`-localised kernel is dominated by a multiple of `|g₀|` in the coarse regime.**

For `16R ≤ ℓ` and `16R ≤ ℓd` the two arguments `z/ℓ` and `z/(ℓd)` land in the polydisc of
radius `1/16` whenever `‖z‖ ≤ R` (the support of `g₀`), so both renormalisation denominators
are bounded below by the positive constants `c₀` (`χ⋆χ`, `exists_conv3_chi_lower`) and
`smallConvLower M` (`χ_M⋆χ_M`, `Work.SmallBoxSliding.conv3Small_coord_lower`).  Hence

    |𝒲(z)| ≤ 1/(smallConvLower M · c₀) · |g₀(z)|

everywhere (outside `ball 0 R` both sides vanish, `g₀` being supported there). -/
private lemma wLocScaled_abs_le_16R {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    {M : ℕ} (hM : 1 ≤ M) :
    ∃ c : ℝ, 0 < c ∧ ∀ {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
      (hRℓ : 16 * R ≤ ℓ) (hRd : 16 * R ≤ ℓ * d) (z : E3),
      |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z
          / Submission.BoseGases.convScale ℓ z|
        ≤ c * |Submission.BoseGases.g0 v h z| := by
  classical
  obtain ⟨cbig, hcbig_pos, hcbig⟩ := exists_conv3_chi_lower
  set s : ℝ := Work.SmallBoxSliding.smallConvLower M with hsdef
  have hs_pos : 0 < s := by
    rw [hsdef]; exact Work.SmallBoxSliding.smallConvLower_pos M
  refine ⟨1 / (s * cbig), by positivity, ?_⟩
  intro ℓ d hℓ hd hRℓ hRd z
  have hR16 : R ≤ ℓ * d / 16 := by linarith
  have hR16ℓ : R ≤ ℓ / 16 := by linarith
  have hg0supp : ∀ z : E3, R ≤ ‖z‖ → Submission.BoseGases.g0 v h z = 0 :=
    fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
  by_cases hnorm : ‖z‖ ≤ R
  · have hcc : cbig ≤ Submission.BoseGases.convScale ℓ z := by
      have hnorm' : ‖(ℓ)⁻¹ • z‖ ≤ 1 / 16 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ)]
        calc ℓ⁻¹ * ‖z‖ ≤ ℓ⁻¹ * R := mul_le_mul_of_nonneg_left hnorm (inv_pos.mpr hℓ).le
          _ ≤ ℓ⁻¹ * (ℓ / 16) := mul_le_mul_of_nonneg_left hR16ℓ (inv_pos.mpr hℓ).le
          _ = 1 / 16 := by field_simp
      have hthis := hcbig ((ℓ)⁻¹ • z) hnorm'
      simpa only [Submission.BoseGases.convScale] using hthis
    have hccpos : 0 < Submission.BoseGases.convScale ℓ z := lt_of_lt_of_le hcbig_pos hcc
    have h1 : |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z|
        ≤ |Submission.BoseGases.g0 v h z| / s := by
      rw [hsdef]
      exact Work.SmallBoxSliding.abs_wSmallScaled_le (M := M) hM (mul_pos hℓ hd) hg0supp hR16 z
    rw [div_eq_mul_inv, abs_mul, abs_of_pos (inv_pos.mpr hccpos)]
    calc |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z|
          * (Submission.BoseGases.convScale ℓ z)⁻¹
        ≤ (|Submission.BoseGases.g0 v h z| / s) * (Submission.BoseGases.convScale ℓ z)⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hccpos.le)
      _ ≤ (|Submission.BoseGases.g0 v h z| / s) * cbig⁻¹ :=
          mul_le_mul_of_nonneg_left
            ((inv_le_inv₀ hccpos hcbig_pos).mpr hcc)
            (div_nonneg (abs_nonneg _) hs_pos.le)
      _ = (1 / (s * cbig)) * |Submission.BoseGases.g0 v h z| := by field_simp
  · have hzR : R ≤ ‖z‖ := le_of_lt (lt_of_not_ge hnorm)
    have hz0 : Submission.BoseGases.g0 v h z = 0 := hg0supp z hzR
    have hw0 : Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z
        = 0 := by
      rw [Submission.BoseGases.wSmallScaled, hz0, zero_div]
    rw [hw0, zero_div, abs_zero, hz0, abs_zero, mul_zero]

/-- **Momentum-side integrability of the `dℓ`-localised pairing weight.**

From the pointwise domination `|𝒲| ≤ c|g₀|` (`wLocScaled_abs_le_16R`) one gets `𝒲 ∈ L¹`,
`0 ≤ᵐ 𝒲` and `𝒲 ≤ᵐ (1+c)·g₀`; the `g₀`-Coulomb double integral is finite by the corpus's
scattering-solution facts, and the sharp comparison transfers its finiteness to `𝒲`.  The
Coulomb inequality `Submission.BoseGases.integrable_pairW_sq_div` then gives the integrability
of `q ↦ (pairW 𝒲 q)²/‖q‖²`. -/
private theorem integrable_pairW_sq_div_wLocScaled {v : E3 → ℝ} {R : ℝ} (hR : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M) {ℓ d c : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (hc : 0 ≤ c)
    (hdle : ∀ z : E3,
      |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z
          / Submission.BoseGases.convScale ℓ z|
        ≤ c * |Submission.BoseGases.g0 v h z|) :
    MeasureTheory.Integrable (fun q : E3 =>
      (Submission.BoseGases.pairW (fun z => Submission.BoseGases.wSmallScaled M (ℓ * d)
        (Submission.BoseGases.g0 v h) z / Submission.BoseGases.convScale ℓ z) q) ^ 2
        / ‖q‖ ^ 2) := by
  have hg0int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  have hWint : MeasureTheory.Integrable (fun z : E3 =>
      Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z
        / Submission.BoseGases.convScale ℓ z) :=
    integrable_wSmallScaled_div_convScale (R := R) (M := M) (c := c) hM hℓ hd h hg0int hdle hc
  have hg0nn : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure E3),
      0 ≤ Submission.BoseGases.g0 v h z :=
    Submission.BoseGases.g0_nonneg_ae hR hv hvrad hv_supp h
  have hW0 : 0 ≤ᵐ[MeasureTheory.volume] (fun z : E3 =>
      Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z
        / Submission.BoseGases.convScale ℓ z) := by
    filter_upwards [hg0nn] with z hz
    show 0 ≤ (Submission.BoseGases.g0 v h z
      / Submission.BoseGases.convScaleSmall M (ℓ * d) z)
      / Submission.BoseGases.convScale ℓ z
    exact div_nonneg (div_nonneg hz (Work.SmallBoxSliding.convScaleSmall_nonneg M (ℓ * d) z))
      (Submission.BoseGases.convScale_nonneg ℓ z)
  have hWle : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure E3),
      (fun z : E3 => Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z
        / Submission.BoseGases.convScale ℓ z) x ≤ (1 + c) * Submission.BoseGases.g0 v h x := by
    filter_upwards [hg0nn] with z hz
    show Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z
        / Submission.BoseGases.convScale ℓ z ≤ (1 + c) * Submission.BoseGases.g0 v h z
    have h1 := hdle z
    rw [abs_of_nonneg hz] at h1
    have h2 : c * Submission.BoseGases.g0 v h z
        ≤ (1 + c) * Submission.BoseGases.g0 v h z := by
      have h3 : c ≤ 1 + c := by linarith
      exact mul_le_mul_of_nonneg_right h3 hz
    linarith [le_abs_self (Submission.BoseGases.wSmallScaled M (ℓ * d)
      (Submission.BoseGases.g0 v h) z / Submission.BoseGases.convScale ℓ z), h1, h2]
  have hGsupp : ∀ x : E3, R ≤ ‖x‖ → Submission.BoseGases.g0 v h x = 0 :=
    fun x hx => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hx h
  have hVgInt := Work.MGroupInput.newtonianSharp_g0_coulPot_integrable (v := v) (R := R)
    hR hv hvrad hv_supp h
  have hGjoint := Work.MGroupInput.newtonianSharp_integrable_double_coulPot (R := R)
    hR hg0int hg0nn hGsupp hVgInt
  have hWjoint := Work.MGroupInput.newtonianSharp_integrable_double_of_sharp (δ := c)
    hc hWint hW0 hWle hGjoint
  exact Submission.BoseGases.integrable_pairW_sq_div hWint hW0 hWjoint

theorem nuPairWNuIntegrable {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {M : ℕ} (hM : 1 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hRℓ : 16 * R ≤ ℓ) (hRd : 16 * R ≤ ℓ * d),
        (∀ q : EuclideanSpace ℝ (Fin 3),
            |Submission.BoseGases.pairW (fun z => Submission.BoseGases.wSmallScaled M (ℓ * d)
                (Submission.BoseGases.g0 v h) z / Submission.BoseGases.convScale ℓ z) q|
              ≤ K * (_root_.BoseGases.a v))
          ∧ MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) =>
              (Submission.BoseGases.pairW (fun z => Submission.BoseGases.wSmallScaled M (ℓ * d)
                (Submission.BoseGases.g0 v h) z / Submission.BoseGases.convScale ℓ z) q) ^ 2
                / ‖q‖ ^ 2)
          ∧ ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3),
              (Submission.BoseGases.pairW (fun z => Submission.BoseGases.wSmallScaled M (ℓ * d)
                (Submission.BoseGases.g0 v h) z / Submission.BoseGases.convScale ℓ z) q) ^ 2
                / ‖q‖ ^ 2
            ≤ K * Submission.BoseGases.g0w0Mass (v := v) h := by
  obtain ⟨K, hK0, hK⟩ :=
    Work.BoseFixB1B.pairRung.nuPairWNuBounds h hv hv1 hvrad hR hv_supp hav hM
  obtain ⟨c, hc_pos, hc⟩ := wLocScaled_abs_le_16R (v := v) h hv hvrad hR hv_supp hM
  refine ⟨K, hK0, ?_⟩
  intro ℓ d hℓ hd hRℓ hRd
  obtain ⟨h1, h3⟩ := hK hℓ hd hRℓ hRd
  refine ⟨h1, ?_, ?_⟩
  · exact integrable_pairW_sq_div_wLocScaled (v := v) (R := R) hR hv hvrad hv_supp h hM hℓ hd
      hc_pos.le (fun z => hc (ℓ := ℓ) (d := d) hℓ hd hRℓ hRd z)
  · rw [← Work.BoseFixB1B.PairMass_eq_g0w0Mass h]
    exact h3

end Work.BoseFixB1S
