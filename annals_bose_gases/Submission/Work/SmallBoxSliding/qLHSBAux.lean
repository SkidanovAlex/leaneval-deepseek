import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.SmallBoxSliding.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary constants and bounds for the `u`-partition of `qLHSwordB`

Shared by the target `Work.SmallBoxSliding.qLHSwordB_integral_u` and the
lemmas proved underneath it.

The `u`-integration of the localised kernels `wSmallPair M ℓ d u h` cancels the
renormalisation denominator `(χ_M ⋆ χ_M)(·/(ℓd))` exactly
(`BoseGases.chiSmallB_w_pair_uint_cancel`), provided the numerator `h` is
supported inside `ball 0 R` with `R ≤ (ℓd)/16`.  To *dominate* the localised
kernel (so that Fubini in `u` is legitimate) one needs a positive lower bound
for the convolution on the support, i.e. on the polydisc
`{z : ∀j, |z_j| ≤ 1/16}`.  `smallConvLower M` is such a bound
(`conv3Small_coord_lower`):

  `smallConvLower M = (((√2/2)³)^M)² · (1/4)³ ≤ (χ_M ⋆ χ_M)(z)`
     for every `z` with `|z_j| ≤ 1/16`.

Everything in this file is sorry-free.
-/

noncomputable section

open MeasureTheory Metric
open scoped Real BigOperators ENNReal Topology

namespace Work.SmallBoxSliding

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-- Universal positive lower bound for the self-convolution `(χ_M ⋆ χ_M)` on
the polydisc `{|z_j| ≤ 1/16}`. -/
noncomputable def smallConvLower (M : ℕ) : ℝ :=
  (((Real.sqrt 2 / 2) ^ 3) ^ M) ^ 2 * (1 / 4) ^ 3

theorem smallConvLower_pos (M : ℕ) : 0 < smallConvLower M := by
  dsimp [smallConvLower]
  have h1 : 0 < Real.sqrt 2 / 2 := by positivity
  have h2 : 0 < ((Real.sqrt 2 / 2) ^ 3) ^ M := pow_pos (pow_pos h1 3) M
  exact mul_pos (pow_pos h2 2) (by norm_num)

theorem smallConvLower_nonneg (M : ℕ) : 0 ≤ smallConvLower M :=
  le_of_lt (smallConvLower_pos M)

/-- **Lower bound for the self-convolution on the polydisc `|z_j| ≤ 1/16`.**
Both factors of the integrand are `≥ ((√2/2)³)^M` on the subcube
`{|y_j| ≤ 1/8}` (there `|y_j| ≤ 1/4` and `|z_j − y_j| ≤ 3/16 ≤ 1/4`), whose
volume is `(1/4)³`. -/
theorem conv3Small_coord_lower {M : ℕ} (hM : 1 ≤ M) (z : ℝ³)
    (hz : ∀ j : Fin 3, |z.ofLp j| ≤ 1 / 16) :
    smallConvLower M ≤ conv3Small M z := by
  set c : ℝ := ((Real.sqrt 2 / 2) ^ 3) ^ M with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    exact pow_pos (pow_pos (by positivity) 3) M
  have hcnn : 0 ≤ c := hcpos.le
  set C : Set ℝ³ := {y : ℝ³ | ∀ j : Fin 3, |y.ofLp j| ≤ 1 / 8} with hCdef
  have hCmeas : MeasurableSet C := eucl_cube_measurable (c := (1 / 8 : ℝ))
  have hCvolE : (volume : Measure ℝ³) C = ENNReal.ofReal (1 / 64) := by
    rw [eucl_cube_volume (c := (1 / 8 : ℝ)) (by norm_num)]
    norm_num
  have hCfin : (volume : Measure ℝ³) C ≠ (∞ : ℝ≥0∞) :=
    ne_of_lt (lt_of_le_of_lt (le_of_eq hCvolE) ENNReal.ofReal_lt_top)
  have hCvol : (volume : Measure ℝ³).real C = 1 / 64 := by
    rw [measureReal_def, hCvolE, ENNReal.toReal_ofReal (by norm_num)]
  have hcont2 : Continuous (fun y : ℝ³ => chiSmall M (z - y)) :=
    (chiSmall_continuous hM).comp (continuous_const.sub continuous_id)
  have hI : Integrable (fun y : ℝ³ => chiSmall M y) :=
    (chiSmall_continuous hM).integrable_of_hasCompactSupport (chiSmall_hasCompactSupport hM)
  have hint : Integrable (fun y : ℝ³ => chiSmall M y * chiSmall M (z - y)) :=
    hI.mul_bdd hcont2.aestronglyMeasurable
      (ae_of_all _ (fun y => by
        rw [Real.norm_eq_abs]
        exact chiSmall_decay_coord_le_decay hM (z - y)))
  have hnn : ∀ y : ℝ³, 0 ≤ chiSmall M y * chiSmall M (z - y) :=
    fun y => mul_nonneg (chiSmall_nonneg M y) (chiSmall_nonneg M (z - y))
  have hlb : ∀ y ∈ C, c ^ 2 ≤ chiSmall M y * chiSmall M (z - y) := by
    intro y hy
    have hy4 : ∀ j : Fin 3, |y.ofLp j| ≤ 1 / 4 :=
      fun j => le_trans (hy j) (by norm_num)
    have hzy4 : ∀ j : Fin 3, |(z - y).ofLp j| ≤ 1 / 4 := by
      intro j
      have h1 : |z.ofLp j - y.ofLp j| ≤ |z.ofLp j| + |y.ofLp j| := abs_sub _ _
      have h2 : |z.ofLp j| + |y.ofLp j| ≤ 1 / 16 + 1 / 8 := add_le_add (hz j) (hy j)
      calc |(z - y).ofLp j| = |z.ofLp j - y.ofLp j| := by simp
        _ ≤ |z.ofLp j| + |y.ofLp j| := h1
        _ ≤ 1 / 16 + 1 / 8 := h2
        _ ≤ 1 / 4 := by norm_num
    have h1 : c ≤ chiSmall M y := by
      rw [hcdef]; exact chiSmall_cube_lower hM y hy4
    have h2 : c ≤ chiSmall M (z - y) := by
      rw [hcdef]; exact chiSmall_cube_lower hM (z - y) hzy4
    calc c ^ 2 = c * c := by ring
      _ ≤ chiSmall M y * chiSmall M (z - y) :=
          mul_le_mul h1 h2 hcnn (chiSmall_nonneg M y)
  have hstep1 : c ^ 2 * (1 / 64) ≤ ∫ y in C, chiSmall M y * chiSmall M (z - y) := by
    have hconst : IntegrableOn (fun _ : ℝ³ => c ^ 2) C volume :=
      integrableOn_const (s := C) hCfin
    have hmono := setIntegral_mono_on hconst hint.integrableOn hCmeas hlb
    have hcval : (∫ y in C, (fun _ : ℝ³ => c ^ 2) y) = c ^ 2 * (1 / 64) := by
      rw [setIntegral_const, hCvol]
      simp only [smul_eq_mul]
      ring
    rw [hcval] at hmono
    exact hmono
  calc smallConvLower M = c ^ 2 * (1 / 64) := by
        rw [smallConvLower, hcdef]
        norm_num
    _ ≤ ∫ y in C, chiSmall M y * chiSmall M (z - y) := hstep1
    _ ≤ ∫ y : ℝ³, chiSmall M y * chiSmall M (z - y) :=
        setIntegral_le_integral hint (ae_of_all _ hnn)
    _ = conv3Small M z := rfl

/-- **Domination of the renormalised localised kernel by its numerator.**
If the numerator `h` is supported inside `ball 0 R` with `R ≤ c/16`, then on
the support the denominator `(χ_M ⋆ χ_M)(·/c)` is `≥ smallConvLower M > 0`,
so `|h/denominator| ≤ |h|/smallConvLower M`; off the support both sides
vanish. -/
theorem abs_wSmallScaled_le {M : ℕ} (hM : 1 ≤ M) {c R : ℝ} (hc : 0 < c)
    {h : ℝ³ → ℝ}
    (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0) (hR : R ≤ c / 16) (z : ℝ³) :
    |wSmallScaled M c h z| ≤ |h z| / smallConvLower M := by
  by_cases hz : h z = 0
  · have hzero : wSmallScaled M c h z = 0 := by
      rw [show wSmallScaled M c h z = h z / convScaleSmall M c z from rfl, hz, zero_div]
    rw [hzero, hz, abs_zero, zero_div]
  · have hlt : ‖z‖ < R := by
      by_contra hcon
      exact hz (hsupp z (le_of_not_gt hcon))
    have hnorm : ‖c⁻¹ • z‖ < 1 / 16 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
      have h1 : c⁻¹ * ‖z‖ < c⁻¹ * R := mul_lt_mul_of_pos_left hlt (inv_pos.mpr hc)
      have h2 : c⁻¹ * R ≤ c⁻¹ * (c / 16) := mul_le_mul_of_nonneg_left hR (inv_pos.mpr hc).le
      have h3 : c⁻¹ * (c / 16) = 1 / 16 := by
        field_simp
      calc c⁻¹ * ‖z‖ < c⁻¹ * R := h1
        _ ≤ c⁻¹ * (c / 16) := h2
        _ = 1 / 16 := h3
    have hcoord : ∀ j : Fin 3, |(c⁻¹ • z).ofLp j| ≤ 1 / 16 := by
      intro j
      exact le_of_lt (lt_of_le_of_lt (coord_abs_le_norm _ j) hnorm)
    have hlow : smallConvLower M ≤ convScaleSmall M c z :=
      conv3Small_coord_lower hM (c⁻¹ • z) hcoord
    have hmpos : 0 < smallConvLower M := smallConvLower_pos M
    have hden : 0 < convScaleSmall M c z := lt_of_lt_of_le hmpos hlow
    have hsplit : wSmallScaled M c h z = h z / convScaleSmall M c z := rfl
    rw [hsplit, abs_div, abs_of_pos hden]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hmpos hlow

/-- Pointwise domination of the two-factor cutoff `χ_{B(u)}` by the
`ℓd`-scale bump (at the REPOINTED cutoff the `ℓ`-scale factor is the corpus
bump `χ(x/ℓ)`, bounded by its sup `chiSupAbs`; the `ℓd`-scale factor is
nonnegative). -/
theorem abs_chiSmallB_le {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (u x : ℝ³) :
    |chiSmallB M ℓ d u x| ≤ chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • x - u) := by
  have h1 : |chiScale ℓ x| ≤ chiSupAbs := chiScale_abs_le_sup ℓ x
  have h2 : |chiSmall M ((ℓ * d)⁻¹ • x - u)| = chiSmall M ((ℓ * d)⁻¹ • x - u) :=
    abs_of_nonneg (chiSmall_nonneg M _)
  dsimp [chiSmallB]
  rw [abs_mul, h2]
  exact mul_le_mul_of_nonneg_right h1 (chiSmall_nonneg M _)

/-- Integrability of a reflected translate of the bump: `u ↦ χ_M(a − u)`. -/
theorem integrable_chiSmall_shift {M : ℕ} (hM : 1 ≤ M) (a : ℝ³) :
    Integrable (fun u : ℝ³ => chiSmall M (a - u)) := by
  have hInt : Integrable (chiSmall M) :=
    (chiSmall_continuous hM).integrable_of_hasCompactSupport (chiSmall_hasCompactSupport hM)
  exact hInt.comp_sub_left a

/-- `tsupport v ⊆ ball 0 R` is the support hypothesis consumed by the
renormalisation-cancellation lemmas: `v` vanishes for `R ≤ ‖z‖`. -/
theorem eq_zero_of_tsupport_subset_ball {v : ℝ³ → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) {z : ℝ³} (hz : R ≤ ‖z‖) :
    v z = 0 := by
  by_contra hne
  have hmem : z ∈ tsupport v := subset_tsupport v (Function.mem_support.mpr hne)
  have hball := hv_supp hmem
  rw [Metric.mem_ball, dist_zero_right] at hball
  exact absurd hball (not_lt.mpr hz)

/-- **`u`-integrated localised pair kernel at the potential `v`** (the
two-body half of the telescoping), at the REPOINTED kernels: under
`tsupport v ⊆ ball 0 R0` and the renormalisation regime `R0 ≤ (ℓd)/16`,

  `∫_u wSmallPair M ℓ d u v a b = χ(a/ℓ)·(v(a−b)/(χ⋆χ)((a−b)/ℓ))·χ(b/ℓ)`,
  i.e. the corpus global kernel `wPairC ℓ v a b`. -/
theorem wSmallPair_v_uint_eq {v : ℝ³ → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R0)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ (ℓ * d) / 16) (a b : ℝ³) :
    (∫ u : ℝ³, wSmallPair M ℓ d u v a b)
      = chiScale ℓ a * (v (a - b) / convScale ℓ (a - b)) * chiScale ℓ b := by
  rw [chiSmallB_w_pair_uint_cancel (h := v) hM hℓ hd
        (fun z hz => eq_zero_of_tsupport_subset_ball hv_supp hz) hR a b]
  ring

end Work.SmallBoxSliding
