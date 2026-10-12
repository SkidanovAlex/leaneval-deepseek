import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseB7AK.W1rows.W1fun_bounds_ae
import Submission.Work.BoseFixR.FarLat.coulPair_latDistL_eq
import Submission.Work.BoseFixR.FarLat.fold_periodic_lintegral
import Submission.Work.BoseFixR.FarLat.g0_coulPot_lintegral_ae_le
import Submission.Work.BoseFixR.FarLat.integrableOn_latDistL_pair
import Submission.Work.BoseFixR.FarLat.inv_latDistL_le_latFin9
import Submission.Work.BoseFixR.FarLat.latGreen_le_latDistL_pair
import Submission.Work.BoseFixR.FarLat.latGreen_period_integrable
import Submission.Work.BoseFixR.FarLat.pairKernel_latFin9_lintegral_lt_top
import Submission.Work.BoseFixR.LatGreen.LatGreenParsevalB
import Submission.Work.BoseFixR.LatGreen.W1funDecay
import Submission.Work.BoseFixR.LatGreen.W1funPeriodSummable
import Submission.Work.BoseFixR.Rb5Lin.chiR0_le_one
import Submission.Work.BoseK15.card_le_of_vec_norm_le
import Submission.Work.BoseK15.sum_inv_one_add_norm_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

open MeasureTheory Metric
open scoped Real BigOperators

/-! ## 1. Summability of the lattice row

These three lemmas are self-contained copies of the auxiliary statements of
`Submission/Work/BoseFixR/farLatRow.lean` (`vec_onePlusSq_inv_sq_summable`, `one_le_norm_vec`,
`inv_four_le_inv_sq_sq` followed by `W1funRowSummable`); they are reproduced here because that
file's import cone is blocked by an unrelated broken sibling module.  They deliver the
summability hypothesis `hsum` of `LatGreenParsevalB`. -/

/-- `Σ_{k ∈ ℤ³}(1 + ‖vec k‖²)^{-2} < ∞`. -/
lemma vec_onePlusSq_inv_sq_summable_farLat :
    Summable (fun k : Fin 3 → ℤ => (((1 : ℝ) + ‖Work.BoseB4.vec k‖ ^ 2) ^ 2)⁻¹) := by
  obtain ⟨C, _hC0, hCle⟩ := Work.BoseK15.sum_inv_one_add_norm_le 2 (by norm_num)
  exact summable_of_sum_le
    (f := fun k : Fin 3 → ℤ => (((1 : ℝ) + ‖Work.BoseB4.vec k‖ ^ 2) ^ 2)⁻¹)
    (c := C) (fun k => by positivity) hCle

/-- A nonzero lattice label has `‖vec k‖ ≥ 1`. -/
lemma one_le_norm_vec_farLat {k : Fin 3 → ℤ} (hk : k ≠ 0) : 1 ≤ ‖Work.BoseB4.vec k‖ := by
  classical
  have hex : ∃ i : Fin 3, k i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hk (funext fun i => hcon i)
  obtain ⟨i, hi⟩ := hex
  have hcoord : (1 : ℝ) ≤ |((k i : ℤ) : ℝ)| := by
    have h2 : (0 : ℤ) < |k i| := abs_pos.mpr hi
    have h3 : (1 : ℤ) ≤ |k i| := by omega
    exact_mod_cast h3
  have hle := Work.BoseK15.two_pi_mul_abs_coord_le_norm_vec k i
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hprod : (1 : ℝ) ≤ 2 * Real.pi * |((k i : ℤ) : ℝ)| := by
    have h := mul_le_mul hpi hcoord (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    simpa using h
  linarith

/-- For `x ≥ 1`, `x^{-4} ≤ 4(1+x²)^{-2}`. -/
lemma inv_four_le_inv_sq_sq_farLat {x : ℝ} (hx : 1 ≤ x) : 1 / x ^ 4 ≤ 4 / (1 + x ^ 2) ^ 2 := by
  have h0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hx2 : 1 ≤ x ^ 2 := by nlinarith [hx]
  have hfac : 0 ≤ (3 * x ^ 2 + 1) * (x ^ 2 - 1) :=
    mul_nonneg (by positivity) (by linarith)
  have h1 : (1 + x ^ 2) ^ 2 ≤ 4 * x ^ 4 := by nlinarith [hfac]
  have h2 : 0 < (1 + x ^ 2) ^ 2 / 4 := by positivity
  have h3 : 1 / x ^ 4 ≤ 1 / ((1 + x ^ 2) ^ 2 / 4) := by
    apply one_div_le_one_div_of_le h2
    linarith
  rwa [one_div_div] at h3

/-- **Summability of the weighted full-lattice row** (the `hsum` input of
`LatGreen.LatGreenParsevalB`): from `|Ŵ₁(q)| ≤ C/(1+‖q‖)`, the terms
`Ŵ₁(ℓ⁻¹•vec k)²/‖ℓ⁻¹•vec k‖²` are bounded by `4C²ℓ⁴(1+‖vec k‖²)^{-2}`, a summable family. -/
theorem chat_sq_div_summable {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v) {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    Summable (fun k : Fin 3 → ℤ => if k = 0 then 0 else
      (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec k)) ^ 2
        / ‖ℓ⁻¹ • Work.BoseB4.vec k‖ ^ 2) := by
  obtain ⟨C, _hC0, hC⟩ := Work.BoseFixR.LatGreen.W1funDecay h hv hvrad hR hℓ hv_supp hRℓ
  have hmaj : Summable (fun k : Fin 3 → ℤ =>
      (4 * C ^ 2 * ℓ ^ 4) * (((1 : ℝ) + ‖Work.BoseB4.vec k‖ ^ 2) ^ 2)⁻¹) :=
    vec_onePlusSq_inv_sq_summable_farLat.mul_left _
  refine Summable.of_nonneg_of_le
    (f := fun k : Fin 3 → ℤ =>
      (4 * C ^ 2 * ℓ ^ 4) * (((1 : ℝ) + ‖Work.BoseB4.vec k‖ ^ 2) ^ 2)⁻¹)
    (g := fun k : Fin 3 → ℤ => if k = 0 then 0 else
      (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec k)) ^ 2
        / ‖ℓ⁻¹ • Work.BoseB4.vec k‖ ^ 2) ?_ ?_ hmaj
  · intro k
    by_cases hk : k = 0
    · rw [if_pos hk]
    · rw [if_neg hk]
      positivity
  · intro k
    by_cases hk : k = 0
    · rw [if_pos hk]
      have h0 : 0 ≤ (4 * C ^ 2 * ℓ ^ 4) * (((1 : ℝ) + ‖Work.BoseB4.vec k‖ ^ 2) ^ 2)⁻¹ := by
        positivity
      linarith
    · rw [if_neg hk]
      set q : EuclideanSpace ℝ (Fin 3) := ℓ⁻¹ • Work.BoseB4.vec k with hqdef
      have hvk : 1 ≤ ‖Work.BoseB4.vec k‖ := one_le_norm_vec_farLat hk
      have hqnorm : ‖q‖ = ℓ⁻¹ * ‖Work.BoseB4.vec k‖ := by
        rw [hqdef, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ℓ⁻¹)]
      have hqpos : 0 < ‖q‖ := by
        rw [hqnorm]
        exact mul_pos (inv_pos.mpr hℓ) (lt_of_lt_of_le zero_lt_one hvk)
      have hsq : (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2
          ≤ C ^ 2 / (1 + ‖q‖) ^ 2 := by
        have h1 := hC q
        have h2 : |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q| ^ 2
            ≤ (C / (1 + ‖q‖)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        rwa [sq_abs, div_pow] at h2
      have hstep1 : (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2 / ‖q‖ ^ 2
          ≤ C ^ 2 / ((1 + ‖q‖) ^ 2 * ‖q‖ ^ 2) := by
        calc (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2 / ‖q‖ ^ 2
            = (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2 * (1 / ‖q‖ ^ 2) := by ring
          _ ≤ (C ^ 2 / (1 + ‖q‖) ^ 2) * (1 / ‖q‖ ^ 2) :=
              mul_le_mul_of_nonneg_right hsq (by positivity)
          _ = C ^ 2 / ((1 + ‖q‖) ^ 2 * ‖q‖ ^ 2) := by
            simp only [div_eq_mul_inv, one_div, mul_inv, mul_assoc, one_mul]
      have hstep2 : C ^ 2 / ((1 + ‖q‖) ^ 2 * ‖q‖ ^ 2)
          ≤ C ^ 2 * ℓ ^ 4 / ‖Work.BoseB4.vec k‖ ^ 4 := by
        have hden : (ℓ ^ 4)⁻¹ * ‖Work.BoseB4.vec k‖ ^ 4 ≤ (1 + ‖q‖) ^ 2 * ‖q‖ ^ 2 := by
          have h1 : ℓ⁻¹ * ‖Work.BoseB4.vec k‖ ≤ 1 + ‖q‖ := by rw [← hqnorm]; linarith [hqpos]
          have h2 : (ℓ⁻¹ * ‖Work.BoseB4.vec k‖) ^ 2 ≤ (1 + ‖q‖) ^ 2 :=
            pow_le_pow_left₀ (by positivity) h1 2
          have h3 : ((ℓ⁻¹ * ‖Work.BoseB4.vec k‖) ^ 2) * ‖q‖ ^ 2
              ≤ (1 + ‖q‖) ^ 2 * ‖q‖ ^ 2 :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
          have h4 : ((ℓ⁻¹ * ‖Work.BoseB4.vec k‖) ^ 2) * ‖q‖ ^ 2
              = (ℓ ^ 4)⁻¹ * ‖Work.BoseB4.vec k‖ ^ 4 := by
            rw [hqnorm, ← inv_pow]
            ring
          rw [← h4]
          exact h3
        have hkey : 1 / ((1 + ‖q‖) ^ 2 * ‖q‖ ^ 2) ≤ ℓ ^ 4 / ‖Work.BoseB4.vec k‖ ^ 4 := by
          have hpos : 0 < (ℓ ^ 4)⁻¹ * ‖Work.BoseB4.vec k‖ ^ 4 := by
            have : 0 < ‖Work.BoseB4.vec k‖ := lt_of_lt_of_le zero_lt_one hvk
            positivity
          have h1 : 1 / ((1 + ‖q‖) ^ 2 * ‖q‖ ^ 2)
              ≤ 1 / ((ℓ ^ 4)⁻¹ * ‖Work.BoseB4.vec k‖ ^ 4) :=
            one_div_le_one_div_of_le hpos hden
          have h2 : 1 / ((ℓ ^ 4)⁻¹ * ‖Work.BoseB4.vec k‖ ^ 4)
              = ℓ ^ 4 / ‖Work.BoseB4.vec k‖ ^ 4 := by
            simp only [div_eq_mul_inv, one_div, mul_inv, inv_inv, mul_one, one_mul]
          rwa [h2] at h1
        calc C ^ 2 / ((1 + ‖q‖) ^ 2 * ‖q‖ ^ 2)
            = C ^ 2 * (1 / ((1 + ‖q‖) ^ 2 * ‖q‖ ^ 2)) := by ring
          _ ≤ C ^ 2 * (ℓ ^ 4 / ‖Work.BoseB4.vec k‖ ^ 4) :=
              mul_le_mul_of_nonneg_left hkey (sq_nonneg C)
          _ = C ^ 2 * ℓ ^ 4 / ‖Work.BoseB4.vec k‖ ^ 4 := by ring
      have hstep3 : C ^ 2 * ℓ ^ 4 / ‖Work.BoseB4.vec k‖ ^ 4
          ≤ (4 * C ^ 2 * ℓ ^ 4) * (((1 : ℝ) + ‖Work.BoseB4.vec k‖ ^ 2) ^ 2)⁻¹ := by
        have h1 := inv_four_le_inv_sq_sq_farLat hvk
        have h2 : C ^ 2 * ℓ ^ 4 * (1 / ‖Work.BoseB4.vec k‖ ^ 4)
            ≤ C ^ 2 * ℓ ^ 4 * (4 / (1 + ‖Work.BoseB4.vec k‖ ^ 2) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        calc C ^ 2 * ℓ ^ 4 / ‖Work.BoseB4.vec k‖ ^ 4
            = C ^ 2 * ℓ ^ 4 * (1 / ‖Work.BoseB4.vec k‖ ^ 4) := by ring
          _ ≤ C ^ 2 * ℓ ^ 4 * (4 / (1 + ‖Work.BoseB4.vec k‖ ^ 2) ^ 2) := h2
          _ = (4 * C ^ 2 * ℓ ^ 4) * (((1 : ℝ) + ‖Work.BoseB4.vec k‖ ^ 2) ^ 2)⁻¹ := by
            rw [div_eq_mul_inv]; ring
      calc (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec k)) ^ 2
            / ‖ℓ⁻¹ • Work.BoseB4.vec k‖ ^ 2
          = (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2 / ‖q‖ ^ 2 := by rw [hqdef]
        _ ≤ C ^ 2 / ((1 + ‖q‖) ^ 2 * ‖q‖ ^ 2) := hstep1
        _ ≤ C ^ 2 * ℓ ^ 4 / ‖Work.BoseB4.vec k‖ ^ 4 := hstep2
        _ ≤ (4 * C ^ 2 * ℓ ^ 4) * (((1 : ℝ) + ‖Work.BoseB4.vec k‖ ^ 2) ^ 2)⁻¹ := hstep3

/-! ## 2. The a.e. Coulomb-potential bound for `W₁ = wScaled ℓ (g₀)`, and the pair-kernel finiteness

`g0_coulPot_lintegral_ae_le` (delegated) gives `∫⁻ g₀(y)/‖x-y‖ ≤ 8π` a.e., and the a.e. sandwich
`g₀ ≤ W₁ ≤ 2g₀` (`W1fun_bounds_ae`, plus the pointwise vanishing of both off `ball 0 R`) upgrades
it to `W₁`.  `pairKernel_latFin9_lintegral_lt_top` (delegated) then pays every shifted Coulomb
kernel of the finite window `latFin9` by that bound. -/

/-- **The a.e. Coulomb-potential bound for `W₁`.** -/
lemma W1fun_coulPot_lintegral_ae_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v) {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    ∀ᵐ x : EuclideanSpace ℝ (Fin 3),
      (∫⁻ y : EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (Work.BoseFixR.W1fun v h ℓ y * ‖x - y‖⁻¹))
        ≤ ENNReal.ofReal (32 * Real.pi) := by
  have hg0 := Work.BoseFixR.FarLat.g0_coulPot_lintegral_ae_le h hv hvrad hR hv_supp
  have hbd := Work.BoseB7AK.W1rows.W1fun_bounds_ae hR hℓ hv hvrad hv_supp h hRℓ
  have hsand : ∀ᵐ y : EuclideanSpace ℝ (Fin 3),
      Work.BoseFixR.W1fun v h ℓ y ≤ 2 * Submission.BoseGases.g0 v h y := by
    filter_upwards [hbd] with y hy
    by_cases hyR : ‖y‖ ≤ R
    · exact (hy hyR).2
    · have hyR' : R ≤ ‖y‖ := le_of_lt (lt_of_not_ge hyR)
      rw [Work.BoseFixR.LatGreen.W1fun_eq_zero_of_le_norm h hv_supp hyR',
        Submission.BoseGases.g0_zero_of_norm_ge hv_supp hyR' h]
      norm_num
  filter_upwards [hg0] with x hx
  have hle : (fun y : EuclideanSpace ℝ (Fin 3) =>
        ENNReal.ofReal (Work.BoseFixR.W1fun v h ℓ y * ‖x - y‖⁻¹))
      ≤ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))]
        (fun y : EuclideanSpace ℝ (Fin 3) =>
          2 * ENNReal.ofReal (Submission.BoseGases.g0 v h y * ‖x - y‖⁻¹)) := by
    filter_upwards [hsand] with y hy
    have h2 : Work.BoseFixR.W1fun v h ℓ y * ‖x - y‖⁻¹
        ≤ (2 * Submission.BoseGases.g0 v h y) * ‖x - y‖⁻¹ :=
      mul_le_mul_of_nonneg_right hy (inv_nonneg.mpr (norm_nonneg _))
    calc ENNReal.ofReal (Work.BoseFixR.W1fun v h ℓ y * ‖x - y‖⁻¹)
        ≤ ENNReal.ofReal ((2 * Submission.BoseGases.g0 v h y) * ‖x - y‖⁻¹) :=
          ENNReal.ofReal_le_ofReal h2
      _ = 2 * ENNReal.ofReal (Submission.BoseGases.g0 v h y * ‖x - y‖⁻¹) := by
          rw [show (2 * Submission.BoseGases.g0 v h y) * ‖x - y‖⁻¹
              = 2 * (Submission.BoseGases.g0 v h y * ‖x - y‖⁻¹) by ring,
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  calc (∫⁻ y : EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (Work.BoseFixR.W1fun v h ℓ y * ‖x - y‖⁻¹))
      ≤ ∫⁻ y : EuclideanSpace ℝ (Fin 3),
          2 * ENNReal.ofReal (Submission.BoseGases.g0 v h y * ‖x - y‖⁻¹) :=
        lintegral_mono_ae hle
    _ = 2 * ∫⁻ y : EuclideanSpace ℝ (Fin 3),
          ENNReal.ofReal (Submission.BoseGases.g0 v h y * ‖x - y‖⁻¹) :=
        lintegral_const_mul' 2 _ (by norm_num)
    _ ≤ 2 * ENNReal.ofReal (8 * Real.pi) := by gcongr
    _ ≤ ENNReal.ofReal (32 * Real.pi) := by
        have h2 : (2 : ENNReal) * ENNReal.ofReal (8 * Real.pi)
            = ENNReal.ofReal (16 * Real.pi) := by
          rw [← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 1
          ring
        rw [h2]
        exact ENNReal.ofReal_le_ofReal (by nlinarith [Real.pi_pos])

open Work.BoseFixR.FarLat in
/-- **The pair-kernel finiteness at the `latFin9` window for `W₁`.** -/
lemma W1fun_pairKernel_latFin9_lintegral_lt_top {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v) {R ℓ : ℝ} (hR : 0 < R)
    (hℓ : 0 < ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    (∫⁻ q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (Work.BoseFixR.W1fun v h ℓ q.1 * Work.BoseFixR.W1fun v h ℓ q.2
          * (∑ p ∈ Work.BoseFixR.latFin9,
              (‖q.1 - q.2 - Work.BoseFixR.lat ℓ p‖)⁻¹))) < ⊤ :=
  Work.BoseFixR.FarLat.pairKernel_latFin9_lintegral_lt_top hℓ (by positivity)
    (Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ)
    (Submission.BoseGases.wScaled_g0_nonneg_ae hR hv hvrad hv_supp h)
    (W1fun_coulPot_lintegral_ae_le h hv hvrad hR hℓ hv_supp hRℓ)

/-! ## 4. The comparison of the `ofReal`-clamped products -/

open Work.BoseFixR.FarLat in
/-- If `0 ≤ c ≤ s` then `ofReal (a * c) ≤ ofReal (a * s)` for **every** real `a`: for `a ≥ 0` this
is monotonicity, and for `a < 0` the left side is `ofReal` of a nonpositive number, i.e. `0`.
This is what makes the pointwise comparison of the cell and window kernels insensitive to the sign
of the periodised charge. -/
lemma ofReal_mul_le_ofReal_mul {a c s : ℝ} (hc : 0 ≤ c) (hcs : c ≤ s) :
    ENNReal.ofReal (a * c) ≤ ENNReal.ofReal (a * s) := by
  by_cases ha : 0 ≤ a
  · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hcs ha)
  · have h1 : a * c ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ha) hc
    rw [ENNReal.ofReal_eq_zero.mpr h1]
    exact zero_le

theorem farLatParseval {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) {μ : ℝ} (hμ : 0 < μ)
    (hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0) :
    (∑' k : Fin 3 → ℤ, if k = 0 then 0 else
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))
            ((Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec k)) ^ 2
          / ‖(Work.BoseFixR.ell v μ)⁻¹ • Work.BoseB4.vec k‖ ^ 2)
      ≤ (Work.BoseFixR.ell v μ) ^ 3 / (4 * Real.pi) *
          ∫ z : EuclideanSpace ℝ (Fin 3),
            (∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ) x
              * Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ) (x + z))
            / Metric.infDist z (Set.range (fun n : Fin 3 → ℤ => Work.BoseFixR.lat (Work.BoseFixR.ell v μ) n)) := by
  have key : ∀ ℓ : ℝ, 0 < ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 →
      (∑' k : Fin 3 → ℤ, if k = 0 then 0 else
          (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec k)) ^ 2
            / ‖ℓ⁻¹ • Work.BoseB4.vec k‖ ^ 2)
        ≤ ℓ ^ 3 / (4 * Real.pi) *
            ∫ z : EuclideanSpace ℝ (Fin 3),
              (∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h ℓ x
                * Work.BoseFixR.W1fun v h ℓ (x + z))
              / Metric.infDist z (Set.range (fun n : Fin 3 → ℤ => Work.BoseFixR.lat ℓ n)) := by


    intro ℓ hℓ hRℓ'
    -- ## 0. The basic facts about `W = W₁ = wScaled ℓ (g₀)`
    have hchi : Submission.BoseGases.chiR0 ≤ 1 := Work.BoseFixR.Rb5Lin.chiR0_le_one
    have hRle : R ≤ ℓ := by
      calc R ≤ ℓ * Submission.BoseGases.chiR0 := hRℓ'
        _ ≤ ℓ * 1 := by nlinarith [hchi, hℓ]
        _ = ℓ := mul_one ℓ
    have hW : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ) :=
      Submission.BoseGases.wScaled_g0_integrable (ℓ := ℓ) hR hv_supp h hℓ hRℓ'
    have hWnn : 0 ≤ᵐ[MeasureTheory.volume] Work.BoseFixR.W1fun v h ℓ :=
      Submission.BoseGases.wScaled_g0_nonneg_ae (ℓ := ℓ) hR hv hvrad hv_supp h
    have hWev : ∀ x : EuclideanSpace ℝ (Fin 3),
        Work.BoseFixR.W1fun v h ℓ (-x) = Work.BoseFixR.W1fun v h ℓ x :=
      Work.BoseFixR.isEven_W1fun h hvrad ℓ
    have hWper : ∀ x : EuclideanSpace ℝ (Fin 3),
        Summable (fun n : Fin 3 → ℤ =>
          Work.BoseFixR.W1fun v h ℓ (x - Work.BoseFixR.lat ℓ n)) :=
      Work.BoseFixR.LatGreen.W1funPeriodSummable h hR hℓ hv_supp
    have hsum : Summable (fun k : Fin 3 → ℤ => if k = 0 then 0 else
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec k)) ^ 2
          / ‖ℓ⁻¹ • Work.BoseB4.vec k‖ ^ 2) :=
      chat_sq_div_summable h hv hvrad hR hℓ hv_supp hRℓ'
    -- ## 1. The folding identity for the periodic kernel `(latDistL ℓ ·)⁻¹`
    have hφm : Measurable
        (fun z : EuclideanSpace ℝ (Fin 3) => (Work.BoseFixR.latDistL ℓ z)⁻¹) :=
      measurable_infDist.inv
    have hφnn : 0 ≤ᵐ[MeasureTheory.volume]
        (fun z : EuclideanSpace ℝ (Fin 3) => (Work.BoseFixR.latDistL ℓ z)⁻¹) :=
      Filter.Eventually.of_forall fun z => inv_nonneg.mpr (Work.BoseFixR.latDistL_nonneg ℓ z)
    have hφper : ∀ (z : EuclideanSpace ℝ (Fin 3)) (n : Fin 3 → ℤ),
        (fun z : EuclideanSpace ℝ (Fin 3) => (Work.BoseFixR.latDistL ℓ z)⁻¹)
            (z + Work.BoseFixR.lat ℓ n)
          = (fun z : EuclideanSpace ℝ (Fin 3) => (Work.BoseFixR.latDistL ℓ z)⁻¹) z := by
      intro z n
      simp only
      rw [Work.BoseFixR.latDistL_period]
    have hfold := Work.BoseFixR.FarLat.fold_periodic_lintegral hℓ hW hWnn hWper
      (φ := fun z : EuclideanSpace ℝ (Fin 3) => (Work.BoseFixR.latDistL ℓ z)⁻¹)
      hφm hφnn hφper
    -- ## 2. The pointwise comparison against the finite window `latFin9`
    have hcmp : (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          ENNReal.ofReal (Work.BoseFixR.W1fun v h ℓ q.1 * Work.BoseFixR.W1fun v h ℓ q.2
            * (Work.BoseFixR.latDistL ℓ (q.1 - q.2))⁻¹))
        ≤ᵐ[MeasureTheory.volume]
        (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          ENNReal.ofReal (Work.BoseFixR.W1fun v h ℓ q.1 * Work.BoseFixR.W1fun v h ℓ q.2
            * (∑ p ∈ Work.BoseFixR.latFin9,
                (‖q.1 - q.2 - Work.BoseFixR.lat ℓ p‖)⁻¹))) := by
      filter_upwards with q
      by_cases h2 : ‖q.1 - q.2‖ ≤ 2 * ℓ
      · exact ofReal_mul_le_ofReal_mul
          (inv_nonneg.mpr (Work.BoseFixR.latDistL_nonneg ℓ _))
          (Work.BoseFixR.FarLat.inv_latDistL_le_latFin9 hℓ h2)
      · have hlt : 2 * ℓ < ‖q.1 - q.2‖ := lt_of_not_ge h2
        have hzero : Work.BoseFixR.W1fun v h ℓ q.1 = 0
            ∨ Work.BoseFixR.W1fun v h ℓ q.2 = 0 := by
          by_contra hc
          push_neg at hc
          have hsuppW := Work.BoseFixR.tsupport_W1fun_subset h hv_supp ℓ
          have h1 : q.1 ∈ tsupport (Work.BoseFixR.W1fun v h ℓ) :=
            subset_tsupport _ (Function.mem_support.mpr hc.1)
          have h2' : q.2 ∈ tsupport (Work.BoseFixR.W1fun v h ℓ) :=
            subset_tsupport _ (Function.mem_support.mpr hc.2)
          have h3 : ‖q.1‖ < R := by
            have := hsuppW h1
            simpa [Metric.mem_ball, dist_zero_right] using this
          have h4 : ‖q.2‖ < R := by
            have := hsuppW h2'
            simpa [Metric.mem_ball, dist_zero_right] using this
          have h5 : ‖q.1 - q.2‖ ≤ ‖q.1‖ + ‖q.2‖ := norm_sub_le _ _
          linarith
        rcases hzero with hz | hz <;> simp [hz]
    -- ## 3. The cell-side finiteness of the `(latDistL)⁻¹` pair integral
    have hF : (∫⁻ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
        ENNReal.ofReal (Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.1
          * Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.2
          * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹)) < ⊤ := by
      rw [hfold]
      exact lt_of_le_of_lt (MeasureTheory.lintegral_mono_ae hcmp)
        (W1fun_pairKernel_latFin9_lintegral_lt_top h hv hvrad hR hℓ hv_supp hRℓ')
    have hR3fin : (∫⁻ q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (Work.BoseFixR.W1fun v h ℓ q.1 * Work.BoseFixR.W1fun v h ℓ q.2
          * (Work.BoseFixR.latDistL ℓ (q.1 - q.2))⁻¹)) < ⊤ := by
      rw [← hfold]
      exact hF
    -- ## 4. The `(B)` integrability and the lattice Parseval identity
    have hB := Work.BoseFixR.FarLat.latGreen_period_integrable hℓ hW hWnn hWper hF
    have hP := Work.BoseFixR.LatGreen.LatGreenParsevalB hℓ hW hWev hWper hsum hB
    -- ## 5. The ℝ³-side identification of the single kernel
    have hI := Work.BoseFixR.FarLat.coulPair_latDistL_eq hℓ hW hWnn hR3fin
    -- ## 6. `ofReal`-bookkeeping: the cell integral and the ℝ³ integral agree
    have hPnn_ae : ∀ᵐ x ∂(MeasureTheory.volume :
        MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
        0 ≤ Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ x :=
      Work.BoseFixR.period_nonneg_ae hWnn
    have hPnn_cell : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ)),
        0 ≤ Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ x :=
      hPnn_ae.filter_mono MeasureTheory.ae_restrict_le
    have hμc : MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ)
        = (MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ)).prod
          (MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ)) := by
      rw [MeasureTheory.Measure.volume_eq_prod (EuclideanSpace ℝ (Fin 3))
        (EuclideanSpace ℝ (Fin 3))]
      exact (MeasureTheory.Measure.prod_restrict _ _).symm
    have hnn_cell : 0 ≤ᵐ[MeasureTheory.volume.restrict
        (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ)]
        (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.1
            * Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.2
            * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹) := by
      have h1 : ∀ᵐ p ∂((MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ)).prod
          (MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ))),
          0 ≤ Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.1 :=
        MeasureTheory.Measure.quasiMeasurePreserving_fst.ae hPnn_cell
      have h2 : ∀ᵐ p ∂((MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ)).prod
          (MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ))),
          0 ≤ Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.2 :=
        MeasureTheory.Measure.quasiMeasurePreserving_snd.ae hPnn_cell
      rw [hμc]
      filter_upwards [h1, h2] with p hp1 hp2
      exact mul_nonneg (mul_nonneg hp1 hp2)
        (inv_nonneg.mpr (Work.BoseFixR.latDistL_nonneg ℓ _))
    have hcellInt : MeasureTheory.IntegrableOn
        (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.1
            * Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.2
            * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹)
        (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ) :=
      Work.BoseFixR.FarLat.integrableOn_latDistL_pair hℓ hW hWnn hWper hF
    have hR3nn : 0 ≤ᵐ[(MeasureTheory.volume :
        MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)))]
        (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          Work.BoseFixR.W1fun v h ℓ q.1 * Work.BoseFixR.W1fun v h ℓ q.2
            * (Work.BoseFixR.latDistL ℓ (q.1 - q.2))⁻¹) := by
      have h1 : 0 ≤ᵐ[(MeasureTheory.volume :
          MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)))]
          (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
            Work.BoseFixR.W1fun v h ℓ q.1) :=
        MeasureTheory.Measure.quasiMeasurePreserving_fst.ae hWnn
      have h2 : 0 ≤ᵐ[(MeasureTheory.volume :
          MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)))]
          (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
            Work.BoseFixR.W1fun v h ℓ q.2) :=
        MeasureTheory.Measure.quasiMeasurePreserving_snd.ae hWnn
      filter_upwards [h1, h2] with q hq1 hq2
      exact mul_nonneg (mul_nonneg hq1 hq2)
        (inv_nonneg.mpr (Work.BoseFixR.latDistL_nonneg ℓ _))
    have hR3asm : AEStronglyMeasurable
        (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          Work.BoseFixR.W1fun v h ℓ q.1 * Work.BoseFixR.W1fun v h ℓ q.2
            * (Work.BoseFixR.latDistL ℓ (q.1 - q.2))⁻¹) MeasureTheory.volume := by
      have hA : AEMeasurable (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          Work.BoseFixR.W1fun v h ℓ q.1) MeasureTheory.volume := hW.aemeasurable.comp_fst
      have hBm : AEMeasurable (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          Work.BoseFixR.W1fun v h ℓ q.2) MeasureTheory.volume := hW.aemeasurable.comp_snd
      have hC : AEMeasurable (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          (Work.BoseFixR.latDistL ℓ (q.1 - q.2))⁻¹) MeasureTheory.volume :=
        ((measurable_infDist.comp (measurable_fst.sub measurable_snd)).inv).aemeasurable
      exact ((hA.mul hBm).mul hC).aestronglyMeasurable
    have hR3int : MeasureTheory.Integrable
        (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          Work.BoseFixR.W1fun v h ℓ q.1 * Work.BoseFixR.W1fun v h ℓ q.2
            * (Work.BoseFixR.latDistL ℓ (q.1 - q.2))⁻¹) MeasureTheory.volume :=
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hR3asm hR3nn).mp
        (ne_top_of_lt hR3fin)
    have hcell : (∫ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
          Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.1
            * Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.2
            * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹)
        = ∫ z : EuclideanSpace ℝ (Fin 3),
            (∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h ℓ x
              * Work.BoseFixR.W1fun v h ℓ (x + z))
            * (Work.BoseFixR.latDistL ℓ z)⁻¹ := by
      have h1 : ENNReal.ofReal (∫ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
            Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.1
              * Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.2
              * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹)
          = ENNReal.ofReal (∫ z : EuclideanSpace ℝ (Fin 3),
              (∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h ℓ x
                * Work.BoseFixR.W1fun v h ℓ (x + z))
              * (Work.BoseFixR.latDistL ℓ z)⁻¹) := by
        rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hcellInt hnn_cell, hfold, ← hI,
          MeasureTheory.ofReal_integral_eq_lintegral_ofReal hR3int hR3nn]
      have hnn1 : (0 : ℝ) ≤ ∫ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
            Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.1
              * Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.2
              * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹ :=
        MeasureTheory.integral_nonneg_of_ae hnn_cell
      have hnn2 : (0 : ℝ) ≤ ∫ z : EuclideanSpace ℝ (Fin 3),
              (∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h ℓ x
                * Work.BoseFixR.W1fun v h ℓ (x + z))
              * (Work.BoseFixR.latDistL ℓ z)⁻¹ := by
        refine MeasureTheory.integral_nonneg_of_ae ?_
        filter_upwards with z
        have hinner : (0 : ℝ) ≤ ∫ x : EuclideanSpace ℝ (Fin 3),
            Work.BoseFixR.W1fun v h ℓ x * Work.BoseFixR.W1fun v h ℓ (x + z) := by
          refine MeasureTheory.integral_nonneg_of_ae ?_
          filter_upwards [hWnn, (MeasureTheory.measurePreserving_add_right
            MeasureTheory.volume z).quasiMeasurePreserving.ae hWnn] with x hx hxz
          exact mul_nonneg hx hxz
        exact mul_nonneg hinner (inv_nonneg.mpr (Work.BoseFixR.latDistL_nonneg ℓ _))
      calc (∫ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
            Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.1
              * Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.2
              * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹)
          = (ENNReal.ofReal (∫ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
              Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.1
                * Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.2
                * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹)).toReal :=
              (ENNReal.toReal_ofReal hnn1).symm
        _ = (ENNReal.ofReal (∫ z : EuclideanSpace ℝ (Fin 3),
              (∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h ℓ x
                * Work.BoseFixR.W1fun v h ℓ (x + z))
              * (Work.BoseFixR.latDistL ℓ z)⁻¹)).toReal := by rw [h1]
        _ = ∫ z : EuclideanSpace ℝ (Fin 3),
              (∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h ℓ x
                * Work.BoseFixR.W1fun v h ℓ (x + z))
              * (Work.BoseFixR.latDistL ℓ z)⁻¹ := ENNReal.toReal_ofReal hnn2
    -- ## 7. The Fubini passage from the iterated to the product integral
    have hfub : (∫ x in Work.BoseFixR.cell ℓ, ∫ y in Work.BoseFixR.cell ℓ,
          Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ x
            * Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ y
            * (ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (x - y))))
        = ∫ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
            Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.1
              * Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.2
              * (ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2))) := by
      have hlgb : AEMeasurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2))) MeasureTheory.volume :=
        ((Work.BoseFixR.LatGreen.measurable_latGreen.comp
          ((measurable_fst.sub measurable_snd).const_smul (ℓ⁻¹ : ℝ))).const_mul (ℓ ^ 2)).aemeasurable
      have hasm : AEStronglyMeasurable
          (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
            Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.1
              * Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.2
              * (ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2))))
          ((MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ)).prod
            (MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ))) := by
        have hPae : AEMeasurable (Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ)
            (MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ)) :=
          (Work.BoseFixR.LatGreen.integrableOn_period hℓ hW hWper).1.aemeasurable
        have h1 : AEMeasurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
            Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.1)
            ((MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ)).prod
              (MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ))) := hPae.comp_fst
        have h2 : AEMeasurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
            Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.2)
            ((MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ)).prod
              (MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ))) := hPae.comp_snd
        have h3 : AEMeasurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
            ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2)))
            ((MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ)).prod
              (MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ))) :=
          hlgb.mono_measure (by
            rw [MeasureTheory.Measure.prod_restrict]
            exact MeasureTheory.Measure.restrict_le_self)
        exact (((h1.mul h2).mul h3).aestronglyMeasurable)
      -- (`h3` is transferred from the ambient measure to the restricted product)
      have hint : MeasureTheory.Integrable
          (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
            Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.1
              * Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.2
              * (ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2))))
          ((MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ)).prod
            (MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ))) := by
        have hB' : MeasureTheory.Integrable
            (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
              |Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.1
                * Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.2
                * (ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2)))|)
            ((MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ)).prod
              (MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ))) := by
          rw [← hμc]
          exact hB
        exact hB'.mono' hasm (Filter.Eventually.of_forall fun p => le_of_eq (by
          rw [Real.norm_eq_abs]))
      have h := MeasureTheory.integral_prod
        (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.1
            * Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.2
            * (ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2)))) hint
      rw [hμc]
      exact h.symm
    -- ## 8. The comparison of the two kernels (delegated)
    have hmono : (∫ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
          Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.1
            * Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.2
            * (ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2))))
        ≤ ℓ ^ 3 / (4 * Real.pi) *
            (∫ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
              Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.1
                * Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.2
                * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹) :=
      Work.BoseFixR.FarLat.latGreen_le_latDistL_pair hℓ hW hWnn hWper hB hF
    -- ## 9. The final chain
    calc (∑' k : Fin 3 → ℤ, if k = 0 then 0 else
            (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec k)) ^ 2
              / ‖ℓ⁻¹ • Work.BoseB4.vec k‖ ^ 2)
        = ∫ x in Work.BoseFixR.cell ℓ, ∫ y in Work.BoseFixR.cell ℓ,
            Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ x
              * Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ y
              * (ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (x - y))) := hP
      _ = ∫ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
            Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.1
              * Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.2
              * (ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2))) := hfub
      _ ≤ ℓ ^ 3 / (4 * Real.pi) *
            (∫ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
              Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.1
                * Work.BoseFixR.LatGreen.period (Work.BoseFixR.W1fun v h ℓ) ℓ p.2
                * (Work.BoseFixR.latDistL ℓ (p.1 - p.2))⁻¹) := hmono
      _ = ℓ ^ 3 / (4 * Real.pi) *
            ∫ z : EuclideanSpace ℝ (Fin 3),
              (∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h ℓ x
                * Work.BoseFixR.W1fun v h ℓ (x + z))
              * (Work.BoseFixR.latDistL ℓ z)⁻¹ := by rw [hcell]
      _ = ℓ ^ 3 / (4 * Real.pi) *
            ∫ z : EuclideanSpace ℝ (Fin 3),
              (∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h ℓ x
                * Work.BoseFixR.W1fun v h ℓ (x + z))
              / Metric.infDist z
                  (Set.range (fun n : Fin 3 → ℤ => Work.BoseFixR.lat ℓ n)) := rfl

  exact key (Work.BoseFixR.ell v μ) (Work.BoseFixR.ell_pos' v hμ hav) hRℓ

end Work.BoseFixR
