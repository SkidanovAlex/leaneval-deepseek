import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBox.q3windowWeak
import Submission.Work.BoseBoxFock.chiTail_bound
import Submission.Work.BoseBoxFock.cnPlus_le_bigM_mul
import Submission.Work.BoseBoxFock.thetaTail_bound
import Submission.Work.BoseBoxFock.wLoc_fibre_kernelCompare
import Submission.Work.BoseFixB2.DvApriori.exists_adm_chiR0_ge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotChiLin_aux` — the elementary arithmetic of the `χ`-row assembly

This module collects the small, assembly-independent facts used by
`Submission/Work/BoseBoxFock/PotChiLin_exists.lean`:

* `wScaled_int_abs_le` — the `L¹` mass of the renormalised kernel in the dilute regime;
* `g0_abs_integral_le`, `g0w0_abs_integral_le` — the `L¹` masses of `g₀` and `g₀ω`;
* `errKafz_ge_slot` — the slot `Cμ²R²ℓ³t/a` inside FS's error;
* `one_le_mu_mul_side_sq` — `1 ≤ μ(a v)ℓ²` (from `ℓ = (μσ³)^{-3/646}(μσ)^{-1/2}`);
* `exists_tails_dil` — the `N^{-1}` tails below `C·(μa³)`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The `L¹` mass of the renormalised kernel -/

/-- **`∫|wScaled ℓ h| ≤ 2∫|h|`** in the dilute regime `R ≤ ℓ·chiR0` for `h` supported in
`ball 0 R`: the renormalised kernel is at most twice its numerator there
(`Submission.BoseGases.wScaled_abs_le_two`). -/
theorem wScaled_int_abs_le {ℓ R M : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) {g : E3 → ℝ}
    (hgsupp : ∀ z : E3, R ≤ ‖z‖ → g z = 0) (hgint : MeasureTheory.Integrable g)
    (hM : (∫ z : E3, |g z|) ≤ M) :
    (∫ z : E3, |Submission.BoseGases.wScaled ℓ g z|) ≤ 2 * M := by
  have hpt : ∀ z : E3, |Submission.BoseGases.wScaled ℓ g z| ≤ 2 * |g z| :=
    fun z => Submission.BoseGases.wScaled_abs_le_two hℓ hR hRℓ hgsupp z
  have h1 : (∫ z : E3, |Submission.BoseGases.wScaled ℓ g z|) ≤ ∫ z : E3, 2 * |g z| :=
    MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _)
      (hgint.abs.const_mul 2) (Filter.Eventually.of_forall hpt)
  rw [MeasureTheory.integral_const_mul] at h1
  linarith

/-- **The `L¹` mass of `g₀`**: `∫|g₀| = ∫g₀ = 8πa`. -/
theorem g0_abs_integral_le {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hR : 0 < R) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) :
    (∫ x : E3, |Submission.BoseGases.g0 v h x|) ≤ 8 * Real.pi * BoseGases.a v := by
  have hnn := Submission.BoseGases.g0_nonneg_ae hR hv hvrad hv_supp h
  have h1 : (∫ x : E3, |Submission.BoseGases.g0 v h x|)
      = ∫ x : E3, Submission.BoseGases.g0 v h x := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hnn] with x hx
    exact abs_of_nonneg hx
  rw [h1, Submission.BoseGases.g0_integral hR hv_supp h]

/-- **The `L¹` mass of `g₀ω`**: `∫|g₀ω| = ∫g₀ω ≤ 8πa`. -/
theorem g0w0_abs_integral_le {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hR : 0 < R) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) :
    (∫ x : E3, |Submission.BoseGases.g0 v h x * Classical.choose h x|)
      ≤ 8 * Real.pi * BoseGases.a v := by
  obtain ⟨hrad, hsol⟩ := Classical.choose_spec h
  have hb := Submission.BoseGases.scattering_bounds_ae hR hv hvrad hv_supp hrad hsol
  have hnn0 := Submission.BoseGases.g0_nonneg_ae hR hv hvrad hv_supp h
  have hnn : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure E3),
      0 ≤ Submission.BoseGases.g0 v h x * Classical.choose h x := by
    filter_upwards [hnn0, hb.1] with x hx hy
    exact mul_nonneg hx hy
  have h1 : (∫ x : E3, |Submission.BoseGases.g0 v h x * Classical.choose h x|)
      = ∫ x : E3, Submission.BoseGases.g0 v h x * Classical.choose h x := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hnn] with x hx
    exact abs_of_nonneg hx
  rw [h1]
  exact (Submission.BoseGases.chosen_gomega_integral_bounds hR hv hvrad hv_supp h).2

/-! ## 2. The slot inside FS's error -/

/-- **The slot `Cμ²R²ℓ³(μa³)/a` sits inside `errKafz v R μ C`** (the `(R/a)²√t` row of FS's
error bracket). -/
theorem errKafz_ge_slot {v : E3 → ℝ} {R μ C : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v)
    (hR : 0 ≤ R) (hC : 0 ≤ C) :
    C * μ ^ 2 * R ^ 2 * (Work.BoseFixR.ell v μ) ^ 3 * Work.BoseFixR.dil v μ / BoseGases.a v
      ≤ Work.BoseFixR.errKafz v R μ C := by
  have ha : 0 < BoseGases.a v := hav
  have ht0 : 0 ≤ Work.BoseFixR.dil v μ := by
    rw [Work.BoseFixR.dil]; positivity
  have hst : Real.sqrt (Work.BoseFixR.dil v μ) * Real.sqrt (Work.BoseFixR.dil v μ)
      = Work.BoseFixR.dil v μ := by
    rw [← sq, Real.sq_sqrt ht0]
  have hKlpos : 0 < (Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl := by
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hK3 : 0 ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl ^ (-(3 : ℝ)) :=
    Real.rpow_nonneg hKlpos.le _
  have hX : 0 ≤ Work.BoseFixR.fsX v μ ^ 2 := sq_nonneg _
  have hE : 0 ≤ Work.BoseFixR.errExp v μ := by
    rw [Work.BoseFixR.errExp]; exact Real.rpow_nonneg ht0 _
  have hbracket : (R / BoseGases.a v) ^ 2 * Real.sqrt (Work.BoseFixR.dil v μ)
      ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl ^ (-(3 : ℝ)) + Work.BoseFixR.fsX v μ ^ 2
          + (R / BoseGases.a v) ^ 2 * Real.sqrt (Work.BoseFixR.dil v μ)
          + Work.BoseFixR.errExp v μ := by linarith
  have hℓp : 0 < Work.BoseFixR.ell v μ := Work.BoseBox.sideAt_pos hμ hav
  have hpre : 0 ≤ C * μ ^ 2 * BoseGases.a v * (Work.BoseFixR.ell v μ) ^ 3
      * Real.sqrt (Work.BoseFixR.dil v μ) := by positivity
  have hmain := mul_le_mul_of_nonneg_left hbracket hpre
  have hid : C * μ ^ 2 * R ^ 2 * (Work.BoseFixR.ell v μ) ^ 3 * Work.BoseFixR.dil v μ
          / BoseGases.a v
      = C * μ ^ 2 * BoseGases.a v * (Work.BoseFixR.ell v μ) ^ 3
          * Real.sqrt (Work.BoseFixR.dil v μ)
          * ((R / BoseGases.a v) ^ 2 * Real.sqrt (Work.BoseFixR.dil v μ)) := by
    conv_lhs => rw [show Work.BoseFixR.dil v μ
      = Real.sqrt (Work.BoseFixR.dil v μ) * Real.sqrt (Work.BoseFixR.dil v μ) from hst.symm]
    rw [div_pow]
    field_simp
  rw [Work.BoseFixR.errKafz, hid]
  exact hmain

/-! ## 3. The regime `1 ≤ μ(a v)ℓ²` -/

/-- The box side at `(μ, σ)`: `sideAt μ σ = (μσ³)^{-3/646}(μσ)^{-1/2}`. -/
theorem sideAt_eq_rpow' {σ μ : ℝ} (hσ : 0 < σ) (hμ : 0 < μ) :
    Work.BoseBox.sideAt μ σ
      = (μ * σ ^ 3) ^ (-(3 / 646 : ℝ)) * (μ * σ) ^ (-(1 / 2 : ℝ)) := by
  dsimp only [Work.BoseBox.sideAt, Work.BoseBox.boxSide, Work.BoseBox.paramsAt,
    Work.BoseBox.fsParams, Work.BoseBox.fsXp]
  norm_num

/-- **`1 ≤ μσℓ²` for `ℓ = sideAt μ σ` and `μσ³ ≤ 1`**: since `μσℓ² = (μσ³)^{-3/323} ≥ 1`. -/
theorem one_le_mu_mul_side_sq {σ μ : ℝ} (hσ : 0 < σ) (hμ : 0 < μ) (ht : μ * σ ^ 3 ≤ 1) :
    1 ≤ μ * σ * (Work.BoseBox.sideAt μ σ) ^ 2 := by
  have hpos : (0 : ℝ) < μ * σ ^ 3 := by positivity
  have hpos' : (0 : ℝ) < μ * σ := by positivity
  have hℓ := sideAt_eq_rpow' hσ hμ
  have ha2 : (((μ * σ ^ 3) ^ (-(3 / 646 : ℝ))) ^ 2) = (μ * σ ^ 3) ^ (-(3 / 323 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    norm_num
  have hb2 : (((μ * σ) ^ (-(1 / 2 : ℝ))) ^ 2) = (μ * σ) ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos'.le]
    norm_num
  have hcancel : μ * σ * (μ * σ) ^ (-(1 : ℝ)) = 1 := by
    rw [Real.rpow_neg_one, mul_inv_cancel₀ (ne_of_gt hpos')]
  have hkey : μ * σ * (Work.BoseBox.sideAt μ σ) ^ 2 = (μ * σ ^ 3) ^ (-(3 / 323 : ℝ)) := by
    rw [hℓ, mul_pow, ha2, hb2]
    have hstep : μ * σ * ((μ * σ ^ 3) ^ (-(3 / 323 : ℝ)) * (μ * σ) ^ (-(1 : ℝ)))
        = (μ * σ ^ 3) ^ (-(3 / 323 : ℝ)) * (μ * σ * (μ * σ) ^ (-(1 : ℝ))) := by ring
    rw [hstep, hcancel, mul_one]
  rw [hkey]
  have h1 : (1 : ℝ) ^ (-(3 / 323 : ℝ)) ≤ (μ * σ ^ 3) ^ (-(3 / 323 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hpos ht (by norm_num)
  rwa [Real.one_rpow] at h1

/-! ## 4. The truncation tails below `C·(μa³)` -/

/-- **The two truncation tails at `N ≥ ⌈(μa³)^{-1}⌉`** are at most `Cd·(μa³)`, for a universal
constant `Cd`. -/
theorem exists_tails_dil :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ {v : E3 → ℝ} {μ : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v)
      {N : ℕ}, Nat.ceil ((Work.BoseFixR.dil v μ)⁻¹) ≤ N →
      (∀ x : E3, ‖chiTail (Work.BoseBox.sideAt μ (BoseGases.a v)) N x‖
          ≤ Cd * Work.BoseFixR.dil v μ)
        ∧ (∀ x : E3, ‖thetaTail (Work.BoseBox.sideAt μ (BoseGases.a v)) N x‖
          ≤ Cd * Work.BoseFixR.dil v μ) := by
  obtain ⟨D1, hD10, hD1⟩ := chiTail_bound 1
  obtain ⟨D2, hD20, hD2⟩ := thetaTail_bound 1
  refine ⟨D1 + D2, by positivity, ?_⟩
  intro v μ hμ hav N hN
  have ht : 0 < Work.BoseFixR.dil v μ := by rw [Work.BoseFixR.dil]; positivity
  have hℓ : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
  have hle : ((Work.BoseFixR.dil v μ)⁻¹) ≤ (N : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
  have hden : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hkey : ((N : ℝ) + 1)⁻¹ ≤ Work.BoseFixR.dil v μ := by
    rw [inv_le_iff_one_le_mul₀ hden]
    have h1 : 1 ≤ Work.BoseFixR.dil v μ * (N : ℝ) := by
      have h2 := mul_le_mul_of_nonneg_left hle ht.le
      rwa [mul_inv_cancel₀ (ne_of_gt ht)] at h2
    have h3 : Work.BoseFixR.dil v μ * (N : ℝ) ≤ Work.BoseFixR.dil v μ * ((N : ℝ) + 1) := by
      have := mul_le_mul_of_nonneg_left (by linarith : (N : ℝ) ≤ (N : ℝ) + 1) ht.le
      linarith
    linarith
  constructor
  · intro x
    have h1 : D1 * ((N : ℝ) + 1)⁻¹ ≤ D1 * Work.BoseFixR.dil v μ :=
      mul_le_mul_of_nonneg_left hkey hD10
    calc ‖chiTail (Work.BoseBox.sideAt μ (BoseGases.a v)) N x‖
        ≤ D1 / ((N : ℝ) + 1) ^ 1 := hD1 _ hℓ N x
      _ = D1 * ((N : ℝ) + 1)⁻¹ := by rw [pow_one, div_eq_mul_inv]
      _ ≤ D1 * Work.BoseFixR.dil v μ := h1
      _ ≤ (D1 + D2) * Work.BoseFixR.dil v μ := by
          have hle' : D1 ≤ D1 + D2 := le_add_of_nonneg_right hD20
          linarith [mul_le_mul_of_nonneg_right hle' ht.le]
  · intro x
    have h1 : D2 * ((N : ℝ) + 1)⁻¹ ≤ D2 * Work.BoseFixR.dil v μ :=
      mul_le_mul_of_nonneg_left hkey hD20
    calc ‖thetaTail (Work.BoseBox.sideAt μ (BoseGases.a v)) N x‖
        ≤ D2 / ((N : ℝ) + 1) ^ 1 := hD2 _ hℓ N x
      _ = D2 * ((N : ℝ) + 1)⁻¹ := by rw [pow_one, div_eq_mul_inv]
      _ ≤ D2 * Work.BoseFixR.dil v μ := h1
      _ ≤ (D1 + D2) * Work.BoseFixR.dil v μ := by
          have hle' : D2 ≤ D1 + D2 := le_add_of_nonneg_left hD10
          linarith [mul_le_mul_of_nonneg_right hle' ht.le]

end Work.BoseBoxFock
