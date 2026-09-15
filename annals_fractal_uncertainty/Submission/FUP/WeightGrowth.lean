import Submission.FUP.WeightReg
import Submission.Commons.Measure.Real.integral_log_rpow_decay
import Submission.Commons.Measure.EuclideanSpace.porous_line_measure_annulus

open FractalUncertainty MeasureTheory FourierTransform Metric
open scoped ENNReal BigOperators
open Submission.FUP

set_option autoImplicit false
attribute [local instance] Classical.propDecidable
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# The growth condition for the §6.1 weight `ω`

We prove that `ω` satisfies the growth condition `∫_0^∞ G*(r)/(1+r²) dr < ∞` of the
higher-dimensional Beurling–Malliavin theorem, where `G*(r) = sup_{‖x‖=r} ∫_{1/2}^2 |ω(t x)| dt`.
The estimate uses the line-porosity of `Y` (through the one-dimensional measure bound for
porous sets) and the elementary integral `Commons.Measure.Real.integral_log_rpow_decay`.
-/

section Basic

/-- `|ω_k| = (2^k/k^α)·Ψ_k` (both factors are nonnegative). -/
lemma abs_omegaK (s α : ℝ) (k : ℕ) (Y : Set ℝᵈ) (x : ℝᵈ) :
    |omegaK s α k Y x| =
      coefK α k * psiK (Rk k) (Wk s k) (Wk_pos s k) (Nk s k) Y (Ak k) x := by
  rw [omegaK_apply, abs_mul, abs_neg, abs_of_nonneg (coefK_nonneg α k),
    abs_of_nonneg (psiK_nonneg (Rk k) (Wk s k) (Wk_pos s k) (Nk s k) Y (Ak k) x)]

/-- `|ω| = Σ_k |ω_k|`, because every `ω_k ≤ 0`. -/
lemma abs_omega (s α : ℝ) (k₀ K : ℕ) (Y : Set ℝᵈ) (x : ℝᵈ) :
    |omega s α k₀ K Y x| = ∑ k ∈ Finset.Icc k₀ K, |omegaK s α k Y x| := by
  rw [abs_of_nonpos (omega_nonpos s α k₀ K Y x)]
  have h : omega s α k₀ K Y x = ∑ k ∈ Finset.Icc k₀ K, omegaK s α k Y x := rfl
  rw [h, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun k _ => by rw [abs_of_nonpos (omegaK_nonpos s α k Y x)])

/-- `ω_k` vanishes outside the annulus `{2^{k-1} ≤ ‖x‖ ≤ 2^{k+2}}`. -/
lemma omegaK_eq_zero_of_norm_gt {s : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hW : Real.sqrt (d:ℝ) * Wk s k ≤ (2:ℝ)^(k-1)) {α : ℝ} (Y : Set ℝᵈ) {x : ℝᵈ}
    (hx : (2:ℝ)^(k+2) < ‖x‖) : omegaK s α k Y x = 0 := by
  refine omegaK_eq_zero_of_notMem_yCover (s := s) (α := α) (Y := Y) ?_
  intro hmem
  have h := yCover_subset_annulusRk (k := k) hk hW hmem
  rw [mem_annulus] at h
  linarith [h.2]

/-- `ω_k` vanishes on the ray `{t • x}` outside a bounded interval. -/
lemma omegaK_ray_support {s : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hW : Real.sqrt (d:ℝ) * Wk s k ≤ (2:ℝ)^(k-1)) {α : ℝ} (Y : Set ℝᵈ) {x : ℝᵈ}
    {t : ℝ} (ht : (2:ℝ)^(k+2) < ‖t • x‖) : omegaK s α k Y (t • x) = 0 :=
  omegaK_eq_zero_of_norm_gt hk hW Y ht

end Basic

section Ray

/-- **Pointwise bound along a ray.**  `|ω_k(t•x)| ≤ (2^k/k^α)·3^d · 1_{t•x ∈ 𝕐_k}`. -/
lemma abs_omegaK_le_indicator (s α : ℝ) (k : ℕ) (Y : Set ℝᵈ) (x : ℝᵈ) (t : ℝ) :
    |omegaK s α k Y (t • x)| ≤
      coefK α k * (3:ℝ)^d *
        (yCover (Rk k) (Wk s k) (Nk s k) Y (Ak k)).indicator (fun _ => (1:ℝ)) (t • x) := by
  rw [abs_omegaK]
  by_cases hp : t • x ∈ yCover (Rk k) (Wk s k) (Nk s k) Y (Ak k)
  · rw [Set.indicator_of_mem hp, mul_one]
    have h3 : psiK (Rk k) (Wk s k) (Wk_pos s k) (Nk s k) Y (Ak k) (t • x) ≤ (3:ℝ)^d :=
      psiK_le (Rk k) (Wk s k) (Wk_pos s k) (Nk s k) Y (Ak k) (t • x)
    nlinarith [coefK_nonneg α k, h3]
  · rw [Set.indicator_of_notMem hp, mul_zero]
    rw [psiK_eq_zero_of_notMem_yCover _ _ _ _ _ _ hp, mul_zero]

/-- **Lintegral bound along a ray.** -/
lemma omegaK_ray_lintegral_le (s α : ℝ) (j : ℕ) (Y : Set ℝᵈ) (x : ℝᵈ) :
    ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal |omegaK s α j Y (t • x)| ≤
      ENNReal.ofReal (coefK α j * (3:ℝ)^d) *
        volume (Set.Ioi (0:ℝ) ∩ (fun t : ℝ => t • x) ⁻¹'
          yCover (Rk j) (Wk s j) (Nk s j) Y (Ak j)) := by
  classical
  have hPm : MeasurableSet ((fun t : ℝ => t • x) ⁻¹'
      yCover (Rk j) (Wk s j) (Nk s j) Y (Ak j)) :=
    (isClosed_yCover (Rk j) (Wk s j) (Nk s j) Y (Ak j)).measurableSet.preimage
      (continuous_id.smul continuous_const).measurable
  have hSP : MeasurableSet (Set.Ioi (0:ℝ) ∩ (fun t : ℝ => t • x) ⁻¹'
      yCover (Rk j) (Wk s j) (Nk s j) Y (Ak j)) := measurableSet_Ioi.inter hPm
  have hpoint : ∀ t : ℝ, (Set.Ioi (0:ℝ)).indicator
        (fun t => ENNReal.ofReal |omegaK s α j Y (t • x)|) t
      ≤ ENNReal.ofReal (coefK α j * (3:ℝ)^d) *
        (Set.Ioi (0:ℝ) ∩ (fun t : ℝ => t • x) ⁻¹'
          yCover (Rk j) (Wk s j) (Nk s j) Y (Ak j)).indicator (fun _ => (1:ℝ≥0∞)) t := by
    intro t
    by_cases ht : t ∈ Set.Ioi (0:ℝ)
    · rw [Set.indicator_of_mem ht]
      by_cases hp : t • x ∈ yCover (Rk j) (Wk s j) (Nk s j) Y (Ak j)
      · have hmem : t ∈ Set.Ioi (0:ℝ) ∩ (fun t : ℝ => t • x) ⁻¹'
            yCover (Rk j) (Wk s j) (Nk s j) Y (Ak j) := ⟨ht, hp⟩
        rw [Set.indicator_of_mem hmem, mul_one]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [abs_omegaK]
        have h3 : psiK (Rk j) (Wk s j) (Wk_pos s j) (Nk s j) Y (Ak j) (t • x) ≤ (3:ℝ)^d :=
          psiK_le (Rk j) (Wk s j) (Wk_pos s j) (Nk s j) Y (Ak j) (t • x)
        nlinarith [coefK_nonneg α j, h3]
      · rw [Set.indicator_of_notMem (fun h => hp h.2), mul_zero]
        rw [abs_omegaK, psiK_eq_zero_of_notMem_yCover _ _ _ _ _ _ hp, mul_zero]
        simp
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem (fun h => ht h.1), mul_zero]
  calc ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal |omegaK s α j Y (t • x)|
      = ∫⁻ t, (Set.Ioi (0:ℝ)).indicator
          (fun t => ENNReal.ofReal |omegaK s α j Y (t • x)|) t :=
        (MeasureTheory.lintegral_indicator measurableSet_Ioi _).symm
    _ ≤ ∫⁻ t, ENNReal.ofReal (coefK α j * (3:ℝ)^d) *
          (Set.Ioi (0:ℝ) ∩ (fun t : ℝ => t • x) ⁻¹'
            yCover (Rk j) (Wk s j) (Nk s j) Y (Ak j)).indicator (fun _ => (1:ℝ≥0∞)) t :=
        lintegral_mono hpoint
    _ = ENNReal.ofReal (coefK α j * (3:ℝ)^d) *
          ∫⁻ t, (Set.Ioi (0:ℝ) ∩ (fun t : ℝ => t • x) ⁻¹'
            yCover (Rk j) (Wk s j) (Nk s j) Y (Ak j)).indicator (fun _ => (1:ℝ≥0∞)) t :=
        MeasureTheory.lintegral_const_mul _ (measurable_const.indicator hSP)
    _ = ENNReal.ofReal (coefK α j * (3:ℝ)^d) *
          volume (Set.Ioi (0:ℝ) ∩ (fun t : ℝ => t • x) ⁻¹'
            yCover (Rk j) (Wk s j) (Nk s j) Y (Ak j)) := by
        congr 1
        exact lintegral_indicator_one hSP

/-- **Integral over a ray.** -/
lemma omegaK_ray_integral_le (s α : ℝ) (j : ℕ) (Y : Set ℝᵈ) (x : ℝᵈ) {B : ℝ} (hB0 : 0 ≤ B)
    (hmeas : volume ((fun t : ℝ => t • x) ⁻¹'
        yCover (Rk j) (Wk s j) (Nk s j) Y (Ak j)) ≤ ENNReal.ofReal B) :
    ∫ t in Set.Ioi (0:ℝ), |omegaK s α j Y (t • x)| ≤ coefK α j * (3:ℝ)^d * B := by
  set P : Set ℝ := (fun t : ℝ => t • x) ⁻¹' yCover (Rk j) (Wk s j) (Nk s j) Y (Ak j) with hP
  have hcont : Continuous (fun t : ℝ => omegaK s α j Y (t • x)) :=
    (omegaK_contDiff s α j Y).continuous.comp (continuous_id.smul continuous_const)
  have h1 : ∫ t in Set.Ioi (0:ℝ), |omegaK s α j Y (t • x)|
      = (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal |omegaK s α j Y (t • x)|).toReal :=
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun t => abs_nonneg _) hcont.abs.aestronglyMeasurable
  have hlin := omegaK_ray_lintegral_le s α j Y x
  have hc0 : (0:ℝ) ≤ coefK α j * (3:ℝ)^d := mul_nonneg (coefK_nonneg α j) (by positivity)
  have hfin : volume (Set.Ioi (0:ℝ) ∩ P) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (le_trans (measure_mono Set.inter_subset_right) (by simpa [hP] using hmeas))
  rw [h1]
  have hstep : (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal |omegaK s α j Y (t • x)|).toReal
      ≤ (ENNReal.ofReal (coefK α j * (3:ℝ)^d) * volume (Set.Ioi (0:ℝ) ∩ P)).toReal := by
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) ?_
    simpa [hP] using hlin
  refine hstep.trans ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0]
  have hmono : (volume (Set.Ioi (0:ℝ) ∩ P)).toReal ≤ B := by
    refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (le_trans (measure_mono Set.inter_subset_right) (by simpa [hP] using hmeas))) ?_
    exact le_of_eq (ENNReal.toReal_ofReal hB0)
  exact mul_le_mul_of_nonneg_left hmono hc0

end Ray

section MeasureBound

/-- Neighbourhoods are monotone in the radius. -/
lemma nbhd_mono {Y : Set ℝᵈ} {r r' : ℝ} (h : r ≤ r') : nbhd Y r ⊆ nbhd Y r' := by
  refine closure_mono ?_
  rintro z ⟨y, hy, w, hw, rfl⟩
  exact ⟨y, hy, w, closedBall_subset_closedBall h hw, rfl⟩

/-- `(A/(j:ℝ)^s)^γ = A^γ · j^{-(sγ)}` for `A ≥ 0`, `j ≥ 1`. -/
lemma div_pow_mul_rpow_neg {A s γ : ℝ} {j : ℕ} (hA : 0 ≤ A) (hj : 1 ≤ j) :
    (A / (j : ℝ) ^ s) ^ γ = A ^ γ * (j : ℝ) ^ (-(s * γ)) := by
  have hjpos : (0:ℝ) < (j:ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hjs : (0:ℝ) < (j:ℝ)^s := Real.rpow_pos_of_pos hjpos s
  rw [Real.div_rpow hA hjs.le, ← Real.rpow_mul hjpos.le, Real.rpow_neg hjpos.le,
    div_eq_mul_inv]

/-- **One-dimensional measure of `𝕐_j` on a line.**  If `Y` is `ν`-porous on lines from `μ` to
`h⁻¹` and `Y ⊆ [-12h⁻¹, 12h⁻¹]^d`, then the set `𝕐_j` of §6.1 meets every unit-speed line in
one-dimensional measure at most `C·2^j·j^{-sγ}`. -/
lemma yCover_measure_le' {ν μ s h γ C₀ : ℝ} {j : ℕ} {Y : Set ℝᵈ}
    (hν : 0 < ν) (hγ : 0 < γ) (hC₀ : 0 < C₀)
    (hbd : ∀ (α₀ α₁ a b : ℝ) (Z : Set ℝᵈ),
        0 < α₀ → 0 < α₁ → 0 < a → a ≤ b → MeasurableSet Z →
        (∀ R ∈ Set.Ioo α₀ α₁, ∀ (y₁ y₂ : ℝᵈ), dist y₁ y₂ = R →
          ∃ x ∈ segment ℝ y₁ y₂, closedBall x (ν / 2 * R) ∩ Z = ∅) →
        Z ⊆ {x : ℝᵈ | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} →
        ∀ (p v : ℝᵈ), ‖v‖ = 1 →
          (volume ((fun t : ℝ => p + t • v) ⁻¹' Z) : ℝ≥0∞) ≤
            ENNReal.ofReal (C₀ * b * (α₀ / min (α₁ / 2) (2 * b)) ^ γ))
    (hμ : 0 < μ) (hd : 1 ≤ d) (hs : 0 < s) (hh : 0 < h) (hj : 1 ≤ j)
    (hY : PorousOnLines ν μ h⁻¹ Y) (hYbox : Y ⊆ cube (-(12 * h⁻¹)) (12 * h⁻¹))
    (hμW : μ ≤ 4 * (2 * Real.sqrt (d:ℝ) * Wk s j) / ν)
    (hWs : 2 * Real.sqrt (d:ℝ) * Wk s j ≤ (2:ℝ)^(j-1)) :
    ∀ (p v : ℝᵈ), ‖v‖ = 1 →
      (volume ((fun t : ℝ => p + t • v) ⁻¹' yCover (Rk j) (Wk s j) (Nk s j) Y (Ak j)) : ℝ≥0∞) ≤
        ENNReal.ofReal ((4 * C₀ * ((Real.sqrt (d:ℝ) / ν)^γ + (192 * (d:ℝ) / ν)^γ)) *
          (2:ℝ)^j * (j:ℝ)^(-(s*γ))) := by
  have hsqd : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < d))
  have hjpos : (0:ℝ) < (j:ℝ) := by exact_mod_cast (by omega : 0 < j)
  set r : ℝ := 2 * Real.sqrt (d:ℝ) * Wk s j with hrdef
  have hrpos : 0 < r := by rw [hrdef]; exact mul_pos (mul_pos (by norm_num) hsqd) (Wk_pos s j)
  have hrnn : 0 ≤ r := le_of_lt hrpos
  have hα₀ : 0 < 4 * r / ν := by positivity
  have hα₁ : 0 < h⁻¹ := inv_pos.mpr hh
  have hbpos : 0 < (2:ℝ)^(j+2) := pow_pos (by norm_num) _
  have hamin : (2:ℝ)^(j-1) ≤ (2:ℝ)^(j+2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hj1 : 1 ≤ j := hj
  have hZpor : PorousOnLines (ν / 2) (4 * r / ν) h⁻¹ (nbhd (Y ∩ Ak j) r) := by
    refine PorousOnLines_nbhd hμ hν ?_ (PorousOnLines.mono_set hY Set.inter_subset_left)
    rw [hrdef]
    exact hμW
  have hZsub : nbhd (Y ∩ Ak j) r ⊆ annulus ((2:ℝ)^(j-1)) ((2:ℝ)^(j+2)) := by
    refine closure_minimal ?_ (isClosed_annulus _ _)
    rintro z ⟨y, hy, w, hw, rfl⟩
    have hy' : y ∈ annulus ((2:ℝ)^j) ((2:ℝ)^(j+1)) := hy.2
    have hw' : ‖w‖ ≤ r := by
      simpa [dist_eq_norm, sub_zero] using (Metric.mem_closedBall.mp hw : dist w 0 ≤ r)
    rw [mem_annulus] at hy' ⊢
    have h2j : (2:ℝ)^j = 2 * (2:ℝ)^(j-1) := by
      calc (2:ℝ)^j = (2:ℝ)^((j-1)+1) := by rw [Nat.sub_add_cancel hj1]
        _ = (2:ℝ)^(j-1) * 2 := by rw [pow_succ]
        _ = 2 * (2:ℝ)^(j-1) := by ring
    have h2j1 : (2:ℝ)^(j+1) = 4 * (2:ℝ)^(j-1) := by
      rw [pow_succ, h2j]; ring
    have h2j2 : (2:ℝ)^(j+2) = 8 * (2:ℝ)^(j-1) := by
      have e : (2:ℝ)^(j+2) = (2:ℝ)^(j+1) * 2 := by
        rw [show j + 2 = (j+1) + 1 by omega, pow_succ]
      rw [e, h2j1]; ring
    have hx : 0 < (2:ℝ)^(j-1) := pow_pos (by norm_num) _
    constructor
    · have hnorm : ‖y‖ - ‖w‖ ≤ ‖y + w‖ := by
        have h := norm_add_le (y + w) (-w)
        rw [add_neg_cancel_right, norm_neg] at h
        linarith
      have h1 : (2:ℝ)^j - r ≤ ‖y + w‖ := by linarith [hy'.1, hw', hnorm]
      have h2 : (2:ℝ)^(j-1) ≤ (2:ℝ)^j - r := by linarith [hWs, h2j]
      linarith
    · have h1 : ‖y + w‖ ≤ ‖y‖ + ‖w‖ := norm_add_le y w
      have h2 : (2:ℝ)^(j+1) + r ≤ (2:ℝ)^(j+2) := by
        have h3 : r ≤ (2:ℝ)^(j-1) := by rw [hrdef]; exact hWs
        linarith [h2j1, h2j2, hx, h3]
      linarith
  have hsub : yCover (Rk j) (Wk s j) (Nk s j) Y (Ak j) ⊆ nbhd (Y ∩ Ak j) r := by
    refine (yCover_subset_nbhd (Rk j) (Wk s j) (Nk s j) Y (Ak j)
      (le_of_lt (Wk_pos s j))).trans (nbhd_mono ?_)
    rw [hrdef]
    nlinarith [Real.sqrt_nonneg (d:ℝ), le_of_lt (Wk_pos s j)]
  have hvolZ : ∀ (p v : ℝᵈ), ‖v‖ = 1 →
      (volume ((fun t : ℝ => p + t • v) ⁻¹' nbhd (Y ∩ Ak j) r) : ℝ≥0∞) ≤
        ENNReal.ofReal (C₀ * (2:ℝ)^(j+2) *
          ((4 * r / ν) / min (h⁻¹ / 2) (2 * (2:ℝ)^(j+2)))^γ) :=
    fun p v hv => hbd (4 * r / ν) h⁻¹ ((2:ℝ)^(j-1)) ((2:ℝ)^(j+2)) (nbhd (Y ∩ Ak j) r)
      hα₀ hα₁ (show (0:ℝ) < (2:ℝ)^(j-1) by positivity) hamin (measurableSet_nbhd _ _)
      hZpor hZsub p v hv
  intro p v hv
  rcases eq_or_ne (yCover (Rk j) (Wk s j) (Nk s j) Y (Ak j)) ∅ with hemp | hne
  · rw [hemp, Set.preimage_empty, measure_empty]
    exact bot_le
  · have hne' : (yCover (Rk j) (Wk s j) (Nk s j) Y (Ak j)).Nonempty := Set.nonempty_iff_ne_empty.mpr hne
    have h2j_le : (2:ℝ)^j ≤ 12 * Real.sqrt (d:ℝ) * h⁻¹ := by
      rcases hne' with ⟨x, jj, ⟨y, hybox, hyY, hyA⟩, hxbox⟩
      have h1 : (2:ℝ)^j ≤ ‖y‖ := (mem_Ak.mp hyA).1
      have h2 : ‖y‖ ≤ Real.sqrt (d:ℝ) * (12 * h⁻¹) :=
        norm_le_of_mem_cube_center (by positivity) (hYbox hyY)
      linarith
    refine (measure_mono (Set.preimage_mono hsub)).trans ((hvolZ p v hv).trans ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    have hj1 : 1 ≤ j := hj
    rcases le_total (2 * (2:ℝ)^(j+2)) (h⁻¹ / 2) with hcase | hcase
    · have hmin : min (h⁻¹ / 2) (2 * (2:ℝ)^(j+2)) = 2 * (2:ℝ)^(j+2) :=
        min_eq_right hcase
      have ht : (4 * r / ν) / min (h⁻¹ / 2) (2 * (2:ℝ)^(j+2)) =
          (Real.sqrt (d:ℝ) / ν) / (j:ℝ)^s := by
        rw [hmin, hrdef, Wk_eq s hj1]
        field_simp
        ring
      have hp : ((4 * r / ν) / min (h⁻¹ / 2) (2 * (2:ℝ)^(j+2)))^γ =
          (Real.sqrt (d:ℝ) / ν)^γ * (j:ℝ)^(-(s*γ)) := by
        rw [ht]
        exact div_pow_mul_rpow_neg (div_nonneg (Real.sqrt_nonneg _) (le_of_lt hν)) hj1
      have h2j4 : (2:ℝ)^(j+2) = 4 * (2:ℝ)^j := by
        rw [show j + 2 = j + 2 from rfl, pow_add]; ring
      have hle : 4 * C₀ * (Real.sqrt (d:ℝ) / ν)^γ ≤
          4 * C₀ * ((Real.sqrt (d:ℝ) / ν)^γ + (192 * (d:ℝ) / ν)^γ) := by
        have h2 : 0 ≤ (192 * (d:ℝ) / ν)^γ :=
          Real.rpow_nonneg (div_nonneg (by positivity) (le_of_lt hν)) γ
        have h1 : 0 ≤ (Real.sqrt (d:ℝ) / ν)^γ :=
          Real.rpow_nonneg (div_nonneg (Real.sqrt_nonneg _) (le_of_lt hν)) γ
        nlinarith [hC₀.le]
      have hnonneg : 0 ≤ (2:ℝ)^j * (j:ℝ)^(-(s*γ)) :=
        mul_nonneg (pow_nonneg (by norm_num) _) (Real.rpow_nonneg (le_of_lt hjpos) _)
      calc C₀ * (2:ℝ)^(j+2) * ((4 * r / ν) / min (h⁻¹ / 2) (2 * (2:ℝ)^(j+2)))^γ
          = (4 * C₀ * (Real.sqrt (d:ℝ) / ν)^γ) * ((2:ℝ)^j * (j:ℝ)^(-(s*γ))) := by
            rw [hp, h2j4]; ring
        _ ≤ (4 * C₀ * ((Real.sqrt (d:ℝ) / ν)^γ + (192 * (d:ℝ) / ν)^γ)) *
              ((2:ℝ)^j * (j:ℝ)^(-(s*γ))) := mul_le_mul_of_nonneg_right hle hnonneg
        _ = (4 * C₀ * ((Real.sqrt (d:ℝ) / ν)^γ + (192 * (d:ℝ) / ν)^γ)) *
              (2:ℝ)^j * (j:ℝ)^(-(s*γ)) := by ring
    · have hmin : min (h⁻¹ / 2) (2 * (2:ℝ)^(j+2)) = h⁻¹ / 2 := min_eq_left hcase
      have ht : (4 * r / ν) / min (h⁻¹ / 2) (2 * (2:ℝ)^(j+2)) =
          (16 * Real.sqrt (d:ℝ) * (2:ℝ)^j * h / ν) / (j:ℝ)^s := by
        rw [hmin, hrdef, Wk_eq s hj1]
        field_simp
        ring
      have hA : 16 * Real.sqrt (d:ℝ) * (2:ℝ)^j * h / ν ≤ 192 * (d:ℝ) / ν := by
        rw [div_le_div_iff_of_pos_right hν]
        have hstep : 16 * Real.sqrt (d:ℝ) * (2:ℝ)^j * h ≤ 16 * Real.sqrt (d:ℝ) * (12 * Real.sqrt (d:ℝ) * h⁻¹) * h :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2j_le (by positivity)) (le_of_lt hh)
        have hsimp : 16 * Real.sqrt (d:ℝ) * (12 * Real.sqrt (d:ℝ) * h⁻¹) * h = 192 * (d:ℝ) := by
          have hhinv : h⁻¹ * h = 1 := inv_mul_cancel₀ (ne_of_gt hh)
          have hsq : Real.sqrt (d:ℝ) * Real.sqrt (d:ℝ) = (d:ℝ) :=
            Real.mul_self_sqrt (by positivity)
          calc 16 * Real.sqrt (d:ℝ) * (12 * Real.sqrt (d:ℝ) * h⁻¹) * h
              = 192 * (Real.sqrt (d:ℝ) * Real.sqrt (d:ℝ)) * (h⁻¹ * h) := by ring
            _ = 192 * (d:ℝ) := by rw [hsq, hhinv]; ring
        linarith
      have hp : ((4 * r / ν) / min (h⁻¹ / 2) (2 * (2:ℝ)^(j+2)))^γ =
          (16 * Real.sqrt (d:ℝ) * (2:ℝ)^j * h / ν)^γ * (j:ℝ)^(-(s*γ)) := by
        rw [ht]
        exact div_pow_mul_rpow_neg (by positivity) hj1
      have hAγ : (16 * Real.sqrt (d:ℝ) * (2:ℝ)^j * h / ν)^γ ≤ (192 * (d:ℝ) / ν)^γ :=
        Real.rpow_le_rpow (by positivity) hA (le_of_lt hγ)
      have h2j4 : (2:ℝ)^(j+2) = 4 * (2:ℝ)^j := by
        rw [show j + 2 = j + 2 from rfl, pow_add]; ring
      have hle : 4 * C₀ * (192 * (d:ℝ) / ν)^γ ≤
          4 * C₀ * ((Real.sqrt (d:ℝ) / ν)^γ + (192 * (d:ℝ) / ν)^γ) := by
        have h2 : 0 ≤ (Real.sqrt (d:ℝ) / ν)^γ :=
          Real.rpow_nonneg (div_nonneg (Real.sqrt_nonneg _) (le_of_lt hν)) γ
        have h1 : 0 ≤ (192 * (d:ℝ) / ν)^γ :=
          Real.rpow_nonneg (div_nonneg (by positivity) (le_of_lt hν)) γ
        nlinarith [hC₀.le]
      have hnonneg : 0 ≤ (2:ℝ)^j * (j:ℝ)^(-(s*γ)) :=
        mul_nonneg (pow_nonneg (by norm_num) _) (Real.rpow_nonneg (le_of_lt hjpos) _)
      calc C₀ * (2:ℝ)^(j+2) * ((4 * r / ν) / min (h⁻¹ / 2) (2 * (2:ℝ)^(j+2)))^γ
          = C₀ * (2:ℝ)^(j+2) * (16 * Real.sqrt (d:ℝ) * (2:ℝ)^j * h / ν)^γ *
              (j:ℝ)^(-(s*γ)) := by rw [hp]; ring
        _ ≤ C₀ * (2:ℝ)^(j+2) * (192 * (d:ℝ) / ν)^γ * (j:ℝ)^(-(s*γ)) := by
            have h2 : 0 ≤ (j:ℝ)^(-(s*γ)) := Real.rpow_nonneg (le_of_lt hjpos) _
            have h3 : 0 ≤ C₀ * (2:ℝ)^(j+2) := by positivity
            have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAγ h3) h2
            linarith [this]
        _ = (4 * C₀ * (192 * (d:ℝ) / ν)^γ) * ((2:ℝ)^j * (j:ℝ)^(-(s*γ))) := by
            rw [h2j4]; ring
        _ ≤ (4 * C₀ * ((Real.sqrt (d:ℝ) / ν)^γ + (192 * (d:ℝ) / ν)^γ)) *
              ((2:ℝ)^j * (j:ℝ)^(-(s*γ))) := mul_le_mul_of_nonneg_right hle hnonneg
        _ = (4 * C₀ * ((Real.sqrt (d:ℝ) / ν)^γ + (192 * (d:ℝ) / ν)^γ)) *
              (2:ℝ)^j * (j:ℝ)^(-(s*γ)) := by ring

/-- **One-dimensional measure of `𝕐_j` on a line.**  If `Y` is `ν`-porous on lines from `μ` to
`h⁻¹` and `Y ⊆ [-12h⁻¹, 12h⁻¹]^d`, then the set `𝕐_j` of §6.1 meets every unit-speed line in
one-dimensional measure at most `C·2^j·j^{-sγ}`. -/
lemma yCover_measure_le {ν μ s h : ℝ} {j : ℕ} {Y : Set ℝᵈ}
    (hν : 0 < ν) (hμ : 0 < μ) (hd : 1 ≤ d) (hs : 0 < s) (hh : 0 < h) (hj : 1 ≤ j)
    (hY : PorousOnLines ν μ h⁻¹ Y) (hYbox : Y ⊆ cube (-(12 * h⁻¹)) (12 * h⁻¹))
    (hμW : μ ≤ 4 * (2 * Real.sqrt (d:ℝ) * Wk s j) / ν)
    (hWs : 2 * Real.sqrt (d:ℝ) * Wk s j ≤ (2:ℝ)^(j-1)) :
    ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧ ∀ (p v : ℝᵈ), ‖v‖ = 1 →
      (volume ((fun t : ℝ => p + t • v) ⁻¹' yCover (Rk j) (Wk s j) (Nk s j) Y (Ak j)) : ℝ≥0∞) ≤
        ENNReal.ofReal (C * (2:ℝ)^j * (j:ℝ)^(-(s*γ))) := by
  obtain ⟨γ, C₀, hγ, hC₀, hbd⟩ :=
    Commons.Measure.EuclideanSpace.porous_line_measure_annulus d (ν := ν / 2) (by positivity)
  have hsqd : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < d))
  have hCpos : 0 < 4 * C₀ * ((Real.sqrt (d:ℝ) / ν)^γ + (192 * (d:ℝ) / ν)^γ) := by
    have h1 : 0 < (Real.sqrt (d:ℝ) / ν)^γ := Real.rpow_pos_of_pos (div_pos hsqd hν) γ
    have h2 : 0 < (192 * (d:ℝ) / ν)^γ :=
      Real.rpow_pos_of_pos (div_pos (mul_pos (by norm_num)
        (by exact_mod_cast (by omega : 0 < d))) hν) γ
    positivity
  exact ⟨γ, 4 * C₀ * ((Real.sqrt (d:ℝ) / ν)^γ + (192 * (d:ℝ) / ν)^γ), hγ, hCpos,
    yCover_measure_le' hν hγ hC₀ hbd hμ hd hs hh hj hY hYbox hμW hWs⟩

/-- **The ray integral of `ω_j`** with an explicit `γ` and `C₀` (the output of
`porous_line_measure_annulus`). -/
lemma omegaK_ray_bound' {ν μ s α h γ C₀ : ℝ} {j : ℕ} {Y : Set ℝᵈ}
    (hν : 0 < ν) (hγ : 0 < γ) (hC₀ : 0 < C₀)
    (hbd : ∀ (α₀ α₁ a b : ℝ) (Z : Set ℝᵈ),
        0 < α₀ → 0 < α₁ → 0 < a → a ≤ b → MeasurableSet Z →
        (∀ R ∈ Set.Ioo α₀ α₁, ∀ (y₁ y₂ : ℝᵈ), dist y₁ y₂ = R →
          ∃ x ∈ segment ℝ y₁ y₂, closedBall x (ν / 2 * R) ∩ Z = ∅) →
        Z ⊆ {x : ℝᵈ | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} →
        ∀ (p v : ℝᵈ), ‖v‖ = 1 →
          (volume ((fun t : ℝ => p + t • v) ⁻¹' Z) : ℝ≥0∞) ≤
            ENNReal.ofReal (C₀ * b * (α₀ / min (α₁ / 2) (2 * b)) ^ γ))
    (hμ : 0 < μ) (hd : 1 ≤ d) (hs : 0 < s) (hh : 0 < h) (hj : 1 ≤ j)
    (hY : PorousOnLines ν μ h⁻¹ Y) (hYbox : Y ⊆ cube (-(12 * h⁻¹)) (12 * h⁻¹))
    (hμW : μ ≤ 4 * (2 * Real.sqrt (d:ℝ) * Wk s j) / ν)
    (hWs : 2 * Real.sqrt (d:ℝ) * Wk s j ≤ (2:ℝ)^(j-1)) :
    ∀ (v : ℝᵈ), ‖v‖ = 1 →
      ∫ t in Set.Ioi (0:ℝ), |omegaK s α j Y (t • v)| ≤
        (4 * C₀ * ((Real.sqrt (d:ℝ) / ν)^γ + (192 * (d:ℝ) / ν)^γ) * (3:ℝ)^d) *
          (4:ℝ)^j * (j:ℝ)^(-(α + s*γ)) := by
  have hmeas := yCover_measure_le' hν hγ hC₀ hbd hμ hd hs hh hj hY hYbox hμW hWs
  set C₀' : ℝ := 4 * C₀ * ((Real.sqrt (d:ℝ) / ν)^γ + (192 * (d:ℝ) / ν)^γ) with hC₀'
  have hjpos : (0:ℝ) < (j:ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hBx : 0 ≤ C₀' * (2:ℝ)^j * (j:ℝ)^(-(s*γ)) := by
    have : 0 ≤ (j:ℝ)^(-(s*γ)) := Real.rpow_nonneg (le_of_lt hjpos) _
    positivity
  have h4j : (4:ℝ)^j = (2:ℝ)^j * (2:ℝ)^j := by
    have h4 : (4:ℝ) = (2:ℝ)^2 := by norm_num
    rw [h4, ← pow_mul, show 2 * j = j + j by ring, pow_add]
  have hrpow : (j:ℝ)^(-α) * (j:ℝ)^(-(s*γ)) = (j:ℝ)^(-(α + s*γ)) := by
    rw [← Real.rpow_add hjpos]
    ring_nf
  have hcoef : coefK α j = (2:ℝ)^j / (j:ℝ)^α := by
    rw [coefK, max_eq_left (by exact_mod_cast hj)]
  intro v hv
  have hme : volume ((fun t : ℝ => t • v) ⁻¹' yCover (Rk j) (Wk s j) (Nk s j) Y (Ak j))
      ≤ ENNReal.ofReal (C₀' * (2:ℝ)^j * (j:ℝ)^(-(s*γ))) := by
    simpa [hC₀'] using hmeas 0 v hv
  refine (omegaK_ray_integral_le s α j Y v hBx hme).trans ?_
  rw [hcoef]
  refine le_of_eq ?_
  calc (2:ℝ)^j / (j:ℝ)^α * (3:ℝ)^d * (C₀' * (2:ℝ)^j * (j:ℝ)^(-(s*γ)))
      = C₀' * (3:ℝ)^d * ((4:ℝ)^j * (j:ℝ)^(-(α + s*γ))) := by
        rw [h4j, ← hrpow, div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hjpos)]
        ring
    _ = C₀' * (3:ℝ)^d * (4:ℝ)^j * (j:ℝ)^(-(α + s*γ)) := by ring

/-- **The ray integral of `ω_j`.**  Under the hypotheses of `yCover_measure_le`, for every unit
vector `v` the integral of `|ω_j|` along the ray `t ↦ t v` is at most
`C·4^j·j^{-(α+sγ)}`. -/
lemma omegaK_ray_bound {ν μ s α h : ℝ} {j : ℕ} {Y : Set ℝᵈ}
    (hν : 0 < ν) (hμ : 0 < μ) (hd : 1 ≤ d) (hs : 0 < s) (hh : 0 < h) (hj : 1 ≤ j)
    (hY : PorousOnLines ν μ h⁻¹ Y) (hYbox : Y ⊆ cube (-(12 * h⁻¹)) (12 * h⁻¹))
    (hμW : μ ≤ 4 * (2 * Real.sqrt (d:ℝ) * Wk s j) / ν)
    (hWs : 2 * Real.sqrt (d:ℝ) * Wk s j ≤ (2:ℝ)^(j-1)) :
    ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧ ∀ (v : ℝᵈ), ‖v‖ = 1 →
      ∫ t in Set.Ioi (0:ℝ), |omegaK s α j Y (t • v)| ≤
        C * (4:ℝ)^j * (j:ℝ)^(-(α + s*γ)) := by
  obtain ⟨γ, C₀, hγ, hC₀, hbd⟩ :=
    Commons.Measure.EuclideanSpace.porous_line_measure_annulus d (ν := ν / 2) (by positivity)
  refine ⟨γ, 4 * C₀ * ((Real.sqrt (d:ℝ) / ν)^γ + (192 * (d:ℝ) / ν)^γ) * (3:ℝ)^d, hγ,
    by positivity, ?_⟩
  exact omegaK_ray_bound' hν hγ hC₀ hbd hμ hd hs hh hj hY hYbox hμW hWs
section IntervalBound

/-- **Set-integral version of the line bound.**  For any measurable `S ⊆ ℝ` the integral of
`|ω_j|` along `t ↦ t x` over `S` is at most `coefK α j · 3^d` times the measure of
`S ∩ {t : t x ∈ 𝕐_j}`. -/
lemma omegaK_set_integral_le (s α : ℝ) (j : ℕ) (Y : Set ℝᵈ) (x : ℝᵈ) {S : Set ℝ}
    (hS : MeasurableSet S) {B : ℝ} (hB0 : 0 ≤ B)
    (hmeas : volume (S ∩ (fun t : ℝ => t • x) ⁻¹'
      yCover (Rk j) (Wk s j) (Nk s j) Y (Ak j)) ≤ ENNReal.ofReal B) :
    ∫ t in S, |omegaK s α j Y (t • x)| ≤ coefK α j * (3:ℝ)^d * B := by
  classical
  set P : Set ℝ := (fun t : ℝ => t • x) ⁻¹' yCover (Rk j) (Wk s j) (Nk s j) Y (Ak j) with hP
  have hPm : MeasurableSet P :=
    (isClosed_yCover (Rk j) (Wk s j) (Nk s j) Y (Ak j)).measurableSet.preimage
      (continuous_id.smul continuous_const).measurable
  have hSPm : MeasurableSet (S ∩ P) := hS.inter hPm
  have hcont : Continuous (fun t : ℝ => omegaK s α j Y (t • x)) :=
    (omegaK_contDiff s α j Y).continuous.comp (continuous_id.smul continuous_const)
  have hpoint : ∀ t : ℝ, S.indicator
        (fun t => ENNReal.ofReal |omegaK s α j Y (t • x)|) t
      ≤ ENNReal.ofReal (coefK α j * (3:ℝ)^d) *
        (S ∩ P).indicator (fun _ => (1:ℝ≥0∞)) t := by
    intro t
    by_cases ht : t ∈ S
    · rw [Set.indicator_of_mem ht]
      by_cases hp : t ∈ P
      · have hmem : t ∈ S ∩ P := ⟨ht, hp⟩
        rw [Set.indicator_of_mem hmem, mul_one]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [abs_omegaK]
        have h3 : psiK (Rk j) (Wk s j) (Wk_pos s j) (Nk s j) Y (Ak j) (t • x) ≤ (3:ℝ)^d :=
          psiK_le (Rk j) (Wk s j) (Wk_pos s j) (Nk s j) Y (Ak j) (t • x)
        nlinarith [coefK_nonneg α j, h3]
      · rw [Set.indicator_of_notMem (fun h => hp h.2), mul_zero]
        rw [abs_omegaK, psiK_eq_zero_of_notMem_yCover _ _ _ _ _ _ hp, mul_zero]
        simp
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem (fun h => ht h.1), mul_zero]
  have hlin : ∫⁻ t in S, ENNReal.ofReal |omegaK s α j Y (t • x)| ≤
      ENNReal.ofReal (coefK α j * (3:ℝ)^d) * volume (S ∩ P) := by
    calc ∫⁻ t in S, ENNReal.ofReal |omegaK s α j Y (t • x)|
        = ∫⁻ t, S.indicator (fun t => ENNReal.ofReal |omegaK s α j Y (t • x)|) t :=
          (MeasureTheory.lintegral_indicator hS _).symm
      _ ≤ ∫⁻ t, ENNReal.ofReal (coefK α j * (3:ℝ)^d) *
            (S ∩ P).indicator (fun _ => (1:ℝ≥0∞)) t := lintegral_mono hpoint
      _ = ENNReal.ofReal (coefK α j * (3:ℝ)^d) *
            ∫⁻ t, (S ∩ P).indicator (fun _ => (1:ℝ≥0∞)) t :=
          MeasureTheory.lintegral_const_mul _ (measurable_const.indicator hSPm)
      _ = ENNReal.ofReal (coefK α j * (3:ℝ)^d) * volume (S ∩ P) := by
          congr 1
          exact lintegral_indicator_one hSPm
  have h1 : ∫ t in S, |omegaK s α j Y (t • x)|
      = (∫⁻ t in S, ENNReal.ofReal |omegaK s α j Y (t • x)|).toReal :=
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun t => abs_nonneg _) hcont.abs.aestronglyMeasurable
  have hc0 : (0:ℝ) ≤ coefK α j * (3:ℝ)^d := mul_nonneg (coefK_nonneg α j) (by positivity)
  have hfin : volume (S ∩ P) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (by simpa [hP] using hmeas)
  rw [h1]
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hlin).trans ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0]
  have hmono : (volume (S ∩ P)).toReal ≤ B :=
    le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top (by simpa [hP] using hmeas))
      (le_of_eq (ENNReal.toReal_ofReal hB0))
  exact mul_le_mul_of_nonneg_left hmono hc0

/-- **Segment estimate for `ω_j`.**  If `‖x‖ = r` and the unit-speed line through `0` in
direction `r⁻¹x` meets `𝕐_j` in measure at most `B`, then
`∫_{1/2}^{2} |ω_j(t x)| dt ≤ coefK α j · 3^d · B / r`. -/
lemma omegaK_segment_integral_le {s α : ℝ} {j : ℕ} {Y : Set ℝᵈ} {x : ℝᵈ} {r B : ℝ}
    (hr : 0 < r) (hx : ‖x‖ = r) (hB0 : 0 ≤ B)
    (hmeas : volume ((fun u : ℝ => u • (r⁻¹ • x)) ⁻¹'
      yCover (Rk j) (Wk s j) (Nk s j) Y (Ak j)) ≤ ENNReal.ofReal B) :
    ∫ t in (1/2:ℝ)..2, |omegaK s α j Y (t • x)| ≤ coefK α j * (3:ℝ)^d * (B / r) := by
  classical
  set 𝕐 : Set ℝᵈ := yCover (Rk j) (Wk s j) (Nk s j) Y (Ak j) with h𝕐
  have hrne : r ≠ 0 := ne_of_gt hr
  have hrm : (0:ℝ) < r⁻¹ := inv_pos.mpr hr
  have hset : Set.Ioc (1/2:ℝ) 2 ∩ (fun t : ℝ => t • x) ⁻¹' 𝕐 =
      (fun t : ℝ => t * r) ⁻¹' (Set.Ioc (r / 2) (2 * r) ∩ (fun u : ℝ => u • (r⁻¹ • x)) ⁻¹' 𝕐) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioc]
    have hsm : t • x = (t * r) • (r⁻¹ • x) := by
      rw [smul_smul, mul_assoc, mul_inv_cancel₀ hrne, mul_one]
    constructor
    · rintro ⟨ht, h𝕐t⟩
      exact ⟨⟨by have := mul_lt_mul_of_pos_right ht.1 hr; linarith,
        by have := mul_le_mul_of_nonneg_right ht.2 (le_of_lt hr); linarith⟩, by rwa [← hsm]⟩
    · rintro ⟨⟨h1, h2⟩, h𝕐t⟩
      exact ⟨⟨by nlinarith [h1, hr], by nlinarith [h2, hr]⟩, by rwa [hsm]⟩
  have hvol : volume (Set.Ioc (1/2:ℝ) 2 ∩ (fun t : ℝ => t • x) ⁻¹' 𝕐) ≤
      ENNReal.ofReal (B / r) := by
    rw [hset, Real.volume_preimage_mul_right hrne]
    have hmono : volume (Set.Ioc (r / 2) (2 * r) ∩ (fun u : ℝ => u • (r⁻¹ • x)) ⁻¹' 𝕐) ≤
        ENNReal.ofReal B :=
      le_trans (measure_mono Set.inter_subset_right) (by simpa [h𝕐] using hmeas)
    have habs : ENNReal.ofReal |r⁻¹| = ENNReal.ofReal r⁻¹ := by
      rw [abs_of_pos hrm]
    rw [habs]
    calc ENNReal.ofReal r⁻¹ * volume (Set.Ioc (r / 2) (2 * r) ∩ (fun u : ℝ => u • (r⁻¹ • x)) ⁻¹' 𝕐)
        ≤ ENNReal.ofReal r⁻¹ * ENNReal.ofReal B :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = ENNReal.ofReal (r⁻¹ * B) := (ENNReal.ofReal_mul (le_of_lt hrm)).symm
      _ = ENNReal.ofReal (B / r) := by rw [div_eq_mul_inv, mul_comm]
  have hle := omegaK_set_integral_le s α j Y x (S := Set.Ioc (1/2:ℝ) 2)
    measurableSet_Ioc (div_nonneg hB0 (le_of_lt hr)) hvol
  have hgoal : ∫ t in (1/2:ℝ)..2, |omegaK s α j Y (t • x)| =
      ∫ t in Set.Ioc (1/2:ℝ) 2, |omegaK s α j Y (t • x)| :=
    intervalIntegral.integral_of_le (by norm_num)
  exact hgoal.trans_le (hle.trans (le_of_eq (by rw [div_eq_mul_inv])))

end IntervalBound

section SegmentBound

/-- **The per-`j` segment bound** with explicit `γ, C₀`.  For `x ≠ 0`,
`∫_{1/2}^2 |ω_j(t x)| dt ≤ ‖x‖⁻¹ · C₂ · 4^j · j^{-(α+sγ)}` with
`C₂ = 4 C₀ ((√d/ν)^γ + (192d/ν)^γ) · 3^d`. -/
lemma omegaK_segment_bound {ν μ s α h γ C₀ : ℝ} {j : ℕ} {Y : Set ℝᵈ}
    (hν : 0 < ν) (hγ : 0 < γ) (hC₀ : 0 < C₀)
    (hbd : ∀ (α₀ α₁ a b : ℝ) (Z : Set ℝᵈ),
        0 < α₀ → 0 < α₁ → 0 < a → a ≤ b → MeasurableSet Z →
        (∀ R ∈ Set.Ioo α₀ α₁, ∀ (y₁ y₂ : ℝᵈ), dist y₁ y₂ = R →
          ∃ x ∈ segment ℝ y₁ y₂, closedBall x (ν / 2 * R) ∩ Z = ∅) →
        Z ⊆ {x : ℝᵈ | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} →
        ∀ (p v : ℝᵈ), ‖v‖ = 1 →
          (volume ((fun t : ℝ => p + t • v) ⁻¹' Z) : ℝ≥0∞) ≤
            ENNReal.ofReal (C₀ * b * (α₀ / min (α₁ / 2) (2 * b)) ^ γ))
    (hμ : 0 < μ) (hd : 1 ≤ d) (hs : 0 < s) (hh : 0 < h) (hj : 1 ≤ j)
    (hY : PorousOnLines ν μ h⁻¹ Y) (hYbox : Y ⊆ cube (-(12 * h⁻¹)) (12 * h⁻¹))
    (hμW : μ ≤ 4 * (2 * Real.sqrt (d:ℝ) * Wk s j) / ν)
    (hWs : 2 * Real.sqrt (d:ℝ) * Wk s j ≤ (2:ℝ)^(j-1)) {x : ℝᵈ} (hx : x ≠ 0) :
    ∫ t in (1/2:ℝ)..2, |omegaK s α j Y (t • x)| ≤
      (1 / ‖x‖) * ((4 * C₀ * ((Real.sqrt (d:ℝ) / ν)^γ + (192 * (d:ℝ) / ν)^γ) * (3:ℝ)^d) *
        (4:ℝ)^j * (j:ℝ)^(-(α + s*γ))) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hjpos : (0:ℝ) < (j:ℝ) := by exact_mod_cast (by omega : 0 < j)
  set C₀' : ℝ := 4 * C₀ * ((Real.sqrt (d:ℝ) / ν)^γ + (192 * (d:ℝ) / ν)^γ) with hC₀'
  have hunit : ‖(‖x‖)⁻¹ • x‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']
  have hmeas0 := yCover_measure_le' hν hγ hC₀ hbd hμ hd hs hh hj hY hYbox hμW hWs
    (0 : ℝᵈ) ((‖x‖)⁻¹ • x) hunit
  have hB0 : 0 ≤ C₀' * (2:ℝ)^j * (j:ℝ)^(-(s*γ)) := by
    have : 0 ≤ (j:ℝ)^(-(s*γ)) := Real.rpow_nonneg (le_of_lt hjpos) _
    positivity
  have hme : volume ((fun u : ℝ => u • ((‖x‖)⁻¹ • x)) ⁻¹'
      yCover (Rk j) (Wk s j) (Nk s j) Y (Ak j)) ≤
      ENNReal.ofReal (C₀' * (2:ℝ)^j * (j:ℝ)^(-(s*γ))) := by
    simpa [hC₀'] using hmeas0
  have hseg := omegaK_segment_integral_le (s := s) (α := α) (j := j) (Y := Y) (x := x)
    (r := ‖x‖) (B := C₀' * (2:ℝ)^j * (j:ℝ)^(-(s*γ))) hr rfl hB0 hme
  refine hseg.trans (le_of_eq ?_)
  have h4j : (4:ℝ)^j = (2:ℝ)^j * (2:ℝ)^j := by
    have h4 : (4:ℝ) = (2:ℝ)^2 := by norm_num
    rw [h4, ← pow_mul, show 2 * j = j + j by ring, pow_add]
  have hrpow : (j:ℝ)^(-α) * (j:ℝ)^(-(s*γ)) = (j:ℝ)^(-(α + s*γ)) := by
    rw [← Real.rpow_add hjpos]
    ring_nf
  have hcoef : coefK α j = (2:ℝ)^j / (j:ℝ)^α := by
    rw [coefK, max_eq_left (by exact_mod_cast hj)]
  rw [hcoef, h4j, ← hrpow, div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hjpos)]
  ring

end SegmentBound

section Growth

/-- The real-arithmetic core of the growth estimate: replacing `4^{k+4}` by `256 r²` and
`(k-3)^{-β}` by `(8 log 2)^β (log(2+r))^{-β}` using `2^k ≤ r < 2^{k+1}`. -/
lemma growth_algebra {β C₂ r : ℝ} {k : ℕ} (hβ : 0 < β) (hC₂ : 0 < C₂) (hr : 0 < r)
    (hk : 4 ≤ k) (hk1 : (2:ℝ)^k ≤ r) (hk2 : r < (2:ℝ)^(k+1)) :
    8 * ((1 / r) * (C₂ * (4:ℝ)^(k+4) * (((k-3:ℕ)):ℝ)^(-β)))
      ≤ (2048 * C₂ * (8 * Real.log 2)^β) * r / (Real.log (2 + r))^β := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 < Real.log (2 + r) := Real.log_pos (by linarith)
  have hKpos : 0 < (((k-3:ℕ)):ℝ) := by exact_mod_cast (by omega : 0 < k-3)
  have hKb : 0 < (((k-3:ℕ)):ℝ)^β := Real.rpow_pos_of_pos hKpos β
  have hA : 0 ≤ 8 * Real.log 2 := by positivity
  -- the logarithmic comparison
  have hlogr : Real.log (2 + r) ≤ (8 * Real.log 2) * (((k-3:ℕ)):ℝ) := by
    have h1 : (2:ℝ) + r ≤ (2:ℝ)^(k+2) := by
      have h2k : (2:ℝ)^(k+2) = 4 * (2:ℝ)^k := by
        rw [show k+2 = (k+1)+1 by omega, pow_succ, pow_succ]; ring
      have h2 : (2:ℝ) ≤ (2:ℝ)^(k+1) := by
        calc (2:ℝ) = (2:ℝ)^1 := (pow_one 2).symm
          _ ≤ (2:ℝ)^(k+1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have h3 : (2:ℝ)^(k+2) = 2 * (2:ℝ)^(k+1) := by rw [show k+2 = (k+1)+1 by omega, pow_succ]; ring
      linarith
    have h2 := Real.log_le_log (by linarith) h1
    rw [Real.log_pow] at h2
    have h4 : (((k+2 : ℕ)):ℝ) ≤ 8 * (((k-3:ℕ)):ℝ) := by
      have : k + 2 ≤ 8 * (k - 3) := by omega
      exact_mod_cast this
    have h5 : (((k+2 : ℕ)):ℝ) * Real.log 2 ≤ (8 * (((k-3:ℕ)):ℝ)) * Real.log 2 :=
      mul_le_mul_of_nonneg_right h4 hlog2.le
    linarith [h2, h5]
  -- invert the logarithmic comparison
  have hKle : (((k-3:ℕ)):ℝ)^(-β) ≤ (8 * Real.log 2)^β * (Real.log (2 + r))^(-β) := by
    have h1 : (Real.log (2+r))^β ≤ (8 * Real.log 2)^β * (((k-3:ℕ)):ℝ)^β := by
      have h2 := Real.rpow_le_rpow hL.le hlogr hβ.le
      rwa [Real.mul_rpow hA hKpos.le] at h2
    have h3 : (Real.log (2+r))^β / (((k-3:ℕ)):ℝ)^β ≤ (8 * Real.log 2)^β :=
      (div_le_iff₀ hKb).mpr h1
    have h4 : (((k-3:ℕ)):ℝ)^(-β) * (Real.log (2+r))^β ≤ (8 * Real.log 2)^β := by
      have he : (((k-3:ℕ)):ℝ)^(-β) * (Real.log (2+r))^β =
          (Real.log (2+r))^β / (((k-3:ℕ)):ℝ)^β := by
        rw [Real.rpow_neg hKpos.le, div_eq_mul_inv]; ring
      rw [he]; exact h3
    have h5 := mul_le_mul_of_nonneg_right h4 (le_of_lt (Real.rpow_pos_of_pos hL (-β)))
    have h6 : (((k-3:ℕ)):ℝ)^(-β) * (Real.log (2+r))^β * (Real.log (2+r))^(-β)
        = (((k-3:ℕ)):ℝ)^(-β) := by
      rw [mul_assoc, ← Real.rpow_add hL, add_neg_cancel, Real.rpow_zero, mul_one]
    linarith [h5, h6]
  have h4k : (4:ℝ)^k = ((2:ℝ)^k)^2 := by
    have h1 : (4:ℝ)^k = (2:ℝ)^(k*2) := by
      rw [show (4:ℝ) = (2:ℝ)^2 by norm_num, ← pow_mul, Nat.mul_comm]
    have h2 : ((2:ℝ)^k)^2 = (2:ℝ)^(k*2) := by rw [pow_mul]
    rw [h1, h2]
  have hp4 : (4:ℝ)^(k+4) = 256 * (4:ℝ)^k := by
    rw [pow_add]; norm_num; ring
  have hpow_le : (4:ℝ)^k ≤ r^2 := by
    rw [h4k]
    exact pow_le_pow_left₀ (pow_nonneg (by norm_num) k) hk1 2
  have hrinv : r^2 * r⁻¹ = r := by
    rw [sq, mul_assoc, mul_inv_cancel₀ hr.ne', mul_one]
  have h2048 : 0 ≤ (2048:ℝ) * C₂ := mul_nonneg (by norm_num) hC₂.le
  have h2048r : 0 ≤ (2048:ℝ) * C₂ * r := mul_nonneg h2048 hr.le
  have hKb0 : 0 ≤ (((k-3:ℕ)):ℝ)^(-β) := Real.rpow_nonneg hKpos.le _
  have h4kle : (4:ℝ)^k * r⁻¹ ≤ r := by
    have h2 : (4:ℝ)^k * r⁻¹ ≤ r^2 * r⁻¹ :=
      mul_le_mul_of_nonneg_right hpow_le (inv_nonneg.mpr hr.le)
    linarith [h2, hrinv]
  calc 8 * ((1 / r) * (C₂ * (4:ℝ)^(k+4) * (((k-3:ℕ)):ℝ)^(-β)))
      = 2048 * C₂ * ((4:ℝ)^k * r⁻¹) * (((k-3:ℕ)):ℝ)^(-β) := by
        rw [hp4, div_eq_mul_inv]; ring
    _ ≤ 2048 * C₂ * r * (((k-3:ℕ)):ℝ)^(-β) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4kle h2048) hKb0
    _ ≤ 2048 * C₂ * r * ((8 * Real.log 2)^β * (Real.log (2 + r))^(-β)) :=
        mul_le_mul_of_nonneg_left hKle h2048r
    _ = (2048 * C₂ * (8 * Real.log 2)^β) * r / (Real.log (2 + r))^β := by
        rw [Real.rpow_neg hL.le, div_eq_mul_inv]; ring

end Growth

section GrowthBound

/-- **The growth condition for `ω`** (pointwise form): for `‖x‖ = r`,
`∫_{1/2}^2 |ω(t x)| dt ≤ C r (log(2+r))^{-β}` with `β = α + sγ`. -/
theorem omega_growth_pointwise {s α γ C₂ : ℝ} {k₀ K : ℕ} {Y : Set ℝᵈ}
    (hγ : 0 < γ) (hβ : 0 < α + s * γ) (hC₂ : 0 < C₂)
    (hk₀ : 8 ≤ k₀) (hkK : k₀ ≤ K)
    (hW : ∀ j ∈ Finset.Icc k₀ K, Real.sqrt (d:ℝ) * Wk s j ≤ (2:ℝ)^(j-1))
    (hseg : ∀ j ∈ Finset.Icc k₀ K, ∀ x : ℝᵈ, x ≠ 0 →
      ∫ t in (1/2:ℝ)..2, |omegaK s α j Y (t • x)| ≤
        (1 / ‖x‖) * (C₂ * (4:ℝ)^j * (j:ℝ)^(-(α + s*γ)))) :
    ∀ r ∈ Set.Ioi (0:ℝ), ∀ x : ℝᵈ, ‖x‖ = r →
      ∫ t in (1/2:ℝ)..2, |omega s α k₀ K Y (t • x)| ≤
        (2048 * C₂ * (8 * Real.log 2)^(α + s*γ)) * r / (Real.log (2 + r))^(α + s*γ) := by
  intro r hr x hx
  have hrpos : 0 < r := by simpa using hr
  set β : ℝ := α + s * γ with hβdef
  have hβpos : 0 < β := by rw [hβdef]; exact hβ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLpos : 0 < Real.log (2 + r) := Real.log_pos (by linarith)
  have hApos : 0 < (8:ℝ) * Real.log 2 := by linarith
  have hAβ : 0 < (8 * Real.log 2)^β := Real.rpow_pos_of_pos hApos β
  have hLβ : 0 < (Real.log (2 + r))^β := Real.rpow_pos_of_pos hLpos β
  have hRHSnn : 0 ≤ (2048 * C₂ * (8 * Real.log 2)^β) * r / (Real.log (2 + r))^β :=
    le_of_lt (div_pos (mul_pos (mul_pos (mul_pos (by norm_num) hC₂) hAβ) hrpos) hLβ)
  have hk₀1 : 1 ≤ k₀ := by omega
  by_cases hsmall : r < (2:ℝ)^(k₀ - 2)
  · -- below the first scale `ω` vanishes on `[1/2,2] · x`
    have hzero : ∫ t in (1/2:ℝ)..2, |omega s α k₀ K Y (t • x)| = 0 := by
      have hcongr : ∫ t in (1/2:ℝ)..2, |omega s α k₀ K Y (t • x)| =
          ∫ t in (1/2:ℝ)..2, (0:ℝ) := by
        refine intervalIntegral.integral_congr (fun t ht => ?_)
        have ht' : t ∈ Set.Icc (1/2:ℝ) 2 := by
          have h := ht
          rwa [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 2)] at h
        have htn : ‖t • x‖ = t * r := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht'.1]), hx]
        have hvan : omega s α k₀ K Y (t • x) = 0 := by
          refine Finset.sum_eq_zero (fun j hj => ?_)
          refine omegaK_eq_zero_of_norm_lt (le_trans hk₀1 (Finset.mem_Icc.mp hj).1) (hW j hj) ?_
          have hp : (2:ℝ)^(k₀-1) = 2 * (2:ℝ)^(k₀-2) := by
            rw [show k₀-1 = (k₀-2)+1 by omega, pow_succ]; ring
          have h1 : t * r ≤ 2 * r := mul_le_mul_of_nonneg_right ht'.2 hrpos.le
          have h2 : 2 * r < 2 * (2:ℝ)^(k₀-2) := mul_lt_mul_of_pos_left hsmall (by norm_num)
          have h3 : ‖t • x‖ < (2:ℝ)^(k₀-1) := by rw [htn, hp]; linarith
          exact lt_of_lt_of_le h3 (pow_le_pow_right₀ (by norm_num)
            (Nat.sub_le_sub_right (Finset.mem_Icc.mp hj).1 1))
        rw [hvan, abs_zero]
      rw [hcongr, intervalIntegral.integral_zero]
    rw [hzero]
    exact hRHSnn
  · have hr1 : 1 ≤ r := by
      have h1 : (1:ℝ) ≤ (2:ℝ)^(k₀-2) := one_le_pow₀ (by norm_num)
      linarith [not_lt.mp hsmall]
    obtain ⟨k, hk1, hk2⟩ := exists_pow_le_lt hr1
    have hkge : k₀ - 2 ≤ k := by
      by_contra h
      push_neg at h
      have h1 : (2:ℝ)^(k+1) ≤ (2:ℝ)^(k₀-2) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith [hk2, not_lt.mp hsmall, h1]
    have hk4 : 4 ≤ k := by omega
    have hxne : x ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hx
      linarith
    -- decompose `ω` into its pieces
    have hodec : ∫ t in (1/2:ℝ)..2, |omega s α k₀ K Y (t • x)| =
        ∑ j ∈ Finset.Icc k₀ K, ∫ t in (1/2:ℝ)..2, |omegaK s α j Y (t • x)| := by
      have h1 : ∫ t in (1/2:ℝ)..2, |omega s α k₀ K Y (t • x)| =
          ∫ t in (1/2:ℝ)..2, ∑ j ∈ Finset.Icc k₀ K, |omegaK s α j Y (t • x)| :=
        intervalIntegral.integral_congr (fun t _ => abs_omega s α k₀ K Y (t • x))
      rw [h1, intervalIntegral.integral_finsetSum]
      intro j _
      exact (((omegaK_contDiff s α j Y).continuous.comp
        (continuous_id.smul continuous_const)).abs).intervalIntegrable _ _
    -- the pieces outside the window `[k-3, k+4]` vanish
    have hvanish : ∀ j ∈ Finset.Icc k₀ K, j ∉ Finset.Icc (k-3) (k+4) →
        ∫ t in (1/2:ℝ)..2, |omegaK s α j Y (t • x)| = 0 := by
      intro j hj hjS
      have hjI := Finset.mem_Icc.mp hj
      have hj1 : 1 ≤ j := le_trans hk₀1 hjI.1
      have hz : ∀ t ∈ Set.Icc (1/2:ℝ) 2, omegaK s α j Y (t • x) = 0 := by
        intro t ht
        have htn : ‖t • x‖ = t * r := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.1]), hx]
        by_cases hlo : j + 4 ≤ k
        · refine omegaK_eq_zero_of_norm_gt (s := s) (α := α) (k := j) (Y := Y)
            (x := t • x) hj1 (hW j hj) ?_
          have h1 : (2:ℝ)^(j+2) < (2:ℝ)^(k-1) :=
            pow_lt_pow_right₀ (by norm_num) (by omega)
          have h2 : (2:ℝ)^(k-1) ≤ t * r := by
            have h3 : (2:ℝ)^(k-1) * 2 = (2:ℝ)^k := by
              rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
            have h4 : (1/2:ℝ) * r ≤ t * r := mul_le_mul_of_nonneg_right ht.1 hrpos.le
            linarith [h3, hk1, h4]
          rw [htn]; linarith
        · have hjhi : k + 5 ≤ j := by
            have hgt : k + 4 < j := by
              by_contra h
              push_neg at h
              exact hjS (Finset.mem_Icc.mpr ⟨by omega, h⟩)
            omega
          refine omegaK_eq_zero_of_norm_lt (s := s) (α := α) (k := j) (Y := Y)
            (x := t • x) hj1 (hW j hj) ?_
          have h1 : (2:ℝ)^(k+2) ≤ (2:ℝ)^(j-1) := pow_le_pow_right₀ (by norm_num) (by omega)
          have h2 : t * r < (2:ℝ)^(k+2) := by
            have h3 : t * r ≤ 2 * r := mul_le_mul_of_nonneg_right ht.2 hrpos.le
            have h4 : (2:ℝ)^(k+2) = 2 * (2:ℝ)^(k+1) := by
              rw [show k+2 = (k+1)+1 by omega, pow_succ]; ring
            linarith
          rw [htn]; exact lt_of_lt_of_le h2 h1
      have hcongr : ∫ t in (1/2:ℝ)..2, |omegaK s α j Y (t • x)| =
          ∫ t in (1/2:ℝ)..2, (0:ℝ) := by
        refine intervalIntegral.integral_congr (fun t ht => ?_)
        have ht' : t ∈ Set.Icc (1/2:ℝ) 2 := by
          have h := ht
          rwa [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 2)] at h
        rw [hz t ht', abs_zero]
      rw [hcongr, intervalIntegral.integral_zero]
    -- each surviving piece is bounded by the window constant
    have hterm : ∀ j ∈ Finset.Icc k₀ K ∩ Finset.Icc (k-3) (k+4),
        ∫ t in (1/2:ℝ)..2, |omegaK s α j Y (t • x)| ≤
          (1/r) * (C₂ * (4:ℝ)^(k+4) * (((k-3:ℕ)):ℝ)^(-β)) := by
      intro j hj
      have hjK := (Finset.mem_inter.mp hj).1
      have hjS := Finset.mem_Icc.mp (Finset.mem_inter.mp hj).2
      have h4 : (4:ℝ)^j ≤ (4:ℝ)^(k+4) := pow_le_pow_right₀ (by norm_num) hjS.2
      have hjr : (j:ℝ)^(-β) ≤ (((k-3:ℕ)):ℝ)^(-β) := by
        refine Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (by omega : 0 < k-3))
          (by exact_mod_cast hjS.1) (by linarith [hβpos])
      have hle := hseg j hjK x hxne
      rw [hx] at hle
      refine hle.trans ?_
      have hstep : C₂ * (4:ℝ)^j * (j:ℝ)^(-β) ≤ C₂ * (4:ℝ)^(k+4) * (((k-3:ℕ)):ℝ)^(-β) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h4 hC₂.le) hjr
          (Real.rpow_nonneg (Nat.cast_nonneg j) _)
          (mul_nonneg hC₂.le (pow_nonneg (by norm_num) _))
      exact mul_le_mul_of_nonneg_left hstep
        (show (0:ℝ) ≤ 1/r by exact le_of_lt (div_pos one_pos hrpos))
    -- the sum over the (at most eight) surviving indices
    have hcard : (Finset.Icc k₀ K ∩ Finset.Icc (k-3) (k+4)).card ≤ 8 := by
      have h1 : (Finset.Icc k₀ K ∩ Finset.Icc (k-3) (k+4)).card
          ≤ (Finset.Icc (k-3) (k+4)).card := Finset.card_le_card Finset.inter_subset_right
      have h2 : (Finset.Icc (k-3) (k+4)).card ≤ 8 := by
        have hsub : Finset.Icc (k-3) (k+4) ⊆ (Finset.range 8).image (fun i => (k-3) + i) := by
          intro j hj
          rw [Finset.mem_Icc] at hj
          exact Finset.mem_image.mpr ⟨j - (k-3), by rw [Finset.mem_range]; omega, by omega⟩
        calc (Finset.Icc (k-3) (k+4)).card ≤ ((Finset.range 8).image (fun i => (k-3) + i)).card :=
              Finset.card_le_card hsub
          _ ≤ (Finset.range 8).card := Finset.card_image_le
          _ = 8 := Finset.card_range 8
      omega
    have hc : 0 ≤ (1/r) * (C₂ * (4:ℝ)^(k+4) * (((k-3:ℕ)):ℝ)^(-β)) := by
      have h1 : (0:ℝ) ≤ 1/r := le_of_lt (div_pos one_pos hrpos)
      have h2 : 0 ≤ (((k-3:ℕ)):ℝ)^(-β) :=
        Real.rpow_nonneg (Nat.cast_nonneg (k-3)) _
      positivity
    have hsum_le : ∑ j ∈ Finset.Icc k₀ K, ∫ t in (1/2:ℝ)..2, |omegaK s α j Y (t • x)|
        ≤ 8 * ((1/r) * (C₂ * (4:ℝ)^(k+4) * (((k-3:ℕ)):ℝ)^(-β))) := by
      calc ∑ j ∈ Finset.Icc k₀ K, ∫ t in (1/2:ℝ)..2, |omegaK s α j Y (t • x)|
          = ∑ j ∈ Finset.Icc k₀ K ∩ Finset.Icc (k-3) (k+4),
              ∫ t in (1/2:ℝ)..2, |omegaK s α j Y (t • x)| :=
            (Finset.sum_subset Finset.inter_subset_left
              (fun j hj hjS => hvanish j hj (fun h => hjS (Finset.mem_inter.mpr ⟨hj, h⟩)))).symm
        _ ≤ ∑ _j ∈ Finset.Icc k₀ K ∩ Finset.Icc (k-3) (k+4),
              (1/r) * (C₂ * (4:ℝ)^(k+4) * (((k-3:ℕ)):ℝ)^(-β)) := Finset.sum_le_sum hterm
        _ = ((Finset.Icc k₀ K ∩ Finset.Icc (k-3) (k+4)).card : ℝ) *
              ((1/r) * (C₂ * (4:ℝ)^(k+4) * (((k-3:ℕ)):ℝ)^(-β))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 8 * ((1/r) * (C₂ * (4:ℝ)^(k+4) * (((k-3:ℕ)):ℝ)^(-β))) := by
            have hcast : (((Finset.Icc k₀ K ∩ Finset.Icc (k-3) (k+4)).card : ℕ) : ℝ) ≤ 8 := by
              exact_mod_cast hcard
            nlinarith [hcast, hc]
    rw [hodec]
    exact hsum_le.trans (growth_algebra hβpos hC₂ hrpos hk4 hk1 hk2)

/-- **The growth condition for `ω`** in the form needed by the Beurling–Malliavin theorem:
the supremum over the sphere of radius `r` of the small-time integral of `|ω|`. -/
theorem omega_growth {s α γ C₂ : ℝ} {k₀ K : ℕ} {Y : Set ℝᵈ}
    (hd : 1 ≤ d) (hγ : 0 < γ) (hβ : 0 < α + s * γ) (hC₂ : 0 < C₂)
    (hk₀ : 8 ≤ k₀) (hkK : k₀ ≤ K)
    (hW : ∀ j ∈ Finset.Icc k₀ K, Real.sqrt (d:ℝ) * Wk s j ≤ (2:ℝ)^(j-1))
    (hseg : ∀ j ∈ Finset.Icc k₀ K, ∀ x : ℝᵈ, x ≠ 0 →
      ∫ t in (1/2:ℝ)..2, |omegaK s α j Y (t • x)| ≤
        (1 / ‖x‖) * (C₂ * (4:ℝ)^j * (j:ℝ)^(-(α + s*γ)))) :
    ∀ r ∈ Set.Ioi (0:ℝ),
      (⨆ x : {x : ℝᵈ // ‖x‖ = r}, ∫ t in (1/2:ℝ)..2, |omega s α k₀ K Y (t • (x:ℝᵈ))|) ≤
        (2048 * C₂ * (8 * Real.log 2)^(α + s*γ)) * r / (Real.log (2 + r))^(α + s*γ) := by
  intro r hr
  have hrpos : 0 < r := by simpa using hr
  let u : ℝᵈ := EuclideanSpace.single ⟨0, by omega⟩ (1:ℝ)
  have hu : ‖u‖ = 1 := by
    rw [EuclideanSpace.norm_single]; norm_num
  haveI : Nonempty {x : ℝᵈ // ‖x‖ = r} :=
    ⟨⟨r • u, by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hrpos.le, hu, mul_one]⟩⟩
  exact ciSup_le (fun x => omega_growth_pointwise hγ hβ hC₂ hk₀ hkK hW hseg r hr (x:ℝᵈ) x.2)

/-- **Uniform ray/segment control from porosity.**  If `Y` is `ν`-porous on lines with
`Y ⊆ [-12h⁻¹,12h⁻¹]^d`, then a single pair `(γ, C₂)` works for every index `j ∈ [k₀,K]`. -/
theorem omegaK_segment_uniform {ν μ s α h : ℝ} {k₀ K : ℕ} {Y : Set ℝᵈ}
    (hν : 0 < ν) (hμ : 0 < μ) (hd : 1 ≤ d) (hs : 0 < s) (hh : 0 < h) (hk₀ : 1 ≤ k₀)
    (hY : PorousOnLines ν μ h⁻¹ Y) (hYbox : Y ⊆ cube (-(12 * h⁻¹)) (12 * h⁻¹))
    (hμW : ∀ j ∈ Finset.Icc k₀ K, μ ≤ 4 * (2 * Real.sqrt (d:ℝ) * Wk s j) / ν)
    (hWs : ∀ j ∈ Finset.Icc k₀ K, 2 * Real.sqrt (d:ℝ) * Wk s j ≤ (2:ℝ)^(j-1)) :
    ∃ γ C₂ : ℝ, 0 < γ ∧ 0 < C₂ ∧
      ∀ j ∈ Finset.Icc k₀ K, ∀ x : ℝᵈ, x ≠ 0 →
        ∫ t in (1/2:ℝ)..2, |omegaK s α j Y (t • x)| ≤
          (1 / ‖x‖) * (C₂ * (4:ℝ)^j * (j:ℝ)^(-(α + s*γ))) := by
  obtain ⟨γ, C₀, hγ, hC₀, hbd⟩ :=
    Commons.Measure.EuclideanSpace.porous_line_measure_annulus d (ν := ν / 2) (by positivity)
  have hsqd : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < d))
  have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hC₂pos : 0 < (4 * C₀ * ((Real.sqrt (d:ℝ) / ν)^γ + (192 * (d:ℝ) / ν)^γ)) * (3:ℝ)^d := by
    have h1 : 0 < (Real.sqrt (d:ℝ) / ν)^γ := Real.rpow_pos_of_pos (div_pos hsqd hν) γ
    have h2 : 0 < (192 * (d:ℝ) / ν)^γ :=
      Real.rpow_pos_of_pos (div_pos (mul_pos (by norm_num) hd0) hν) γ
    have h3 : 0 < (3:ℝ)^d := pow_pos (by norm_num) d
    have h4 : 0 < 4 * C₀ * ((Real.sqrt (d:ℝ) / ν)^γ + (192 * (d:ℝ) / ν)^γ) :=
      mul_pos (mul_pos (by norm_num) hC₀) (add_pos h1 h2)
    exact mul_pos h4 h3
  refine ⟨γ, (4 * C₀ * ((Real.sqrt (d:ℝ) / ν)^γ + (192 * (d:ℝ) / ν)^γ)) * (3:ℝ)^d,
    hγ, hC₂pos, ?_⟩
  intro j hj x hx
  exact omegaK_segment_bound hν hγ hC₀ hbd hμ hd hs hh (le_trans hk₀ (Finset.mem_Icc.mp hj).1)
    hY hYbox (hμW j hj) (hWs j hj) hx

/-- **The growth integral of `ω`** with an explicit constant.  A pointwise bound
`G(r) ≤ C r (log(2+r))^{-β}` with `β > 1` gives the finiteness of the Beurling–Malliavin
growth integral, with the constant scaling linearly in `C`. -/
theorem omega_growth_integral_le {s α β C Cint : ℝ} {k₀ K : ℕ} {Y : Set ℝᵈ}
    (hC : 0 < C)
    (hint : ∀ (G : ℝ → ℝ), (∀ r ∈ Set.Ioi (0:ℝ), 0 ≤ G r) →
      (∀ r ∈ Set.Ioi (0:ℝ), G r ≤ r / (Real.log (2 + r))^β) →
      (∫ r in Set.Ioi (0:ℝ), G r / (1 + r^2)) ≤ Cint)
    (hbd : ∀ r ∈ Set.Ioi (0:ℝ),
      (⨆ x : {x : ℝᵈ // ‖x‖ = r}, ∫ t in (1/2:ℝ)..2, |omega s α k₀ K Y (t • (x:ℝᵈ))|)
        ≤ C * r / (Real.log (2 + r))^β) :
    (∫ r in Set.Ioi (0:ℝ),
      (⨆ x : {x : ℝᵈ // ‖x‖ = r}, ∫ t in (1/2:ℝ)..2, |omega s α k₀ K Y (t • (x:ℝᵈ))|)
        / (1 + r^2)) ≤ C * Cint := by
  have hnn : ∀ r ∈ Set.Ioi (0:ℝ),
      0 ≤ (⨆ x : {x : ℝᵈ // ‖x‖ = r}, ∫ t in (1/2:ℝ)..2, |omega s α k₀ K Y (t • (x:ℝᵈ))|) :=
    fun r _ => Real.iSup_nonneg (fun x =>
      intervalIntegral.integral_nonneg (by norm_num) (fun u _ => abs_nonneg _))
  have hH : ∀ r ∈ Set.Ioi (0:ℝ),
      (⨆ x : {x : ℝᵈ // ‖x‖ = r}, ∫ t in (1/2:ℝ)..2, |omega s α k₀ K Y (t • (x:ℝᵈ))|) / C
        ≤ r / (Real.log (2 + r))^β := by
    intro r hr
    have hrpos : 0 < r := by simpa using hr
    have hlog : 0 < Real.log (2 + r) := Real.log_pos (by linarith)
    have hLβ : 0 < (Real.log (2 + r))^β := Real.rpow_pos_of_pos hlog β
    have hmul : (⨆ x : {x : ℝᵈ // ‖x‖ = r},
        ∫ t in (1/2:ℝ)..2, |omega s α k₀ K Y (t • (x:ℝᵈ))|) * (Real.log (2 + r))^β ≤ C * r := by
      have h := mul_le_mul_of_nonneg_right (hbd r hr) hLβ.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hLβ)] at h
    rw [div_le_iff₀ hC]
    rw [show (r / (Real.log (2 + r))^β) * C = (r * C) / (Real.log (2 + r))^β by ring]
    rw [le_div_iff₀ hLβ]
    linarith [hmul]
  have heq : ∫ r in Set.Ioi (0:ℝ),
        (⨆ x : {x : ℝᵈ // ‖x‖ = r}, ∫ t in (1/2:ℝ)..2, |omega s α k₀ K Y (t • (x:ℝᵈ))|)
          / (1 + r^2)
      = C * ∫ r in Set.Ioi (0:ℝ),
        ((⨆ x : {x : ℝᵈ // ‖x‖ = r}, ∫ t in (1/2:ℝ)..2, |omega s α k₀ K Y (t • (x:ℝᵈ))|) / C)
          / (1 + r^2) := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext r
    field_simp
  rw [heq]
  refine mul_le_mul_of_nonneg_left (hint _ (fun r hr => div_nonneg (hnn r hr) hC.le) hH) hC.le

/-- **The growth integral of `ω`.**  A pointwise bound `G(r) ≤ C r (log(2+r))^{-β}` with
`β > 1` gives the finiteness of the Beurling–Malliavin growth integral. -/
theorem omega_growth_integral {s α β C : ℝ} {k₀ K : ℕ} {Y : Set ℝᵈ}
    (hβ : 1 < β) (hC : 0 < C)
    (hbd : ∀ r ∈ Set.Ioi (0:ℝ),
      (⨆ x : {x : ℝᵈ // ‖x‖ = r}, ∫ t in (1/2:ℝ)..2, |omega s α k₀ K Y (t • (x:ℝᵈ))|)
        ≤ C * r / (Real.log (2 + r))^β) :
    ∃ Cgr : ℝ, 0 < Cgr ∧
      (∫ r in Set.Ioi (0:ℝ),
        (⨆ x : {x : ℝᵈ // ‖x‖ = r}, ∫ t in (1/2:ℝ)..2, |omega s α k₀ K Y (t • (x:ℝᵈ))|)
          / (1 + r^2)) ≤ Cgr := by
  obtain ⟨Cint, hCint, hint⟩ := Commons.Measure.Real.integral_log_rpow_decay β hβ
  exact ⟨C * Cint, mul_pos hC hCint, omega_growth_integral_le hC hint hbd⟩

end GrowthBound

end MeasureBound

end Submission.FUP
