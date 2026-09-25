import Mathlib
import Submission.Commons.Analysis.Inequalities.sum_rpow_inv_le_sum_rpow_inv
import Submission.Commons.Analysis.Fourier.fourierInv_mul_fourier_eq_convolution
import Submission.Commons.Analysis.Fourier.lintegral_fourierInv_eq
import Submission.Commons.Analysis.Fourier.triangular_fourier
import Submission.Commons.Analysis.Fourier.one_sided_geometric_maximal_l2
import Submission.Commons.Analysis.Fourier.separated_maximal_of_smooth_window
import Submission.Commons.Analysis.Fourier.bourgain_smooth_window_maximal_l2_smooth
import Submission.Commons.Analysis.Fourier.neighborhood_maximal_arbitrary_of_separated
import Submission.Commons.Analysis.Fourier.bandOp_l2_multiplier_bound
import Submission.Commons.Analysis.Fourier.sharp_of_smooth_window_maximal_l2
import Submission.Commons.Analysis.Fourier.aestronglyMeasurable_conv
import Submission.Commons.Analysis.Fourier.boundary_layer_l2
import Submission.Commons.Analysis.Fourier.fourier_toLp_eq_fourier_integral
import Submission.Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv

namespace Commons.Analysis.Fourier

open _root_.MeasureTheory
open scoped FourierTransform
open scoped _root_.ENNReal
open VectorFourier

private lemma sep_enorm_eq_ofReal_norm_aux {E : Type*} [SeminormedAddCommGroup E] (z : E) :
    ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by simp [enorm_eq_nnnorm]

private lemma lp_add_le_of_nonneg {ι : Type*} (t : Finset ι) {s : ℝ} (hs : 1 ≤ s) (x y : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    (∑ i ∈ t, (x i + y i) ^ s) ^ ((1:ℝ)/s)
      ≤ (∑ i ∈ t, x i ^ s) ^ ((1:ℝ)/s) + (∑ i ∈ t, y i ^ s) ^ ((1:ℝ)/s) := by
  have h := Real.Lp_add_le t x y hs
  simpa only [abs_of_nonneg (hx _), abs_of_nonneg (hy _),
    abs_of_nonneg (add_nonneg (hx _) (hy _))] using h

/-- **Dyadic variation versus the square function of the values.**
For an `E`-valued family `a` indexed by `ℤ` and `s ≥ 2`, the `s`-variation over increasing
subsequences of `ℤ` is dominated by four times the `ℓ²`-square function of the values. -/
lemma dyadicVar_sq_le_squareFunction {E : Type*} [NormedAddCommGroup E] (a : ℤ → E) {s : ℝ}
    (hs : 2 ≤ s) :
    (⨆ (J : ℕ) (k : Fin (J + 1) → ℤ), ⨆ (_ : StrictMono k),
        ENNReal.ofReal ((∑ j : Fin J, ‖a (k (Fin.castSucc j)) - a (k (Fin.succ j))‖ ^ s)
          ^ ((1:ℝ)/s))) ^ (2:ℝ)
      ≤ 4 * ∑' i : ℤ, ‖a i‖ₑ ^ (2:ℝ) := by
  have hs0 : 0 < s := by linarith
  have hs1 : 1 ≤ s := by linarith
  set S : ℝ≥0∞ := ∑' i : ℤ, ‖a i‖ₑ ^ (2:ℝ) with hSdef
  have hV : (⨆ (J : ℕ) (k : Fin (J + 1) → ℤ), ⨆ (_ : StrictMono k),
        ENNReal.ofReal ((∑ j : Fin J, ‖a (k (Fin.castSucc j)) - a (k (Fin.succ j))‖ ^ s)
          ^ ((1:ℝ)/s))) ≤ 2 * S ^ ((1:ℝ)/2) := by
    refine iSup_le (fun J => iSup_le (fun k => iSup_le (fun hk => ?_)))
    set F : Finset ℤ := Finset.univ.image k with hFdef
    have hreal : (∑ j : Fin J, ‖a (k (Fin.castSucc j)) - a (k (Fin.succ j))‖ ^ s) ^ ((1:ℝ)/s)
        ≤ 2 * (∑ i ∈ F, ‖a i‖ ^ s) ^ ((1:ℝ)/s) := by
      have hstep1 : (∑ j : Fin J, ‖a (k (Fin.castSucc j)) - a (k (Fin.succ j))‖ ^ s) ^ ((1:ℝ)/s)
          ≤ (∑ j : Fin J,
              (‖a (k (Fin.castSucc j))‖ + ‖a (k (Fin.succ j))‖) ^ s) ^ ((1:ℝ)/s) := by
        refine Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => by positivity)
          (Finset.sum_le_sum fun j _ => ?_) (by positivity)
        exact Real.rpow_le_rpow (norm_nonneg _) (norm_sub_le _ _) (by linarith)
      have hstep2 : (∑ j : Fin J,
              (‖a (k (Fin.castSucc j))‖ + ‖a (k (Fin.succ j))‖) ^ s) ^ ((1:ℝ)/s)
          ≤ (∑ j : Fin J, ‖a (k (Fin.castSucc j))‖ ^ s) ^ ((1:ℝ)/s)
            + (∑ j : Fin J, ‖a (k (Fin.succ j))‖ ^ s) ^ ((1:ℝ)/s) :=
        lp_add_le_of_nonneg Finset.univ hs1
          (fun j => ‖a (k (Fin.castSucc j))‖) (fun j => ‖a (k (Fin.succ j))‖)
          (fun j => norm_nonneg _) (fun j => norm_nonneg _)
      have hsub : ∀ (g : Fin J → ℤ), Function.Injective g → (∀ j, g j ∈ F) →
          (∑ j : Fin J, ‖a (g j)‖ ^ s) ^ ((1:ℝ)/s) ≤ (∑ i ∈ F, ‖a i‖ ^ s) ^ ((1:ℝ)/s) := by
        intro g hg hgF
        refine Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => by positivity) ?_ (by positivity)
        calc ∑ j : Fin J, ‖a (g j)‖ ^ s
            = ∑ i ∈ (Finset.univ.image g), ‖a i‖ ^ s := by
                rw [Finset.sum_image (s := Finset.univ) hg.injOn]
          _ ≤ ∑ i ∈ F, ‖a i‖ ^ s :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (fun i hi => by
                  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
                  exact hgF j)
                (fun i _ _ => by positivity)
      have h3 := hsub (fun j => k (Fin.castSucc j))
        (hk.injective.comp Fin.strictMono_castSucc.injective)
        (fun j => Finset.mem_image.mpr ⟨Fin.castSucc j, Finset.mem_univ _, rfl⟩)
      have h4 := hsub (fun j => k (Fin.succ j))
        (hk.injective.comp Fin.strictMono_succ.injective)
        (fun j => Finset.mem_image.mpr ⟨Fin.succ j, Finset.mem_univ _, rfl⟩)
      calc (∑ j : Fin J, ‖a (k (Fin.castSucc j)) - a (k (Fin.succ j))‖ ^ s) ^ ((1:ℝ)/s)
          ≤ (∑ j : Fin J,
              (‖a (k (Fin.castSucc j))‖ + ‖a (k (Fin.succ j))‖) ^ s) ^ ((1:ℝ)/s) := hstep1
        _ ≤ (∑ j : Fin J, ‖a (k (Fin.castSucc j))‖ ^ s) ^ ((1:ℝ)/s)
            + (∑ j : Fin J, ‖a (k (Fin.succ j))‖ ^ s) ^ ((1:ℝ)/s) := hstep2
        _ ≤ (∑ i ∈ F, ‖a i‖ ^ s) ^ ((1:ℝ)/s) + (∑ i ∈ F, ‖a i‖ ^ s) ^ ((1:ℝ)/s) :=
            add_le_add h3 h4
        _ = 2 * (∑ i ∈ F, ‖a i‖ ^ s) ^ ((1:ℝ)/s) := by ring
    -- transfer: `ofReal(LHS) ≤ 2 * (∑_F ‖a i‖ₑ^s)^{1/s}`
    have hkey : (ENNReal.ofReal (∑ i ∈ F, ‖a i‖ ^ s)) = (∑ i ∈ F, ‖a i‖ₑ ^ s) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [sep_enorm_eq_ofReal_norm_aux, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by positivity)]
    have hY : ENNReal.ofReal ((∑ i ∈ F, ‖a i‖ ^ s) ^ ((1:ℝ)/s))
        ≤ (∑ i ∈ F, ‖a i‖ₑ ^ s) ^ ((1:ℝ)/s) := by
      rw [← ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity) (by positivity),
        hkey]
    have hENN : ENNReal.ofReal ((∑ j : Fin J, ‖a (k (Fin.castSucc j)) - a (k (Fin.succ j))‖ ^ s)
          ^ ((1:ℝ)/s))
        ≤ 2 * (∑ i ∈ F, ‖a i‖ₑ ^ s) ^ ((1:ℝ)/s) := by
      refine le_trans (ENNReal.ofReal_le_ofReal hreal) ?_
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
        show (ENNReal.ofReal (2:ℝ) : ℝ≥0∞) = 2 by norm_num]
      exact mul_le_mul' le_rfl hY
    -- ℓ^s ⊆ ℓ² and monotonicity of the tsum
    have hls : (∑ i ∈ F, ‖a i‖ₑ ^ s) ^ ((1:ℝ)/s) ≤ S ^ ((1:ℝ)/2) := by
      refine le_trans (Commons.Analysis.Inequalities.sum_rpow_inv_le_sum_rpow_inv F
        (fun i => ‖a i‖ₑ) (by norm_num : (0:ℝ) < 2) hs) ?_
      exact ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum F) (by norm_num)
    calc ENNReal.ofReal ((∑ j : Fin J, ‖a (k (Fin.castSucc j)) - a (k (Fin.succ j))‖ ^ s)
          ^ ((1:ℝ)/s))
        ≤ 2 * (∑ i ∈ F, ‖a i‖ₑ ^ s) ^ ((1:ℝ)/s) := hENN
      _ ≤ 2 * S ^ ((1:ℝ)/2) := mul_le_mul' le_rfl hls
  have hsq : (2 * S ^ ((1:ℝ)/2)) ^ (2:ℝ) = 4 * S := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2),
      ← ENNReal.rpow_mul, show (1/2 : ℝ) * 2 = 1 by ring, ENNReal.rpow_one]
    norm_num
  calc (⨆ (J : ℕ) (k : Fin (J + 1) → ℤ), ⨆ (_ : StrictMono k),
        ENNReal.ofReal ((∑ j : Fin J, ‖a (k (Fin.castSucc j)) - a (k (Fin.succ j))‖ ^ s)
          ^ ((1:ℝ)/s))) ^ (2:ℝ)
      ≤ (2 * S ^ ((1:ℝ)/2)) ^ (2:ℝ) := ENNReal.rpow_le_rpow hV (by norm_num)
    _ = 4 * S := hsq


private lemma quarter_pow_sum_le (n : ℕ) :
    ∑ k ∈ Finset.range n, ((1/4:ℝ)^k) ≤ 4/3 := by
  rw [geom_sum_eq (by norm_num : (1/4:ℝ) ≠ 1)]
  rw [show ((1/4:ℝ)^n - 1) / (1/4 - 1) = (1 - (1/4:ℝ)^n) / (3/4) by ring]
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 3/4)]
  nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/4) n]

private lemma pow4_sum_range_le (K : ℕ) :
    ∑ k ∈ Finset.range (K+1), ((4:ℝ)^k) ≤ (4:ℝ)^(K+1) / 3 := by
  rw [geom_sum_eq (by norm_num : (4:ℝ) ≠ 1)]
  norm_num
  rw [div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 3)]
  linarith [pow_pos (by norm_num : (0:ℝ) < 4) (K+1)]

private lemma min_div_pow_sum_le (b : ℝ) (hb : 0 < b) (n : ℕ) :
    ∑ k ∈ Finset.range n, min (b / (4:ℝ)^k) ((4:ℝ)^k / b) ≤ 4 := by
  have h4pos : (0:ℝ) < 4 := by norm_num
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlow : ∀ k : ℕ, (4:ℝ)^k ≤ b → min (b / (4:ℝ)^k) ((4:ℝ)^k / b) = (4:ℝ)^k / b := by
    intro k hk
    refine min_eq_right ?_
    rw [div_le_div_iff₀ hb (pow_pos h4pos k)]
    nlinarith [hk, hb, pow_pos h4pos k]
  have hhigh : ∀ k : ℕ, b ≤ (4:ℝ)^k → min (b / (4:ℝ)^k) ((4:ℝ)^k / b) = b / (4:ℝ)^k := by
    intro k hk
    refine min_eq_left ?_
    rw [div_le_div_iff₀ (pow_pos h4pos k) hb]
    nlinarith [hk, hb, pow_pos h4pos k]
  rcases lt_or_ge b 1 with hb1 | hb1
  · have hkey : ∀ k : ℕ, min (b / (4:ℝ)^k) ((4:ℝ)^k / b) = b / (4:ℝ)^k :=
      fun k => hhigh k (le_trans hb1.le (one_le_pow₀ (by norm_num)))
    calc ∑ k ∈ Finset.range n, min (b / (4:ℝ)^k) ((4:ℝ)^k / b)
        = ∑ k ∈ Finset.range n, b * ((1/4:ℝ)^k) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [hkey k, div_eq_mul_inv, ← inv_pow]; norm_num
      _ = b * ∑ k ∈ Finset.range n, ((1/4:ℝ)^k) := by rw [Finset.mul_sum]
      _ ≤ b * (4/3) := mul_le_mul_of_nonneg_left (quarter_pow_sum_le n) hb.le
      _ ≤ 4 := by nlinarith [hb, hb1]
  · set K : ℕ := ⌊Real.log b / Real.log 4⌋₊ with hKdef
    have hKle : ((K:ℝ)) ≤ Real.log b / Real.log 4 :=
      Nat.floor_le (div_nonneg (Real.log_nonneg hb1) hlog4.le)
    have hKlt : Real.log b / Real.log 4 < (K:ℝ) + 1 := Nat.lt_floor_add_one _
    have h4K : (4:ℝ)^K ≤ b := by
      have h1 : Real.log ((4:ℝ)^K) ≤ Real.log b := by
        rw [Real.log_pow]
        rw [le_div_iff₀ hlog4] at hKle
        linarith [hKle]
      exact (Real.log_le_log_iff (by positivity) hb).mp h1
    have h4K' : b < (4:ℝ)^(K+1) := by
      have h1 : Real.log b < Real.log ((4:ℝ)^(K+1)) := by
        rw [Real.log_pow]
        rw [div_lt_iff₀ hlog4] at hKlt
        push_cast at hKlt ⊢
        linarith [hKlt]
      exact (Real.log_lt_log_iff hb (by positivity)).mp h1
    have hbase : b * ((1/4:ℝ)^(K+1)) ≤ 1 := by
      rw [show ((1/4:ℝ)) = (4:ℝ)⁻¹ by norm_num, inv_pow, ← div_eq_mul_inv]
      rw [div_le_one (by positivity : (0:ℝ) < (4:ℝ)^(K+1))]
      exact h4K'.le
    have hA : ∑ k ∈ Finset.range (K+1), min (b / (4:ℝ)^k) ((4:ℝ)^k / b) ≤ 4/3 := by
      have hcongr : ∀ k ∈ Finset.range (K+1),
          min (b / (4:ℝ)^k) ((4:ℝ)^k / b) = (4:ℝ)^k / b := by
        intro k hk
        refine hlow k ?_
        rw [Finset.mem_range] at hk
        exact le_trans (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 4) (by omega)) h4K
      rw [Finset.sum_congr rfl hcongr, ← Finset.sum_div]
      rw [div_le_div_iff₀ hb (by norm_num : (0:ℝ) < 3)]
      have h := pow4_sum_range_le K
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 3)] at h
      have hsucc : (4:ℝ)^(K+1) = 4 * (4:ℝ)^K := by rw [pow_succ]; ring
      nlinarith [h, h4K, hsucc, pow_pos h4pos K]
    have hB : ∀ m : ℕ, ∑ j ∈ Finset.range m,
        min (b / (4:ℝ)^((K+1) + j)) ((4:ℝ)^((K+1) + j) / b) ≤ 4/3 := by
      intro m
      have hcongr : ∀ j ∈ Finset.range m,
          min (b / (4:ℝ)^((K+1) + j)) ((4:ℝ)^((K+1) + j) / b)
            = b * ((1/4:ℝ)^((K+1) + j)) := by
        intro j _
        rw [hhigh ((K+1) + j) (le_trans h4K'.le (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 4)
          (by omega)))]
        rw [div_eq_mul_inv, ← inv_pow]; norm_num
      rw [Finset.sum_congr rfl hcongr]
      have hfac : ∀ j : ℕ, b * ((1/4:ℝ)^((K+1) + j))
          = (b * ((1/4:ℝ)^(K+1))) * ((1/4:ℝ)^j) := by
        intro j
        rw [pow_add]
        ring
      rw [Finset.sum_congr rfl (fun j _ => hfac j), ← Finset.mul_sum]
      calc (b * ((1/4:ℝ)^(K+1))) * ∑ j ∈ Finset.range m, ((1/4:ℝ)^j)
          ≤ 1 * (4/3) :=
            mul_le_mul hbase (quarter_pow_sum_le m) (by positivity) (by norm_num)
        _ ≤ 4/3 := by norm_num
    by_cases hn : K+1 ≤ n
    · rw [show n = (K+1) + (n - (K+1)) by omega, Finset.sum_range_add]
      linarith [hA, hB (n - (K+1))]
    · have hsub : Finset.range n ⊆ Finset.range (K+1) := fun k hk => by
        rw [Finset.mem_range] at hk ⊢; omega
      calc ∑ k ∈ Finset.range n, min (b / (4:ℝ)^k) ((4:ℝ)^k / b)
          ≤ ∑ k ∈ Finset.range (K+1), min (b / (4:ℝ)^k) ((4:ℝ)^k / b) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
        _ ≤ 4/3 := hA
        _ ≤ 4 := by norm_num



lemma tsum_nat_min_div_four_pow_le (b : ℝ) (hb : 0 < b) :
    ∑' k : ℕ, ENNReal.ofReal (min (b / (4:ℝ)^k) ((4:ℝ)^k / b)) ≤ 4 := by
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le (fun n => ?_)
  calc ∑ k ∈ Finset.range n, ENNReal.ofReal (min (b / (4:ℝ)^k) ((4:ℝ)^k / b))
      = ENNReal.ofReal (∑ k ∈ Finset.range n, min (b / (4:ℝ)^k) ((4:ℝ)^k / b)) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
    _ ≤ ENNReal.ofReal 4 := ENNReal.ofReal_le_ofReal (min_div_pow_sum_le b hb n)
    _ = 4 := by norm_num


private lemma min_sq_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    min x y ^ 2 = min (x ^ 2) (y ^ 2) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (by nlinarith)]
  · rw [min_eq_right h, min_eq_right (by nlinarith)]

private lemma two_pow_neg_sq (k : ℕ) : ((2:ℝ)^(-(k:ℝ))) ^ 2 = (1/4:ℝ)^k := by
  rw [← Real.rpow_natCast ((2:ℝ)^(-(k:ℝ))) 2, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [show (-(k:ℝ)) * ((2:ℕ):ℝ) = -(((2*k:ℕ)):ℝ) by push_cast; ring]
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, ← inv_pow, pow_mul]
  norm_num

lemma tsum_fourier_dyadic_le_of_decay {K : ℝ → ℂ} (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ u : ℝ, ‖(𝓕 K) u‖ ≤ B * min |u| |u|⁻¹) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ξ : ℝ,
      ∑' k : ℕ, ‖(𝓕 K) ((2:ℝ)^(-(k:ℝ)) * ξ)‖ₑ ^ (2:ℝ) ≤ ENNReal.ofReal (A^2) := by
  refine ⟨2 * B, by positivity, fun ξ => ?_⟩
  rcases eq_or_ne ξ 0 with rfl | hξ
  · have h0 : ‖(𝓕 K) 0‖ = 0 := by
      have h1 := h 0
      simp only [abs_zero, inv_zero, min_self, mul_zero] at h1
      exact le_antisymm h1 (norm_nonneg _)
    have hz : ∀ k : ℕ, ‖(𝓕 K) ((2:ℝ)^(-(k:ℝ)) * 0)‖ₑ ^ (2:ℝ) = 0 := by
      intro k; rw [mul_zero, sep_enorm_eq_ofReal_norm_aux, h0]; simp
    rw [tsum_congr hz]; simp
  · have hterm : ∀ k : ℕ, ‖(𝓕 K) ((2:ℝ)^(-(k:ℝ)) * ξ)‖ₑ ^ (2:ℝ)
        ≤ ENNReal.ofReal (B^2) * ENNReal.ofReal (min (ξ^2 / (4:ℝ)^k) ((4:ℝ)^k / ξ^2)) := by
      intro k
      set t : ℝ := (2:ℝ)^(-(k:ℝ)) with ht
      have htpos : 0 < t := Real.rpow_pos_of_pos (by norm_num) _
      have ht2 : t^2 = (1/4:ℝ)^k := two_pow_neg_sq k
      have hnorm : ‖(𝓕 K) (t * ξ)‖ ≤ B * min (t * |ξ|) ((t * |ξ|)⁻¹) := by
        have h1 := h (t * ξ)
        rwa [abs_mul, abs_of_pos htpos] at h1
      have h14 : (1/4:ℝ)^k = ((4:ℝ)^k)⁻¹ := by
        rw [show (1/4:ℝ) = (4:ℝ)⁻¹ by norm_num, inv_pow]
      have hm1 : (t * |ξ|)^2 = ξ^2 / (4:ℝ)^k := by
        rw [mul_pow, ht2, sq_abs, h14, div_eq_mul_inv, mul_comm]
      have hm2 : ((t * |ξ|)⁻¹)^2 = (4:ℝ)^k / ξ^2 := by
        rw [inv_pow, hm1, inv_div]
      have hms : (min (t * |ξ|) ((t * |ξ|)⁻¹)) ^ 2 = min (ξ^2 / (4:ℝ)^k) ((4:ℝ)^k / ξ^2) := by
        rw [min_sq_of_nonneg (by positivity) (by positivity), hm1, hm2]
      rw [sep_enorm_eq_ofReal_norm_aux, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num,
        ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (norm_nonneg _) 2]
      have hreal : ‖(𝓕 K) (t * ξ)‖ ^ 2 ≤ B^2 * min (ξ^2 / (4:ℝ)^k) ((4:ℝ)^k / ξ^2) := by
        calc ‖(𝓕 K) (t * ξ)‖ ^ 2 ≤ (B * min (t * |ξ|) ((t * |ξ|)⁻¹))^2 :=
              pow_le_pow_left₀ (norm_nonneg _) hnorm 2
          _ = B^2 * (min (t * |ξ|) ((t * |ξ|)⁻¹))^2 := by rw [mul_pow]
          _ = B^2 * min (ξ^2 / (4:ℝ)^k) ((4:ℝ)^k / ξ^2) := by rw [hms]
      calc ENNReal.ofReal (‖(𝓕 K) (t * ξ)‖ ^ 2)
          ≤ ENNReal.ofReal (B^2 * min (ξ^2 / (4:ℝ)^k) ((4:ℝ)^k / ξ^2)) :=
            ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal (B^2) * ENNReal.ofReal (min (ξ^2 / (4:ℝ)^k) ((4:ℝ)^k / ξ^2)) :=
            ENNReal.ofReal_mul (by positivity)
    calc ∑' k : ℕ, ‖(𝓕 K) ((2:ℝ)^(-(k:ℝ)) * ξ)‖ₑ ^ (2:ℝ)
        ≤ ∑' k : ℕ, ENNReal.ofReal (B^2) *
            ENNReal.ofReal (min (ξ^2 / (4:ℝ)^k) ((4:ℝ)^k / ξ^2)) :=
          ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal (B^2) * ∑' k : ℕ,
            ENNReal.ofReal (min (ξ^2 / (4:ℝ)^k) ((4:ℝ)^k / ξ^2)) :=
          ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (B^2) * 4 :=
          mul_le_mul' le_rfl (tsum_nat_min_div_four_pow_le (ξ^2) (by positivity))
      _ = ENNReal.ofReal ((2 * B)^2) := by
          rw [show (4 : ℝ≥0∞) = ENNReal.ofReal (4:ℝ) by norm_num,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring



/-- **Fourier transform of a real dilation.**  For `c > 0`,
`𝓕 (z ↦ c · K (c z)) ξ = (𝓕 K) (ξ / c)`. -/
lemma fourier_dilation {K : ℝ → ℂ} {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    𝓕 (fun z : ℝ => (c : ℂ) * K (c * z)) ξ = (𝓕 K) (ξ / c) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  rw [Real.fourier_eq, Real.fourier_eq]
  simp_rw [Real.inner_apply]
  have h1 : (∫ z : ℝ, Real.fourierChar (-(z * ξ)) • ((c : ℂ) * K (c * z)))
      = (c : ℂ) * ∫ z : ℝ, Real.fourierChar (-(z * ξ)) • K (c * z) := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [Circle.smul_def, smul_eq_mul]
    ring
  rw [h1]
  have h2 : (∫ z : ℝ, Real.fourierChar (-(z * ξ)) • K (c * z))
      = |c⁻¹| • ∫ u : ℝ, Real.fourierChar (-((u / c) * ξ)) • K u := by
    have hsub := MeasureTheory.Measure.integral_comp_mul_left
      (fun u : ℝ => Real.fourierChar (-((u / c) * ξ)) • K u) c
    have heq : (∫ z : ℝ, Real.fourierChar (-(z * ξ)) • K (c * z))
        = ∫ z : ℝ, (fun u : ℝ => Real.fourierChar (-((u / c) * ξ)) • K u) (c * z) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only []
      rw [show -(z * ξ) = -((c * z / c) * ξ) by field_simp]
    rw [heq, hsub]
  rw [h2, abs_of_pos (inv_pos.mpr hc), Complex.real_smul, ← mul_assoc, Complex.ofReal_inv,
    mul_inv_cancel₀ (by exact_mod_cast hcne), one_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only []
  rw [show -(u / c * ξ) = -(u * (ξ / c)) by ring]


lemma integrable_dilation {K : ℝ → ℂ} (hK : MeasureTheory.Integrable K) {c : ℝ} (hc : c ≠ 0) :
    MeasureTheory.Integrable (fun z : ℝ => (c : ℂ) * K (c * z)) :=
  (hK.comp_smul hc).const_mul _

lemma integrable_fourier_dilation {K : ℝ → ℂ} (hK : MeasureTheory.Integrable (𝓕 K)) {c : ℝ}
    (hc : c ≠ 0) :
    MeasureTheory.Integrable (fun ξ : ℝ => (𝓕 K) (c * ξ)) :=
  hK.comp_smul hc

/-- **Per-scale Plancherel for the dilated convolution.** -/
lemma lintegral_dilated_convolution_sq {K g : ℝ → ℂ} (hKc : Continuous K)
    (hK : MeasureTheory.Integrable K) (hKF : MeasureTheory.Integrable (𝓕 K))
    (hg : MeasureTheory.Integrable g) {c : ℝ} (hc : 0 < c)
    (h1 : MeasureTheory.MemLp (fun ξ : ℝ => (𝓕 K : ℝ → ℂ) (ξ / c) * (𝓕 g : ℝ → ℂ) ξ) 1 volume)
    (h2 : MeasureTheory.MemLp (fun ξ : ℝ => (𝓕 K : ℝ → ℂ) (ξ / c) * (𝓕 g : ℝ → ℂ) ξ) 2 volume) :
    ∫⁻ x, ENNReal.ofReal ‖∫ y : ℝ, g y * ((c : ℂ) * K (c * (x - y)))‖ ^ (2:ℝ)
      = ∫⁻ ξ, ENNReal.ofReal ‖(𝓕 K) (ξ / c) * 𝓕 g ξ‖ ^ (2:ℝ) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hKt_int : MeasureTheory.Integrable (fun z : ℝ => (c : ℂ) * K (c * z)) :=
    integrable_dilation hK hcne
  have hKt_cont : Continuous (fun z : ℝ => (c : ℂ) * K (c * z)) :=
    (hKc.comp (by fun_prop : Continuous fun z : ℝ => c * z)).const_mul _
  have hFt : (𝓕 (fun z : ℝ => (c : ℂ) * K (c * z))) = fun ξ : ℝ => (𝓕 K) (ξ / c) :=
    funext (fun ξ => fourier_dilation hc ξ)
  have hsym_int : MeasureTheory.Integrable (fun ξ : ℝ => (𝓕 K : ℝ → ℂ) (ξ / c)) :=
    (integrable_fourier_dilation (c := c⁻¹) hKF (inv_ne_zero hcne)).congr
      (Filter.Eventually.of_forall (fun ξ => by simp only []; rw [div_eq_inv_mul]))
  have hFt_int : MeasureTheory.Integrable (𝓕 (fun z : ℝ => (c : ℂ) * K (c * z))) :=
    hsym_int.congr (Filter.Eventually.of_forall (fun ξ => (congrFun hFt ξ).symm))
  have hinv : 𝓕⁻ (fun ξ : ℝ => (𝓕 K : ℝ → ℂ) (ξ / c))
      = (fun z : ℝ => (c : ℂ) * K (c * z)) := by
    have h := hKt_cont.fourierInv_fourier_eq hKt_int hFt_int
    have h2 : 𝓕⁻ (fun ξ : ℝ => (𝓕 K : ℝ → ℂ) (ξ / c))
        = 𝓕⁻ (𝓕 (fun z : ℝ => (c : ℂ) * K (c * z))) := by
      congr 1
      funext ξ
      exact (congrFun hFt ξ).symm
    rw [h2, h]
  have hm : MeasureTheory.Integrable (fun ξ : ℝ => (𝓕 K : ℝ → ℂ) (ξ / c)) := by
    rw [← hFt]; exact hFt_int
  have hconv : ∀ x : ℝ, 𝓕⁻ (fun ξ : ℝ => (𝓕 K : ℝ → ℂ) (ξ / c) * (𝓕 g : ℝ → ℂ) ξ) x
      = ∫ y : ℝ, g y * ((c : ℂ) * K (c * (x - y))) := by
    intro x
    rw [fourierInv_mul_fourier_eq_convolution hm hg x, hinv]
  have key := lintegral_fourierInv_eq h1 h2
  have hgoal : (∫⁻ x, ENNReal.ofReal
        ‖∫ y : ℝ, g y * ((c : ℂ) * K (c * (x - y)))‖ ^ (2:ℝ))
      = ∫⁻ x, ENNReal.ofReal
          ‖𝓕⁻ (fun ξ : ℝ => (𝓕 K : ℝ → ℂ) (ξ / c) * (𝓕 g : ℝ → ℂ) ξ) x‖ ^ (2:ℝ) := by
    refine lintegral_congr (fun x => ?_)
    rw [← hconv x]
  exact hgoal.trans key



/-- The inverse Fourier integral of an integrable function is continuous. -/
lemma continuous_fourierInv_of_integrable_sep {h : ℝ → ℂ} (hh : MeasureTheory.Integrable h) :
    Continuous (𝓕⁻ h) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner.neg hh

/-- **The dilated convolution as an inverse Fourier integral.** -/
lemma convolution_dilation_eq_fourierInv {K g : ℝ → ℂ} (hKc : Continuous K)
    (hK : MeasureTheory.Integrable K) (hKF : MeasureTheory.Integrable (𝓕 K))
    (hg : MeasureTheory.Integrable g) {c : ℝ} (hc : 0 < c) (x : ℝ) :
    𝓕⁻ (fun ξ : ℝ => (𝓕 K : ℝ → ℂ) (ξ / c) * (𝓕 g : ℝ → ℂ) ξ) x
      = ∫ y : ℝ, g y * ((c : ℂ) * K (c * (x - y))) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hKt_int : MeasureTheory.Integrable (fun z : ℝ => (c : ℂ) * K (c * z)) :=
    integrable_dilation hK hcne
  have hKt_cont : Continuous (fun z : ℝ => (c : ℂ) * K (c * z)) :=
    (hKc.comp (by fun_prop : Continuous fun z : ℝ => c * z)).const_mul _
  have hFt : (𝓕 (fun z : ℝ => (c : ℂ) * K (c * z))) = fun ξ : ℝ => (𝓕 K) (ξ / c) :=
    funext (fun ξ => fourier_dilation hc ξ)
  have hsym_int : MeasureTheory.Integrable (fun ξ : ℝ => (𝓕 K : ℝ → ℂ) (ξ / c)) :=
    (integrable_fourier_dilation (c := c⁻¹) hKF (inv_ne_zero hcne)).congr
      (Filter.Eventually.of_forall (fun ξ => by simp only []; rw [div_eq_inv_mul]))
  have hFt_int : MeasureTheory.Integrable (𝓕 (fun z : ℝ => (c : ℂ) * K (c * z))) :=
    hsym_int.congr (Filter.Eventually.of_forall (fun ξ => (congrFun hFt ξ).symm))
  have hinv : 𝓕⁻ (fun ξ : ℝ => (𝓕 K : ℝ → ℂ) (ξ / c))
      = (fun z : ℝ => (c : ℂ) * K (c * z)) := by
    have h := hKt_cont.fourierInv_fourier_eq hKt_int hFt_int
    have h2 : 𝓕⁻ (fun ξ : ℝ => (𝓕 K : ℝ → ℂ) (ξ / c))
        = 𝓕⁻ (𝓕 (fun z : ℝ => (c : ℂ) * K (c * z))) := by
      congr 1
      funext ξ
      exact (congrFun hFt ξ).symm
    rw [h2, h]
  rw [fourierInv_mul_fourier_eq_convolution hsym_int hg x, hinv]

lemma continuous_fourier_of_integrable_sep {f : ℝ → ℂ} (hf : MeasureTheory.Integrable f) :
    Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf

lemma mean_zero_dyadic_square_function {K : ℝ → ℂ} (hKc : Continuous K)
    (hK : MeasureTheory.Integrable K) (hKF : MeasureTheory.Integrable (𝓕 K)) {A : ℝ}
    (hA : ∀ ξ : ℝ, ∑' k : ℕ, ‖(𝓕 K) ((2:ℝ)^(-(k:ℝ)) * ξ)‖ₑ ^ (2:ℝ)
        ≤ ENNReal.ofReal (A^2))
    {g : ℝ → ℂ} (hg1 : MeasureTheory.Integrable g)
    (hg2 : MeasureTheory.MemLp g 2 MeasureTheory.volume) :
    ∫⁻ x, ∑' k : ℕ, ENNReal.ofReal
        ‖∫ y : ℝ, g y * (Complex.ofReal ((2:ℝ)^(k:ℝ)) *
          K (((2:ℝ)^(k:ℝ)) * (x - y)))‖ ^ (2:ℝ)
      ≤ ENNReal.ofReal (A^2) * ∫⁻ x, ENNReal.ofReal ‖g x‖ ^ (2:ℝ) := by
  have hFg_cont : Continuous (𝓕 g) := continuous_fourier_of_integrable_sep hg1
  have hFK_cont : Continuous (𝓕 K) := continuous_fourier_of_integrable_sep hK
  have hFgb : ∀ ξ : ℝ, ‖(𝓕 g) ξ‖ ≤ ∫ y, ‖g y‖ := by
    intro ξ
    rw [Real.fourier_eq]
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Circle.norm_smul]
  have hFg_top : MeasureTheory.MemLp (fun ξ : ℝ => (𝓕 g) ξ) ⊤ volume :=
    memLp_top_of_bound hFg_cont.aestronglyMeasurable _ (Filter.Eventually.of_forall hFgb)
  have hFg_two : MeasureTheory.MemLp (fun ξ : ℝ => (𝓕 g) ξ) 2 volume :=
    (MeasureTheory.Lp.memLp (𝓕 (hg2.toLp g))).ae_eq
      (fourier_toLp_ae_eq_fourier_of_memLp (memLp_one_iff_integrable.mpr hg1) hg2)
  have hK1 : ∀ k : ℕ, MeasureTheory.MemLp (fun ξ : ℝ => (𝓕 K) (ξ / (2:ℝ)^(k:ℝ))) 1 volume := by
    intro k
    refine memLp_one_iff_integrable.mpr ((integrable_fourier_dilation
      (c := ((2:ℝ)^(k:ℝ))⁻¹) hKF (inv_ne_zero (by positivity))).congr
      (Filter.Eventually.of_forall (fun ξ => by simp only []; rw [div_eq_inv_mul])))
  have hKtop : ∀ k : ℕ, MeasureTheory.MemLp (fun ξ : ℝ => (𝓕 K) (ξ / (2:ℝ)^(k:ℝ))) ⊤ volume := by
    intro k
    refine memLp_top_of_bound ((hFK_cont.comp (by fun_prop :
      Continuous fun ξ : ℝ => ξ / (2:ℝ)^(k:ℝ)))).aestronglyMeasurable (∫ y, ‖K y‖) ?_
    refine Filter.Eventually.of_forall (fun ξ => ?_)
    rw [Real.fourier_eq]
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Circle.norm_smul]
  have hprod1 : ∀ k : ℕ, MeasureTheory.MemLp
      (fun ξ : ℝ => (𝓕 K) (ξ / (2:ℝ)^(k:ℝ)) * (𝓕 g) ξ) 1 volume := fun k =>
    hFg_top.mul' (hK1 k) |> fun h => h.ae_eq (Filter.Eventually.of_forall (fun ξ => mul_comm _ _))
  have hprod2 : ∀ k : ℕ, MeasureTheory.MemLp
      (fun ξ : ℝ => (𝓕 K) (ξ / (2:ℝ)^(k:ℝ)) * (𝓕 g) ξ) 2 volume := fun k =>
    hFg_two.mul' (hKtop k) |> fun h => h.ae_eq (Filter.Eventually.of_forall (fun ξ => mul_comm _ _))
  have hstep : ∀ k : ℕ,
      (∫⁻ x, ENNReal.ofReal
        ‖∫ y : ℝ, g y * (Complex.ofReal ((2:ℝ)^(k:ℝ)) *
          K (((2:ℝ)^(k:ℝ)) * (x - y)))‖ ^ (2:ℝ))
      = ∫⁻ ξ, ENNReal.ofReal
          ‖(𝓕 K) ((2:ℝ)^(-(k:ℝ)) * ξ) * (𝓕 g) ξ‖ ^ (2:ℝ) := by
    intro k
    set c : ℝ := (2:ℝ)^(k:ℝ) with hcdef
    have hcpos : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
    have hcpt : ∀ ξ : ℝ, (𝓕 K) ((2:ℝ)^(-(k:ℝ)) * ξ) = (𝓕 K) (ξ / c) := by
      intro ξ
      congr 1
      rw [hcdef, div_eq_inv_mul, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), mul_comm]
    have hk := lintegral_dilated_convolution_sq hKc hK hKF hg1 (c := c) hcpos
      (by rw [hcdef]; exact hprod1 k) (by rw [hcdef]; exact hprod2 k)
    have e1 : (∫⁻ x, ENNReal.ofReal ‖∫ y : ℝ, g y * (Complex.ofReal ((2:ℝ)^(k:ℝ)) *
          K (((2:ℝ)^(k:ℝ)) * (x - y)))‖ ^ (2:ℝ))
        = ∫⁻ x, ENNReal.ofReal ‖∫ y : ℝ, g y * ((c : ℂ) * K (c * (x - y)))‖ ^ (2:ℝ) := by
      rw [hcdef]
    rw [e1, hk]
    refine lintegral_congr (fun ξ => ?_)
    rw [hcpt ξ]
  have hmeas : ∀ k : ℕ, AEMeasurable (fun ξ : ℝ => ENNReal.ofReal
      ‖(𝓕 K) ((2:ℝ)^(-(k:ℝ)) * ξ) * (𝓕 g) ξ‖ ^ (2:ℝ)) volume := by
    intro k
    have h1 : Measurable (fun ξ : ℝ => ‖(𝓕 K) ((2:ℝ)^(-(k:ℝ)) * ξ) * (𝓕 g) ξ‖) :=
      ((hFK_cont.comp (by fun_prop : Continuous fun ξ : ℝ => (2:ℝ)^(-(k:ℝ)) * ξ)).measurable.mul
        hFg_cont.measurable).norm
    exact ((ENNReal.measurable_ofReal.comp h1).pow_const _).aemeasurable
  have hplanch : ∫⁻ x, ENNReal.ofReal ‖(𝓕 g) x‖ ^ (2:ℝ)
      = ∫⁻ x, ENNReal.ofReal ‖g x‖ ^ (2:ℝ) := by
    have hneg_mp : MeasurePreserving (fun x : ℝ => -x) volume volume :=
      Measure.measurePreserving_neg volume
    have hg1' : MeasureTheory.MemLp (fun x : ℝ => g (-x)) 1 volume :=
      (memLp_one_iff_integrable.mpr hg1).comp_measurePreserving hneg_mp
    have hg2' : MeasureTheory.MemLp (fun x : ℝ => g (-x)) 2 volume :=
      hg2.comp_measurePreserving hneg_mp
    have hpl := lintegral_fourierInv_eq hg1' hg2'
    have hpt : ∀ x : ℝ, 𝓕⁻ (fun y : ℝ => g (-y)) x = (𝓕 g) x := by
      intro x
      rw [Real.fourierInv_eq_fourier_comp_neg]
      simp
    calc ∫⁻ x, ENNReal.ofReal ‖(𝓕 g) x‖ ^ (2:ℝ)
        = ∫⁻ x, ENNReal.ofReal ‖𝓕⁻ (fun y : ℝ => g (-y)) x‖ ^ (2:ℝ) := by
          refine lintegral_congr (fun x => ?_); rw [hpt x]
      _ = ∫⁻ x, ENNReal.ofReal ‖g (-x)‖ ^ (2:ℝ) := hpl
      _ = ∫⁻ x, ENNReal.ofReal ‖g x‖ ^ (2:ℝ) :=
          lintegral_neg_eq_self (fun x : ℝ => ENNReal.ofReal ‖g x‖ ^ (2:ℝ))
  have htsum : ∀ ξ : ℝ, (∑' k : ℕ, ENNReal.ofReal
        ‖(𝓕 K) ((2:ℝ)^(-(k:ℝ)) * ξ) * (𝓕 g) ξ‖ ^ (2:ℝ))
      = (∑' k : ℕ, ‖(𝓕 K) ((2:ℝ)^(-(k:ℝ)) * ξ)‖ₑ ^ (2:ℝ)) * ‖(𝓕 g) ξ‖ₑ ^ (2:ℝ) := by
    intro ξ
    have hterm : ∀ k : ℕ, ENNReal.ofReal ‖(𝓕 K) ((2:ℝ)^(-(k:ℝ)) * ξ) * (𝓕 g) ξ‖ ^ (2:ℝ)
        = ‖(𝓕 K) ((2:ℝ)^(-(k:ℝ)) * ξ)‖ₑ ^ (2:ℝ) * ‖(𝓕 g) ξ‖ₑ ^ (2:ℝ) := by
      intro k
      have hA1 : ENNReal.ofReal ‖(𝓕 K) ((2:ℝ)^(-(k:ℝ)) * ξ) * (𝓕 g) ξ‖
          = ‖(𝓕 K) ((2:ℝ)^(-(k:ℝ)) * ξ) * (𝓕 g) ξ‖ₑ :=
        (sep_enorm_eq_ofReal_norm_aux _).symm
      calc ENNReal.ofReal ‖(𝓕 K) ((2:ℝ)^(-(k:ℝ)) * ξ) * (𝓕 g) ξ‖ ^ (2:ℝ)
          = ‖(𝓕 K) ((2:ℝ)^(-(k:ℝ)) * ξ) * (𝓕 g) ξ‖ₑ ^ (2:ℝ) := by rw [hA1]
        _ = (‖(𝓕 K) ((2:ℝ)^(-(k:ℝ)) * ξ)‖ₑ * ‖(𝓕 g) ξ‖ₑ) ^ (2:ℝ) := by rw [enorm_mul]
        _ = ‖(𝓕 K) ((2:ℝ)^(-(k:ℝ)) * ξ)‖ₑ ^ (2:ℝ) * ‖(𝓕 g) ξ‖ₑ ^ (2:ℝ) :=
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)
    rw [tsum_congr hterm, ENNReal.tsum_mul_right]
  have hint : ∀ k : ℕ, AEMeasurable (fun x : ℝ => ENNReal.ofReal
      ‖∫ y : ℝ, g y * (Complex.ofReal ((2:ℝ)^(k:ℝ)) *
        K (((2:ℝ)^(k:ℝ)) * (x - y)))‖ ^ (2:ℝ)) volume := by
    intro k
    set c : ℝ := (2:ℝ)^(k:ℝ) with hcdef
    have hcpos : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
    have hcont : Continuous (fun x : ℝ =>
        𝓕⁻ (fun ξ : ℝ => (𝓕 K : ℝ → ℂ) (ξ / c) * (𝓕 g : ℝ → ℂ) ξ) x) :=
      continuous_fourierInv_of_integrable_sep (memLp_one_iff_integrable.mp (by rw [hcdef]; exact hprod1 k))
    have hfun : (fun x : ℝ => ENNReal.ofReal ‖∫ y : ℝ, g y * ((c : ℂ) * K (c * (x - y)))‖ ^ (2:ℝ))
        = fun x : ℝ => ENNReal.ofReal
            ‖𝓕⁻ (fun ξ : ℝ => (𝓕 K : ℝ → ℂ) (ξ / c) * (𝓕 g : ℝ → ℂ) ξ) x‖ ^ (2:ℝ) := by
      funext x
      rw [convolution_dilation_eq_fourierInv hKc hK hKF hg1 hcpos x]
    rw [hfun]
    exact ((ENNReal.measurable_ofReal.comp hcont.measurable.norm).pow_const _).aemeasurable
  calc ∫⁻ x, ∑' k : ℕ, ENNReal.ofReal
        ‖∫ y : ℝ, g y * (Complex.ofReal ((2:ℝ)^(k:ℝ)) *
          K (((2:ℝ)^(k:ℝ)) * (x - y)))‖ ^ (2:ℝ)
      = ∑' k : ℕ, ∫⁻ x, ENNReal.ofReal
          ‖∫ y : ℝ, g y * (Complex.ofReal ((2:ℝ)^(k:ℝ)) *
            K (((2:ℝ)^(k:ℝ)) * (x - y)))‖ ^ (2:ℝ) := lintegral_tsum hint
    _ = ∑' k : ℕ, ∫⁻ ξ, ENNReal.ofReal
          ‖(𝓕 K) ((2:ℝ)^(-(k:ℝ)) * ξ) * (𝓕 g) ξ‖ ^ (2:ℝ) := tsum_congr hstep
    _ = ∫⁻ ξ, ∑' k : ℕ, ENNReal.ofReal
          ‖(𝓕 K) ((2:ℝ)^(-(k:ℝ)) * ξ) * (𝓕 g) ξ‖ ^ (2:ℝ) := (lintegral_tsum hmeas).symm
    _ = ∫⁻ ξ, (∑' k : ℕ, ‖(𝓕 K) ((2:ℝ)^(-(k:ℝ)) * ξ)‖ₑ ^ (2:ℝ)) * ‖(𝓕 g) ξ‖ₑ ^ (2:ℝ) :=
        lintegral_congr htsum
    _ ≤ ∫⁻ ξ, ENNReal.ofReal (A^2) * ‖(𝓕 g) ξ‖ₑ ^ (2:ℝ) :=
        lintegral_mono (fun ξ => mul_le_mul' (hA ξ) le_rfl)
    _ = ENNReal.ofReal (A^2) * ∫⁻ ξ, ‖(𝓕 g) ξ‖ₑ ^ (2:ℝ) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (A^2) * ∫⁻ x, ENNReal.ofReal ‖g x‖ ^ (2:ℝ) := by
        congr 1
        rw [← hplanch]
        refine lintegral_congr (fun ξ => ?_)
        rw [sep_enorm_eq_ofReal_norm_aux]


/-- `‖𝐞(t) − 1‖ ≤ 2π|t|`. -/
lemma norm_fourierChar_sub_one_le (t : ℝ) :
    ‖(Real.fourierChar t : ℂ) - 1‖ ≤ 4 * Real.pi * |t| := by
  rw [Real.fourierChar_apply]
  set x : ℂ := ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I with hx
  have hre : x.re = 0 := by simp [hx]
  have hnorm : ‖x‖ = 2 * Real.pi * |t| := by
    rw [hx, norm_mul, Complex.norm_I, mul_one]
    rw [show ‖((2 * Real.pi * t : ℝ) : ℂ)‖ = |2 * Real.pi * t| from
      RCLike.norm_ofReal (K := ℂ) _]
    rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  rcases lt_or_ge ‖x‖ 1 with h | h
  · have h2 := Complex.norm_exp_sub_one_le (le_of_lt h)
    rw [hnorm] at h2
    linarith
  · have h1 : ‖Complex.exp x - 1‖ ≤ 2 := by
      calc ‖Complex.exp x - 1‖ ≤ ‖Complex.exp x‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [Complex.norm_exp, hre, Real.exp_zero, norm_one]; norm_num
    have hx2 : (2:ℝ) ≤ 4 * Real.pi * |t| := by
      have hh := h
      rw [hnorm] at hh
      linarith
    linarith


/-- **Near-zero decay of the Fourier transform of a mean-zero kernel.** -/
lemma norm_fourier_le_const_mul_abs (K : ℝ → ℂ) (hK : MeasureTheory.Integrable K)
    (hK0 : ∫ x, K x = 0) (hxK : MeasureTheory.Integrable (fun x : ℝ => |x| * ‖K x‖)) (u : ℝ) :
    ‖(𝓕 K) u‖ ≤ 4 * Real.pi * |u| * ∫ x, |x| * ‖K x‖ := by
  have hc : Continuous fun x : ℝ => (Real.fourierChar (-(x * u)) : ℂ) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  have hInt1 : MeasureTheory.Integrable fun x : ℝ => K x * (Real.fourierChar (-(x * u)) : ℂ) :=
    hK.mul_bdd (c := 1) hc.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by rw [Circle.norm_coe]))
  have h1 : (𝓕 K) u = ∫ x, K x * (Real.fourierChar (-(x * u)) : ℂ) := by
    rw [Real.fourier_eq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.inner_apply, Circle.smul_def, smul_eq_mul]
    ring
  have h2 : (𝓕 K) u = ∫ x, ((Real.fourierChar (-(x * u)) : ℂ) - 1) * K x := by
    rw [h1]
    have hpid : ∀ x : ℝ, ((Real.fourierChar (-(x * u)) : ℂ) - 1) * K x
        = K x * (Real.fourierChar (-(x * u)) : ℂ) - K x := by intro x; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpid),
      MeasureTheory.integral_sub hInt1 hK, hK0, sub_zero]
  rw [h2]
  have hgint : MeasureTheory.Integrable fun x : ℝ => 4 * Real.pi * |u| * (|x| * ‖K x‖) :=
    hxK.const_mul _
  have hfint : MeasureTheory.Integrable fun x : ℝ =>
      ‖((Real.fourierChar (-(x * u)) : ℂ) - 1) * K x‖ := by
    refine hgint.mono' ((hc.sub continuous_const).aestronglyMeasurable.mul hK.1).norm ?_
    filter_upwards with x
    rw [norm_mul, Real.norm_of_nonneg (by positivity)]
    calc ‖(Real.fourierChar (-(x * u)) : ℂ) - 1‖ * ‖K x‖
        ≤ 4 * Real.pi * |-(x * u)| * ‖K x‖ :=
          mul_le_mul_of_nonneg_right (norm_fourierChar_sub_one_le _) (norm_nonneg _)
      _ = 4 * Real.pi * |u| * (|x| * ‖K x‖) := by rw [abs_neg, abs_mul]; ring
  calc ‖∫ x, ((Real.fourierChar (-(x * u)) : ℂ) - 1) * K x‖
      ≤ ∫ x, ‖((Real.fourierChar (-(x * u)) : ℂ) - 1) * K x‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x, 4 * Real.pi * |u| * (|x| * ‖K x‖) := by
        refine integral_mono_ae hfint hgint ?_
        filter_upwards with x
        rw [norm_mul]
        calc ‖(Real.fourierChar (-(x * u)) : ℂ) - 1‖ * ‖K x‖
            ≤ 4 * Real.pi * |-(x * u)| * ‖K x‖ :=
              mul_le_mul_of_nonneg_right (norm_fourierChar_sub_one_le _) (norm_nonneg _)
          _ = 4 * Real.pi * |u| * (|x| * ‖K x‖) := by rw [abs_neg, abs_mul]; ring
    _ = 4 * Real.pi * |u| * ∫ x, |x| * ‖K x‖ := by
        rw [← MeasureTheory.integral_const_mul]


/-- The tent (de la Vallée Poussin) function `x ↦ max 0 (1 - |x|)`, of integral `1`. -/
noncomputable def tent (x : ℝ) : ℝ := max 0 (1 - |x|)

lemma tent_nonneg (x : ℝ) : 0 ≤ tent x := le_max_left _ _
lemma tent_le_one (x : ℝ) : tent x ≤ 1 :=
  max_le (by norm_num) (by linarith [abs_nonneg x])
lemma tent_continuous : Continuous tent := by unfold tent; fun_prop
lemma tent_eq_zero_of_one_le_abs {x : ℝ} (h : 1 ≤ |x|) : tent x = 0 := by
  unfold tent; exact max_eq_left (by linarith)
lemma tent_eq_of_abs_le_one {x : ℝ} (h : |x| ≤ 1) : tent x = 1 - |x| := by
  unfold tent; exact max_eq_right (by linarith)
lemma tent_support_subset : Function.support tent ⊆ Set.Icc (-1:ℝ) 1 := by
  intro x hx
  rw [Set.mem_Icc]
  by_contra hcon
  rw [not_and_or] at hcon
  rcases hcon with h | h
  · push Not at h
    exact hx (tent_eq_zero_of_one_le_abs (by rw [abs_of_neg (by linarith)]; linarith))
  · push Not at h
    exact hx (tent_eq_zero_of_one_le_abs (by rw [abs_of_pos (by linarith)]; linarith))
lemma hasCompactSupport_tent : HasCompactSupport tent :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc tent_support_subset
lemma integrable_tent : Integrable tent :=
  tent_continuous.integrable_of_hasCompactSupport hasCompactSupport_tent

lemma intervalIntegral_tent : ∫ x in (-1:ℝ)..1, tent x = 1 := by
  rw [intervalIntegral.integral_congr (fun x hx => tent_eq_of_abs_le_one ?_)]
  · have h := triangular_fourier 1 (by norm_num) 0
    simp only [Int.cast_zero, mul_zero, neg_zero, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, mul_one, Real.sinc_zero, one_pow, Complex.ofReal_one, div_one] at h
    have h2 : ((↑(∫ x in (-1:ℝ)..1, (fun x : ℝ => 1 - |x|) x) : ℂ)) = 1 := by
      rw [← intervalIntegral.integral_ofReal (a := -1) (b := 1) (f := fun x : ℝ => 1 - |x|)]
      simpa using h
    exact_mod_cast h2
  · rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] at hx
    exact abs_le.mpr ⟨hx.1, hx.2⟩

lemma integral_tent : ∫ x, tent x = 1 := by
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Set.Icc (-1:ℝ) 1) (f := tent) (fun x hx => ?_)]
  · rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
    exact intervalIntegral_tent
  · rw [Set.mem_Icc, not_and_or] at hx
    rcases hx with h | h
    · push Not at h
      exact tent_eq_zero_of_one_le_abs (by rw [abs_of_neg (by linarith)]; linarith)
    · push Not at h
      exact tent_eq_zero_of_one_le_abs (by rw [abs_of_pos (by linarith)]; linarith)

/-- The mean-zero remainder `x ↦ Ψ x − (∫Ψ)·Λ x`, with `Λ` the tent function. -/
noncomputable def meanZeroPart (Ψ : SchwartzMap ℝ ℂ) : ℝ → ℂ :=
  fun x => (Ψ : ℝ → ℂ) x - (∫ t, (Ψ : ℝ → ℂ) t) * (tent x : ℂ)

lemma continuous_meanZeroPart (Ψ : SchwartzMap ℝ ℂ) : Continuous (meanZeroPart Ψ) :=
  Ψ.continuous.sub (continuous_const.mul (Complex.continuous_ofReal.comp tent_continuous))

lemma integrable_meanZeroPart (Ψ : SchwartzMap ℝ ℂ) : Integrable (meanZeroPart Ψ) :=
  Ψ.integrable.sub ((MeasureTheory.Integrable.ofReal integrable_tent).const_mul _)

-- NOTE (Lean gotcha, cost two rounds): when a goal has been produced by `unfold`/`change` on a
-- `def`, its integrand stays *beta-unreduced* (`(fun x => ...) x`), and `rw` then silently fails to
-- find the pattern even though the goal prints correctly.  `simp only [<def>]` beta-reduces and
-- fixes it (see `integral_meanZeroPart`).  Same failure mode bit `integral_ofReal`: the *global*
-- lemma would not fire on `∫ x, ↑(tent x)`, while the *interval* version
-- `intervalIntegral.integral_ofReal` did — mirror `intervalIntegral_tent`'s glue instead of fighting
-- the global form.

lemma integral_tent_complex : ∫ x, (tent x : ℂ) = 1 := by
  have hIcc : (∫ x in (-1:ℝ)..1, (tent x : ℂ)) = 1 := by
    rw [intervalIntegral.integral_ofReal (f := tent) (a := -1) (b := 1), intervalIntegral_tent,
      Complex.ofReal_one]
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Set.Icc (-1:ℝ) 1) (f := fun x => (tent x : ℂ)) (fun x hx => ?_)]
  · rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
    exact hIcc
  · rw [Set.mem_Icc, not_and_or] at hx
    rcases hx with h | h
    · push Not at h
      rw [tent_eq_zero_of_one_le_abs (by rw [abs_of_neg (by linarith)]; linarith)]
      simp
    · push Not at h
      rw [tent_eq_zero_of_one_le_abs (by rw [abs_of_pos (by linarith)]; linarith)]
      simp

lemma integral_meanZeroPart (Ψ : SchwartzMap ℝ ℂ) : ∫ x, meanZeroPart Ψ x = 0 := by
  have h2 : Integrable fun x : ℝ => (∫ t, (Ψ : ℝ → ℂ) t) * (tent x : ℂ) :=
    (MeasureTheory.Integrable.ofReal integrable_tent).const_mul _
  simp only [meanZeroPart]
  rw [MeasureTheory.integral_sub Ψ.integrable h2, integral_const_mul, integral_tent_complex,
    mul_one, sub_self]

/-- Pointwise split of the mean-zero remainder. -/
lemma norm_meanZeroPart_le (Ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖meanZeroPart Ψ x‖ ≤ ‖(Ψ : ℝ → ℂ) x‖ + ‖∫ t, (Ψ : ℝ → ℂ) t‖ * tent x := by
  simp only [meanZeroPart]
  calc ‖(Ψ : ℝ → ℂ) x - (∫ t, (Ψ : ℝ → ℂ) t) * (tent x : ℂ)‖
      ≤ ‖(Ψ : ℝ → ℂ) x‖ + ‖(∫ t, (Ψ : ℝ → ℂ) t) * (tent x : ℂ)‖ := norm_sub_le _ _
    _ = ‖(Ψ : ℝ → ℂ) x‖ + ‖∫ t, (Ψ : ℝ → ℂ) t‖ * tent x := by
        rw [norm_mul]
        congr 1
        rw [show ‖((tent x : ℝ) : ℂ)‖ = |tent x| from RCLike.norm_ofReal _,
          abs_of_nonneg (tent_nonneg x)]

lemma hasCompactSupport_abs_mul_tent : HasCompactSupport fun x : ℝ => |x| * tent x :=
  hasCompactSupport_tent.mono (fun x hx h => hx (by simp [h]))

lemma integrable_abs_mul_tent : Integrable fun x : ℝ => |x| * tent x :=
  (continuous_abs.mul tent_continuous).integrable_of_hasCompactSupport hasCompactSupport_abs_mul_tent



lemma integrable_abs_mul_norm_schwartz (Ψ : SchwartzMap ℝ ℂ) :
    Integrable fun x : ℝ => |x| * ‖(Ψ : ℝ → ℂ) x‖ := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x : ℝ, (1 + |x|)^3 * ‖(Ψ : ℝ → ℂ) x‖ ≤ C := by
    refine ⟨2 ^ ((3, 0) : ℕ × ℕ).1 *
      ((Finset.Iic (3, 0)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) Ψ, fun x => ?_⟩
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (3, 0)) (k := 3) (n := 0)
      le_rfl le_rfl Ψ x
    rw [Real.norm_eq_abs] at h
    have hnorm : (1 + |x|)^3 * ‖(Ψ : ℝ → ℂ) x‖
        ≤ (1 + |x|)^3 * ‖iteratedFDeriv ℝ 0 (⇑Ψ) x‖ := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have h1 : (iteratedFDeriv ℝ 0 (⇑Ψ) x) (0 : Fin 0 → ℝ) = (Ψ : ℝ → ℂ) x :=
        iteratedFDeriv_zero_apply 0
      calc ‖(Ψ : ℝ → ℂ) x‖ = ‖(iteratedFDeriv ℝ 0 (⇑Ψ) x) (0 : Fin 0 → ℝ)‖ := by rw [h1]
        _ ≤ ‖iteratedFDeriv ℝ 0 (⇑Ψ) x‖ * ∏ i : Fin 0, ‖(0 : Fin 0 → ℝ) i‖ :=
            ContinuousMultilinearMap.le_opNorm _ _
        _ = ‖iteratedFDeriv ℝ 0 (⇑Ψ) x‖ := by simp
    linarith [h, hnorm]
  have hCnn : 0 ≤ C := le_trans (by positivity : (0:ℝ) ≤ (1 + |0|)^3 * ‖(Ψ : ℝ → ℂ) 0‖) (hC 0)
  have hbdd : ∀ x : ℝ, |x| * ‖(Ψ : ℝ → ℂ) x‖ ≤ C * (1 + x^2)⁻¹ := by
    intro x
    have hpos : 0 < (1 + |x|)^3 := by positivity
    have h1 : ‖(Ψ : ℝ → ℂ) x‖ ≤ C / (1 + |x|)^3 := by
      rw [le_div_iff₀ hpos]; linarith [hC x]
    calc |x| * ‖(Ψ : ℝ → ℂ) x‖ ≤ |x| * (C / (1 + |x|)^3) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg x)
      _ = C * (|x| / (1 + |x|)^3) := by ring
      _ ≤ C * (1 + x^2)⁻¹ := by
          refine mul_le_mul_of_nonneg_left ?_ hCnn
          rw [div_le_iff₀ hpos, inv_eq_one_div,
            show (1:ℝ) / (1 + x^2) * (1 + |x|)^3 = (1 + |x|)^3 / (1 + x^2) by ring,
            le_div_iff₀ (by positivity : (0:ℝ) < 1 + x^2), ← sq_abs x]
          nlinarith [abs_nonneg x, sq_nonneg (|x| - 1)]
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul C) ?_ ?_
  · exact ((continuous_abs.mul Ψ.continuous.norm).aestronglyMeasurable)
  · filter_upwards with x
    rw [Real.norm_of_nonneg (show (0:ℝ) ≤ |x| * ‖(Ψ : ℝ → ℂ) x‖ by positivity)]
    exact hbdd x



/-- **`x ↦ |x|·‖K x‖` is integrable for the mean-zero remainder `K = Ψ − (∫Ψ)Λ`.** -/
lemma integrable_abs_mul_norm_meanZeroPart (Ψ : SchwartzMap ℝ ℂ) :
    Integrable fun x : ℝ => |x| * ‖meanZeroPart Ψ x‖ := by
  have hbdd : ∀ x : ℝ, |x| * ‖meanZeroPart Ψ x‖
      ≤ |x| * ‖(Ψ : ℝ → ℂ) x‖ + ‖∫ t, (Ψ : ℝ → ℂ) t‖ * (|x| * tent x) := by
    intro x
    calc |x| * ‖meanZeroPart Ψ x‖
        ≤ |x| * (‖(Ψ : ℝ → ℂ) x‖ + ‖∫ t, (Ψ : ℝ → ℂ) t‖ * tent x) :=
          mul_le_mul_of_nonneg_left (norm_meanZeroPart_le Ψ x) (abs_nonneg x)
      _ = |x| * ‖(Ψ : ℝ → ℂ) x‖ + ‖∫ t, (Ψ : ℝ → ℂ) t‖ * (|x| * tent x) := by ring
  refine Integrable.mono' (g := fun x : ℝ =>
      |x| * ‖(Ψ : ℝ → ℂ) x‖ + ‖∫ t, (Ψ : ℝ → ℂ) t‖ * (|x| * tent x)) ?_ ?_ ?_
  · exact (integrable_abs_mul_norm_schwartz Ψ).add (integrable_abs_mul_tent.const_mul _)
  · exact (continuous_abs.mul (continuous_meanZeroPart Ψ).norm).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_of_nonneg (show (0:ℝ) ≤ |x| * ‖meanZeroPart Ψ x‖ by positivity)]
    exact hbdd x



/-- **Geometric annulus separation.**  If `0 < a` and `b < 2 * a`, then a real number `x` can lie
in at most one of the geometrically shrinking annuli `(a·2^{-j}, b·2^{-j}]`: if `x` lies in the
`k`-th annulus and above the lower bound of the `j`-th one, then `k ≤ j`.

This is the disjointness fact behind the square-function bound for the boundary layer of the
band-pass maximal estimate (the "annuli" of the smooth/boundary splitting have radii in a fixed
ratio `< 2`). -/
lemma le_of_geometric_annulus_mem {a b x : ℝ} (ha : 0 < a) (hb : b < 2 * a) {j k : ℕ}
    (hj : a * (2 : ℝ) ^ (-(j : ℝ)) < x) (hk : x ≤ b * (2 : ℝ) ^ (-(k : ℝ))) : k ≤ j := by
  have hxk : a * (2 : ℝ) ^ (-(j : ℝ)) < b * (2 : ℝ) ^ (-(k : ℝ)) := lt_of_lt_of_le hj hk
  have e1 : (2 : ℝ) ^ (-(j : ℝ)) * (2 : ℝ) ^ (k : ℝ) = (2 : ℝ) ^ ((k : ℝ) - (j : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have e2 : (2 : ℝ) ^ (-(k : ℝ)) * (2 : ℝ) ^ (k : ℝ) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    simp
  have h1 : a * (2 : ℝ) ^ ((k : ℝ) - (j : ℝ)) < b := by
    calc a * (2 : ℝ) ^ ((k : ℝ) - (j : ℝ))
        = (a * (2 : ℝ) ^ (-(j : ℝ))) * (2 : ℝ) ^ (k : ℝ) := by rw [mul_assoc, e1]
      _ < (b * (2 : ℝ) ^ (-(k : ℝ))) * (2 : ℝ) ^ (k : ℝ) :=
          mul_lt_mul_of_pos_right hxk (by positivity)
      _ = b := by rw [mul_assoc, e2, mul_one]
  have h3 : (2 : ℝ) ^ ((k : ℝ) - (j : ℝ)) < b / a := by
    rw [lt_div_iff₀ ha]
    linarith [h1, mul_comm ((2 : ℝ) ^ ((k : ℝ) - (j : ℝ))) a]
  have h4 : (2 : ℝ) ^ ((k : ℝ) - (j : ℝ)) < (2 : ℝ) ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    calc (2 : ℝ) ^ ((k : ℝ) - (j : ℝ)) < b / a := h3
      _ < 2 * a / a := div_lt_div_of_pos_right hb ha
      _ = 2 := by field_simp
  have h5 : (k : ℝ) - (j : ℝ) < 1 :=
    (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp h4
  have h6 : (k : ℕ) < j + 1 := by
    have : (k : ℝ) < ((j + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  omega

/-! ## The one-sided geometric maximal at an arbitrary point

The commons `Commons.Analysis.Fourier.one_sided_geometric_maximal_l2` bounds the maximal over the
dyadic scales of the band-pass onto the one-sided interval `[0, 2^{-j-1}]`.  Each tile of the
boundary layer of the band-pass maximal estimate is a one-sided interval attached to a *fixed*
point of the fundamental domain (possibly the boundary `±1/2` itself), so we need the same bound
for the interval `[a, a + 2^{-j-1}]` with `a : ℝ` arbitrary, *uniformly in `a`*.  This follows from
the commons lemma by the frequency-shift (= modulation) identity: the interval `[a,a+h]` applied to
`f` equals (up to the unimodular factor `e^{-iax}`) the interval `[0,h]` applied to the modulated
function `y ↦ e^{iay} f y`, and modulation is an isometry of `L²`. -/

/-- **Pointwise shift identity.**  The oscillatory integral over `[a, a+h]` is the integral over
`[0,h]` times `e^{iay}` and `e^{-iax}`. -/
lemma interval_shift_pointwise (a x : ℝ) {h : ℝ} (y : ℝ) :
    (∫ θ in a..(a + h), Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))
      = Complex.exp (-(Complex.I * (a : ℂ) * (x : ℂ))) *
        (Complex.exp (Complex.I * (a : ℂ) * (y : ℂ)) *
          (∫ θ in (0 : ℝ)..h,
            Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))) := by
  have hsub : (∫ θ in a..(a + h), Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))
      = ∫ η in (0 : ℝ)..h,
          Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (((a + η : ℝ)) : ℂ))) := by
    have h := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := h) (d := a)
      (fun θ : ℝ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))
    simp only [add_zero] at h
    exact h.symm
  rw [hsub]
  have hpt : ∀ η : ℝ,
      Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (((a + η : ℝ)) : ℂ)))
        = Complex.exp (-(Complex.I * (a : ℂ) * (x : ℂ))) *
          (Complex.exp (Complex.I * (a : ℂ) * (y : ℂ)) *
            Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (η : ℂ)))) := by
    intro η
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [intervalIntegral.integral_congr (fun η _ => hpt η)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- The modulation `y ↦ e^{iay}` preserves the `L²` norm. -/
lemma lintegral_enorm_sq_modulation (a : ℝ) (f : ℝ → ℂ) :
    ∫⁻ y : ℝ, ‖Complex.exp (Complex.I * (a : ℂ) * ((y : ℝ) : ℂ)) * f y‖ₑ ^ (2 : ℝ)
      = ∫⁻ y : ℝ, ‖f y‖ₑ ^ (2 : ℝ) := by
  refine lintegral_congr fun y => ?_
  have h1 : ‖Complex.exp (Complex.I * (a : ℂ) * (y : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (Complex.I * (a : ℂ) * (y : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero]
  rw [enorm_mul]
  have h2 : ‖Complex.exp (Complex.I * (a : ℂ) * (y : ℂ))‖ₑ = 1 := by
    rw [show ‖Complex.exp (Complex.I * (a : ℂ) * (y : ℂ))‖ₑ
        = ENNReal.ofReal ‖Complex.exp (Complex.I * (a : ℂ) * (y : ℂ))‖ from
          Commons.Analysis.Fourier.enorm_eq_ofReal_norm _, h1, ENNReal.ofReal_one]
  rw [h2, one_mul]

/-- The modulation `y ↦ e^{iay} f y` of an `L²` function is in `L²`. -/
lemma memLp_modulation (a : ℝ) {f : ℝ → ℂ} (hf : MeasureTheory.MemLp f 2 MeasureTheory.volume) :
    MeasureTheory.MemLp (fun y : ℝ => Complex.exp (Complex.I * (a : ℂ) * ((y : ℝ) : ℂ)) * f y)
      2 MeasureTheory.volume := by
  have hb : MeasureTheory.MemLp
      (fun y : ℝ => Complex.exp (Complex.I * (a : ℂ) * ((y : ℝ) : ℂ))) ⊤ MeasureTheory.volume := by
    refine MeasureTheory.memLp_top_of_bound ?_ 1 (Filter.Eventually.of_forall fun y => ?_)
    · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    · rw [Complex.norm_exp]
      have hre : (Complex.I * (a : ℂ) * (y : ℂ)).re = 0 := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [hre, Real.exp_zero]
  exact hb.mul hf

open Commons.Analysis.Fourier in
/-- **One-sided geometric maximal at an arbitrary point.**  The commons estimate for the interval
`[0, 2^{-j-1}]` holds verbatim for `[a, a + 2^{-j-1}]`, uniformly in `a : ℝ`. -/
theorem one_sided_geometric_maximal_l2_shift :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (f : ℝ → ℂ),
      MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
      ∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, f y *
          (∫ θ in a..(a + (2 : ℝ) ^ (-(j : ℝ) - 1)),
            Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ) ^ (2 : ℝ)
        ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)
      ≤ ENNReal.ofReal (C ^ 2) *
          ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  obtain ⟨C, hC, h⟩ := one_sided_geometric_maximal_l2
  refine ⟨C, hC, fun a f hf => ?_⟩
  set g : ℝ → ℂ := fun y => Complex.exp (Complex.I * (a : ℂ) * ((y : ℝ) : ℂ)) * f y with hg
  have hg2 : MeasureTheory.MemLp g 2 MeasureTheory.volume := memLp_modulation a hf
  have hkey : ∀ (j : ℕ) (x : ℝ),
      (∫ y : ℝ, f y * (∫ θ in a..(a + (2 : ℝ) ^ (-(j : ℝ) - 1)),
          Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))))
        = Complex.exp (-(Complex.I * (a : ℂ) * (x : ℂ))) *
          (∫ y : ℝ, g y * (∫ θ in (0 : ℝ)..((2 : ℝ) ^ (-(j : ℝ) - 1)),
              Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))) := by
    intro j x
    have h1 : ∀ y : ℝ, f y * (∫ θ in a..(a + (2 : ℝ) ^ (-(j : ℝ) - 1)),
            Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))
        = Complex.exp (-(Complex.I * (a : ℂ) * (x : ℂ))) *
          (g y * (∫ θ in (0 : ℝ)..((2 : ℝ) ^ (-(j : ℝ) - 1)),
              Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))) := by
      intro y
      rw [interval_shift_pointwise a x y]
      simp only [hg]
      ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h1),
      MeasureTheory.integral_const_mul]
  have hnorm : ∀ (j : ℕ) (x : ℝ), ‖∫ y : ℝ, f y *
        (∫ θ in a..(a + (2 : ℝ) ^ (-(j : ℝ) - 1)),
          Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ
      = ‖∫ y : ℝ, g y * (∫ θ in (0 : ℝ)..((2 : ℝ) ^ (-(j : ℝ) - 1)),
          Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ := by
    intro j x
    rw [hkey j x, enorm_mul]
    have h1 : ‖Complex.exp (-(Complex.I * (a : ℂ) * (x : ℂ)))‖ = 1 := by
      rw [Complex.norm_exp]
      have hre : (-(Complex.I * (a : ℂ) * (x : ℂ))).re = 0 := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [hre, Real.exp_zero]
    have h2 : ‖Complex.exp (-(Complex.I * (a : ℂ) * (x : ℂ)))‖ₑ = 1 := by
      rw [show ‖Complex.exp (-(Complex.I * (a : ℂ) * (x : ℂ)))‖ₑ
          = ENNReal.ofReal ‖Complex.exp (-(Complex.I * (a : ℂ) * (x : ℂ)))‖ from
            Commons.Analysis.Fourier.enorm_eq_ofReal_norm _, h1, ENNReal.ofReal_one]
    rw [h2, one_mul]
  calc ∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, f y *
        (∫ θ in a..(a + (2 : ℝ) ^ (-(j : ℝ) - 1)),
          Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ) ^ (2 : ℝ)
      = ∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, g y *
          (∫ θ in (0 : ℝ)..((2 : ℝ) ^ (-(j : ℝ) - 1)),
            Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ) ^ (2 : ℝ) := by
        refine lintegral_congr fun x => ?_
        exact congrArg (fun t : ℝ≥0∞ => t ^ (2 : ℝ)) (iSup_congr fun j => hnorm j x)
    _ ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) := h g hg2
    _ = ENNReal.ofReal (C ^ 2) * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) := by
        rw [lintegral_enorm_sq_modulation a f]

namespace BandLift

/-- The representative of `t` modulo `1` in `Ico (-1/2) (1/2)`. -/
noncomputable def resRep (t : ℝ) : ℝ := Int.fract (t + 1 / 2) - 1 / 2

lemma resRep_mem (t : ℝ) : resRep t ∈ Set.Ico (-(1 / 2) : ℝ) (1 / 2) := by
  have h1 : 0 ≤ Int.fract (t + 1 / 2) := Int.fract_nonneg _
  have h2 : Int.fract (t + 1 / 2) < 1 := Int.fract_lt_one _
  simp only [resRep, Set.mem_Ico]
  constructor <;> linarith

lemma resRep_int (t : ℝ) : ∃ n : ℤ, resRep t = t + n := by
  refine ⟨-(⌊t + 1 / 2⌋), ?_⟩
  have h := Int.fract_add_floor (t + 1 / 2)
  simp only [resRep]
  push_cast
  linarith [h]

/-- The lifted frequency set: the representatives of `-(lam k)` modulo `1`, together with their
two integer neighbours. -/
noncomputable def liftedSet (N : ℕ) (lam : Fin N → ℝ) : Finset ℝ :=
  Finset.univ.biUnion fun k : Fin N =>
    (Finset.Icc (-1 : ℤ) 1).image fun m : ℤ => resRep (-(lam k)) - (m : ℝ)

lemma mem_liftedSet {N : ℕ} {lam : Fin N → ℝ} {a : ℝ} :
    a ∈ liftedSet N lam ↔ ∃ k : Fin N, ∃ m : ℤ, m ∈ Finset.Icc (-1 : ℤ) 1 ∧
      resRep (-(lam k)) - (m : ℝ) = a := by
  simp only [liftedSet, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]

lemma liftedSet_card_le (N : ℕ) (lam : Fin N → ℝ) : (liftedSet N lam).card ≤ 3 * N := by
  have h3 : (Finset.Icc (-1 : ℤ) 1).card = 3 := by decide
  calc (liftedSet N lam).card
      ≤ ∑ k ∈ Finset.univ, ((Finset.Icc (-1 : ℤ) 1).image
          (fun m : ℤ => resRep (-(lam k)) - (m : ℝ))).card := Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ Finset.univ, 3 := Finset.sum_le_sum (fun k _ =>
          le_trans Finset.card_image_le (le_of_eq h3))
    _ = 3 * N := by simp [Finset.sum_const, Finset.card_univ, mul_comm]

lemma int_mem_Icc_of_abs_le (z : ℤ) (h : |((z : ℤ) : ℝ)| ≤ 3 / 2) :
    z ∈ Finset.Icc (-1 : ℤ) 1 := by
  rw [Finset.mem_Icc]
  rw [abs_le] at h
  constructor
  · by_contra hc
    push Not at hc
    have h2 : ((z : ℤ) : ℝ) ≤ -2 := by exact_mod_cast (by omega : z ≤ (-2 : ℤ))
    linarith [h.1]
  · by_contra hc
    push Not at hc
    have h2 : (2 : ℝ) ≤ ((z : ℤ) : ℝ) := by exact_mod_cast (by omega : (2 : ℤ) ≤ z)
    linarith [h.2]

lemma sep_dyadic_pos (j : ℕ) : 0 < (2 : ℝ) ^ (-(j : ℝ) - 1) := Real.rpow_pos_of_pos (by norm_num) _

lemma sep_dyadic_le_half (j : ℕ) : (2 : ℝ) ^ (-(j : ℝ) - 1) ≤ 1 / 2 := by
  have h : (-(j : ℝ) - 1) ≤ (-1 : ℝ) := by
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  calc (2 : ℝ) ^ (-(j : ℝ) - 1) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h
    _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num

/-- **The periodisation (lifting) lemma.**  On the fundamental domain `[-1/2, 1/2]`, the
`r`-neighbourhood of the coset `⋃_k (lam k + ℤ)` (`r ≤ 1/2`) is the `r`-neighbourhood of the
finite lifted set `liftedSet N lam`. -/
lemma periodic_set_eq {N : ℕ} (lam : Fin N → ℝ) {r : ℝ} (hrpos : 0 < r) (hr : r ≤ 1 / 2)
    {ξ : ℝ} (hξ : ξ ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)) :
    (∃ k : Fin N, ∃ l : ℤ, |ξ + (l : ℝ) + lam k| ≤ r)
      ↔ (∃ a ∈ liftedSet N lam, |ξ - a| ≤ r) := by
  have hbound : ∀ k : Fin N, |ξ - resRep (-(lam k))| ≤ 1 := by
    intro k
    have h := resRep_mem (-(lam k))
    have h1 : -(1 / 2 : ℝ) ≤ resRep (-(lam k)) := h.1
    have h2 : resRep (-(lam k)) < 1 / 2 := h.2
    rw [abs_le]
    constructor <;> linarith [h1, h2, hξ.1, hξ.2]
  constructor
  · rintro ⟨k, l, hl⟩
    obtain ⟨n, hn⟩ := resRep_int (-(lam k))
    have hN : resRep (-(lam k)) + lam k = (n : ℝ) := by
      have h : resRep (-(lam k)) = -(lam k) + n := hn
      rw [h]; push_cast; ring
    have hz : |(((l + n : ℤ) : ℝ))| ≤ 3 / 2 := by
      have heq : ((l + n : ℤ) : ℝ) = (ξ + (l : ℝ) + lam k) - (ξ - resRep (-(lam k))) := by
        push_cast; linarith [hN]
      rw [heq]
      have habs : |(ξ + (l : ℝ) + lam k) - (ξ - resRep (-(lam k)))|
          ≤ |ξ + (l : ℝ) + lam k| + |ξ - resRep (-(lam k))| := by
        rw [sub_eq_add_neg]
        simpa [abs_sub_comm] using abs_add_le (ξ + (l : ℝ) + lam k) (-(ξ - resRep (-(lam k))))
      calc |(ξ + (l : ℝ) + lam k) - (ξ - resRep (-(lam k)))|
          ≤ |ξ + (l : ℝ) + lam k| + |ξ - resRep (-(lam k))| := habs
        _ ≤ r + 1 := by linarith [hl, hbound k]
        _ ≤ 3 / 2 := by linarith
    refine ⟨resRep (-(lam k)) - ((l + n : ℤ) : ℝ), ?_, ?_⟩
    · rw [mem_liftedSet]
      exact ⟨k, l + n, int_mem_Icc_of_abs_le _ hz, rfl⟩
    · have heq : ξ - (resRep (-(lam k)) - ((l + n : ℤ) : ℝ)) = ξ + (l : ℝ) + lam k := by
        push_cast; linarith [hN]
      rw [heq]; exact hl
  · rintro ⟨a, ha, ha'⟩
    rw [mem_liftedSet] at ha
    obtain ⟨k, m, hm, rfl⟩ := ha
    obtain ⟨n, hn⟩ := resRep_int (-(lam k))
    have hN : resRep (-(lam k)) + lam k = (n : ℝ) := by
      have h : resRep (-(lam k)) = -(lam k) + n := hn
      rw [h]; push_cast; ring
    refine ⟨k, m - n, ?_⟩
    have heq : ξ + ((m - n : ℤ) : ℝ) + lam k
        = ξ - (resRep (-(lam k)) - (m : ℝ)) := by
      push_cast; linarith [hN]
    rw [heq]; exact ha'

/-- The band-pass operator with frequency set `C`: keep, in the Fourier transform, only the
frequencies in `C ∩ [-1/2, 1/2]`, and invert. -/
noncomputable def bandPass (C : Set ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ ξ in (-(1 / 2) : ℝ)..(1 / 2),
    (𝓕 g) ξ * Set.indicator C (fun _ => (1 : ℂ)) ξ *
      Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ))

/-- Band-pass operators with frequency sets that agree on the fundamental domain agree. -/
lemma bandPass_congr (g : ℝ → ℂ) {C D : Set ℝ}
    (h : ∀ ξ ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2), (ξ ∈ C ↔ ξ ∈ D)) :
    ∀ x : ℝ, bandPass C g x = bandPass D g x := by
  intro x
  refine intervalIntegral.integral_congr (fun ξ hξ => ?_)
  rw [Set.uIcc_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)] at hξ
  have hidx : Set.indicator C (fun _ => (1 : ℂ)) ξ = Set.indicator D (fun _ => (1 : ℂ)) ξ := by
    by_cases hC : ξ ∈ C
    · rw [Set.indicator_of_mem hC, Set.indicator_of_mem ((h ξ hξ).mp hC)]
    · rw [Set.indicator_of_notMem hC, Set.indicator_of_notMem]
      intro hcon
      exact hC ((h ξ hξ).mpr hcon)
  rw [hidx]

/-- `bandPass C f` is the inverse Fourier integral of `1_C · 1_{[-1/2,1/2]} · 𝓕 f`. -/
lemma bandPass_eq_fourierInv {C : Set ℝ} (f : ℝ → ℂ)
    (hf : MeasureTheory.Integrable f) (x : ℝ) :
    bandPass C f x
      = 𝓕⁻ (fun ξ : ℝ => Set.indicator C (fun _ => (1 : ℂ)) ξ *
          Set.indicator (Set.Icc (-(1 / 2) : ℝ) (1 / 2)) (fun _ => (1 : ℂ)) ξ *
          (𝓕 f) ξ) x := by
  classical
  have harg : ∀ ξ : ℝ,
      (↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I
        = 2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ) := by
    intro ξ
    rw [Real.inner_apply]
    push_cast
    ring
  rw [bandPass, Real.fourierInv_eq']
  rw [intervalIntegral.integral_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
  refine MeasureTheory.integral_congr_ae ?_
  have hnull : ∀ᵐ ξ : ℝ ∂MeasureTheory.volume, ξ ≠ (-(1 / 2) : ℝ) := by
    rw [MeasureTheory.ae_iff]
    simpa using MeasureTheory.measure_singleton (-(1 / 2) : ℝ)
  filter_upwards [hnull] with ξ hξ
  have hmem : ξ ∈ Set.Ioc (-(1 / 2) : ℝ) (1 / 2) ↔ ξ ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) := by
    constructor
    · intro h; exact ⟨le_of_lt h.1, h.2⟩
    · intro h
      rcases eq_or_lt_of_le h.1 with h1 | h1
      · exact absurd h1.symm hξ
      · exact ⟨h1, h.2⟩
  simp only [Set.indicator_apply]
  by_cases hI : ξ ∈ Set.Ioc (-(1 / 2) : ℝ) (1 / 2)
  · rw [if_pos hI, if_pos (hmem.mp hI), harg ξ]
    by_cases hC : ξ ∈ C
    · rw [if_pos hC]; ring
    · rw [if_neg hC]; ring
  · rw [if_neg hI, if_neg (fun h => hI (hmem.mpr h))]
    by_cases hC : ξ ∈ C
    · rw [if_pos hC]; ring
    · rw [if_neg hC]; ring

/-- The `2^{-j-1}`-neighbourhood of a finite set of frequencies. -/
noncomputable def freqNeigh (s : Finset ℝ) (j : ℕ) : Set ℝ :=
  {ξ : ℝ | ∃ a ∈ (s : Set ℝ), |ξ - a| ≤ (2 : ℝ) ^ (-(j : ℝ) - 1)}

/-- **The real-line band-pass maximal estimate** for an arbitrary finite frequency set: the
single remaining analytic input.  In Bourgain's notation this is (a band-pass form of) his
Lemma 4.11; its proof reduces to Lemma 4.26 (`1`-separated) and thence to Lemma 4.13 and the deep
entropy input of §3 (Lépingle's variation inequality). -/
def RealLineBandpassMaximal : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset ℝ) (f : ℝ → ℂ), Integrable f →
    ∫⁻ (x : ℝ), (⨆ j : ℕ, ‖bandPass (freqNeigh s j) f x‖ₑ) ^ (2 : ℝ) ∂volume
      ≤ ENNReal.ofReal ((C * Real.log ((s.card : ℝ) + 2) ^ 2) ^ 2)
          * ∫⁻ (x : ℝ), ‖f x‖ₑ ^ (2 : ℝ) ∂volume

/-- **The periodic band-pass maximal estimate follows from the real-line one.**

This is the requested statement with the outer `lintegral` taken over the **real line** (the
correct reading; see the warning at the top of the file).  The periodic set `R j` is replaced, on
the fundamental domain, by the lifted finite set `liftedSet N lam` of at most `3N` frequencies,
which costs the constant `log (3N + 2) ≤ 3 log (N + 2)`. -/
theorem separated_real_line_bandpass_maximal_l2_real (H : RealLineBandpassMaximal) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (lam : Fin N → ℝ),
      (∀ i j : Fin N, i ≠ j → (2 : ℝ) ^ (-(3 : ℤ)) ≤ |lam i - lam j|) →
      ∀ (g : ℝ → ℂ), Integrable g →
        ∫⁻ (x : ℝ), (⨆ j : ℕ, ‖bandPass
            {ξ : ℝ | ∃ k : Fin N, ∃ l : ℤ, |ξ + (l : ℝ) + lam k| ≤ (2 : ℝ) ^ (-(j : ℝ) - 1)}
            g x‖ₑ) ^ (2 : ℝ) ∂volume
          ≤ ENNReal.ofReal ((C * Real.log ((N : ℝ) + 2) ^ 2) ^ 2)
              * ∫⁻ (x : ℝ), ‖g x‖ₑ ^ (2 : ℝ) ∂volume := by
  obtain ⟨C, hCpos, hC⟩ := H
  refine ⟨9 * C, by positivity, ?_⟩
  intro N lam _hsep g hg
  set Λ : Finset ℝ := liftedSet N lam with hΛ
  have hlog : Real.log ((Λ.card : ℝ) + 2) ≤ 3 * Real.log ((N : ℝ) + 2) := by
    have hN2 : (2 : ℝ) ≤ (N : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
    have hlogN2 : Real.log 2 ≤ Real.log ((N : ℝ) + 2) := Real.log_le_log (by norm_num) hN2
    have hcard' : (Λ.card : ℝ) + 2 ≤ 3 * ((N : ℝ) + 2) := by
      have h := liftedSet_card_le N lam
      have hcast : (Λ.card : ℝ) ≤ 3 * (N : ℝ) := by
        have h' : (Λ.card : ℝ) ≤ ((3 * N : ℕ) : ℝ) := by exact_mod_cast h
        simpa using h'
      linarith
    have hlog3 : Real.log 3 ≤ 2 * Real.log 2 := by
      have h4 : Real.log ((2 : ℝ) ^ 2) = 2 * Real.log 2 := by
        rw [Real.log_pow]; norm_num
      calc Real.log 3 ≤ Real.log ((2 : ℝ) ^ 2) := Real.log_le_log (by norm_num) (by norm_num)
        _ = 2 * Real.log 2 := h4
    calc Real.log ((Λ.card : ℝ) + 2) ≤ Real.log (3 * ((N : ℝ) + 2)) :=
          Real.log_le_log (by positivity) hcard'
      _ = Real.log 3 + Real.log ((N : ℝ) + 2) :=
          Real.log_mul (by norm_num) (by positivity)
      _ ≤ 3 * Real.log ((N : ℝ) + 2) := by linarith
  -- the two frequency sets agree on the fundamental domain
  have hsets : ∀ j : ℕ, ∀ ξ ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2),
      (ξ ∈ {ξ : ℝ | ∃ k : Fin N, ∃ l : ℤ, |ξ + (l : ℝ) + lam k| ≤ (2 : ℝ) ^ (-(j : ℝ) - 1)}
        ↔ ξ ∈ freqNeigh Λ j) := by
    intro j ξ hξ
    exact periodic_set_eq lam (sep_dyadic_pos j) (sep_dyadic_le_half j) hξ
  have hsup : ∀ x : ℝ,
      (⨆ j : ℕ, ‖bandPass
          {ξ : ℝ | ∃ k : Fin N, ∃ l : ℤ, |ξ + (l : ℝ) + lam k| ≤ (2 : ℝ) ^ (-(j : ℝ) - 1)}
          g x‖ₑ)
        = (⨆ j : ℕ, ‖bandPass (freqNeigh Λ j) g x‖ₑ) := by
    intro x
    exact iSup_congr (fun j => by rw [bandPass_congr g (hsets j) x])
  have hN2 : (1 : ℝ) ≤ (N : ℝ) + 2 := by
    have h : (1 : ℕ) ≤ N + 2 := by omega
    exact_mod_cast h
  have hlogpos : (0 : ℝ) ≤ Real.log ((N : ℝ) + 2) := Real.log_nonneg hN2
  have hlogcardpos : (0 : ℝ) ≤ Real.log ((Λ.card : ℝ) + 2) := by
    refine Real.log_nonneg ?_
    have : (0 : ℝ) ≤ (Λ.card : ℝ) := Nat.cast_nonneg _
    linarith
  have hconst : (C * Real.log ((Λ.card : ℝ) + 2) ^ 2) ^ 2
      ≤ (9 * C * Real.log ((N : ℝ) + 2) ^ 2) ^ 2 := by
    have h1 : Real.log ((Λ.card : ℝ) + 2) ^ 2 ≤ 9 * Real.log ((N : ℝ) + 2) ^ 2 := by
      nlinarith [hlog, hlogpos, hlogcardpos]
    have h2 : C * Real.log ((Λ.card : ℝ) + 2) ^ 2
        ≤ 9 * C * Real.log ((N : ℝ) + 2) ^ 2 := by nlinarith [hCpos.le, h1]
    exact pow_le_pow_left₀ (by positivity) h2 2
  calc (∫⁻ (x : ℝ), (⨆ j : ℕ, ‖bandPass
          {ξ : ℝ | ∃ k : Fin N, ∃ l : ℤ, |ξ + (l : ℝ) + lam k| ≤ (2 : ℝ) ^ (-(j : ℝ) - 1)}
          g x‖ₑ) ^ (2 : ℝ))
      = (∫⁻ (x : ℝ), (⨆ j : ℕ, ‖bandPass (freqNeigh Λ j) g x‖ₑ) ^ (2 : ℝ)) := by
        refine lintegral_congr (fun x => ?_)
        rw [hsup x]
    _ ≤ ENNReal.ofReal ((C * Real.log ((Λ.card : ℝ) + 2) ^ 2) ^ 2)
          * ∫⁻ (x : ℝ), ‖g x‖ₑ ^ (2 : ℝ) := hC Λ g hg
    _ ≤ ENNReal.ofReal ((9 * C * Real.log ((N : ℝ) + 2) ^ 2) ^ 2)
          * ∫⁻ (x : ℝ), ‖g x‖ₑ ^ (2 : ℝ) :=
        mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hconst) zero_le

/-- `freqNeigh s j` is a finite union of closed intervals, hence measurable. -/
lemma measurableSet_freqNeigh (s : Finset ℝ) (j : ℕ) : MeasurableSet (freqNeigh s j) := by
  have h : freqNeigh s j
      = ⋃ a ∈ s, Set.Icc (a - (2 : ℝ) ^ (-(j : ℝ) - 1)) (a + (2 : ℝ) ^ (-(j : ℝ) - 1)) := by
    ext ξ
    simp only [freqNeigh, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Icc, Finset.mem_coe]
    constructor
    · rintro ⟨a, ha, habs⟩
      rw [abs_le] at habs
      exact ⟨a, ha, by constructor <;> linarith [habs.1, habs.2]⟩
    · rintro ⟨a, ha, h1, h2⟩
      exact ⟨a, ha, by rw [abs_le]; constructor <;> linarith⟩
  rw [h]
  exact Finset.measurableSet_biUnion s (fun a _ => measurableSet_Icc)

/-- `freqNeigh s j` is bounded. -/
lemma isBounded_freqNeigh (s : Finset ℝ) (j : ℕ) : Bornology.IsBounded (freqNeigh s j) := by
  have h : freqNeigh s j
      = ⋃ a ∈ s, Set.Icc (a - (2 : ℝ) ^ (-(j : ℝ) - 1)) (a + (2 : ℝ) ^ (-(j : ℝ) - 1)) := by
    ext ξ
    simp only [freqNeigh, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Icc, Finset.mem_coe]
    constructor
    · rintro ⟨a, ha, habs⟩
      rw [abs_le] at habs
      exact ⟨a, ha, by constructor <;> linarith [habs.1, habs.2]⟩
    · rintro ⟨a, ha, h1, h2⟩
      exact ⟨a, ha, by rw [abs_le]; constructor <;> linarith⟩
  rw [h]
  exact (s.finite_toSet.isCompact_biUnion fun a _ => isCompact_Icc).isBounded

/-- The target's band-pass operator is the inverse Fourier integral of the indicator of
`freqNeigh s j ∩ [-1/2,1/2]`. -/
lemma bandPass_freqNeigh_eq_fourierInv {s : Finset ℝ} {f : ℝ → ℂ}
    (hf : MeasureTheory.Integrable f) (j : ℕ) (x : ℝ) :
    bandPass (freqNeigh s j) f x
      = 𝓕⁻ (fun ξ : ℝ => Set.indicator (freqNeigh s j) (fun _ => (1 : ℂ)) ξ *
          Set.indicator (Set.Icc (-(1 / 2) : ℝ) (1 / 2)) (fun _ => (1 : ℂ)) ξ * (𝓕 f) ξ) x :=
  bandPass_eq_fourierInv f hf x

/-- The conv-form expression of the commons conv form equals `2π` times the commons band-pass
operator on the reflected frequency set (here with the `2π`-free radius `2^{-(j:ℝ)-1}`). -/
lemma convForm_eq_bandOp {K : ℕ} (mu : Fin K → ℝ) (f : ℝ → ℂ)
    (hf1 : MeasureTheory.MemLp f 1 MeasureTheory.volume)
    (hf2 : MeasureTheory.MemLp f 2 MeasureTheory.volume) (j : ℕ) (x : ℝ) :
    (∫ y : ℝ, f y * (∫ θ : ℝ, Set.indicator
        {θ : ℝ | ∃ k : Fin K, |θ - mu k| ≤ (2 : ℝ) ^ (-(j : ℝ) - 1)}
        (fun θ : ℝ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ))
      = 2 * Real.pi * bandOp {ξ : ℝ | -2 * Real.pi * ξ ∈
          {θ : ℝ | ∃ k : Fin K, |θ - mu k| ≤ (2 : ℝ) ^ (-(j : ℝ) - 1)}} f x := by
  have hiUnion : {θ : ℝ | ∃ k : Fin K, |θ - mu k| ≤ (2 : ℝ) ^ (-(j : ℝ) - 1)}
      = ⋃ k : Fin K, Set.Icc (mu k - (2 : ℝ) ^ (-(j : ℝ) - 1))
          (mu k + (2 : ℝ) ^ (-(j : ℝ) - 1)) := by
    ext θ
    constructor
    · rintro ⟨k, hk⟩
      have hk' := abs_le.mp hk
      refine Set.mem_iUnion.mpr ⟨k, ?_⟩
      rw [Set.mem_Icc]
      exact ⟨by linarith [hk'.1, hk'.2], by linarith [hk'.1, hk'.2]⟩
    · rintro hk
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hk
      rw [Set.mem_Icc] at hk
      exact ⟨k, abs_le.mpr ⟨by linarith [hk.1, hk.2], by linarith [hk.1, hk.2]⟩⟩
  have hmeas : MeasurableSet {θ : ℝ | ∃ k : Fin K, |θ - mu k| ≤ (2 : ℝ) ^ (-(j : ℝ) - 1)} := by
    rw [hiUnion]
    exact MeasurableSet.iUnion fun k : Fin K => measurableSet_Icc
  have hbdd : Bornology.IsBounded
      {θ : ℝ | ∃ k : Fin K, |θ - mu k| ≤ (2 : ℝ) ^ (-(j : ℝ) - 1)} := by
    rw [hiUnion]
    exact (isCompact_iUnion fun k : Fin K => isCompact_Icc).isBounded
  simpa only [neg_mul] using
    iterated_integral_eq_bandOp _ hmeas hbdd f hf1 hf2 x

end BandLift


/-! ## `L²`-multiplier infrastructure (`BoundaryLayer`) used for the last-mile reduction

We work with `Lp ℂ 2 volume` and the multiplier operator
`BoundaryLayer.multiplier m hm F = 𝓕⁻ (mulLp m hm (𝓕 F))`, whose basic calculus
(`enorm_multiplier_sq`, `l2_multiplier_square_function`, `mulLp_coe`) lives in the commons file
`boundary_layer_l2`.  Here we add multiplicativity (composition) and the identification of the
multiplier by an indicator `1_C` with the pointwise band operator `bandOp C f`. -/

/-- `‖z‖ₑ ≤ 1` when `‖z‖ ≤ 1`. -/
lemma enorm_le_one_of_norm_le_one {z : ℂ} (h : ‖z‖ ≤ 1) : ‖z‖ₑ ≤ 1 := by
  rw [enorm_eq_ofReal_norm]
  simpa using ENNReal.ofReal_le_ofReal h

/-- The `L²` norm of a product with a function of pointwise norm `≤ 1`. -/
lemma enorm_mulLp_le (m : ℝ → ℂ) (hm : MemLp m ⊤ (volume : Measure ℝ))
    (hmbd : ∀ ξ, ‖m ξ‖ ≤ 1) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖BoundaryLayer.mulLp m hm g‖ₑ ≤ ‖g‖ₑ := by
  rw [BoundaryLayer.enorm_mulLp]
  have hle : ∀ ξ, ‖m ξ‖ₑ ^ (2:ℝ) ≤ 1 := by
    intro ξ
    calc ‖m ξ‖ₑ ^ (2:ℝ) ≤ 1 ^ (2:ℝ) :=
          ENNReal.rpow_le_rpow (enorm_le_one_of_norm_le_one (hmbd ξ)) (by norm_num)
      _ = 1 := by rw [ENNReal.one_rpow]
  calc (∫⁻ ξ, ‖m ξ‖ₑ ^ (2:ℝ) * ‖(g : ℝ → ℂ) ξ‖ₑ ^ (2:ℝ)) ^ (1/2:ℝ)
      ≤ (∫⁻ ξ, 1 * ‖(g : ℝ → ℂ) ξ‖ₑ ^ (2:ℝ)) ^ (1/2:ℝ) := by
        apply ENNReal.rpow_le_rpow _ (by norm_num)
        apply lintegral_mono; intro ξ
        have h2 : (0:ℝ≥0∞) ≤ ‖(g : ℝ → ℂ) ξ‖ₑ ^ (2:ℝ) := bot_le
        exact mul_le_mul_of_nonneg_right (hle ξ) h2
    _ = ‖g‖ₑ := by
        simp only [one_mul]
        rw [← BoundaryLayer.lp_enorm_sq_eq_lintegral g, ← ENNReal.rpow_mul]
        norm_num

/-- `mulLp` is multiplicative. -/
lemma mulLp_mul (m m' : ℝ → ℂ) (hm : MemLp m ⊤ (volume : Measure ℝ))
    (hm' : MemLp m' ⊤ (volume : Measure ℝ))
    (hmm' : MemLp (m * m') ⊤ (volume : Measure ℝ))
    (g : Lp ℂ 2 (volume : Measure ℝ)) :
    BoundaryLayer.mulLp m hm (BoundaryLayer.mulLp m' hm' g)
      = BoundaryLayer.mulLp (m * m') hmm' g := by
  apply Lp.ext
  filter_upwards [BoundaryLayer.mulLp_coe m hm (BoundaryLayer.mulLp m' hm' g),
    BoundaryLayer.mulLp_coe m' hm' g, BoundaryLayer.mulLp_coe (m * m') hmm' g]
    with ξ h1 h2 h3
  simp only [Pi.mul_apply] at h1 h2 h3 ⊢
  rw [h1, h3, h2]
  ring

/-- **Composition of multiplier operators.** -/
lemma multiplier_comp (m m' : ℝ → ℂ) (hm : MemLp m ⊤ (volume : Measure ℝ))
    (hm' : MemLp m' ⊤ (volume : Measure ℝ))
    (hmm' : MemLp (m * m') ⊤ (volume : Measure ℝ))
    (g : Lp ℂ 2 (volume : Measure ℝ)) :
    BoundaryLayer.multiplier m hm (BoundaryLayer.multiplier m' hm' g)
      = BoundaryLayer.multiplier (m * m') hmm' g := by
  unfold BoundaryLayer.multiplier
  have h1 : 𝓕 (𝓕⁻ (BoundaryLayer.mulLp m' hm' (𝓕 g)))
      = BoundaryLayer.mulLp m' hm' (𝓕 g) := FourierInvPair.fourier_fourierInv_eq _
  rw [h1, mulLp_mul m m' hm hm' hmm' (𝓕 g)]

/-- `Set.indicator C (𝓕 f) = (C.indicator 1) * 𝓕 f` pointwise. -/
lemma indicator_mul_fourier (C : Set ℝ) (f : ℝ → ℂ) :
    Set.indicator C (𝓕 f) = (Set.indicator C (fun _ => (1:ℂ))) * (𝓕 f) := by
  funext ξ
  simp only [Pi.mul_apply]
  by_cases h : ξ ∈ C <;> simp [Set.indicator_apply, h]

/-- **The bridge: the `L²` multiplier by `1_C`, applied to the `L²` class of `f`, is a.e. the
pointwise band operator `bandOp C f`.**  For `f ∈ L¹ ∩ L²` and a measurable set `C` of finite
measure. -/
theorem multiplier_indicator_ae_eq_bandOp {C : Set ℝ} (hC : MeasurableSet C)
    (hCfin : volume C < ⊤)
    (hm_top : MemLp (Set.indicator C (fun _ => (1:ℂ))) ⊤ (volume : Measure ℝ))
    {f : ℝ → ℂ} (hf1 : MemLp f 1 (volume : Measure ℝ)) (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    ((BoundaryLayer.multiplier (Set.indicator C (fun _ => (1:ℂ))) hm_top (hf2.toLp f) :
        Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] bandOp C f := by
  set m : ℝ → ℂ := Set.indicator C (fun _ => (1:ℂ)) with hmdef
  have hm1 : MemLp m 1 (volume : Measure ℝ) :=
    memLp_indicator_const 1 hC (1:ℂ) (Or.inr hCfin.ne)
  have hm2 : MemLp m 2 (volume : Measure ℝ) :=
    memLp_indicator_const 2 hC (1:ℂ) (Or.inr hCfin.ne)
  have hfi : Integrable f := memLp_one_iff_integrable.mp hf1
  have hfour : ((𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 f :=
    Commons.Analysis.Fourier.fourier_toLp_ae_eq_fourier_of_memLp hf1 hf2
  have hFTtop : MemLp (𝓕 f) ⊤ (volume : Measure ℝ) := by
    refine memLp_top_of_bound
      (Commons.Analysis.Fourier.BoundaryLayer.measurable_fourier hf1).aestronglyMeasurable
      (∫ x, ‖f x‖) ?_
    filter_upwards with ξ
    exact Commons.Analysis.Fourier.norm_fourier_le f ξ
  have hFT2 : MemLp (𝓕 f) 2 (volume : Measure ℝ) :=
    Commons.Analysis.Fourier.memLp_fourier hfi hf2
  have hprod1' : MemLp (fun x => 𝓕 f x * m x) 1 (volume : Measure ℝ) := hFTtop.mul' hm1
  have hprod2' : MemLp (fun x => 𝓕 f x * m x) 2 (volume : Measure ℝ) := hFT2.mul' hm_top
  have hprod1 : MemLp (m * 𝓕 f) 1 (volume : Measure ℝ) :=
    MemLp.ae_eq (Filter.Eventually.of_forall (fun x => by
      simp only [Pi.mul_apply]; ring)) hprod1'
  have hprod2 : MemLp (m * 𝓕 f) 2 (volume : Measure ℝ) :=
    MemLp.ae_eq (Filter.Eventually.of_forall (fun x => by
      simp only [Pi.mul_apply]; ring)) hprod2'
  have hFcoe : (BoundaryLayer.mulLp m hm_top (𝓕 (hf2.toLp f)) : ℝ → ℂ)
      =ᵐ[volume] m * 𝓕 f := by
    filter_upwards [BoundaryLayer.mulLp_coe m hm_top (𝓕 (hf2.toLp f)), hfour] with ξ h1 h2
    simp only [Pi.mul_apply] at h1 h2 ⊢
    rw [h1, h2]
  have hFeq : BoundaryLayer.mulLp m hm_top (𝓕 (hf2.toLp f))
      = MemLp.toLp (m * 𝓕 f) hprod2 := by
    apply Lp.ext
    filter_upwards [hFcoe, MemLp.coeFn_toLp hprod2] with ξ h1 h2
    simp only [Pi.mul_apply] at h1 h2 ⊢
    rw [h1, h2]
  have key : ((BoundaryLayer.multiplier m hm_top (hf2.toLp f) :
        Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕⁻ (m * 𝓕 f) := by
    change ((𝓕⁻ (BoundaryLayer.mulLp m hm_top (𝓕 (hf2.toLp f))) :
      Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕⁻ (m * 𝓕 f)
    rw [hFeq]
    exact Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv hprod1 hprod2
  refine key.trans ?_
  have hband : bandOp C f = 𝓕⁻ (m * 𝓕 f) := by
    funext x
    simp only [hmdef, bandOp]
    rw [indicator_mul_fourier]
  rw [hband]


/-! ## The last mile: the target from the multiplier form of the convolution maximal estimate

The single clean input left is `MaximalMultiplierBound` below: the arbitrary-centre,
dyadic-radius (`2^{-j-1}`) convolution maximal estimate stated for `L²` classes with the
`L²` multiplier calculus of `BoundaryLayer`.  It is what the commons chain

    `SmoothWindowMaximal` ⟹ `separated_maximal_of_smooth_window` (1-separated sharp θ-form)
      ⟹ `neighborhood_maximal_arbitrary_of_separated` (arbitrary λ, θ-radii `2^{-j-1}`)

produces after (i) the radius-scaling `c = 2π` (the θ-form is invariant under
`λ ↦ cλ`, `ρ ↦ cρ` together with `f ↦ f(·/c)`) and (ii) the θ-form↔multiplier bridge
(`∫ y, f y · bandKernel m (x-y) = 2π 𝓕⁻ (m(-2π·) 𝓕 f) x` for `f ∈ L¹∩L²`, extended to `L²`
by truncation).  Everything below is unconditional. -/

/-- The `r`-neighbourhood of a finite set of frequencies. -/
def nbhdSet (s : Finset ℝ) (j : ℕ) : Set ℝ :=
  {ξ : ℝ | ∃ a ∈ (s : Set ℝ), |ξ - a| ≤ (2 : ℝ) ^ (-(j : ℝ) - 1)}

lemma nbhdSet_eq_freqNeigh (s : Finset ℝ) (j : ℕ) :
    nbhdSet s j = BandLift.freqNeigh s j := rfl

/-- The indicator symbol of `nbhdSet s j`. -/
noncomputable def nbhdInd (s : Finset ℝ) (j : ℕ) : ℝ → ℂ := Set.indicator (nbhdSet s j) (fun _ => (1:ℂ))

lemma memLp_nbhdInd (s : Finset ℝ) (j : ℕ) : MemLp (nbhdInd s j) ⊤ (volume : Measure ℝ) := by
  have := BandLift.measurableSet_freqNeigh s j
  have hfin : volume (nbhdSet s j) < ⊤ := by
    have hb := BandLift.isBounded_freqNeigh s j
    rw [nbhdSet_eq_freqNeigh]
    exact hb.measure_lt_top
  exact memLp_indicator_const ⊤ this (1:ℂ) (Or.inr hfin.ne)

lemma norm_nbhdInd_le (s : Finset ℝ) (j : ℕ) (ξ : ℝ) : ‖nbhdInd s j ξ‖ ≤ 1 := by
  by_cases h : ξ ∈ nbhdSet s j
  · rw [nbhdInd, Set.indicator_of_mem h]; simp
  · rw [nbhdInd, Set.indicator_of_notMem h]; simp

/-- θ-form band operator with the θ-symbol a union of equal intervals. -/
noncomputable def thOp {K : ℕ} (lam : Fin K → ℝ) (rho : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, f y * (∫ θ, Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ rho}
    (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ)

/-- Membership scaling: `cθ` lies in the `cρ`-neighbourhood of `cλ` iff `θ` lies in the
`ρ`-neighbourhood of `λ` (for `c > 0`). -/
lemma mem_scale {K : ℕ} (lam : Fin K → ℝ) (rho c θ : ℝ) (hc : 0 < c) :
    (∃ k : Fin K, |c * θ - c * lam k| ≤ c * rho) ↔ (∃ k : Fin K, |θ - lam k| ≤ rho) := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h1 : |c * θ - c * lam k| = c * |θ - lam k| := by
      rw [← mul_sub, abs_mul, abs_of_pos hc]
    rw [h1] at hk
    exact le_of_mul_le_mul_left hk hc
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← mul_sub, abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left hk hc.le

/-- Scaling of the θ-symbol indicator. -/
lemma indicator_scale {K : ℕ} (lam : Fin K → ℝ) (rho c θ : ℝ) (hc : 0 < c) :
    Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - c * lam k| ≤ c * rho} (fun _ => (1:ℂ)) (c * θ)
      = Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ rho} (fun _ => (1:ℂ)) θ := by
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  by_cases h : ∃ k : Fin K, |θ - lam k| ≤ rho
  · have h' : ∃ k : Fin K, |c * θ - c * lam k| ≤ c * rho := (mem_scale lam rho c θ hc).mpr h
    rw [if_pos h', if_pos h]
  · have h' : ¬ (∃ k : Fin K, |c * θ - c * lam k| ≤ c * rho) :=
      fun hc' => h ((mem_scale lam rho c θ hc).mp hc')
    rw [if_neg h', if_neg h]

/-- Kernel scaling: the θ-symbol `nbhd(cλ, cρ)` at frequency `w` equals `c` times the
θ-symbol `nbhd(λ, ρ)` at frequency `c w`. -/
lemma kernel_scale {K : ℕ} (lam : Fin K → ℝ) (rho c w : ℝ) (hc : 0 < c) :
    (∫ θ, Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - c * lam k| ≤ c * rho}
        (fun θ => Complex.exp (-(Complex.I * (w : ℂ) * (θ : ℂ)))) θ)
      = c * ∫ θ, Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ rho}
        (fun θ => Complex.exp (-(Complex.I * ((c * w : ℝ) : ℂ) * (θ : ℂ)))) θ := by
  set Gc : ℝ → ℂ := fun θ => Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - c * lam k| ≤ c * rho}
      (fun θ => Complex.exp (-(Complex.I * (w : ℂ) * (θ : ℂ)))) θ with hGcdef
  set G1 : ℝ → ℂ := fun θ => Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ rho}
      (fun θ => Complex.exp (-(Complex.I * ((c * w : ℝ) : ℂ) * (θ : ℂ)))) θ with hG1def
  have hG : ∀ θ : ℝ, Gc (c * θ) = G1 θ := by
    intro θ
    rw [hGcdef, hG1def]
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    by_cases h : ∃ k : Fin K, |θ - lam k| ≤ rho
    · have h' : ∃ k : Fin K, |c * θ - c * lam k| ≤ c * rho := (mem_scale lam rho c θ hc).mpr h
      rw [if_pos h', if_pos h, Complex.ofReal_mul]
      congr 1
      push_cast
      ring
    · have h' : ¬ (∃ k : Fin K, |c * θ - c * lam k| ≤ c * rho) :=
        fun hc' => h ((mem_scale lam rho c θ hc).mp hc')
      rw [if_neg h', if_neg h]
  have hset : {θ : ℝ | ∃ k : Fin K, |θ - c * lam k| ≤ c * rho}
      = ⋃ k : Fin K, Set.Icc (c * lam k - c * rho) (c * lam k + c * rho) := by
    ext θ
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Icc, abs_le]
    constructor
    · rintro ⟨k, h1, h2⟩
      exact ⟨k, by linarith, by linarith⟩
    · rintro ⟨k, h1, h2⟩
      exact ⟨k, by linarith, by linarith⟩
  have h1 := MeasureTheory.Measure.integral_comp_mul_left Gc c
  simp only [hG] at h1
  rw [h1, Complex.real_smul, abs_of_pos (inv_pos.mpr hc)]
  have hcC : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hcC, one_mul]

/-- **Scaling of the θ-form band operator.**  Replacing the centres `λ` by `cλ` and the radius
`ρ` by `cρ` is the same as applying the unrescaled operator to `f(·/c)` and evaluating at `c x`. -/
theorem thOp_scale {K : ℕ} (lam : Fin K → ℝ) (rho c : ℝ) (hc : 0 < c) (f : ℝ → ℂ) (x : ℝ) :
    thOp (fun k => c * lam k) (c * rho) f x
      = thOp lam rho (fun y => f (y / c)) (c * x) := by
  unfold thOp
  -- step 1: the inner θ-integral scales
  have h1 : ∀ y : ℝ,
      (∫ θ, Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - c * lam k| ≤ c * rho}
        (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ)
      = c * ∫ θ, Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ rho}
        (fun θ => Complex.exp (-(Complex.I * (((c * x - c * y : ℝ) : ℂ)) * (θ : ℂ)))) θ := by
    intro y
    simpa only [mul_sub] using kernel_scale lam rho c (x - y) hc
  have hmain : (∫ y, f y * (∫ θ, Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - c * lam k| ≤ c * rho}
        (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ))
      = ∫ y, f y * (c * ∫ θ, Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ rho}
        (fun θ => Complex.exp (-(Complex.I * (((c * x - c * y : ℝ) : ℂ)) * (θ : ℂ)))) θ) := by
    apply integral_congr_ae
    filter_upwards with y
    rw [h1 y]
  rw [hmain]
  -- substitute back: `z = c y`
  have hsub : ∀ y : ℝ,
      f y * (c * ∫ θ, Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ rho}
        (fun θ => Complex.exp (-(Complex.I * (((c * x - c * y : ℝ) : ℂ)) * (θ : ℂ)))) θ)
      = c * (f ((c * y) / c) * ∫ θ, Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ rho}
        (fun θ => Complex.exp (-(Complex.I * (((c * x - c * y : ℝ) : ℂ)) * (θ : ℂ)))) θ) := by
    intro y
    rw [mul_div_cancel_left₀ y hc.ne']
    ring
  rw [show (∫ y, f y * (c * ∫ θ, Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ rho}
        (fun θ => Complex.exp (-(Complex.I * (((c * x - c * y : ℝ) : ℂ)) * (θ : ℂ)))) θ))
      = c * ∫ y, f ((c * y) / c) * (∫ θ, Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ rho}
        (fun θ => Complex.exp (-(Complex.I * (((c * x - c * y : ℝ) : ℂ)) * (θ : ℂ)))) θ) from by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    exact hsub y]
  have h5 := MeasureTheory.Measure.integral_comp_mul_left
    (fun z : ℝ => f (z / c) * ∫ θ, Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ rho}
      (fun θ => Complex.exp (-(Complex.I * (((c * x - z : ℝ) : ℂ)) * (θ : ℂ)))) θ) c
  rw [h5, Complex.real_smul, abs_of_pos (inv_pos.mpr hc)]
  have hcC : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hcC, one_mul]

/-- `thOp` is the convolution with the band kernel of the indicator symbol. -/
lemma thOp_eq_conv {K : ℕ} (mu : Fin K → ℝ) (rho : ℝ) (f : ℝ → ℂ) :
    thOp mu rho f = fun x => ∫ y, f y * bandKernel
      (Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - mu k| ≤ rho} (fun _ => (1:ℂ))) (x - y) := by
  funext x
  rw [thOp]
  apply integral_congr_ae
  filter_upwards with y
  congr 1
  rw [bandKernel]
  refine integral_congr_ae ?_
  filter_upwards with θ
  by_cases h : θ ∈ {θ : ℝ | ∃ k : Fin K, |θ - mu k| ≤ rho}
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]

/-- The symbol set is the union of the corresponding closed intervals. -/
lemma nbhd_eq_iUnion {K : ℕ} (mu : Fin K → ℝ) (rho : ℝ) :
    {θ : ℝ | ∃ k : Fin K, |θ - mu k| ≤ rho}
      = ⋃ k : Fin K, Set.Icc (mu k - rho) (mu k + rho) := by
  ext θ
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Icc, abs_le]
  constructor
  · rintro ⟨k, h1, h2⟩
    exact ⟨k, by linarith, by linarith⟩
  · rintro ⟨k, h1, h2⟩
    exact ⟨k, by linarith, by linarith⟩

/-- `thOp` of an `L²` function is a.e.-strongly-measurable. -/
lemma aestronglyMeasurable_thOp {K : ℕ} (mu : Fin K → ℝ) (rho : ℝ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume : Measure ℝ)) : AEStronglyMeasurable (thOp mu rho f) volume := by
  have hS : MeasurableSet {θ : ℝ | ∃ k : Fin K, |θ - mu k| ≤ rho} := by
    rw [nbhd_eq_iUnion]
    exact MeasurableSet.iUnion fun k : Fin K => measurableSet_Icc
  have hmeas : Measurable (bandKernel
      (Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - mu k| ≤ rho} (fun _ => (1:ℂ)))) := by
    have h : bandKernel (Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - mu k| ≤ rho} (fun _ => (1:ℂ)))
        = fun z : ℝ => ∫ θ : ℝ, Set.indicator {θ : ℝ | ∃ k : Fin K, |θ - mu k| ≤ rho}
            (fun _ => (1:ℂ)) θ * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ))) := rfl
    rw [h]
    refine StronglyMeasurable.measurable (StronglyMeasurable.integral_prod_right ?_)
    exact Measurable.stronglyMeasurable
      (Measurable.mul ((measurable_const.indicator hS).comp measurable_snd) (by fun_prop))
  rw [thOp_eq_conv]
  exact aestronglyMeasurable_conv hf hmeas

/-- The dilation identity for `∫⁻` along `y ↦ y / c`. -/
lemma lintegral_comp_div (c : ℝ) (hc : 0 < c) {F : ℝ → ℝ≥0∞} (hF : AEMeasurable F volume) :
    ∫⁻ y, F (y / c) = ENNReal.ofReal c * ∫⁻ u, F u := by
  have h := Sharp8.lintegral_comp_const_mul c⁻¹ (inv_ne_zero hc.ne') hF
  have h1 : ∀ y : ℝ, c⁻¹ * y = y / c := fun y => by rw [inv_mul_eq_div]
  simp only [h1] at h
  rwa [inv_inv, abs_of_pos hc] at h

/-- **The maximal form of the radius rescaling.**  If the θ-form convolution maximal estimate
holds with the dyadic θ-radii `2^{-(j:ℝ)-1}` and arbitrary centres `λ`, then it holds with the
rescaled θ-radii `c · 2^{-(j:ℝ)-1}` and rescaled centres `c · λ`, with the same constant: apply
the hypothesis to `f (·/c)` (whose `L²` norm is `c` times that of `f`), transport the supremum
with `thOp_scale`, and let the two factors of `c` cancel. -/
theorem conv_form_scaling
    (hconv : ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (lam : Fin K → ℝ) (f : ℝ → ℂ),
      MemLp f 2 (volume : Measure ℝ) →
      ∫⁻ x, (⨆ j : ℕ, ‖thOp lam ((2:ℝ) ^ (-(j : ℝ) - 1)) f x‖ₑ) ^ (2:ℝ)
        ≤ ENNReal.ofReal ((C * Real.log ((K : ℝ) + 2) ^ 2) ^ 2) * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℝ) (hc : 0 < c) (K : ℕ) (lam : Fin K → ℝ) (f : ℝ → ℂ),
      MemLp f 2 (volume : Measure ℝ) →
      ∫⁻ x, (⨆ j : ℕ, ‖thOp (fun k => c * lam k) (c * ((2:ℝ) ^ (-(j : ℝ) - 1))) f x‖ₑ) ^ (2:ℝ)
        ≤ ENNReal.ofReal ((C * Real.log ((K : ℝ) + 2) ^ 2) ^ 2) * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
  obtain ⟨C, hCpos, hC⟩ := hconv
  refine ⟨C, hCpos, ?_⟩
  intro c hc K lam f hf
  set g : ℝ → ℂ := fun y => f (y / c) with hgdef
  -- the `L²` facts for `g`
  have hgasm : AEStronglyMeasurable g (volume : Measure ℝ) := by
    have hq : Measure.QuasiMeasurePreserving (fun y : ℝ => y / c) volume volume := by
      have h2 : (fun y : ℝ => y / c) = fun y => c⁻¹ • y := by
        funext y; simp [div_eq_inv_mul]
      rw [h2]
      exact Measure.quasiMeasurePreserving_smul volume (inv_ne_zero hc.ne')
    exact hf.aestronglyMeasurable.comp_quasiMeasurePreserving hq
  have hglin : ∫⁻ y, ‖g y‖ₑ ^ (2:ℝ) = ENNReal.ofReal c * ∫⁻ u, ‖f u‖ₑ ^ (2:ℝ) := by
    rw [hgdef]
    simp only []
    exact lintegral_comp_div c hc (hf.aestronglyMeasurable.enorm.pow_const (2:ℝ))
  have hflt : ∫⁻ u, ‖f u‖ₑ ^ (2:ℝ) < ⊤ :=
    lintegral_enorm_sq_lt_top_of_memLp hf
  have hgmem : MemLp g 2 (volume : Measure ℝ) :=
    memLp_two_of_lintegral_enorm_lt_top hgasm (by rw [hglin]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hflt)
  -- the hypothesis applied to `g`
  have hmain := hC K lam g hgmem
  -- pointwise transport
  have hpt : ∀ j : ℕ, ∀ u : ℝ,
      thOp lam ((2:ℝ) ^ (-(j : ℝ) - 1)) g u
        = thOp (fun k => c * lam k) (c * ((2:ℝ) ^ (-(j : ℝ) - 1))) f (u / c) := by
    intro j u
    have h := thOp_scale lam ((2:ℝ) ^ (-(j : ℝ) - 1)) c hc f (u / c)
    rw [mul_div_cancel₀ u hc.ne'] at h
    exact h.symm
  -- transport the lintegral
  have hLHS : ∫⁻ u, (⨆ j : ℕ, ‖thOp lam ((2:ℝ) ^ (-(j : ℝ) - 1)) g u‖ₑ) ^ (2:ℝ)
      = ENNReal.ofReal c
        * ∫⁻ x, (⨆ j : ℕ, ‖thOp (fun k => c * lam k) (c * ((2:ℝ) ^ (-(j : ℝ) - 1))) f x‖ₑ) ^ (2:ℝ) := by
    have h1 : ∀ u : ℝ, (⨆ j : ℕ, ‖thOp lam ((2:ℝ) ^ (-(j : ℝ) - 1)) g u‖ₑ)
        = (⨆ j : ℕ, ‖thOp (fun k => c * lam k) (c * ((2:ℝ) ^ (-(j : ℝ) - 1))) f (u / c)‖ₑ) := by
      intro u
      exact iSup_congr (fun j => by rw [hpt j u])
    rw [lintegral_congr (fun u => by rw [h1 u])]
    exact lintegral_comp_div c hc
      ((AEMeasurable.iSup (fun j : ℕ => AEMeasurable.enorm ((aestronglyMeasurable_thOp
        (fun k => c * lam k) (c * ((2:ℝ) ^ (-(j : ℝ) - 1))) hf).aemeasurable))).pow_const (2:ℝ))
  -- combine
  rw [hLHS] at hmain
  rw [hglin] at hmain
  -- `ofReal c * X ≤ K * (ofReal c * Y)` gives `X ≤ K * Y`
  have hc0 : (ENNReal.ofReal c) ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have hct : (ENNReal.ofReal c) ≠ ⊤ := ENNReal.ofReal_ne_top
  refine (ENNReal.mul_le_mul_iff_left hc0 hct).mp ?_
  calc (∫⁻ x, (⨆ j : ℕ, ‖thOp (fun k => c * lam k)
          (c * ((2:ℝ) ^ (-(j : ℝ) - 1))) f x‖ₑ) ^ (2:ℝ)) * ENNReal.ofReal c
      = ENNReal.ofReal c * ∫⁻ x, (⨆ j : ℕ, ‖thOp (fun k => c * lam k)
          (c * ((2:ℝ) ^ (-(j : ℝ) - 1))) f x‖ₑ) ^ (2:ℝ) := mul_comm _ _
    _ ≤ ENNReal.ofReal ((C * Real.log ((K : ℝ) + 2) ^ 2) ^ 2)
          * (ENNReal.ofReal c * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) := hmain
    _ = (ENNReal.ofReal ((C * Real.log ((K : ℝ) + 2) ^ 2) ^ 2)
          * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) * ENNReal.ofReal c := by
        rw [mul_comm (ENNReal.ofReal c) (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)), mul_assoc]

/-- **The clean last-mile input**: the arbitrary-centre dyadic-radius convolution maximal
estimate in `L²`-multiplier form. -/
def MaximalMultiplierBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset ℝ) (F : Lp ℂ 2 (volume : Measure ℝ)),
    ∫⁻ x, (⨆ j : ℕ, ‖(BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) F :
        Lp ℂ 2 (volume : Measure ℝ)) x‖ₑ) ^ (2 : ℝ)
      ≤ ENNReal.ofReal ((C * Real.log ((s.card : ℝ) + 2) ^ 2) ^ 2) * ‖F‖ₑ ^ (2 : ℝ)

/-- The fundamental-domain indicator is an `L^∞` symbol. -/
lemma memLp_domInd :
    MemLp (Set.indicator (Set.Icc (-(1 / 2) : ℝ) (1 / 2)) (fun _ => (1:ℂ))) ⊤
      (volume : Measure ℝ) :=
  memLp_indicator_const ⊤ measurableSet_Icc (1:ℂ)
    (Or.inr (ne_of_lt (isCompact_Icc.measure_lt_top (μ := volume))))

lemma norm_domInd_le (ξ : ℝ) :
    ‖Set.indicator (Set.Icc (-(1 / 2) : ℝ) (1 / 2)) (fun _ => (1:ℂ)) ξ‖ ≤ 1 := by
  by_cases h : ξ ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)
  · rw [Set.indicator_of_mem h]; simp
  · rw [Set.indicator_of_notMem h]; simp

/-- On the fundamental domain, `nbhdSet s j ∩ dom = freqNeigh s j ∩ dom`. -/
lemma nbhdInterDom_eq (s : Finset ℝ) (j : ℕ) :
    nbhdSet s j ∩ Set.Icc (-(1 / 2) : ℝ) (1 / 2)
      = BandLift.freqNeigh s j ∩ Set.Icc (-(1 / 2) : ℝ) (1 / 2) := by
  rw [nbhdSet_eq_freqNeigh]

/-- **θ-form/multiplier bridge, `L¹ ∩ L²` case.**  For a bounded compactly supported symbol `m`
and `g ∈ L¹ ∩ L²`, the θ-form convolution `∫ y, g y · bandKernel m (x-y)` is a.e. `2π` times the
`L²` multiplier with symbol `m (-2π ·)` applied to the `L²` class of `g`. -/
theorem theta_form_eq_multiplier_of_memLp_one {m : ℝ → ℂ} (hm : MemLp m ⊤ (volume : Measure ℝ))
    (hmm : Measurable m) (hmbd : ∀ θ : ℝ, ‖m θ‖ ≤ 1) (hsupp : HasCompactSupport m)
    (hmc : MemLp (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) ⊤ (volume : Measure ℝ))
    {g : ℝ → ℂ} (hg1 : MemLp g 1 (volume : Measure ℝ)) (hg2 : MemLp g 2 (volume : Measure ℝ)) :
    (fun x : ℝ => ∫ y : ℝ, g y * bandKernel m (x - y))
      =ᵐ[volume] fun x : ℝ => (2 * Real.pi : ℂ) *
        ((BoundaryLayer.multiplier (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) hmc (hg2.toLp g) :
          Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x := by
  have hm1 : MemLp m 1 (volume : Measure ℝ) :=
    hsupp.memLp_of_bound hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall hmbd)
  have hm2 : MemLp m 2 (volume : Measure ℝ) :=
    hsupp.memLp_of_bound hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall hmbd)
  -- pointwise formula for the θ-form operator
  have hpoint : ∀ x : ℝ, (∫ y : ℝ, g y * bandKernel m (x - y))
      = (2 * Real.pi : ℂ) * 𝓕⁻ (fun ξ : ℝ => m (-(2 * Real.pi) * ξ) * 𝓕 g ξ) x := by
    intro x
    rw [bandOp_pointwise m g hmm hm1 hm2 hm hg1 hg2 x, twoPiC_coe]
    push_cast
    ring
  -- the multiplier side
  have hfm : MemLp (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) ⊤ (volume : Measure ℝ) := hmc
  have hfour : ((𝓕 (hg2.toLp g) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 g :=
    fourier_toLp_ae_eq_fourier_of_memLp hg1 hg2
  have hFTtop : MemLp (𝓕 g) ⊤ (volume : Measure ℝ) :=
    memLp_top_of_bound (BoundaryLayer.measurable_fourier hg1).aestronglyMeasurable
      (∫ x, ‖g x‖) (Filter.Eventually.of_forall (fun ξ => norm_fourier_le g ξ))
  have hFT2 : MemLp (𝓕 g) 2 (volume : Measure ℝ) := memLp_fourier (memLp_one_iff_integrable.mp hg1) hg2
  have hsupp' : HasCompactSupport (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) :=
    hasCompactSupport_comp_mul m hsupp (-(2 * Real.pi))
      (by intro h; linarith [Real.pi_pos, h])
  have hm1' : MemLp (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) 1 (volume : Measure ℝ) :=
    hsupp'.memLp_of_bound hmc.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun ξ => hmbd (-(2 * Real.pi) * ξ)))
  have hprod2 : MemLp ((fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) * 𝓕 g) 2 (volume : Measure ℝ) :=
    hmc.mul' hFT2
  have hprod1 : MemLp ((fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) * 𝓕 g) 1 (volume : Measure ℝ) :=
    hm1'.mul' hFTtop
  have hcoe : (BoundaryLayer.mulLp (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) hmc (𝓕 (hg2.toLp g)) :
        ℝ → ℂ)
      =ᵐ[volume] (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) * 𝓕 g := by
    filter_upwards [BoundaryLayer.mulLp_coe (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) hmc
      (𝓕 (hg2.toLp g)), hfour] with ξ h1 h2
    simp only [Pi.mul_apply] at h1 h2 ⊢
    rw [h1, h2]
  have heq : BoundaryLayer.mulLp (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) hmc (𝓕 (hg2.toLp g))
      = MemLp.toLp _ hprod2 := by
    apply Lp.ext
    filter_upwards [hcoe, MemLp.coeFn_toLp hprod2] with ξ h1 h2
    simp only [Pi.mul_apply] at h1 h2
    rw [h1, h2]
  have hmult : ((BoundaryLayer.multiplier (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) hmc (hg2.toLp g) :
        Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] 𝓕⁻ (fun ξ : ℝ => m (-(2 * Real.pi) * ξ) * 𝓕 g ξ) := by
    change ((𝓕⁻ (BoundaryLayer.mulLp (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) hmc
      (𝓕 (hg2.toLp g))) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
        =ᵐ[volume] 𝓕⁻ (fun ξ : ℝ => m (-(2 * Real.pi) * ξ) * 𝓕 g ξ)
    rw [heq]
    exact fourierInv_toLp_ae_eq_fourierInv hprod1 hprod2
  filter_upwards [hmult] with x hx
  rw [hpoint x, hx]

/-- **`mulLp` is additive in its `Lp` argument** — the argument-version companion of the
commons `BoundaryLayer.mulLp_sub` / `multiplier_sub`, which are the *symbol*-difference versions.
Here the two sides involve different functions (`m * ↑(g-h)` vs `m * ↑g - m * ↑h`), so the
a.e.-congruence is separated out first and `MemLp.toLp_sub` is applied with every argument pinned. -/
lemma mulLp_sub_arg {m : ℝ → ℂ} (hm : MemLp m ⊤ (volume : Measure ℝ))
    (g h : Lp ℂ 2 (volume : Measure ℝ)) :
    BoundaryLayer.mulLp m hm (g - h)
      = BoundaryLayer.mulLp m hm g - BoundaryLayer.mulLp m hm h := by
  have hmem_g : MemLp (m * (g : ℝ → ℂ)) 2 (volume : Measure ℝ) := hm.mul (Lp.memLp g)
  have hmem_h : MemLp (m * (h : ℝ → ℂ)) 2 (volume : Measure ℝ) := hm.mul (Lp.memLp h)
  have h₁ : BoundaryLayer.mulLp m hm (g - h)
      = MemLp.toLp (m * (g : ℝ → ℂ) - m * (h : ℝ → ℂ)) (hmem_g.sub hmem_h) := by
    rw [BoundaryLayer.mulLp]
    exact MemLp.toLp_congr (hm.mul (Lp.memLp (g - h))) (hmem_g.sub hmem_h)
      (by
        filter_upwards [MeasureTheory.Lp.coeFn_sub (μ := volume) g h] with x hx
        simp only [Pi.mul_apply, Pi.sub_apply]
        rw [hx]
        simp only [Pi.sub_apply]
        ring)
  have h₂ : MemLp.toLp (m * (g : ℝ → ℂ) - m * (h : ℝ → ℂ)) (hmem_g.sub hmem_h)
      = MemLp.toLp (m * (g : ℝ → ℂ)) hmem_g - MemLp.toLp (m * (h : ℝ → ℂ)) hmem_h :=
    MemLp.toLp_sub hmem_g hmem_h
  rw [h₁, h₂, BoundaryLayer.mulLp, BoundaryLayer.mulLp]

/-- The band kernel of a measurable symbol is measurable (as an integral of a measurable family). -/
lemma measurable_bandKernel {m : ℝ → ℂ} (hmm : Measurable m) : Measurable (bandKernel m) := by
  have h : bandKernel m
      = fun z : ℝ => ∫ θ : ℝ, m θ * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ))) := rfl
  rw [h]
  refine StronglyMeasurable.measurable (StronglyMeasurable.integral_prod_right ?_)
  exact Measurable.stronglyMeasurable (Measurable.mul (hmm.comp measurable_snd) (by fun_prop))

/-- The θ-form convolution operator of an `L²` class is a.e.-strongly-measurable. -/
lemma aestronglyMeasurable_thetaOp {m : ℝ → ℂ} (hmm : Measurable m)
    (G : Lp ℂ 2 (volume : Measure ℝ)) :
    AEStronglyMeasurable (fun x : ℝ => ∫ y : ℝ, (G : ℝ → ℂ) y * bandKernel m (x - y)) volume :=
  aestronglyMeasurable_conv (Lp.memLp G) (measurable_bandKernel hmm)

/-- **The θ-form convolution operator is bounded on `L²`.**  This is
`bandOp_l2_multiplier_bound` (commons) with the inner kernel written as `bandKernel`; the
constant `400` is inherited.  Together with `aestronglyMeasurable_thOp` this makes
`G ↦ (fun x => ∫ y, G y * bandKernel m (x - y)).toLp` a bounded linear map on `Lp ℂ 2 volume`. -/
lemma thetaOp_lintegral_le {m : ℝ → ℂ} (hmm : Measurable m) (hmbd : ∀ θ : ℝ, ‖m θ‖ ≤ 1)
    (hsupp : HasCompactSupport m) (G : Lp ℂ 2 (volume : Measure ℝ)) :
    ∫⁻ x, ‖∫ y : ℝ, (G : ℝ → ℂ) y * bandKernel m (x - y)‖ₑ ^ (2:ℝ)
      ≤ ENNReal.ofReal 400 * ‖G‖ₑ ^ (2:ℝ) := by
  have h := bandOp_l2_multiplier_bound m hmm hmbd hsupp (G : ℝ → ℂ) (Lp.memLp G)
  rw [BoundaryLayer.lp_enorm_sq_eq_lintegral G]
  refine le_trans (le_of_eq ?_) h
  apply lintegral_congr
  intro x
  have hK : (fun y : ℝ => (G : ℝ → ℂ) y * bandKernel m (x - y))
      = fun y : ℝ => (G : ℝ → ℂ) y * (∫ θ, m θ *
          Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) := by
    funext y
    simp only [bandKernel]
  rw [hK]

/-- Multipliers with a.e. equal symbols agree. -/
lemma multiplier_congr_ae {m m' : ℝ → ℂ} (hm : MemLp m ⊤ (volume : Measure ℝ))
    (hm' : MemLp m' ⊤ (volume : Measure ℝ)) (h : m =ᵐ[volume] m')
    (F : Lp ℂ 2 (volume : Measure ℝ)) :
    BoundaryLayer.multiplier m hm F = BoundaryLayer.multiplier m' hm' F := by
  unfold BoundaryLayer.multiplier
  congr 1
  apply Lp.ext
  filter_upwards [BoundaryLayer.mulLp_coe m hm (𝓕 F), BoundaryLayer.mulLp_coe m' hm' (𝓕 F),
    h] with ξ h1 h2 h3
  simp only [Pi.mul_apply] at h1 h2 ⊢
  rw [h1, h2, h3]

/-- The intersection symbol is the product of the two indicators. -/
lemma nbhdInd_mul_domInd (s : Finset ℝ) (j : ℕ) :
    nbhdInd s j * Set.indicator (Set.Icc (-(1 / 2) : ℝ) (1 / 2)) (fun _ => (1:ℂ))
      = Set.indicator (nbhdSet s j ∩ Set.Icc (-(1 / 2) : ℝ) (1 / 2)) (fun _ => (1:ℂ)) := by
  funext ξ
  simp only [Pi.mul_apply, Set.indicator_apply, nbhdInd]
  by_cases h1 : ξ ∈ nbhdSet s j <;> by_cases h2 : ξ ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) <;>
    simp_all [Set.mem_inter_iff]

/-- **The real-line band-pass maximal estimate follows from `MaximalMultiplierBound`.**

For `f ∈ L¹ ∩ L²` the route is: `bandPass (freqNeigh s j) f` is a.e. the `L²` multiplier by
`1_{nbhdSet s j ∩ dom}` applied to `hf2.toLp f` (the bridge `multiplier_indicator_ae_eq_bandOp`),
and by composition of multipliers this equals `multiplier (nbhdInd s j) (P F)` where
`P := multiplier 1_dom`, since `1_{nbhdSet s j} * 1_dom = 1_{nbhdSet s j ∩ dom}`.  The
hypothesis then bounds `⨆_j |multiplier (nbhdInd s j) (P F)|` by
`C log(#s+2)² ‖P F‖ₑ ≤ C log(#s+2)² ‖F‖ₑ = C log(#s+2)² (∫⁻ ‖f‖ₑ²)^{1/2}`.  For
`f ∉ L²` the right-hand side is infinite. -/
theorem realLineBandpassMaximal_of_multiplierBound (h : MaximalMultiplierBound) :
    BandLift.RealLineBandpassMaximal := by
  obtain ⟨C, hCpos, hC⟩ := h
  refine ⟨C, hCpos, ?_⟩
  intro s f hf1
  by_cases hf2 : MemLp f 2 (volume : Measure ℝ)
  · set F : Lp ℂ 2 (volume : Measure ℝ) := hf2.toLp f with hFdef
    set dom : Set ℝ := Set.Icc (-(1 / 2) : ℝ) (1 / 2) with hdomdef
    set mdom : ℝ → ℂ := Set.indicator dom (fun _ => (1:ℂ)) with hmdomdef
    have hmdtop : MemLp mdom ⊤ (volume : Measure ℝ) := memLp_domInd
    set P : Lp ℂ 2 (volume : Measure ℝ) := BoundaryLayer.multiplier mdom hmdtop F with hPdef
    have hf1' : MemLp f 1 (volume : Measure ℝ) := memLp_one_iff_integrable.mpr hf1
    -- the per-`j` identification of the two operators
    have key : ∀ j : ℕ,
        (fun x => BandLift.bandPass (BandLift.freqNeigh s j) f x)
          =ᵐ[volume]
        (fun x => (BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) P :
          Lp ℂ 2 (volume : Measure ℝ)) x) := by
      intro j
      have hCmeas : MeasurableSet (nbhdSet s j ∩ dom) :=
        (BandLift.measurableSet_freqNeigh s j).inter measurableSet_Icc
      have hCfin : volume (nbhdSet s j ∩ dom) < ⊤ :=
        ((BandLift.isBounded_freqNeigh s j).subset Set.inter_subset_left).measure_lt_top
      have hmC : MemLp (Set.indicator (nbhdSet s j ∩ dom) (fun _ => (1:ℂ))) ⊤
          (volume : Measure ℝ) :=
        memLp_indicator_const ⊤ hCmeas (1:ℂ) (Or.inr hCfin.ne)
      have hsym : nbhdInd s j * mdom = Set.indicator (nbhdSet s j ∩ dom) (fun _ => (1:ℂ)) := by
        have h := nbhdInd_mul_domInd s j
        simp only [hdomdef, hmdomdef] at h ⊢
        exact h
      have hmul : MemLp (nbhdInd s j * mdom) ⊤ (volume : Measure ℝ) := hsym ▸ hmC
      -- (a) `bandPass` is the multiplier by the clipped indicator of the `L²` class of `f`
      have hbp : (fun x => BandLift.bandPass (BandLift.freqNeigh s j) f x)
          =ᵐ[volume]
          (fun x => (BoundaryLayer.multiplier
            (Set.indicator (nbhdSet s j ∩ dom) (fun _ => (1:ℂ))) hmC F :
              Lp ℂ 2 (volume : Measure ℝ)) x) := by
        filter_upwards [multiplier_indicator_ae_eq_bandOp hCmeas hCfin hmC hf1' hf2]
          with x hx
        rw [hx, BandLift.bandPass_eq_fourierInv f hf1 x]
        have hfun : (fun ξ => Set.indicator (BandLift.freqNeigh s j) (fun _ => (1:ℂ)) ξ
              * Set.indicator dom (fun _ => (1:ℂ)) ξ * (𝓕 f) ξ)
            = fun ξ => Set.indicator (nbhdSet s j ∩ dom) (𝓕 f) ξ := by
          funext ξ
          rw [← nbhdSet_eq_freqNeigh]
          simp only [Pi.mul_apply, Set.indicator_apply]
          by_cases h1 : ξ ∈ nbhdSet s j <;> by_cases h2 : ξ ∈ dom <;>
            simp_all [Set.mem_inter_iff]
        rw [hfun]
        rfl
      -- (b) composition of multipliers
      have hcomp : BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) P
          = BoundaryLayer.multiplier (Set.indicator (nbhdSet s j ∩ dom) (fun _ => (1:ℂ)))
              hmC F := by
        rw [hPdef, multiplier_comp (nbhdInd s j) mdom (memLp_nbhdInd s j) hmdtop hmul F]
        exact multiplier_congr_ae hmul hmC
          (Filter.Eventually.of_forall (fun ξ => congrFun hsym ξ)) F
      rw [hcomp]
      exact hbp
    -- the pointwise supremum is the same almost everywhere
    have hLHS : ∫⁻ x, (⨆ j : ℕ, ‖BandLift.bandPass (BandLift.freqNeigh s j) f x‖ₑ) ^ (2:ℝ)
        = ∫⁻ x, (⨆ j : ℕ, ‖(BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) P :
            Lp ℂ 2 (volume : Measure ℝ)) x‖ₑ) ^ (2:ℝ) := by
      apply lintegral_congr_ae
      filter_upwards [ae_all_iff.mpr (fun j => key j)] with x hx
      congr 1
      exact iSup_congr (fun j => by rw [hx j])
    rw [hLHS]
    have hPnorm : ‖P‖ₑ ≤ ‖F‖ₑ := by
      rw [hPdef]
      calc ‖BoundaryLayer.multiplier mdom hmdtop F‖ₑ
          = ‖BoundaryLayer.mulLp mdom hmdtop (𝓕 F)‖ₑ := BoundaryLayer.enorm_fourierInv _
        _ ≤ ‖𝓕 F‖ₑ := enorm_mulLp_le mdom hmdtop (fun ξ => norm_domInd_le ξ) (𝓕 F)
        _ = ‖F‖ₑ := BoundaryLayer.enorm_fourier F
    have hFnorm : ‖F‖ₑ ^ (2:ℝ) = ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) := by
      rw [BoundaryLayer.lp_enorm_sq_eq_lintegral F]
      apply lintegral_congr_ae
      filter_upwards [MemLp.coeFn_toLp (μ := volume) hf2] with x hx
      rw [hx]
    calc ∫⁻ x, (⨆ j : ℕ, ‖(BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) P :
            Lp ℂ 2 (volume : Measure ℝ)) x‖ₑ) ^ (2:ℝ)
        ≤ ENNReal.ofReal ((C * Real.log ((s.card : ℝ) + 2) ^ 2) ^ 2) * ‖P‖ₑ ^ (2:ℝ) :=
          hC s P
      _ ≤ ENNReal.ofReal ((C * Real.log ((s.card : ℝ) + 2) ^ 2) ^ 2) * ‖F‖ₑ ^ (2:ℝ) := by
          exact mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow hPnorm (by norm_num)) zero_le
      _ = ENNReal.ofReal ((C * Real.log ((s.card : ℝ) + 2) ^ 2) ^ 2)
            * ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) := by rw [hFnorm]
  · -- the `¬ L²` case: the right-hand side is infinite
    have htop : ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) = ⊤ := by
      by_contra hne
      exact hf2 (memLp_two_of_lintegral_enorm_lt_top hf1.aestronglyMeasurable
        (lt_top_iff_ne_top.mpr hne))
    have hne0 : (ENNReal.ofReal ((C * Real.log ((s.card : ℝ) + 2) ^ 2) ^ 2)) ≠ 0 := by
      refine (ENNReal.ofReal_pos.mpr ?_).ne'
      refine pow_pos ?_ 2
      exact mul_pos hCpos (pow_pos (Real.log_pos (by
        have : (0:ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
        linarith)) 2)
    rw [htop, ENNReal.mul_top hne0]
    exact le_top

set_option maxHeartbeats 2000000

/-! ## The `L²` form of the θ↔multiplier bridge -/

private lemma fourier_sub_lp2 (f g : Lp ℂ 2 (volume : Measure ℝ)) : 𝓕 (f - g) = 𝓕 f - 𝓕 g := by
  change (Lp.fourierTransformₗᵢ ℝ ℂ) (f - g)
    = (Lp.fourierTransformₗᵢ ℝ ℂ) f - (Lp.fourierTransformₗᵢ ℝ ℂ) g
  exact map_sub _ _ _

private lemma fourierInv_sub_lp2 (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    𝓕⁻ (f - g) = 𝓕⁻ f - 𝓕⁻ g := by
  change ((Lp.fourierTransformₗᵢ ℝ ℂ)).symm (f - g)
    = (Lp.fourierTransformₗᵢ ℝ ℂ).symm f - (Lp.fourierTransformₗᵢ ℝ ℂ).symm g
  exact map_sub _ _ _

lemma multiplier_sub_arg {m : ℝ → ℂ} (hm : MemLp m ⊤ (volume : Measure ℝ))
    (F G : Lp ℂ 2 (volume : Measure ℝ)) :
    BoundaryLayer.multiplier m hm (F - G)
      = BoundaryLayer.multiplier m hm F - BoundaryLayer.multiplier m hm G := by
  simp only [BoundaryLayer.multiplier]
  rw [fourier_sub_lp2, mulLp_sub_arg hm]
  exact fourierInv_sub_lp2 _ _

private lemma enorm_sq_eq_aux (z : ℂ) : ‖z‖ₑ ^ (2:ℝ) = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [BoundaryLayer.enorm_eq_ofReal_norm,
      show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
      ENNReal.ofReal_pow (norm_nonneg z)]

private lemma ofReal_sq_rpow_aux (B : ℝ) (hB : 0 ≤ B) :
    (ENNReal.ofReal B) ^ (2:ℝ) = ENNReal.ofReal (B ^ 2) := by
  rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast, ← ENNReal.ofReal_pow hB]

private lemma enorm_toReal_aux (x : Lp ℂ 2 (volume : Measure ℝ)) : (‖x‖ₑ).toReal = ‖x‖ := by
  rw [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)]

/-- Operator-norm bound for the multiplier with a symbol bounded by `B`. -/
lemma enorm_multiplier_le {m : ℝ → ℂ} (hm : MemLp m ⊤ (volume : Measure ℝ))
    (B : ℝ) (hBnn : 0 ≤ B) (hB : ∀ ξ, ‖m ξ‖ ≤ B) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖BoundaryLayer.multiplier m hm f‖ₑ ≤ ENNReal.ofReal B * ‖f‖ₑ := by
  have hb : ∫⁻ ξ, ‖m ξ‖ₑ ^ (2:ℝ) * ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ)
      ≤ ENNReal.ofReal (B ^ 2) * ‖f‖ₑ ^ (2:ℝ) := by
    calc ∫⁻ ξ, ‖m ξ‖ₑ ^ (2:ℝ) * ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ)
        ≤ ∫⁻ ξ, ENNReal.ofReal (B ^ 2) * ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ) := by
          refine lintegral_mono (fun ξ => mul_le_mul' ?_ le_rfl)
          rw [enorm_sq_eq_aux]
          exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hB ξ) 2)
      _ = ENNReal.ofReal (B ^ 2) * ∫⁻ ξ, ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (B ^ 2) * ‖𝓕 f‖ₑ ^ (2:ℝ) := by
          rw [← BoundaryLayer.lp_enorm_sq_eq_lintegral (𝓕 f)]
      _ = ENNReal.ofReal (B ^ 2) * ‖f‖ₑ ^ (2:ℝ) := by rw [BoundaryLayer.enorm_fourier]
  have hsq : ‖BoundaryLayer.multiplier m hm f‖ₑ ^ (2:ℝ)
      ≤ (ENNReal.ofReal B * ‖f‖ₑ) ^ (2:ℝ) := by
    rw [BoundaryLayer.enorm_multiplier_sq, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
        ofReal_sq_rpow_aux B hBnn]
    exact hb
  have h2 := ENNReal.rpow_le_rpow hsq (show (0:ℝ) ≤ 1/2 by norm_num)
  rwa [← ENNReal.rpow_mul, show (2:ℝ)*(1/2) = 1 by norm_num, ENNReal.rpow_one,
       ← ENNReal.rpow_mul, show (2:ℝ)*(1/2) = 1 by norm_num, ENNReal.rpow_one] at h2

/-- The multiplier operator is `B`-Lipschitz on `L²`. -/
lemma norm_multiplier_sub_le {m : ℝ → ℂ} (hm : MemLp m ⊤ (volume : Measure ℝ))
    (B : ℝ) (hBnn : 0 ≤ B) (hB : ∀ ξ, ‖m ξ‖ ≤ B) (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖BoundaryLayer.multiplier m hm f - BoundaryLayer.multiplier m hm g‖ ≤ B * ‖f - g‖ := by
  have h := enorm_multiplier_le hm B hBnn hB (f - g)
  rw [multiplier_sub_arg hm] at h
  have hfin : ENNReal.ofReal B * ‖f - g‖ₑ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by rw [← ofReal_norm]; exact ENNReal.ofReal_ne_top)
  have hle := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hBnn, enorm_toReal_aux, enorm_toReal_aux] at hle
  exact hle

/-- The θ-form convolution of an `L²` class is square-integrable. -/
lemma memLp_thetaOp {m : ℝ → ℂ} (hmm : Measurable m) (hmbd : ∀ θ : ℝ, ‖m θ‖ ≤ 1)
    (hsupp : HasCompactSupport m) (G : Lp ℂ 2 (volume : Measure ℝ)) :
    MemLp (fun x : ℝ => ∫ y : ℝ, (G : ℝ → ℂ) y * bandKernel m (x - y)) 2
      (volume : Measure ℝ) := by
  refine memLp_two_of_lintegral_enorm_lt_top (aestronglyMeasurable_thetaOp hmm G) ?_
  refine lt_of_le_of_lt (thetaOp_lintegral_le hmm hmbd hsupp G) ?_
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  have hG2 : ‖G‖ₑ ^ (2:ℝ) < ⊤ := by
    rw [BoundaryLayer.lp_enorm_sq_eq_lintegral]
    exact lintegral_enorm_sq_lt_top_of_memLp (Lp.memLp G)
  exact hG2

/-- The θ-form convolution operator as an endomorphism of `Lp ℂ 2 volume`. -/
noncomputable def thetaOpLp {m : ℝ → ℂ} (hmm : Measurable m) (hmbd : ∀ θ : ℝ, ‖m θ‖ ≤ 1)
    (hsupp : HasCompactSupport m) (G : Lp ℂ 2 (volume : Measure ℝ)) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_thetaOp hmm hmbd hsupp G).toLp (fun x : ℝ => ∫ y : ℝ,
    (G : ℝ → ℂ) y * bandKernel m (x - y))

lemma thetaOpLp_coe {m : ℝ → ℂ} (hmm : Measurable m) (hmbd : ∀ θ : ℝ, ‖m θ‖ ≤ 1)
    (hsupp : HasCompactSupport m) (G : Lp ℂ 2 (volume : Measure ℝ)) :
    (thetaOpLp hmm hmbd hsupp G : ℝ → ℂ)
      =ᵐ[volume] fun x : ℝ => ∫ y : ℝ, (G : ℝ → ℂ) y * bandKernel m (x - y) :=
  MemLp.coeFn_toLp _

lemma thetaOpLp_sub {m : ℝ → ℂ} (hmm : Measurable m) (hmbd : ∀ θ : ℝ, ‖m θ‖ ≤ 1)
    (hsupp : HasCompactSupport m) (G H : Lp ℂ 2 (volume : Measure ℝ)) :
    thetaOpLp hmm hmbd hsupp (G - H)
      = thetaOpLp hmm hmbd hsupp G - thetaOpLp hmm hmbd hsupp H := by
  have hK : MemLp (bandKernel m) 2 (volume : Measure ℝ) :=
    bandKernel_memLp m hmm hmbd hsupp
  have hae : ((G - H : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      (G : ℝ → ℂ) - (H : ℝ → ℂ) := Lp.coeFn_sub G H
  apply Lp.ext
  filter_upwards [thetaOpLp_coe hmm hmbd hsupp (G - H),
    thetaOpLp_coe hmm hmbd hsupp G, thetaOpLp_coe hmm hmbd hsupp H,
    Lp.coeFn_sub (thetaOpLp hmm hmbd hsupp G) (thetaOpLp hmm hmbd hsupp H)] with x h1 h2 h3 h5
  simp only [Pi.sub_apply] at h5
  rw [h1, h5, h2, h3]
  have hKx : MemLp (fun y : ℝ => bandKernel m (x - y)) 2 (volume : Measure ℝ) :=
    hK.comp_measurePreserving (Measure.measurePreserving_sub_left (volume : Measure ℝ) x)
  have hGint : Integrable (fun y : ℝ => (G : ℝ → ℂ) y * bandKernel m (x - y)) volume :=
    (Lp.memLp G).integrable_mul hKx
  have hHint : Integrable (fun y : ℝ => (H : ℝ → ℂ) y * bandKernel m (x - y)) volume :=
    (Lp.memLp H).integrable_mul hKx
  have hstep1 : ∫ y : ℝ, ((G - H : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) y
        * bandKernel m (x - y)
      = ∫ y : ℝ, (((G : ℝ → ℂ) y - (H : ℝ → ℂ) y) * bandKernel m (x - y)) :=
    integral_congr_ae (hae.mono (fun y hy => by
      show ((G - H : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) y * bandKernel m (x - y)
        = ((G : ℝ → ℂ) y - (H : ℝ → ℂ) y) * bandKernel m (x - y)
      rw [hy, Pi.sub_apply]))
  have hstep2 : ∫ y : ℝ, (((G : ℝ → ℂ) y - (H : ℝ → ℂ) y) * bandKernel m (x - y))
      = ∫ y : ℝ, ((G : ℝ → ℂ) y * bandKernel m (x - y)
          - (H : ℝ → ℂ) y * bandKernel m (x - y)) :=
    integral_congr_ae (Filter.Eventually.of_forall (fun y => by ring))
  rw [hstep1, hstep2, integral_sub hGint hHint]

/-- The θ-form operator is bounded by `20` in operator norm on `L²`. -/
lemma enorm_thetaOpLp_le {m : ℝ → ℂ} (hmm : Measurable m) (hmbd : ∀ θ : ℝ, ‖m θ‖ ≤ 1)
    (hsupp : HasCompactSupport m) (G : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖thetaOpLp hmm hmbd hsupp G‖ₑ ≤ 20 * ‖G‖ₑ := by
  have h1 : ‖thetaOpLp hmm hmbd hsupp G‖ₑ ^ (2:ℝ)
      = ∫⁻ x : ℝ, ‖∫ y : ℝ, (G : ℝ → ℂ) y * bandKernel m (x - y)‖ₑ ^ (2:ℝ) := by
    rw [BoundaryLayer.lp_enorm_sq_eq_lintegral]
    refine lintegral_congr_ae ?_
    filter_upwards [thetaOpLp_coe hmm hmbd hsupp G] with x hx
    rw [hx]
  have h2 : ∫⁻ x : ℝ, ‖∫ y : ℝ, (G : ℝ → ℂ) y * bandKernel m (x - y)‖ₑ ^ (2:ℝ)
      ≤ ENNReal.ofReal 400 * ‖G‖ₑ ^ (2:ℝ) := thetaOp_lintegral_le hmm hmbd hsupp G
  have h3 : ‖thetaOpLp hmm hmbd hsupp G‖ₑ ^ (2:ℝ) ≤ (20 * ‖G‖ₑ) ^ (2:ℝ) := by
    rw [h1]
    refine le_trans h2 (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    norm_num
  have h4 := ENNReal.rpow_le_rpow h3 (show (0:ℝ) ≤ 1/2 by norm_num)
  rwa [← ENNReal.rpow_mul, show (2:ℝ)*(1/2) = 1 by norm_num, ENNReal.rpow_one,
       ← ENNReal.rpow_mul, show (2:ℝ)*(1/2) = 1 by norm_num, ENNReal.rpow_one] at h4

lemma norm_thetaOpLp_sub_le {m : ℝ → ℂ} (hmm : Measurable m) (hmbd : ∀ θ : ℝ, ‖m θ‖ ≤ 1)
    (hsupp : HasCompactSupport m) (G H : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖thetaOpLp hmm hmbd hsupp G - thetaOpLp hmm hmbd hsupp H‖ ≤ 20 * ‖G - H‖ := by
  have h := enorm_thetaOpLp_le hmm hmbd hsupp (G - H)
  rw [thetaOpLp_sub hmm hmbd hsupp G H] at h
  have hfin : (20:ℝ≥0∞) * ‖G - H‖ₑ ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (by rw [← ofReal_norm]; exact ENNReal.ofReal_ne_top)
  have hle := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat, enorm_toReal_aux, enorm_toReal_aux] at hle
  exact hle

/-- **The `L¹ ∩ L²` case of the θ↔multiplier bridge at the level of `Lp` classes.** -/
lemma thetaOpLp_eq_multiplier_of_memLp_one {m : ℝ → ℂ} (hm : MemLp m ⊤ (volume : Measure ℝ))
    (hmm : Measurable m) (hmbd : ∀ θ : ℝ, ‖m θ‖ ≤ 1) (hsupp : HasCompactSupport m)
    (hmc : MemLp (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) ⊤ (volume : Measure ℝ))
    {g : ℝ → ℂ} (hg1 : MemLp g 1 (volume : Measure ℝ)) (hg2 : MemLp g 2 (volume : Measure ℝ)) :
    thetaOpLp hmm hmbd hsupp (hg2.toLp g)
      = (2 * Real.pi : ℂ) •
        BoundaryLayer.multiplier (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) hmc (hg2.toLp g) := by
  have hbase := theta_form_eq_multiplier_of_memLp_one hm hmm hmbd hsupp hmc hg1 hg2
  apply Lp.ext
  filter_upwards [thetaOpLp_coe hmm hmbd hsupp (hg2.toLp g), hbase,
    Lp.coeFn_smul (2 * Real.pi : ℂ)
      (BoundaryLayer.multiplier (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) hmc (hg2.toLp g))]
    with x h1 h2 h3
  simp only [Pi.smul_apply, smul_eq_mul] at h3
  rw [h1, h3]
  have hstep : ∫ y : ℝ, ((hg2.toLp g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) y
        * bandKernel m (x - y)
      = ∫ y : ℝ, g y * bandKernel m (x - y) :=
    integral_congr_ae ((MemLp.coeFn_toLp hg2).mono (fun y hy => by simp only [hy]))
  rw [hstep, h2]

/-- `L¹ ∩ L²` functions (as `L²` classes) are dense in `L²(ℝ)`. -/
theorem dense_range_memLp_one_two :
    Dense (Set.range (fun g : {g : ℝ → ℂ // MemLp g 1 (volume : Measure ℝ) ∧
        MemLp g 2 (volume : Measure ℝ)} => g.2.2.toLp g.1)) := by
  rw [Metric.dense_iff]
  intro F r hr
  have hε : (ENNReal.ofReal (r / 2)) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith
  obtain ⟨g, hgε, hg1, hg2⟩ := MemLp.induction_dense (p := 2) (E := ℂ) (μ := volume)
    (by norm_num : (2:ℝ≥0∞) ≠ ∞)
    (fun f : ℝ → ℂ => MemLp f 1 (volume : Measure ℝ) ∧ MemLp f 2 (volume : Measure ℝ))
    (by
      intro c s hs hμs ε hε'
      refine ⟨s.indicator (fun _ => c), ?_, memLp_indicator_const 1 hs c (Or.inr hμs.ne),
        memLp_indicator_const 2 hs c (Or.inr hμs.ne)⟩
      simp)
    (by intro f g hf hg; exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩)
    (Lp.memLp F) (ε := ENNReal.ofReal (r / 2)) hε
  have hcoe : (((F - hg2.toLp g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ))
      =ᵐ[volume] (F : ℝ → ℂ) - g := by
    filter_upwards [Lp.coeFn_sub F (hg2.toLp g), MemLp.coeFn_toLp hg2] with x hx hy
    simp only [Pi.sub_apply, hx, hy]
  have hnorm : ‖F - hg2.toLp g‖ ≤ r / 2 := by
    rw [Lp.norm_def, eLpNorm_congr_ae hcoe]
    exact ENNReal.toReal_le_of_le_ofReal (by linarith : (0:ℝ) ≤ r / 2) hgε
  refine ⟨hg2.toLp g, ?_, ⟨⟨g, hg1, hg2⟩, rfl⟩⟩
  have h2 : dist F (hg2.toLp g) ≤ r / 2 := by
    rw [dist_eq_norm]; exact hnorm
  rw [Metric.mem_ball, dist_comm]
  exact lt_of_le_of_lt h2 (by linarith)

/-- **θ-form/multiplier bridge, `L²` case.**  For a bounded compactly supported symbol `m`, the
θ-form convolution operator is `2π` times the `L²` multiplier with symbol `m (-2π ·)`, on all of
`L²`: the `L¹ ∩ L²` identity extends by density, using the additivity and boundedness of the two
operators. -/
theorem theta_form_eq_multiplier_L2 {m : ℝ → ℂ} (hm : MemLp m ⊤ (volume : Measure ℝ))
    (hmm : Measurable m) (hmbd : ∀ θ : ℝ, ‖m θ‖ ≤ 1) (hsupp : HasCompactSupport m)
    (hmc : MemLp (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) ⊤ (volume : Measure ℝ))
    (G : Lp ℂ 2 (volume : Measure ℝ)) :
    thetaOpLp hmm hmbd hsupp G
      = (2 * Real.pi : ℂ) •
        BoundaryLayer.multiplier (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) hmc G := by
  have hcont1 : Continuous
      (fun F : Lp ℂ 2 (volume : Measure ℝ) => thetaOpLp hmm hmbd hsupp F) := by
    refine LipschitzWith.continuous (K := 20) (LipschitzWith.of_dist_le_mul ?_)
    intro F H
    rw [dist_eq_norm, dist_eq_norm]
    simpa using norm_thetaOpLp_sub_le hmm hmbd hsupp F H
  have hcont2 : Continuous (fun F : Lp ℂ 2 (volume : Measure ℝ) =>
      (2 * Real.pi : ℂ) •
        BoundaryLayer.multiplier (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) hmc F) := by
    refine (LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul ?_)).const_smul
      (2 * Real.pi : ℂ)
    intro F H
    rw [dist_eq_norm, dist_eq_norm]
    have h := norm_multiplier_sub_le (m := fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) hmc 1
      (by norm_num) (fun ξ => hmbd (-(2 * Real.pi) * ξ)) F H
    simpa using h
  have hclosed : IsClosed {F : Lp ℂ 2 (volume : Measure ℝ) |
      thetaOpLp hmm hmbd hsupp F - (2 * Real.pi : ℂ) •
        BoundaryLayer.multiplier (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) hmc F = 0} :=
    isClosed_eq (hcont1.sub hcont2) continuous_const
  have hsub : Set.range (fun g : {g : ℝ → ℂ // MemLp g 1 (volume : Measure ℝ) ∧
      MemLp g 2 (volume : Measure ℝ)} => g.2.2.toLp g.1) ⊆
      {F : Lp ℂ 2 (volume : Measure ℝ) | thetaOpLp hmm hmbd hsupp F - (2 * Real.pi : ℂ) •
        BoundaryLayer.multiplier (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) hmc F = 0} := by
    rintro F ⟨g, rfl⟩
    rw [Set.mem_ofPred_eq]
    rw [thetaOpLp_eq_multiplier_of_memLp_one hm hmm hmbd hsupp hmc g.2.1 g.2.2, sub_self]
  have hcl : closure (Set.range (fun g : {g : ℝ → ℂ // MemLp g 1 (volume : Measure ℝ) ∧
      MemLp g 2 (volume : Measure ℝ)} => g.2.2.toLp g.1)) ⊆
      {F : Lp ℂ 2 (volume : Measure ℝ) | thetaOpLp hmm hmbd hsupp F - (2 * Real.pi : ℂ) •
        BoundaryLayer.multiplier (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) hmc F = 0} :=
    (closure_mono hsub).trans hclosed.closure_subset
  rw [dense_range_memLp_one_two.closure_eq] at hcl
  exact sub_eq_zero.mp (hcl (Set.mem_univ G))


/-- **SWM-based input**: `MaximalMultiplierBound` follows from the smooth-window maximal
estimate (Bourgain 1989, Lemma 4.13) through the commons chain and the two conversions
(radius rescaling `2π`, θ-form/multiplier bridge).  This is the single remaining gap. -/
private lemma enorm_le_enorm_two_pi_mul (z : ℂ) : ‖z‖ₑ ≤ ‖(2 * Real.pi : ℂ) * z‖ₑ := by
  have hnorm : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    have h₁ : (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [h₁, show ‖(((2 * Real.pi : ℝ)) : ℂ)‖ = |2 * Real.pi| from by simp,
      abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  have h1 : (1 : ℝ≥0∞) ≤ ‖(2 * Real.pi : ℂ)‖ₑ := by
    rw [BoundaryLayer.enorm_eq_ofReal_norm, ENNReal.one_le_ofReal, hnorm]
    linarith [Real.pi_gt_three]
  calc ‖z‖ₑ = 1 * ‖z‖ₑ := (one_mul _).symm
    _ ≤ ‖(2 * Real.pi : ℂ)‖ₑ * ‖z‖ₑ := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = ‖(2 * Real.pi : ℂ) * z‖ₑ := (enorm_mul _ _).symm

lemma multiplier_le_thOp {s : Finset ℝ} (F : Lp ℂ 2 (volume : Measure ℝ)) (j : ℕ) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      ‖(BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) F :
          Lp ℂ 2 (volume : Measure ℝ)) x‖ₑ
        ≤ ‖thOp (fun k : Fin s.card => 2 * Real.pi * (-(((s.equivFin.symm k : s) : ℝ))))
            (2 * Real.pi * (2 : ℝ) ^ (-(j : ℝ) - 1)) (F : ℝ → ℂ) x‖ₑ := by
  classical
  set ν : Fin s.card → ℝ := fun k => ((s.equivFin.symm k : s) : ℝ) with hν
  set rho : ℝ := 2 * Real.pi * (2 : ℝ) ^ (-(j : ℝ) - 1) with hrho
  set m : ℝ → ℂ := Set.indicator
    {θ : ℝ | ∃ k : Fin s.card, |θ - 2 * Real.pi * (-(ν k))| ≤ rho} (fun _ => (1 : ℂ)) with hm
  have hset : MeasurableSet {θ : ℝ | ∃ k : Fin s.card, |θ - 2 * Real.pi * (-(ν k))| ≤ rho} := by
    have : {θ : ℝ | ∃ k : Fin s.card, |θ - 2 * Real.pi * (-(ν k))| ≤ rho}
        = ⋃ k : Fin s.card,
          Set.Icc (2 * Real.pi * (-(ν k)) - rho) (2 * Real.pi * (-(ν k)) + rho) := by
      ext θ
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_Icc, abs_le]
      constructor
      · rintro ⟨k, h1, h2⟩; exact ⟨k, by linarith, by linarith⟩
      · rintro ⟨k, h1, h2⟩; exact ⟨k, by linarith, by linarith⟩
    rw [this]
    exact MeasurableSet.iUnion fun k => measurableSet_Icc
  have hmm : Measurable m := by
    rw [hm]; exact measurable_const.indicator hset
  have hmbd : ∀ θ : ℝ, ‖m θ‖ ≤ 1 := by
    intro θ
    rw [hm]
    simp only [Set.indicator_apply]
    split_ifs <;> simp
  have hsupp : HasCompactSupport m := by
    refine HasCompactSupport.intro (K := ⋃ k : Fin s.card,
      Set.Icc (2 * Real.pi * (-(ν k)) - rho) (2 * Real.pi * (-(ν k)) + rho))
      (isCompact_iUnion fun k => isCompact_Icc) ?_
    intro x hx
    rw [hm]
    rw [Set.indicator_of_notMem]
    intro hmem
    exact hx (Set.mem_iUnion.mpr (by
      rcases hmem with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [Set.mem_Icc]
      obtain ⟨h1, h2⟩ := abs_le.mp hk
      constructor <;> linarith))
  have hmtop : MemLp m ⊤ (volume : Measure ℝ) :=
    memLp_top_of_bound hmm.aestronglyMeasurable 1 (Filter.Eventually.of_forall hmbd)
  have hcomp : (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) = nbhdInd s j := by
    funext ξ
    rw [hm, nbhdInd, Set.indicator_apply, Set.indicator_apply]
    have hiff : (-(2 * Real.pi) * ξ ∈
          {θ : ℝ | ∃ k : Fin s.card, |θ - 2 * Real.pi * (-(ν k))| ≤ rho})
        ↔ ξ ∈ nbhdSet s j := by
      rw [Set.mem_ofPred_eq, nbhdSet, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨k, hk⟩
        refine ⟨ν k, ?_, ?_⟩
        · have hk' : ν k = ((s.equivFin.symm k : s) : ℝ) := by rw [hν]
          rw [hk']
          exact Finset.mem_coe.mpr (s.equivFin.symm k).property
        have htwopi : (0 : ℝ) < 2 * Real.pi := by positivity
        have h1 : |-(2 * Real.pi) * ξ - 2 * Real.pi * (-(ν k))|
            = 2 * Real.pi * |ν k - ξ| := by
          rw [show -(2 * Real.pi) * ξ - 2 * Real.pi * (-(ν k)) = 2 * Real.pi * (ν k - ξ)
              by ring, abs_mul, abs_of_pos htwopi]
        rw [h1, hrho] at hk
        have h2 := le_of_mul_le_mul_left hk htwopi
        rwa [abs_sub_comm] at h2
      · rintro ⟨a, ha, ha'⟩
        set k : Fin s.card := s.equivFin ⟨a, Finset.mem_coe.mp ha⟩ with hk
        refine ⟨k, ?_⟩
        have hνa : ν k = a := by
          rw [hν, hk]
          simp only [Equiv.symm_apply_apply]
        rw [hrho, hνa]
        have htwopi : (0 : ℝ) < 2 * Real.pi := by positivity
        calc |-(2 * Real.pi) * ξ - 2 * Real.pi * (-a)|
            = 2 * Real.pi * |a - ξ| := by
              rw [show -(2 * Real.pi) * ξ - 2 * Real.pi * (-a) = 2 * Real.pi * (a - ξ) by ring,
                  abs_mul, abs_of_pos htwopi]
          _ = 2 * Real.pi * |ξ - a| := by rw [abs_sub_comm]
          _ ≤ 2 * Real.pi * (2 : ℝ) ^ (-(j : ℝ) - 1) :=
              mul_le_mul_of_nonneg_left ha' htwopi.le
    by_cases h : (-(2 * Real.pi) * ξ ∈
        {θ : ℝ | ∃ k : Fin s.card, |θ - 2 * Real.pi * (-(ν k))| ≤ rho})
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]
  have hmc : MemLp (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) ⊤ (volume : Measure ℝ) := by
    rw [hcomp]; exact memLp_nbhdInd s j
  have hsym : ∀ ξ : ℝ, m (-(2 * Real.pi) * ξ) = nbhdInd s j ξ := fun ξ => congrFun hcomp ξ
  have hbridge : (2 * Real.pi : ℂ) •
      BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) F
        = thetaOpLp hmm hmbd hsupp F := by
    rw [← multiplier_congr_ae hmc (memLp_nbhdInd s j)
      (Filter.Eventually.of_forall hsym) F]
    exact (theta_form_eq_multiplier_L2 hmtop hmm hmbd hsupp hmc F).symm
  have hth : ∀ x : ℝ, (∫ y : ℝ, (F : ℝ → ℂ) y * bandKernel m (x - y))
      = thOp (fun k : Fin s.card => 2 * Real.pi * (-(ν k))) rho (F : ℝ → ℂ) x := by
    intro x
    simp only [thOp_eq_conv, hm]
  filter_upwards [thetaOpLp_coe hmm hmbd hsupp F,
    Lp.coeFn_smul (2 * Real.pi : ℂ)
      (BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) F)] with x h1 h2
  simp only [Pi.smul_apply, smul_eq_mul] at h2
  have hcoe : ((thetaOpLp hmm hmbd hsupp F : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      = ((2 * Real.pi : ℂ) •
          BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) F :
            Lp ℂ 2 (volume : Measure ℝ)) :=
    congrArg (fun Y : Lp ℂ 2 (volume : Measure ℝ) => (Y : ℝ → ℂ)) hbridge.symm
  calc ‖(BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) F :
          Lp ℂ 2 (volume : Measure ℝ)) x‖ₑ
      = ‖(((BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) F :
            Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x)‖ₑ := rfl
    _ ≤ ‖(2 * Real.pi : ℂ) *
          ((BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) F :
            Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x‖ₑ :=
        enorm_le_enorm_two_pi_mul _
    _ = ‖(((2 * Real.pi : ℂ) •
          BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) F :
            Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x‖ₑ := by rw [h2]
    _ = ‖((thetaOpLp hmm hmbd hsupp F : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x‖ₑ := by
        rw [hcoe]
    _ = ‖thOp (fun k : Fin s.card => 2 * Real.pi * (-(ν k))) rho (F : ℝ → ℂ) x‖ₑ := by
        rw [h1, hth]

theorem bourgain_smooth_window_maximal_l2_input :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (lam : Fin K → ℝ),
      (∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) →
      ∀ (φ : ℝ → ℝ), (∀ n : ℕ, ContDiff ℝ n φ) →
        (∀ x : ℝ, |x| ≤ 1 / 2 → φ x = 1) →
        (∀ x : ℝ, 1 ≤ |x| → φ x = 0) → (∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) →
      ∀ (f : ℝ → ℂ), MemLp f 2 (volume : Measure ℝ) →
        ∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, f y *
            (∑ k : Fin K,
              ∫ θ in (lam k - (2 : ℝ) ^ (-(j : ℝ) - 1))..(lam k + (2 : ℝ) ^ (-(j : ℝ) - 1)),
                (φ ((θ - lam k) / (2 : ℝ) ^ (-(j : ℝ) - 1)) : ℂ) *
                  Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ) ^ (2 : ℝ)
          ≤ ENNReal.ofReal ((C * (Real.log ((K : ℝ) + 2)) ^ 2) ^ 2)
            * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) :=
  bourgain_smooth_window_maximal_l2_smooth

theorem maximalMultiplierBound_of_smoothWindow : MaximalMultiplierBound := by
  have hsep : ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (mu : Fin K → ℝ),
      (∀ i j : Fin K, i ≠ j → 1 ≤ |mu i - mu j|) →
      ∀ (f : ℝ → ℂ) (hf : MemLp f 2 (volume : Measure ℝ)),
        ∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, f y *
            (∑ k : Fin K,
              ∫ θ in (mu k - (2 : ℝ) ^ (-(j : ℝ) - 1))..(mu k + (2 : ℝ) ^ (-(j : ℝ) - 1)),
                Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ) ^ (2 : ℝ)
          ≤ ENNReal.ofReal ((C * (Real.log ((K : ℝ) + 2)) ^ 2) ^ 2)
            * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) := by
    obtain ⟨C, hCpos, hC⟩ := separated_maximal_of_smooth_window (by
      obtain ⟨C', hC'pos, hC'⟩ := bourgain_smooth_window_maximal_l2_input
      refine ⟨C', hC'pos, fun K lam hlam φ hφ h1 h0 hbd f hf => ?_⟩
      have := hC' K lam hlam φ hφ h1 h0 hbd f hf
      simpa only [BoundaryLayer.enorm_eq_ofReal_norm] using this)
    refine ⟨C, hCpos, fun K mu hsep f hf => ?_⟩
    have := hC K mu hsep f hf
    simpa only [BoundaryLayer.enorm_eq_ofReal_norm] using this
  obtain ⟨C₁, hC₁pos, hC₁⟩ := neighborhood_maximal_arbitrary_of_separated hsep
  obtain ⟨C₂, hC₂pos, hC₂⟩ :=
    conv_form_scaling ⟨C₁, hC₁pos, fun K lam f hf => hC₁ K lam f hf⟩
  refine ⟨C₂, hC₂pos, ?_⟩
  intro s F
  have hmain := hC₂ (2 * Real.pi) (by positivity) s.card
    (fun k : Fin s.card => -(((s.equivFin.symm k : s) : ℝ))) (F : ℝ → ℂ) (Lp.memLp F)
  rw [← BoundaryLayer.lp_enorm_sq_eq_lintegral F] at hmain
  have hsup : ∀ᵐ x ∂(volume : Measure ℝ),
      (⨆ j : ℕ, ‖(BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) F :
          Lp ℂ 2 (volume : Measure ℝ)) x‖ₑ)
        ≤ (⨆ j : ℕ, ‖thOp (fun k : Fin s.card => 2 * Real.pi * (-(((s.equivFin.symm k : s) : ℝ))))
            (2 * Real.pi * (2 : ℝ) ^ (-(j : ℝ) - 1)) (F : ℝ → ℂ) x‖ₑ) := by
    filter_upwards [ae_all_iff.mpr (fun j => multiplier_le_thOp F j)] with x hx
    exact iSup_mono (fun j => hx j)
  calc ∫⁻ x, (⨆ j : ℕ, ‖(BoundaryLayer.multiplier (nbhdInd s j) (memLp_nbhdInd s j) F :
        Lp ℂ 2 (volume : Measure ℝ)) x‖ₑ) ^ (2 : ℝ)
      ≤ ∫⁻ x, (⨆ j : ℕ, ‖thOp (fun k : Fin s.card => 2 * Real.pi * (-(((s.equivFin.symm k : s) : ℝ))))
          (2 * Real.pi * (2 : ℝ) ^ (-(j : ℝ) - 1)) (F : ℝ → ℂ) x‖ₑ) ^ (2 : ℝ) :=
        lintegral_mono_ae (hsup.mono (fun x hx => ENNReal.rpow_le_rpow hx (by norm_num)))
    _ ≤ ENNReal.ofReal ((C₂ * Real.log ((s.card : ℝ) + 2) ^ 2) ^ 2) * ‖F‖ₑ ^ (2 : ℝ) := hmain


/-- **The real-line band-pass maximal estimate for an arbitrary finite frequency set**
(Bourgain 1989, Lemma 4.26 in band-pass form).  This is the single remaining analytic gap of the
file; it is derived from Bourgain's Lemma 4.13 (`SmoothWindowMaximal`) by the smooth/boundary
splitting plus the periodisation. -/
theorem realLineBandpassMaximal_of_smoothWindow : BandLift.RealLineBandpassMaximal :=
  realLineBandpassMaximal_of_multiplierBound maximalMultiplierBound_of_smoothWindow

/-- Bourgain 1989 Lemma 4.26 in periodic band-pass form on the real line: for `2^{-3}`-separated
`lam : Fin N → ℝ` the maximal band-pass projection onto the periodised `2^{-j-1}`-neighbourhoods
`R_j = {ξ | ∃ k l, |ξ + l + lam k| ≤ 2^{-j-1}}` is bounded on `L²(ℝ)` by `C (log N)²` in norm
(hence `C (log N)⁴` for the square).  The outer `lintegral` is over `ℝ` (the integration variable
is annotated).  This is the only analytic input needed for the `ℓ²(ℤ)` maximal estimate. -/
theorem separated_real_line_bandpass_maximal_l2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (lam : Fin N → ℝ),
      (∀ i j : Fin N, i ≠ j → (2 : ℝ) ^ (-(3 : ℤ)) ≤ |lam i - lam j|) →
      ∀ (g : ℝ → ℂ), MeasureTheory.MemLp g 2 MeasureTheory.volume →
        ∫⁻ (x : ℝ), (⨆ j : ℕ, ‖∫ ξ in (-(1 / 2) : ℝ)..(1 / 2),
            (𝓕 g) ξ *
              Set.indicator {ξ : ℝ | ∃ k : Fin N, ∃ l : ℤ, |ξ + (l : ℝ) + lam k| ≤ (2 : ℝ) ^ (-(j : ℝ) - 1)}
                (fun _ => (1 : ℂ)) ξ *
              Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ))‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.volume
        ≤ ENNReal.ofReal ((C * Real.log ((N : ℝ) + 2) ^ 2) ^ 2)
            * ∫⁻ (x : ℝ), ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume := by
  obtain ⟨C, hCpos, hC⟩ :=
    BandLift.separated_real_line_bandpass_maximal_l2_real realLineBandpassMaximal_of_smoothWindow
  refine ⟨C, hCpos, fun N lam hsep g hg => ?_⟩
  by_cases hg1 : MeasureTheory.Integrable g
  · simpa only [BandLift.bandPass] using hC N lam hsep g hg1
  · have hzero : (𝓕 g : ℝ → ℂ) = 0 := fourier_eq_zero_of_not_integrable hg1
    have hinner : ∀ (j : ℕ) (x : ℝ), ‖∫ ξ in (-(1 / 2) : ℝ)..(1 / 2), (𝓕 g) ξ *
        Set.indicator {ξ : ℝ | ∃ k : Fin N, ∃ l : ℤ,
          |ξ + (l : ℝ) + lam k| ≤ (2 : ℝ) ^ (-(j : ℝ) - 1)} (fun _ => (1 : ℂ)) ξ *
        Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ))‖ₑ = 0 := by
      intro j x
      rw [hzero]
      simp
    have hsup : ∀ x : ℝ, (⨆ j : ℕ, ‖∫ ξ in (-(1 / 2) : ℝ)..(1 / 2), (𝓕 g) ξ *
        Set.indicator {ξ : ℝ | ∃ k : Fin N, ∃ l : ℤ,
          |ξ + (l : ℝ) + lam k| ≤ (2 : ℝ) ^ (-(j : ℝ) - 1)} (fun _ => (1 : ℂ)) ξ *
        Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ))‖ₑ) = 0 := by
      intro x
      exact iSup_eq_bot.mpr (fun j => hinner j x)
    simp only [hsup]
    simp

end Commons.Analysis.Fourier
