import Mathlib
import Submission.Work.BMF.cubic_le_peak

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Sum of `exp(η j log 2 - (j log 2)³/(D L²))` bounded by its integral plus the maximum

For `D, L > 0`, `η ≥ 0` and every `K : ℕ`,

`∑_{j < K} exp (η j log 2 - (j log 2)³/(D L²)) ≤ exp ((2/9) √(3D) η^{3/2} L)
   + 2 ∫_{(0,∞)} exp (η x log 2 - (x log 2)³/(D L²)) dx`.

Writing `A = η log 2 > 0`, `B = (log 2)³/(D L²) > 0`, the summand is `F j = exp (A j - B j³)`,
a unimodal function whose continuous maximum is attained at `s = √(A/(3B))` and equals
`(2/3) A s = (2/9) √(3D) η^{3/2} L` (the `exp` of which is the first term on the right).
Splitting the range at `m = ⌊s⌋`: on `{0,…,m-1}` `F` is monotone, on `{m+1,…}` it is antitone,
and each piece is dominated by the corresponding integral (Mathlib's
`MonotoneOn.sum_le_integral_Ico`, `AntitoneOn.sum_le_integral_Ico`); the single middle term
`F m` is bounded by the maximum.
-/

namespace Work.BMF

open MeasureTheory Real

/-- `x ↦ exp (A x - B x³)` is monotone on `[0, √(A/(3B))]` for `A ≥ 0`, `B > 0`. -/
private theorem exp_cubic_monoOn_aux (A B : ℝ) (hA : 0 ≤ A) (hB : 0 < B) :
    MonotoneOn (fun x : ℝ => Real.exp (A * x - B * x ^ 3))
      (Set.Icc 0 (Real.sqrt (A / (3 * B)))) := by
  intro x hx y hy hxy
  simp only [Set.mem_Icc] at hx hy
  apply Real.exp_le_exp.mpr
  have h3B : 0 < 3 * B := by linarith
  have hss : 0 ≤ Real.sqrt (A / (3 * B)) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt (A / (3 * B))) ^ 2 = A / (3 * B) :=
    Real.sq_sqrt (div_nonneg hA h3B.le)
  have hAeq : A = 3 * B * (Real.sqrt (A / (3 * B))) ^ 2 := by rw [hs2]; field_simp
  have hx0 : 0 ≤ x := hx.1
  have hx_s : x ≤ Real.sqrt (A / (3 * B)) := le_trans hxy hy.2
  have hy_s : y ≤ Real.sqrt (A / (3 * B)) := hy.2
  have hy0 : 0 ≤ y := le_trans hx0 hxy
  have h1 : x ^ 2 ≤ (Real.sqrt (A / (3 * B))) ^ 2 := by nlinarith [hx0, hx_s, hss]
  have h2 : y ^ 2 ≤ (Real.sqrt (A / (3 * B))) ^ 2 := by nlinarith [hy0, hy_s, hss]
  have h3 : x * y ≤ (Real.sqrt (A / (3 * B))) ^ 2 := by nlinarith [hx0, hx_s, hy_s, hss]
  have hY : y ^ 2 + x * y + x ^ 2 ≤ 3 * (Real.sqrt (A / (3 * B))) ^ 2 := by linarith
  have hkey : A * y - B * y ^ 3 - (A * x - B * x ^ 3) ≥ 0 := by
    have hfac : A * y - B * y ^ 3 - (A * x - B * x ^ 3)
        = (y - x) * (A - B * (y ^ 2 + x * y + x ^ 2)) := by ring
    rw [hfac]
    apply mul_nonneg (by linarith)
    rw [hAeq, show 3 * B * (Real.sqrt (A / (3 * B))) ^ 2
          - B * (y ^ 2 + x * y + x ^ 2)
        = B * (3 * (Real.sqrt (A / (3 * B))) ^ 2 - (y ^ 2 + x * y + x ^ 2)) by ring]
    exact mul_nonneg hB.le (by linarith)
  linarith

/-- `x ↦ exp (A x - B x³)` is antitone on `[√(A/(3B)), ∞)` for `B > 0`. -/
private theorem exp_cubic_antitoneOn_aux (A B : ℝ) (hB : 0 < B) :
    AntitoneOn (fun x : ℝ => Real.exp (A * x - B * x ^ 3))
      (Set.Ici (Real.sqrt (A / (3 * B)))) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  rw [Real.exp_le_exp]
  have hs0 : 0 ≤ Real.sqrt (A / (3 * B)) := Real.sqrt_nonneg _
  have hx0 : 0 ≤ x := le_trans hs0 hx
  have hy0 : 0 ≤ y := le_trans hx0 hxy
  have hfac : A * y - B * y ^ 3 - (A * x - B * x ^ 3)
      = (y - x) * (A - B * (y ^ 2 + x * y + x ^ 2)) := by ring
  have hAB : A - B * (y ^ 2 + x * y + x ^ 2) ≤ 0 := by
    rcases le_or_gt 0 A with hA | hA
    · have h3B : 0 < 3 * B := by linarith
      have hs2 : (Real.sqrt (A / (3 * B))) ^ 2 = A / (3 * B) :=
        Real.sq_sqrt (div_nonneg hA h3B.le)
      have hAeq : A = 3 * B * (Real.sqrt (A / (3 * B))) ^ 2 := by rw [hs2]; field_simp
      have h1 : (Real.sqrt (A / (3 * B))) ^ 2 ≤ x ^ 2 := by nlinarith [hx, hs0]
      have h2 : (Real.sqrt (A / (3 * B))) ^ 2 ≤ y ^ 2 := by nlinarith [hy, hs0]
      have h3 : (Real.sqrt (A / (3 * B))) ^ 2 ≤ x * y := by nlinarith [hx, hy, hs0]
      have hY : 3 * (Real.sqrt (A / (3 * B))) ^ 2 ≤ y ^ 2 + x * y + x ^ 2 := by linarith
      rw [hAeq, show 3 * B * (Real.sqrt (A / (3 * B))) ^ 2
            - B * (y ^ 2 + x * y + x ^ 2)
          = B * (3 * (Real.sqrt (A / (3 * B))) ^ 2 - (y ^ 2 + x * y + x ^ 2)) by ring]
      exact mul_nonpos_of_nonneg_of_nonpos hB.le (by linarith)
    · have hnonneg : 0 ≤ y ^ 2 + x * y + x ^ 2 := by
        nlinarith [sq_nonneg x, sq_nonneg y, hx0, hy0]
      have hBnn : 0 ≤ B * (y ^ 2 + x * y + x ^ 2) := mul_nonneg hB.le hnonneg
      nlinarith [hBnn, hA]
  have h1 : 0 ≤ y - x := by linarith
  have : A * y - B * y ^ 3 - (A * x - B * x ^ 3) ≤ 0 := by
    rw [hfac]; exact mul_nonpos_of_nonneg_of_nonpos h1 hAB
  linarith

/-- `x ↦ exp (A x - B x³)` is integrable on `(0, ∞)` for `B > 0`. -/
private theorem integrableOn_exp_cubic_aux (A B : ℝ) (hB : 0 < B) :
    MeasureTheory.IntegrableOn (fun x : ℝ => Real.exp (A * x - B * x ^ 3)) (Set.Ioi 0) := by
  refine integrable_of_isBigO_exp_neg (a := 0) (b := 1) one_pos
    ((by fun_prop : Continuous (fun x : ℝ => Real.exp (A * x - B * x ^ 3))).continuousOn) ?_
  refine Asymptotics.IsBigO.of_bound' ?_
  filter_upwards [Filter.eventually_ge_atTop (max 1 ((A + 1) / B + 1))] with x hx
  rw [Real.norm_of_nonneg (Real.exp_nonneg _), Real.norm_of_nonneg (Real.exp_nonneg _)]
  apply Real.exp_le_exp.mpr
  have h1 : (1 : ℝ) ≤ x := le_trans (le_max_left _ _) hx
  have h2 : (A + 1) / B + 1 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 ≤ x := le_trans zero_le_one h1
  rcases le_or_gt (A + 1) 0 with hA1 | hA1
  · have hBx : 0 ≤ B * x ^ 3 := mul_nonneg hB.le (pow_nonneg hx0 3)
    have hAx : (A + 1) * x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hA1 hx0
    nlinarith [hBx, hAx, hx0]
  · have hx2 : (A + 1) / B ≤ x ^ 2 := by
      have hle : (A + 1) / B ≤ x := by linarith
      nlinarith [hle, h1, hx0]
    have hAx : A + 1 ≤ B * x ^ 2 := by
      rw [div_le_iff₀ hB] at hx2; linarith
    have h3 : (A + 1) * x ≤ B * x ^ 2 * x := mul_le_mul_of_nonneg_right hAx hx0
    nlinarith [h3, hx0]

/-- Closed form of the continuous maximum of the summand. -/
private theorem peak_value_eq_aux (D L η : ℝ) (hD : 0 < D) (hL : 0 < L) (hη : 0 ≤ η) :
    (2 / 3) * (η * Real.log 2) *
        Real.sqrt ((η * Real.log 2) / (3 * ((Real.log 2) ^ 3 / (D * L ^ 2))))
      = (2 / 9) * Real.sqrt (3 * D) * η ^ (3 / 2 : ℝ) * L := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hDL2 : (0 : ℝ) < D * L ^ 2 := mul_pos hD (pow_pos hL 2)
  have hL2ne : Real.log 2 ≠ 0 := ne_of_gt hlog2
  have hDL2ne : D * L ^ 2 ≠ 0 := ne_of_gt hDL2
  have hrpow : η ^ (3 / 2 : ℝ) = η * Real.sqrt η := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add' hη (by norm_num : (1 : ℝ) + 1 / 2 ≠ 0),
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hrpow]
  set Y := (η * Real.log 2) / (3 * ((Real.log 2) ^ 3 / (D * L ^ 2))) with hY
  have hYnn : 0 ≤ Y := by
    rw [hY]
    exact div_nonneg (mul_nonneg hη hlog2.le)
      (mul_nonneg (by norm_num) (div_nonneg (pow_nonneg hlog2.le 3) hDL2.le))
  have h3Dnn : 0 ≤ 3 * D := by positivity
  have hnn2 : 0 ≤ η * Real.sqrt η := mul_nonneg hη (Real.sqrt_nonneg η)
  have hLnn : 0 ≤ (2 / 3) * (η * Real.log 2) * Real.sqrt Y :=
    mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hη hlog2.le)) (Real.sqrt_nonneg _)
  have hRnn : 0 ≤ (2 / 9) * Real.sqrt (3 * D) * (η * Real.sqrt η) * L :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hnn2) hL.le
  apply (pow_left_inj₀ hLnn hRnn (by norm_num : (2 : ℕ) ≠ 0)).mp
  have hsqL : ((2 / 3) * (η * Real.log 2) * Real.sqrt Y) ^ 2
      = (4 / 9) * (η * Real.log 2) ^ 2 * Y := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hYnn]; try ring
  have hsqR : ((2 / 9) * Real.sqrt (3 * D) * (η * Real.sqrt η) * L) ^ 2
      = (2 / 9) ^ 2 * (3 * D) * η ^ 3 * L ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt h3Dnn, mul_pow, Real.sq_sqrt hη]; try ring
  rw [hsqL, hsqR, hY]
  field_simp
  ring

/-- The two terms straddling the continuous maximum of `x ↦ exp (A x - B x³)` cost at most
the maximum `exp ((2/3) A s)`, `s = √(A/(3B))`, plus the integral of `exp (A x - B x³)` over the
unit interval `[N, N+1]` containing `s`.  This is the "middle" comparison used when the integer
`N = ⌊s⌋` cannot be split into a monotone and an antitone part. -/
private theorem exp_cubic_middle_aux (A B : ℝ) (hA : 0 ≤ A) (hB : 0 < B) (N : ℕ)
    (h1 : (N : ℝ) ≤ Real.sqrt (A / (3 * B))) (h2 : Real.sqrt (A / (3 * B)) ≤ (N : ℝ) + 1) :
    Real.exp (A * (N : ℝ) - B * (N : ℝ) ^ 3)
        + Real.exp (A * ((N : ℝ) + 1) - B * ((N : ℝ) + 1) ^ 3)
      ≤ Real.exp ((2 / 3) * A * Real.sqrt (A / (3 * B)))
        + ∫ x in (N : ℝ)..((N : ℝ) + 1), Real.exp (A * x - B * x ^ 3) := by
  let s : ℝ := Real.sqrt (A / (3 * B))
  let F0 : ℝ → ℝ := fun x => Real.exp (A * x - B * x ^ 3)
  have h3B : 0 < 3 * B := by linarith
  have hs_nn : 0 ≤ s := Real.sqrt_nonneg _
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hs2 : s ^ 2 = A / (3 * B) := Real.sq_sqrt (div_nonneg hA h3B.le)
  have hFs : F0 s = Real.exp ((2 / 3) * A * s) := by
    show Real.exp (A * s - B * s ^ 3) = Real.exp ((2 / 3) * A * s)
    congr 1
    rw [show A * s - B * s ^ 3 = A * s - B * s * s ^ 2 by ring, hs2]
    field_simp
    ring
  have hmono : MonotoneOn F0 (Set.Icc 0 s) := exp_cubic_monoOn_aux A B hA hB
  have hanti : AntitoneOn F0 (Set.Ici s) := exp_cubic_antitoneOn_aux A B hB
  have hF0cont : Continuous F0 := by
    change Continuous (fun x : ℝ => Real.exp (A * x - B * x ^ 3))
    fun_prop
  have hFN : F0 (N : ℝ) ≤ Real.exp ((2 / 3) * A * s) := by
    rw [← hFs]
    exact hmono (a := (N : ℝ)) (b := s) ⟨hN0, h1⟩ ⟨hs_nn, le_refl s⟩ h1
  have hFN1 : F0 ((N : ℝ) + 1) ≤ Real.exp ((2 / 3) * A * s) := by
    rw [← hFs]
    exact hanti (a := s) (b := (N : ℝ) + 1) (le_refl s) h2 h2
  have hpt : ∀ x ∈ Set.Icc (N : ℝ) ((N : ℝ) + 1),
      min (F0 (N : ℝ)) (F0 ((N : ℝ) + 1)) ≤ F0 x := by
    intro x hx
    simp only [Set.mem_Icc] at hx
    have hx0 : (0 : ℝ) ≤ x := le_trans hN0 hx.1
    rcases le_or_gt x s with hxs | hxs
    · exact le_trans (min_le_left _ _) (hmono (a := (N : ℝ)) (b := x) ⟨hN0, h1⟩ ⟨hx0, hxs⟩ hx.1)
    · exact le_trans (min_le_right _ _)
        (hanti (a := x) (b := (N : ℝ) + 1) (le_of_lt hxs) h2 hx.2)
  have hmin_le : min (F0 (N : ℝ)) (F0 ((N : ℝ) + 1))
      ≤ ∫ x in (N : ℝ)..((N : ℝ) + 1), F0 x := by
    have hmm := intervalIntegral.integral_mono_on
      (f := fun _ : ℝ => min (F0 (N : ℝ)) (F0 ((N : ℝ) + 1))) (g := F0)
      (a := (N : ℝ)) (b := (N : ℝ) + 1) (show (N : ℝ) ≤ (N : ℝ) + 1 by linarith)
      (intervalIntegrable_const (μ := volume) :
        IntervalIntegrable (fun _ : ℝ => min (F0 (N : ℝ)) (F0 ((N : ℝ) + 1))) volume (N : ℝ) ((N : ℝ) + 1))
      (hF0cont.intervalIntegrable (N : ℝ) ((N : ℝ) + 1)) hpt
    rw [intervalIntegral.integral_const,
      show ((N : ℝ) + 1) - (N : ℝ) = 1 by ring, one_smul] at hmm
    exact hmm
  have hmax : max (F0 (N : ℝ)) (F0 ((N : ℝ) + 1)) ≤ Real.exp ((2 / 3) * A * s) :=
    max_le hFN hFN1
  have hsum : F0 (N : ℝ) + F0 ((N : ℝ) + 1)
      = max (F0 (N : ℝ)) (F0 ((N : ℝ) + 1)) + min (F0 (N : ℝ)) (F0 ((N : ℝ) + 1)) := by
    rcases le_total (F0 (N : ℝ)) (F0 ((N : ℝ) + 1)) with h | h
    · rw [max_eq_right h, min_eq_left h]; try ring
    · rw [max_eq_left h, min_eq_right h]; try ring
  have hgoal : F0 (N : ℝ) + F0 ((N : ℝ) + 1)
      ≤ Real.exp ((2 / 3) * A * s) + ∫ x in (N : ℝ)..((N : ℝ) + 1), F0 x := by
    linarith [hmax, hmin_le, hsum]
  exact hgoal

theorem sum_exp_le_integral_add_max (D L η : ℝ) (hD : 0 < D) (hL : 0 < L) (hη : 0 ≤ η) (K : ℕ) :
    ∑ j ∈ Finset.range K,
        Real.exp (η * (j : ℝ) * Real.log 2 - ((j : ℝ) * Real.log 2) ^ 3 / (D * L ^ 2)) ≤
      Real.exp ((2 / 9) * Real.sqrt (3 * D) * η ^ (3 / 2 : ℝ) * L) +
        2 * ∫ x in Set.Ioi (0 : ℝ),
          Real.exp (η * x * Real.log 2 - (x * Real.log 2) ^ 3 / (D * L ^ 2)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hDL2pos : 0 < D * L ^ 2 := mul_pos hD (pow_pos hL 2)
  obtain ⟨aa, haa⟩ : ∃ a : ℝ, a = η * Real.log 2 := ⟨_, rfl⟩
  obtain ⟨bb, hbb⟩ : ∃ b : ℝ, b = (Real.log 2) ^ 3 / (D * L ^ 2) := ⟨_, rfl⟩
  have haa_nn : 0 ≤ aa := by rw [haa]; exact mul_nonneg hη hlog2.le
  have hbb_pos : 0 < bb := by rw [hbb]; exact div_pos (pow_pos hlog2 3) hDL2pos
  have hfeq : ∀ x : ℝ,
      η * x * Real.log 2 - (x * Real.log 2) ^ 3 / (D * L ^ 2) = aa * x - bb * x ^ 3 := by
    intro x; rw [haa, hbb]; ring
  let F0 : ℝ → ℝ := fun x => Real.exp (aa * x - bb * x ^ 3)
  have hsum_eq : (∑ j ∈ Finset.Ico 0 K,
        Real.exp (η * (j : ℝ) * Real.log 2 - ((j : ℝ) * Real.log 2) ^ 3 / (D * L ^ 2)))
      = ∑ j ∈ Finset.Ico 0 K, F0 (j : ℝ) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [F0, hfeq]
  have hI_eq : (∫ x in Set.Ioi (0 : ℝ),
        Real.exp (η * x * Real.log 2 - (x * Real.log 2) ^ 3 / (D * L ^ 2)))
      = ∫ x in Set.Ioi (0 : ℝ), F0 x := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    simp only [F0, hfeq]
  let m : ℕ := ⌊Real.sqrt (aa / (3 * bb))⌋₊
  have hm_le : (m : ℝ) ≤ Real.sqrt (aa / (3 * bb)) :=
    (Nat.le_floor_iff (Real.sqrt_nonneg _)).mp le_rfl
  have hm_lt : Real.sqrt (aa / (3 * bb)) < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hss_le : Real.sqrt (aa / (3 * bb)) ≤ ((m + 1 : ℕ) : ℝ) := by
    push_cast; linarith
  have hInt : MeasureTheory.IntegrableOn F0 (Set.Ioi 0) :=
    integrableOn_exp_cubic_aux aa bb hbb_pos
  have hInt_le : ∀ (a b : ℝ), 0 ≤ a → a ≤ b →
      (∫ x in a..b, F0 x) ≤ ∫ x in Set.Ioi (0 : ℝ), F0 x := by
    intro a b ha hab
    rw [intervalIntegral.integral_of_le hab]
    refine setIntegral_mono_set hInt (by filter_upwards with x; exact Real.exp_nonneg _) ?_
    filter_upwards with x hx
    simp only [Set.mem_Ioc] at hx
    simp only [Set.mem_Ioi]
    linarith [hx.1, ha]
  have hI_nn : 0 ≤ ∫ x in Set.Ioi (0 : ℝ), F0 x :=
    setIntegral_nonneg measurableSet_Ioi (fun x _ => Real.exp_nonneg _)
  have hpeakE : Real.exp ((2 / 3) * aa * Real.sqrt (aa / (3 * bb)))
      = Real.exp ((2 / 9) * Real.sqrt (3 * D) * η ^ (3 / 2 : ℝ) * L) := by
    congr 1
    rw [haa, hbb]
    exact peak_value_eq_aux D L η hD hL hη
  have hmain : (∑ j ∈ Finset.Ico 0 K, F0 (j : ℝ))
      ≤ Real.exp ((2 / 9) * Real.sqrt (3 * D) * η ^ (3 / 2 : ℝ) * L)
        + 2 * ∫ x in Set.Ioi (0 : ℝ), F0 x := by
    rcases le_or_gt K m with hKm | hmK
    · -- Case K ≤ m: whole sum lies in the monotone range.
      have hK_le : (K : ℝ) ≤ Real.sqrt (aa / (3 * bb)) := by
        have h1 : (K : ℝ) ≤ (m : ℝ) := by exact_mod_cast hKm
        linarith [hm_le]
      have hmono : MonotoneOn F0 (Set.Icc (0 : ℝ) (K : ℝ)) :=
        (exp_cubic_monoOn_aux aa bb haa_nn hbb_pos).mono
          (fun x hx => ⟨hx.1, le_trans hx.2 hK_le⟩)
      have hb1 : (∑ j ∈ Finset.Ico 0 K, F0 (j : ℝ)) ≤ ∫ x in (0 : ℝ)..(K : ℝ), F0 x := by
        simpa only [Nat.cast_zero] using
          (MonotoneOn.sum_le_integral_Ico (f := F0) (a := 0) (b := K) (Nat.zero_le K)
            (by simpa only [Nat.cast_zero] using hmono))
      have hb2 : (∫ x in (0 : ℝ)..(K : ℝ), F0 x) ≤ ∫ x in Set.Ioi (0 : ℝ), F0 x :=
        hInt_le 0 (K : ℝ) le_rfl (by positivity)
      calc (∑ j ∈ Finset.Ico 0 K, F0 (j : ℝ))
          ≤ (∫ x in (0 : ℝ)..(K : ℝ), F0 x) := hb1
        _ ≤ ∫ x in Set.Ioi (0 : ℝ), F0 x := hb2
        _ ≤ Real.exp ((2 / 9) * Real.sqrt (3 * D) * η ^ (3 / 2 : ℝ) * L)
              + 2 * ∫ x in Set.Ioi (0 : ℝ), F0 x := by
            have := Real.exp_nonneg ((2 / 9) * Real.sqrt (3 * D) * η ^ (3 / 2 : ℝ) * L)
            linarith
    · -- Case m < K: split at the peak; the two middle terms are handled by `exp_cubic_middle_aux`.
      have hm1K : m + 1 ≤ K := hmK
      have hstep : (∑ j ∈ Finset.Ico 0 K, F0 (j : ℝ))
          = (∑ j ∈ Finset.Ico 0 m, F0 (j : ℝ)) + F0 (m : ℝ)
            + ∑ j ∈ Finset.Ico (m + 1) K, F0 (j : ℝ) := by
        rw [← Finset.sum_Ico_consecutive (fun j : ℕ => F0 (j : ℝ)) (Nat.zero_le (m + 1)) hm1K,
          Finset.sum_Ico_succ_top (Nat.zero_le m) (fun j : ℕ => F0 (j : ℝ))]
      have hA1 : (∑ j ∈ Finset.Ico 0 m, F0 (j : ℝ)) ≤ ∫ x in (0 : ℝ)..(m : ℝ), F0 x := by
        have hmono : MonotoneOn F0 (Set.Icc (0 : ℝ) (m : ℝ)) :=
          (exp_cubic_monoOn_aux aa bb haa_nn hbb_pos).mono
            (fun x hx => ⟨hx.1, le_trans hx.2 hm_le⟩)
        simpa only [Nat.cast_zero] using
          (MonotoneOn.sum_le_integral_Ico (f := F0) (a := 0) (b := m) (Nat.zero_le m)
            (by simpa only [Nat.cast_zero] using hmono))
      have hmid : F0 (m : ℝ) + F0 ((m : ℝ) + 1)
          ≤ Real.exp ((2 / 9) * Real.sqrt (3 * D) * η ^ (3 / 2 : ℝ) * L)
            + ∫ x in (m : ℝ)..((m : ℝ) + 1), F0 x := by
        calc F0 (m : ℝ) + F0 ((m : ℝ) + 1)
            ≤ Real.exp ((2 / 3) * aa * Real.sqrt (aa / (3 * bb)))
                + ∫ x in (m : ℝ)..((m : ℝ) + 1), F0 x :=
              exp_cubic_middle_aux aa bb haa_nn hbb_pos m hm_le hm_lt.le
          _ = Real.exp ((2 / 9) * Real.sqrt (3 * D) * η ^ (3 / 2 : ℝ) * L)
                + ∫ x in (m : ℝ)..((m : ℝ) + 1), F0 x := by rw [hpeakE]
      have hR2 : (∑ j ∈ Finset.Ico (m + 2) K, F0 (j : ℝ))
          ≤ ∫ x in Set.Ioi ((m : ℝ) + 1), F0 x := by
        have hanti' : AntitoneOn F0 (Set.Icc ((m + 1 : ℕ) : ℝ) ((K - 1 : ℕ) : ℝ)) :=
          (exp_cubic_antitoneOn_aux aa bb hbb_pos).mono (fun x hx => by
            simp only [Set.mem_Icc] at hx; exact le_trans hss_le hx.1)
        have hInt' : MeasureTheory.IntegrableOn F0 (Set.Ioi ((m + 1 : ℕ) : ℝ)) :=
          hInt.mono_set (by
            rintro x (hx : ((m + 1 : ℕ) : ℝ) < x)
            exact lt_of_le_of_lt (Nat.cast_nonneg (m + 1)) hx)
        have h := AntitoneOn.sum_Ico_le_integral (f := F0) (a := m + 1) (b := K - 1) hanti'
          hInt' (fun t _ => Real.exp_nonneg _)
        rw [Finset.sum_Ico_add' (fun k : ℕ => F0 (k : ℝ)) (m + 1) (K - 1) 1] at h
        have hK1 : 1 ≤ K := by omega
        rw [show m + 1 + 1 = m + 2 by omega, Nat.sub_add_cancel hK1,
          Nat.cast_add, Nat.cast_one] at h
        exact h
      have hR : (∑ j ∈ Finset.Ico (m + 1) K, F0 (j : ℝ))
          ≤ F0 ((m : ℝ) + 1) + ∑ j ∈ Finset.Ico (m + 2) K, F0 (j : ℝ) := by
        rcases lt_or_ge (m + 1) K with hK | hK
        · have hcons := Finset.sum_Ico_consecutive (fun j : ℕ => F0 (j : ℝ))
            (show m + 1 ≤ m + 2 by omega) (show m + 2 ≤ K by omega)
          have hsingle : (∑ j ∈ Finset.Ico (m + 1) (m + 2), F0 (j : ℝ)) = F0 ((m : ℝ) + 1) := by
            rw [Finset.sum_Ico_succ_top (le_refl (m + 1)) (fun j : ℕ => F0 (j : ℝ)),
              Finset.Ico_self, Finset.sum_empty, zero_add]
            simp only [Nat.cast_add, Nat.cast_one]
          exact le_of_eq (by rw [← hcons, hsingle])
        · have hK' : K = m + 1 := le_antisymm hK hm1K
          rw [hK', Finset.Ico_self, Finset.sum_empty]
          exact add_nonneg (Real.exp_nonneg _)
            (Finset.sum_nonneg (fun j _ => Real.exp_nonneg _))
      have hadd1 : (∫ x in (0 : ℝ)..(m : ℝ), F0 x) + ∫ x in (m : ℝ)..((m : ℝ) + 1), F0 x
          = ∫ x in (0 : ℝ)..((m : ℝ) + 1), F0 x :=
        intervalIntegral.integral_add_adjacent_intervals
          (by apply Continuous.intervalIntegrable; fun_prop)
          (by apply Continuous.intervalIntegrable; fun_prop)
      have hadd2 : (∫ x in (0 : ℝ)..((m : ℝ) + 1), F0 x)
            + ∫ x in Set.Ioi ((m : ℝ) + 1), F0 x
          = ∫ x in Set.Ioi (0 : ℝ), F0 x :=
        intervalIntegral.integral_interval_add_Ioi hInt
          (hInt.mono_set (by intro x hx; simp only [Set.mem_Ioi] at hx ⊢; linarith [hx]))
      rw [hstep]
      linarith [hA1, hmid, hR, hR2, hadd1, hadd2, hI_nn,
        Real.exp_nonneg ((2 / 9) * Real.sqrt (3 * D) * η ^ (3 / 2 : ℝ) * L)]
  rw [Finset.range_eq_Ico, hsum_eq, hI_eq]
  exact hmain

end Work.BMF
