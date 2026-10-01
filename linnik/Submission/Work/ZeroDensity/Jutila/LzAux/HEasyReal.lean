import Mathlib
import Submission.Work.ZeroDensity.Jutila.LzAux.MertSumLower
import Submission.Work.ZeroDensity.Jutila.grahamDefs
import Submission.Work.ZeroDensity.Jutila.bvDefs
import Submission.Work.ZeroDensity.Jutila.mixedSelbergDefs
import Submission.Work.ZeroDensity.Jutila.MsqDiag
import Submission.Work.ZeroDensity.Jutila.MsqSelErr
import Submission.Work.ZeroDensity.Jutila.grahamBilinearReindex
import Submission.Work.LinnikAreas.Density4.sum_mu_sq_div_totient_sharp
import Submission.Work.LinnikAreas.Density4.sum_abs_selLam_le

namespace Work.ZeroDensity.Jutila.LzAux

open Finset

noncomputable section

/-- `Lz z n` written with the integer cutoff `⌊z⌋₊` (for `z ≥ 0`). -/
lemma HE_Lz_eq_filter_floor (z : ℝ) (hz : 0 ≤ z) (n : ℕ) :
    Work.ZeroDensity.Jutila.Lz z n =
      ∑ d ∈ n.divisors.filter (fun d : ℕ => d ≤ ⌊z⌋₊), Work.ZeroDensity.Jutila.selW z d := by
  unfold Work.ZeroDensity.Jutila.Lz Work.ZeroDensity.Jutila.selW
  refine Finset.sum_congr ?_ (fun d _ => rfl)
  ext d
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hd, hdz⟩
    exact ⟨hd, Nat.le_floor (by exact_mod_cast hdz)⟩
  · rintro ⟨hd, hdfl⟩
    have h1 : (d : ℝ) ≤ (⌊z⌋₊ : ℝ) := by exact_mod_cast hdfl
    have h2 : (⌊z⌋₊ : ℝ) ≤ z := Nat.floor_le hz
    exact ⟨hd, le_trans h1 h2⟩

/-- Pointwise bound for the Selberg weight of a real cutoff. -/
lemma HE_abs_selW_le_log (z : ℝ) (hz : 1 ≤ z) (d : ℕ) (hd1 : 1 ≤ d) (hdz : (d : ℝ) ≤ z) :
    |Work.ZeroDensity.Jutila.selW z d| ≤ Real.log (z / (d : ℝ)) := by
  have hzpos : 0 < z := by linarith
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  have hge1 : 1 ≤ z / (d : ℝ) := by
    rw [le_div_iff₀ hdpos, one_mul]; exact hdz
  have hlog : 0 ≤ Real.log (z / (d : ℝ)) := Real.log_nonneg hge1
  have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
    have h := ArithmeticFunction.abs_moebius_le_one (n := d)
    rw [← Int.cast_abs]
    exact_mod_cast h
  rw [Work.ZeroDensity.Jutila.selW, abs_mul]
  calc |(ArithmeticFunction.moebius d : ℝ)| * |Real.log (z / (d : ℝ))|
      ≤ 1 * |Real.log (z / (d : ℝ))| := mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
    _ = Real.log (z / (d : ℝ)) := by rw [one_mul, abs_of_nonneg hlog]

/-- `Σ_{d ≤ ⌊z⌋₊} |selW z d| ≤ z` for every real `z ≥ 1`. -/
lemma HE_sum_abs_selW_le (z : ℝ) (hz : 1 ≤ z) :
    ∑ d ∈ Finset.Icc 1 ⌊z⌋₊, |Work.ZeroDensity.Jutila.selW z d| ≤ z := by
  have hzpos : 0 < z := by linarith
  set m : ℕ := ⌊z⌋₊ with hm
  have hm1 : 1 ≤ m := by
    rw [hm]; exact Nat.le_floor (by exact_mod_cast hz)
  have hle : (∑ d ∈ Finset.Icc 1 m, |Work.ZeroDensity.Jutila.selW z d|)
      ≤ ∑ d ∈ Finset.Icc 1 m, Real.log (z / (d : ℝ)) := by
    apply Finset.sum_le_sum
    intro d hd
    rw [Finset.mem_Icc] at hd
    exact HE_abs_selW_le_log z hz d hd.1
      (le_trans (by exact_mod_cast hd.2) (Nat.floor_le (le_of_lt hzpos)))
  have hsplit : (∑ d ∈ Finset.Icc 1 m, Real.log (z / (d : ℝ)))
      = ∑ d ∈ Finset.Icc 1 m, (Real.log (z / (m : ℝ)) + Real.log ((m : ℝ) / (d : ℝ))) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    rw [← Real.log_mul (by positivity : (z / (m : ℝ)) ≠ 0) (by positivity : ((m : ℝ) / (d : ℝ)) ≠ 0)]
    congr 1
    field_simp
  have hsum1 : (∑ d ∈ Finset.Icc 1 m, (Real.log (z / (m : ℝ)) + Real.log ((m : ℝ) / (d : ℝ))))
      = (m : ℝ) * Real.log (z / (m : ℝ))
        + ∑ d ∈ Finset.Icc 1 m, Real.log ((m : ℝ) / (d : ℝ)) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    norm_num
  have hcard_le := Work.LinnikAreas.Density4.sum_log_div_le m hm1
  have hlogbound : (m : ℝ) * Real.log (z / (m : ℝ)) + (m : ℝ) ≤ z := by
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have h1 : Real.log (z / (m : ℝ)) ≤ z / (m : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hmpos)
    have h3 : (m : ℝ) * (z / (m : ℝ) - 1) = z - (m : ℝ) := by field_simp
    linarith
  calc (∑ d ∈ Finset.Icc 1 m, |Work.ZeroDensity.Jutila.selW z d|)
        ≤ ∑ d ∈ Finset.Icc 1 m, Real.log (z / (d : ℝ)) := hle
    _ = ∑ d ∈ Finset.Icc 1 m, (Real.log (z / (m : ℝ)) + Real.log ((m : ℝ) / (d : ℝ))) := hsplit
    _ = (m : ℝ) * Real.log (z / (m : ℝ)) + ∑ d ∈ Finset.Icc 1 m, Real.log ((m : ℝ) / (d : ℝ)) := hsum1
    _ ≤ (m : ℝ) * Real.log (z / (m : ℝ)) + (m : ℝ) := by linarith [hcard_le]
    _ ≤ z := hlogbound

/-- Floor comparison: `(⌊N/l⌋ : ℝ) ≤ N/l ≤ (⌊N/l⌋ : ℝ) + 1`. -/
lemma HE_floorDiv_bounds (N l : ℕ) (hl : 0 < l) :
    ((N / l : ℕ) : ℝ) ≤ (N : ℝ) / (l : ℝ)
      ∧ (N : ℝ) / (l : ℝ) - ((N / l : ℕ) : ℝ) ≤ 1 := by
  have h1 : ((N / l : ℕ) : ℝ) = (⌊(N : ℝ) / (l : ℝ)⌋₊ : ℝ) := by
    rw [Nat.floor_div_natCast, Nat.floor_natCast]
  constructor
  · rw [h1]; exact Nat.floor_le (by positivity)
  · rw [h1]
    have h := Nat.lt_floor_add_one ((N : ℝ) / (l : ℝ))
    linarith

/-- Replacing `⌊N/lcm(d,e)⌋` by `N/lcm(d,e)` costs at most `z₁·z₂`. -/
lemma HE_grahamFloorErr (z₁ z₂ : ℝ) (hz1 : 1 ≤ z₁) (hz2 : 1 ≤ z₂) (N : ℕ) :
    |(∑ d ∈ Finset.Icc 1 ⌊z₁⌋₊, ∑ e ∈ Finset.Icc 1 ⌊z₂⌋₊,
          Work.ZeroDensity.Jutila.selW z₁ d * Work.ZeroDensity.Jutila.selW z₂ e
            * ((N / Nat.lcm d e : ℕ) : ℝ))
        - (N : ℝ) * Work.ZeroDensity.Jutila.Msq z₁ z₂| ≤ z₁ * z₂ := by
  have hNm : (N : ℝ) * Work.ZeroDensity.Jutila.Msq z₁ z₂
      = ∑ d ∈ Finset.Icc 1 ⌊z₁⌋₊, ∑ e ∈ Finset.Icc 1 ⌊z₂⌋₊,
          Work.ZeroDensity.Jutila.selW z₁ d * Work.ZeroDensity.Jutila.selW z₂ e
            * ((N : ℝ) / (Nat.lcm d e : ℝ)) := by
    rw [Work.ZeroDensity.Jutila.Msq, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro d _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro e _
    ring
  have hpoint : ∀ d ∈ Finset.Icc 1 ⌊z₁⌋₊, ∀ e ∈ Finset.Icc 1 ⌊z₂⌋₊,
      |((N / Nat.lcm d e : ℕ) : ℝ) - (N : ℝ) / (Nat.lcm d e : ℝ)| ≤ 1 := by
    intro d hd e he
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have hl : 0 < Nat.lcm d e := Nat.lcm_pos (by omega) (by omega)
    have hb := HE_floorDiv_bounds N (Nat.lcm d e) hl
    rw [abs_le]
    exact ⟨by linarith [hb.2], by linarith [hb.1]⟩
  have hEq : (∑ d ∈ Finset.Icc 1 ⌊z₁⌋₊, ∑ e ∈ Finset.Icc 1 ⌊z₂⌋₊,
          Work.ZeroDensity.Jutila.selW z₁ d * Work.ZeroDensity.Jutila.selW z₂ e
            * ((N / Nat.lcm d e : ℕ) : ℝ))
        - (N : ℝ) * Work.ZeroDensity.Jutila.Msq z₁ z₂
      = ∑ d ∈ Finset.Icc 1 ⌊z₁⌋₊, ∑ e ∈ Finset.Icc 1 ⌊z₂⌋₊,
          Work.ZeroDensity.Jutila.selW z₁ d * Work.ZeroDensity.Jutila.selW z₂ e
            * (((N / Nat.lcm d e : ℕ) : ℝ) - (N : ℝ) / (Nat.lcm d e : ℝ)) := by
    rw [hNm, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro d _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro e _
    ring
  rw [hEq]
  calc |∑ d ∈ Finset.Icc 1 ⌊z₁⌋₊, ∑ e ∈ Finset.Icc 1 ⌊z₂⌋₊,
          Work.ZeroDensity.Jutila.selW z₁ d * Work.ZeroDensity.Jutila.selW z₂ e
            * (((N / Nat.lcm d e : ℕ) : ℝ) - (N : ℝ) / (Nat.lcm d e : ℝ))|
      ≤ ∑ d ∈ Finset.Icc 1 ⌊z₁⌋₊,
          |∑ e ∈ Finset.Icc 1 ⌊z₂⌋₊, Work.ZeroDensity.Jutila.selW z₁ d
            * Work.ZeroDensity.Jutila.selW z₂ e
            * (((N / Nat.lcm d e : ℕ) : ℝ) - (N : ℝ) / (Nat.lcm d e : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 ⌊z₁⌋₊, ∑ e ∈ Finset.Icc 1 ⌊z₂⌋₊,
          |Work.ZeroDensity.Jutila.selW z₁ d * Work.ZeroDensity.Jutila.selW z₂ e
            * (((N / Nat.lcm d e : ℕ) : ℝ) - (N : ℝ) / (Nat.lcm d e : ℝ))| := by
        apply Finset.sum_le_sum; intro d _
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 ⌊z₁⌋₊, ∑ e ∈ Finset.Icc 1 ⌊z₂⌋₊,
          |Work.ZeroDensity.Jutila.selW z₁ d| * |Work.ZeroDensity.Jutila.selW z₂ e| * 1 := by
        apply Finset.sum_le_sum; intro d hd
        apply Finset.sum_le_sum; intro e he
        simp only [abs_mul]
        exact mul_le_mul_of_nonneg_left (hpoint d hd e he) (by positivity)
    _ = (∑ d ∈ Finset.Icc 1 ⌊z₁⌋₊, |Work.ZeroDensity.Jutila.selW z₁ d|)
          * (∑ e ∈ Finset.Icc 1 ⌊z₂⌋₊, |Work.ZeroDensity.Jutila.selW z₂ e|) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro d _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro e _
        ring
    _ ≤ z₁ * z₂ :=
        mul_le_mul (HE_sum_abs_selW_le z₁ hz1) (HE_sum_abs_selW_le z₂ hz2)
          (Finset.sum_nonneg (fun e _ => abs_nonneg _)) (by linarith)

/-- **The two-parameter Selberg form has main term `log w`.** -/
lemma HE_msq_mainTerm : ∃ C : ℝ, 0 < C ∧
    ∀ w y : ℝ, 1 ≤ w → w ≤ y → |Work.ZeroDensity.Jutila.Msq w y - Real.log w| ≤ C := by
  obtain ⟨Ce, hCepos, hErr⟩ := Work.ZeroDensity.Jutila.MsqSelErr
  obtain ⟨Cl, hClpos, hLow⟩ := Work.ZeroDensity.Jutila.LzAux.MertSumLower
  obtain ⟨Cu, hCupos, hUpp⟩ := Work.LinnikAreas.Density4.sum_mu_sq_div_totient_sharp
  refine ⟨Ce + max Cl Cu + 1, by positivity, ?_⟩
  intro w y hw hwy
  have hwfl : 1 ≤ ⌊w⌋₊ := Nat.le_floor (by exact_mod_cast hw)
  set S1 : ℝ := ∑ δ ∈ Finset.Icc 1 ⌊w⌋₊,
      ((ArithmeticFunction.moebius δ : ℝ) ^ 2) / (Nat.totient δ : ℝ) with hS1
  set S2 : ℝ := ∑ δ ∈ Finset.Icc 1 ⌊w⌋₊,
      ((ArithmeticFunction.moebius δ : ℝ) ^ 2 * (Nat.totient δ : ℝ)) / ((δ : ℝ) ^ 2) *
        Work.LinnikAreas.Density4.selTheta (w / (δ : ℝ)) δ *
        Work.LinnikAreas.Density4.selTheta (y / (δ : ℝ)) δ with hS2
  have hdiag : Work.ZeroDensity.Jutila.Msq w y = S2 := by
    rw [hS2]; exact Work.ZeroDensity.Jutila.MsqDiag w y hw hwy
  have hE : |S2 - S1| ≤ Ce := by
    rw [hS1, hS2]
    exact hErr w y ⌊w⌋₊ hw hwy (Nat.floor_le (by linarith)) hwfl
  have hLow' : Real.log (⌊w⌋₊ : ℝ) - Cl ≤ S1 := by rw [hS1]; exact hLow ⌊w⌋₊ hwfl
  have hUpp' : S1 ≤ Real.log (⌊w⌋₊ : ℝ) + Cu := by rw [hS1]; exact hUpp ⌊w⌋₊ hwfl
  have hS1abs : |S1 - Real.log (⌊w⌋₊ : ℝ)| ≤ max Cl Cu := by
    rw [abs_le]
    constructor
    · have hCl : Cl ≤ max Cl Cu := le_max_left _ _
      linarith [hLow', hCl]
    · have hCu : Cu ≤ max Cl Cu := le_max_right _ _
      linarith [hUpp', hCu]
  have h3 : |Real.log (⌊w⌋₊ : ℝ) - Real.log w| ≤ 1 := by
    have hw1 : (0 : ℝ) < w := by linarith
    have hflpos : (0 : ℝ) < (⌊w⌋₊ : ℝ) := by
      have : (0 : ℕ) < ⌊w⌋₊ := by omega
      exact_mod_cast this
    have hwle : w ≤ 2 * (⌊w⌋₊ : ℝ) := by
      have h := Nat.lt_floor_add_one w
      have h1 : (1 : ℝ) ≤ (⌊w⌋₊ : ℝ) := by exact_mod_cast hwfl
      linarith
    have hlogle : Real.log (⌊w⌋₊ : ℝ) ≤ Real.log w :=
      Real.log_le_log hflpos (Nat.floor_le (le_of_lt hw1))
    rw [abs_of_nonpos (sub_nonpos.mpr hlogle)]
    have hdiff : -(Real.log (⌊w⌋₊ : ℝ) - Real.log w) = Real.log (w / (⌊w⌋₊ : ℝ)) := by
      rw [Real.log_div (ne_of_gt hw1) (ne_of_gt hflpos)]; ring
    rw [hdiff]
    have h2 : w / (⌊w⌋₊ : ℝ) ≤ 2 := by rw [div_le_iff₀ hflpos]; linarith
    have hlog2 : Real.log (w / (⌊w⌋₊ : ℝ)) ≤ Real.log 2 := Real.log_le_log (by positivity) h2
    have hlog21 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    linarith
  rw [hdiag]
  have hsplit : S2 - Real.log w
      = (S1 - Real.log (⌊w⌋₊ : ℝ)) + (S2 - S1) + (Real.log (⌊w⌋₊ : ℝ) - Real.log w) := by ring
  rw [hsplit]
  calc |(S1 - Real.log (⌊w⌋₊ : ℝ)) + (S2 - S1) + (Real.log (⌊w⌋₊ : ℝ) - Real.log w)|
      ≤ |S1 - Real.log (⌊w⌋₊ : ℝ)| + |S2 - S1| + |Real.log (⌊w⌋₊ : ℝ) - Real.log w| := by
        have h1 := abs_add_le (S1 - Real.log (⌊w⌋₊ : ℝ)) (S2 - S1)
        have h2 := abs_add_le ((S1 - Real.log (⌊w⌋₊ : ℝ)) + (S2 - S1))
          (Real.log (⌊w⌋₊ : ℝ) - Real.log w)
        linarith
    _ ≤ max Cl Cu + Ce + 1 := by linarith [hS1abs, hE, h3]
    _ = Ce + max Cl Cu + 1 := by ring

/-- **The easy case of Graham's two-sided Barban–Vehov estimate for the truncated von Mangoldt
sums** `Lz z n = Σ_{d ∣ n, d ≤ z} μ(d)·log(z/d)`: for real `1 ≤ z₁ ≤ z₂` and every `N ≥ z₂`,
`|Σ_{n ≤ N} Lz_{z₁}(n)·Lz_{z₂}(n) − N·log z₁| ≤ C·(N + z₁·z₂)` with an absolute `C > 0`. -/
theorem HEasyReal : ∃ C : ℝ, 0 < C ∧ ∀ z₁ z₂ : ℝ, 1 ≤ z₁ → z₁ ≤ z₂ → ∀ N : ℕ, z₂ ≤ (N : ℝ) →
      |(∑ n ∈ Finset.Icc 1 N, Work.ZeroDensity.Jutila.Lz z₁ n * Work.ZeroDensity.Jutila.Lz z₂ n)
        - (N : ℝ) * Real.log z₁| ≤ C * ((N : ℝ) + z₁ * z₂) := by

  obtain ⟨Cm, hCmpos, hmain⟩ := HE_msq_mainTerm
  refine ⟨max Cm 1, lt_max_of_lt_left hCmpos, ?_⟩
  intro z₁ z₂ hz1 hz12 N hNz
  have hz2 : 1 ≤ z₂ := le_trans hz1 hz12
  have hz1nn : 0 ≤ z₁ := le_trans zero_le_one hz1
  have hz2nn : 0 ≤ z₂ := le_trans zero_le_one hz2
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hI : (∑ n ∈ Finset.Icc 1 N,
        Work.ZeroDensity.Jutila.Lz z₁ n * Work.ZeroDensity.Jutila.Lz z₂ n)
      = ∑ d ∈ Finset.Icc 1 ⌊z₁⌋₊, ∑ e ∈ Finset.Icc 1 ⌊z₂⌋₊,
          Work.ZeroDensity.Jutila.selW z₁ d * Work.ZeroDensity.Jutila.selW z₂ e
            * ((N / Nat.lcm d e : ℕ) : ℝ) :=
    (Finset.sum_congr rfl (fun n _ => by
      rw [HE_Lz_eq_filter_floor z₁ hz1nn n, HE_Lz_eq_filter_floor z₂ hz2nn n])).trans
      (Work.ZeroDensity.Jutila.grahamBilinearReindex ⌊z₁⌋₊ ⌊z₂⌋₊
        (Work.ZeroDensity.Jutila.selW z₁) (Work.ZeroDensity.Jutila.selW z₂) N)
  have hfloor := HE_grahamFloorErr z₁ z₂ hz1 hz2 N
  have hmain' := hmain z₁ z₂ hz1 hz12
  have h1 : |(∑ n ∈ Finset.Icc 1 N,
        Work.ZeroDensity.Jutila.Lz z₁ n * Work.ZeroDensity.Jutila.Lz z₂ n)
        - (N : ℝ) * Work.ZeroDensity.Jutila.Msq z₁ z₂| ≤ z₁ * z₂ := by
    rw [hI]; exact hfloor
  have h2 : |(N : ℝ) * Work.ZeroDensity.Jutila.Msq z₁ z₂ - (N : ℝ) * Real.log z₁|
      ≤ (N : ℝ) * Cm := by
    have heq : (N : ℝ) * Work.ZeroDensity.Jutila.Msq z₁ z₂ - (N : ℝ) * Real.log z₁
        = (N : ℝ) * (Work.ZeroDensity.Jutila.Msq z₁ z₂ - Real.log z₁) := by ring
    rw [heq, abs_mul, abs_of_nonneg hNnn]
    exact mul_le_mul_of_nonneg_left hmain' hNnn
  calc |(∑ n ∈ Finset.Icc 1 N,
        Work.ZeroDensity.Jutila.Lz z₁ n * Work.ZeroDensity.Jutila.Lz z₂ n)
        - (N : ℝ) * Real.log z₁|
      = |((∑ n ∈ Finset.Icc 1 N,
            Work.ZeroDensity.Jutila.Lz z₁ n * Work.ZeroDensity.Jutila.Lz z₂ n)
          - (N : ℝ) * Work.ZeroDensity.Jutila.Msq z₁ z₂)
          + ((N : ℝ) * Work.ZeroDensity.Jutila.Msq z₁ z₂ - (N : ℝ) * Real.log z₁)| := by
        ring_nf
    _ ≤ |(∑ n ∈ Finset.Icc 1 N,
            Work.ZeroDensity.Jutila.Lz z₁ n * Work.ZeroDensity.Jutila.Lz z₂ n)
          - (N : ℝ) * Work.ZeroDensity.Jutila.Msq z₁ z₂|
          + |(N : ℝ) * Work.ZeroDensity.Jutila.Msq z₁ z₂ - (N : ℝ) * Real.log z₁| :=
        abs_add_le _ _
    _ ≤ z₁ * z₂ + (N : ℝ) * Cm := by linarith [h1, h2]
    _ ≤ max Cm 1 * ((N : ℝ) + z₁ * z₂) := by
        have hprod : (0 : ℝ) ≤ z₁ * z₂ := mul_nonneg hz1nn hz2nn
        have hCmle : Cm ≤ max Cm 1 := le_max_left _ _
        have h1le : (1 : ℝ) ≤ max Cm 1 := le_max_right _ _
        have hA : (N : ℝ) * Cm ≤ (N : ℝ) * max Cm 1 := mul_le_mul_of_nonneg_left hCmle hNnn
        have hB : z₁ * z₂ ≤ z₁ * z₂ * max Cm 1 := by
          have h := mul_le_mul_of_nonneg_left h1le hprod
          simpa using h
        have hEq : max Cm 1 * ((N : ℝ) + z₁ * z₂)
            = (N : ℝ) * max Cm 1 + z₁ * z₂ * max Cm 1 := by ring
        rw [hEq]; linarith

end

end Work.ZeroDensity.Jutila.LzAux
