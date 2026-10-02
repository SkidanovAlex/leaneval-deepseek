import Mathlib
import Submission.Work.ZeroDensity.Jutila.BzCross.BzCrossDefs
import Submission.Work.ZeroDensity.Jutila.grahamCrossAssembly
import Submission.Work.ZeroDensity.Jutila.MulBzAux
import Submission.Work.ZeroDensity.Jutila.LzAux.CzBzReindexTwo
import Submission.Work.ZeroDensity.Jutila.LzAux.HEasyReal
import Submission.Work.LinnikAreas2.cz_inner_eq_s3G
import Submission.Work.LinnikAreas2.cz_inner_filter_eq_empty
import Submission.Work.LinnikAreas2.czLo_le_czUp

/-!
# The easy case (`w·y ≤ N`) of the two-sided `S₃` cross estimate for `czCross`

`czCross w y N` is the exact reindexed two-sided `S₃` sum (`BzCross/BzCrossDefs.lean`):
`Σ_{n ≤ N} Bz_w(n)·Bz_y(n)` for `1 ≤ w ≤ y ≤ N`.  This file proves that in the "easy" range
`w·y ≤ N` one has `czCross w y N = N·log(N/y) + O(N)` with an absolute implied constant.

The proof combines three inputs:

* the exact reindexing `Σ_{n ≤ N} Bz_w(n)·Bz_y(n) = czCross w y N`
  (the two-sided reindexing of the `Bz` cross product, `CzBzReindexTwo`, together with the range
  restriction `cz_inner_filter_eq_empty` and the inner-sum identification `cz_inner_eq_s3G`);
* the easy case of Graham's two-sided Barban–Vehov estimate for `Lz` (`HEasyReal`);
* the mixed von Mangoldt / correction evaluation `Σ_{n ≤ N} Λ(n)Bz_z(n) = −N·log(N/z) + O(N)`
  (`MulBzAux`) together with the second moment `Σ_{n ≤ N} Λ(n)² = N·log N + O(N)`
  (`vonMangoldtSqEval_here`).

Since `Bz_w(n)·Bz_y(n) = (Lz_w(n) − Λ(n))·(Lz_y(n) − Λ(n)) − [n=1]·log w·log y` for `n ≥ 1`
(`Lz_eq_vonMangoldt_add_Bz`), expanding the squares expresses `Σ Bz_w Bz_y` through the four
evaluated sums, and the `N·log w` main terms cancel against `−N log w − N log y + N log N`, while
`w·y ≤ N` turns the `O(w·y)` floor error of the easy case into `O(N)`.
-/

namespace Work.ZeroDensity.Jutila.LzAux

open Finset
open Work.ZeroDensity.Jutila (Bz Lz czMM czUp czLo czQ czR czT czCross)

noncomputable section

/-! ## The reindexing of `Σ_{n ≤ N} Bz_w(n)·Bz_y(n)` -/

/-- The Möbius/`μ²`-weighted inner `m`-sum of the reindexed two-sided `S₃` computation (the
packaged form of the right-hand side of `CzBzReindexTwo`). -/
private def softG (w y : ℝ) (N q r t : ℕ) : ℝ :=
  if Nat.Coprime r t then
    (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) *
      (∑ m ∈ (Finset.Icc 1 (N / (q * r * t))).filter
          (fun m => Nat.Coprime m (r * t) ∧ w < ((m * t : ℕ) : ℝ)
            ∧ y < ((m * r : ℕ) : ℝ)),
        ((ArithmeticFunction.moebius m : ℝ)) ^ 2 *
          Real.log (((m * t : ℕ) : ℝ) / w) *
          Real.log (((m * r : ℕ) : ℝ) / y))
  else 0

/-- `⌊N/a⌋ ≤ N` for `a ≥ 1`; keeps the restricted `q`-, `r`-, `t`-ranges inside `Icc 1 N`. -/
private lemma softCut_le_N (a : ℝ) (N : ℕ) (ha : 1 ≤ a) : ⌊(N : ℝ) / a⌋₊ ≤ N := by
  have h0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hle : (N : ℝ) / a ≤ (N : ℝ) := by
    rw [div_le_iff₀ (by linarith only [ha] : (0 : ℝ) < a)]
    nlinarith only [ha]
  calc ⌊(N : ℝ) / a⌋₊ ≤ ⌊(N : ℝ)⌋₊ := Nat.floor_mono hle
    _ = N := Nat.floor_natCast N

/-- Truncating a sum over `Icc 1 M` at `K ≤ M` is legitimate when the summand vanishes on
`K < x ≤ M`. -/
private lemma soft_sum_Icc_eq_of_eq_zero (M K : ℕ) (hKM : K ≤ M) (f : ℕ → ℝ)
    (hf : ∀ x, K < x → x ≤ M → f x = 0) :
    ∑ x ∈ Finset.Icc 1 M, f x = ∑ x ∈ Finset.Icc 1 K, f x := by
  refine (Finset.sum_subset ?_ ?_).symm
  · intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    exact ⟨hx.1, le_trans hx.2 hKM⟩
  · intro x hx hxs
    simp only [Finset.mem_Icc] at hx
    have hKx : K < x := by
      by_contra h
      exact hxs (by simp only [Finset.mem_Icc]; exact ⟨hx.1, by omega⟩)
    exact hf x hKx hx.2

/-- `softG` vanishes when the inner `m`-filter is empty. -/
private lemma softG_eq_zero_of_empty (w y : ℝ) (N q r t : ℕ)
    (hempty : (Finset.Icc 1 (N / (q * r * t))).filter
        (fun m => Nat.Coprime m (r * t) ∧ w < ((m * t : ℕ) : ℝ)
          ∧ y < ((m * r : ℕ) : ℝ)) = ∅) :
    softG w y N q r t = 0 := by
  unfold softG
  rw [hempty]
  simp

/-- **Exact reindexing of the two-sided `S₃` cross sum.**
`Σ_{n ≤ N} Bz_w(n)·Bz_y(n) = czCross w y N` for `1 ≤ w ≤ y ≤ N`. -/
theorem czCross_eq_soft (w y : ℝ) (N : ℕ) (hw : 1 ≤ w) (hwy : w ≤ y) (hyN : y ≤ (N : ℝ)) :
    (∑ n ∈ Finset.Icc 1 N, Bz w n * Bz y n) = czCross w y N := by
  classical
  have hy1 : 1 ≤ y := le_trans hw hwy
  -- The `n = 1` term vanishes, so the sum may start at `n = 2`.
  have hstep1 : (∑ n ∈ Finset.Icc 1 N, Bz w n * Bz y n) = ∑ n ∈ Finset.Icc 2 N, Bz w n * Bz y n := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro n hn
      simp only [Finset.mem_Icc] at hn ⊢
      omega
    · intro n hn hn2
      rw [Finset.mem_Icc] at hn
      have h2 : ¬ (2 ≤ n) := fun h => hn2 (Finset.mem_Icc.mpr ⟨h, hn.2⟩)
      have hn1 : n = 1 := by omega
      have hBw : Bz w 1 = 0 := Bz_eq_zero_of_le (z := w) (n := 1) (by linarith only [hw]) (by simpa using hw)
      have hBy : Bz y 1 = 0 := Bz_eq_zero_of_le (z := y) (n := 1) (by linarith only [hw, hwy]) (by simpa using hy1)
      rw [hn1, hBw, hBy, mul_zero]
  -- Two-sided reindexing with the packaged inner sum `softG`.
  have hstep2 : (∑ n ∈ Finset.Icc 2 N, Bz w n * Bz y n)
      = ∑ q ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N, ∑ t ∈ Finset.Icc 1 N,
          softG w y N q r t := by
    -- SWAP-IN: simpa only [softG] using CzBzReindexTwo w y N hw hy1
    simpa only [softG] using Work.ZeroDensity.Jutila.LzAux.CzBzReindexTwo w y N hw hy1
  -- Restriction of the `q`-range to `⌊N/y⌋`.
  have h3a : (∑ q ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N, ∑ t ∈ Finset.Icc 1 N,
        softG w y N q r t)
      = ∑ q ∈ Finset.Icc 1 (czQ y N), ∑ r ∈ Finset.Icc 1 N, ∑ t ∈ Finset.Icc 1 N,
          softG w y N q r t := by
    refine soft_sum_Icc_eq_of_eq_zero N (czQ y N) (softCut_le_N y N hy1)
      (fun q => ∑ r ∈ Finset.Icc 1 N, ∑ t ∈ Finset.Icc 1 N, softG w y N q r t) ?_
    intro q hq hqN
    apply Finset.sum_eq_zero
    intro r hr
    apply Finset.sum_eq_zero
    intro t ht
    have hq1 : 1 ≤ q := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) hq)
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
    exact softG_eq_zero_of_empty w y N q r t
      (Work.LinnikAreas2.cz_inner_filter_eq_empty w y N q r t hw hy1 hq1 hr1 ht1 (Or.inl hq))
  -- Restriction of the `r`-range to `⌊N/(qw)⌋`.
  have h3b : (∑ q ∈ Finset.Icc 1 (czQ y N), ∑ r ∈ Finset.Icc 1 N, ∑ t ∈ Finset.Icc 1 N,
          softG w y N q r t)
      = ∑ q ∈ Finset.Icc 1 (czQ y N), ∑ r ∈ Finset.Icc 1 (czR w N q),
            ∑ t ∈ Finset.Icc 1 N, softG w y N q r t := by
    refine Finset.sum_congr rfl (fun q hq => ?_)
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hX1N : czR w N q ≤ N := by
      have h1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
      exact softCut_le_N ((q:ℝ) * w) N (by nlinarith only [h1, hw])
    refine soft_sum_Icc_eq_of_eq_zero N (czR w N q) hX1N
      (fun r => ∑ t ∈ Finset.Icc 1 N, softG w y N q r t) ?_
    intro r hr hrN
    apply Finset.sum_eq_zero
    intro t ht
    have hr1 : 1 ≤ r := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) hr)
    have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
    exact softG_eq_zero_of_empty w y N q r t
      (Work.LinnikAreas2.cz_inner_filter_eq_empty w y N q r t hw hy1 hq1 hr1 ht1
        (Or.inr (Or.inl hr)))
  -- Restriction of the `t`-range to `⌊N/(qy)⌋`.
  have h3c : (∑ q ∈ Finset.Icc 1 (czQ y N), ∑ r ∈ Finset.Icc 1 (czR w N q),
            ∑ t ∈ Finset.Icc 1 N, softG w y N q r t)
      = ∑ q ∈ Finset.Icc 1 (czQ y N), ∑ r ∈ Finset.Icc 1 (czR w N q),
            ∑ t ∈ Finset.Icc 1 (czT y N q), softG w y N q r t := by
    refine Finset.sum_congr rfl (fun q hq => ?_)
    refine Finset.sum_congr rfl (fun r hr => ?_)
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hX2N : czT y N q ≤ N := by
      have h1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
      exact softCut_le_N ((q:ℝ) * y) N (by nlinarith only [h1, hw, hwy])
    refine soft_sum_Icc_eq_of_eq_zero N (czT y N q) hX2N (fun t => softG w y N q r t) ?_
    intro t ht htN
    have ht1 : 1 ≤ t := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) ht)
    exact softG_eq_zero_of_empty w y N q r t
      (Work.LinnikAreas2.cz_inner_filter_eq_empty w y N q r t hw hy1 hq1 hr1 ht1
        (Or.inr (Or.inr ht)))
  -- On the restricted ranges the inner `m`-sum is the `s3G`-difference.
  have h4 : (∑ q ∈ Finset.Icc 1 (czQ y N), ∑ r ∈ Finset.Icc 1 (czR w N q),
            ∑ t ∈ Finset.Icc 1 (czT y N q), softG w y N q r t)
      = czCross w y N := by
    unfold czCross
    refine Finset.sum_congr rfl (fun q hq => Finset.sum_congr rfl (fun r hr =>
      Finset.sum_congr rfl (fun t ht => ?_)))
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
    by_cases hc : Nat.Coprime r t
    · have hinner := Work.LinnikAreas2.cz_inner_eq_s3G w y N q r t hw hy1 hr1 ht1
        (Work.LinnikAreas2.czLo_le_czUp w y N q r t hw hy1 hq1 hr ht)
      unfold czUp at hinner
      unfold softG
      rw [if_pos hc, czMM, if_pos hc]
      unfold czUp
      rw [hinner]
    · unfold softG
      rw [if_neg hc, czMM, if_neg hc, zero_mul]
  exact ((((hstep1.trans hstep2).trans h3a).trans h3b).trans h3c).trans h4

/-! ## The easy-case (`w·y ≤ N`) analytic bound -/

/-- `log w · log y ≤ 4 N` for `1 ≤ w ≤ y ≤ N`. -/
private lemma soft_log_mul_le {w y : ℝ} {N : ℕ} (hw : 1 ≤ w) (hwy : w ≤ y)
    (hyN : y ≤ (N : ℝ)) : Real.log w * Real.log y ≤ 4 * (N : ℝ) := by
  have hy1 : 1 ≤ y := le_trans hw hwy
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ (N : ℝ) := le_trans hy1 hyN
    exact_mod_cast this
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hlogw : 0 ≤ Real.log w := Real.log_nonneg hw
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hwpos : 0 < w := by linarith only [hw]
  have hypos : 0 < y := by linarith only [hw, hwy]
  have hwl : Real.log w ≤ Real.log (N : ℝ) := Real.log_le_log hwpos (le_trans hwy hyN)
  have hyl : Real.log y ≤ Real.log (N : ℝ) := Real.log_le_log hypos hyN
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  have hsq : (Real.log (N : ℝ)) ^ 2 ≤ 4 * (N : ℝ) :=
    Work.ZeroDensity.Jutila.log_sq_le_four_mul N hN1
  nlinarith only [hlogw, hlogy, hwl, hyl, hsq, hlogN]

/-- `|a − b − c − d − e| ≤ |a| + |b| + |c| + |d| + |e|`. -/
private lemma soft_abs_chain (a b c d e : ℝ) :
    |a - b - c - d - e| ≤ |a| + |b| + |c| + |d| + |e| := by
  rw [abs_le]
  constructor <;>
    linarith only [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b, le_abs_self c,
      neg_abs_le c, le_abs_self d, neg_abs_le d, le_abs_self e, neg_abs_le e]

/-- **The `w·y ≤ N` case of the two-sided Graham `S₃` estimate.**  The pointwise splitting
`Bz_z(n) = Lz_z(n) − Λ(n)` (`Lz_eq_vonMangoldt_add_Bz`), the easy case of Graham's two-sided
estimate (`HEasyReal`: the floor error there is controlled by `w·y`), the one-sided evaluation
`Σ Λ·Bz_z = −N log(N/z) + O(N)` (`MulBzAux`) and `Σ Λ² = N log N + O(N)`
(`vonMangoldtSqEval_here`) combine: the `N log w` terms cancel, the `O(w·y)` error of the easy
case is `O(N)` because `w·y ≤ N`, and the `n = 1` correction `log w·log y` is `O(N)`. -/
private theorem czBz_soft_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) → w * y ≤ (N : ℝ) →
      |(∑ n ∈ Finset.Icc 1 N, Bz w n * Bz y n) - (N : ℝ) * Real.log ((N : ℝ) / y)|
        ≤ C * (N : ℝ) := by
  -- SWAP-IN: Work.ZeroDensity.Jutila.LzAux.HEasyReal
  obtain ⟨C₁, hC₁, hG⟩ := Work.ZeroDensity.Jutila.LzAux.HEasyReal
  obtain ⟨C₂, hC₂, hQ⟩ := Work.ZeroDensity.Jutila.vonMangoldtSqEval_here
  obtain ⟨C₃, hC₃, hP⟩ := Work.ZeroDensity.Jutila.MulBzAux
  refine ⟨2 * C₁ + C₂ + 2 * C₃ + 4, by linarith only [hC₁, hC₂, hC₃], ?_⟩
  intro w y N hw hwy hyN hwyN
  have hy1 : 1 ≤ y := le_trans hw hwy
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ (N : ℝ) := le_trans hy1 hyN
    exact_mod_cast this
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hypos : 0 < y := by linarith only [hw, hwy]
  have hwN : w ≤ (N : ℝ) := le_trans hwy hyN
  have hlogmul : Real.log w * Real.log y ≤ 4 * (N : ℝ) := soft_log_mul_le hw hwy hyN
  have hA := hG w y hw hwy N hyN
  have hB := hQ N hN1
  have hC := hP w hw N hwN
  have hD := hP y hy1 N hyN
  have hid := Work.ZeroDensity.Jutila.cross_eq_split hw hy1 hN1
  have hdivw : Real.log ((N : ℝ) / w) = Real.log (N : ℝ) - Real.log w :=
    Real.log_div (ne_of_gt hNpos) (by linarith only [hw] : w ≠ 0)
  have hdivy : Real.log ((N : ℝ) / y) = Real.log (N : ℝ) - Real.log y :=
    Real.log_div (ne_of_gt hNpos) (ne_of_gt hypos)
  have hkey : (∑ n ∈ Finset.Icc 1 N, Bz w n * Bz y n) - (N : ℝ) * Real.log ((N : ℝ) / y)
      = ((∑ n ∈ Finset.Icc 1 N, Lz w n * Lz y n) - (N : ℝ) * Real.log w)
        - ((∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n ^ 2)
            - (N : ℝ) * Real.log (N : ℝ))
        - ((∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * Bz w n)
            + (N : ℝ) * Real.log ((N : ℝ) / w))
        - ((∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * Bz y n)
            + (N : ℝ) * Real.log ((N : ℝ) / y))
        - Real.log w * Real.log y := by
    rw [hid, hdivw, hdivy]
    ring
  have h1 := abs_le.mp hA
  have h2 := abs_le.mp hB
  have h3 := abs_le.mp hC
  have h4 := abs_le.mp hD
  have hlogmul_nn : 0 ≤ Real.log w * Real.log y :=
    mul_nonneg (Real.log_nonneg hw) (Real.log_nonneg hy1)
  have hwy2 : C₁ * ((N : ℝ) + w * y) ≤ 2 * C₁ * (N : ℝ) := by
    have h : (N : ℝ) + w * y ≤ 2 * (N : ℝ) := by linarith only [hwyN]
    linarith only [mul_le_mul_of_nonneg_left h hC₁.le, h, hC₁]
  set A : ℝ := (∑ n ∈ Finset.Icc 1 N, Lz w n * Lz y n) - (N : ℝ) * Real.log w with hAdef
  set B : ℝ := (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n ^ 2)
      - (N : ℝ) * Real.log (N : ℝ) with hBdef
  set C : ℝ := (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * Bz w n)
      + (N : ℝ) * Real.log ((N : ℝ) / w) with hCdef
  set D : ℝ := (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * Bz y n)
      + (N : ℝ) * Real.log ((N : ℝ) / y) with hDdef
  set E : ℝ := Real.log w * Real.log y with hEdef
  have hbA : |A| ≤ 2 * C₁ * (N : ℝ) := by
    rw [hAdef]; exact abs_le.mpr ⟨by linarith only [h1.1, hwy2, h1], by linarith only [h1.2, hwy2, h1]⟩
  have hbB : |B| ≤ C₂ * (N : ℝ) := by rw [hBdef]; exact hB
  have hbC : |C| ≤ C₃ * (N : ℝ) := by rw [hCdef]; exact hC
  have hbD : |D| ≤ C₃ * (N : ℝ) := by rw [hDdef]; exact hD
  have hbE : |E| ≤ 4 * (N : ℝ) := by
    rw [hEdef, abs_of_nonneg hlogmul_nn]; exact hlogmul
  have hkey' : (∑ n ∈ Finset.Icc 1 N, Bz w n * Bz y n) - (N : ℝ) * Real.log ((N : ℝ) / y)
      = A - B - C - D - E := by
    rw [hkey, hAdef, hBdef, hCdef, hDdef, hEdef]
  rw [hkey']
  refine le_trans (soft_abs_chain A B C D E) ?_
  have hsum : |A| + |B| + |C| + |D| + |E|
      ≤ (2 * C₁ + C₂ + 2 * C₃ + 4) * (N : ℝ) := by
    have hNnn : (0 : ℝ) ≤ (N : ℝ) := hNpos.le
    linarith only [hbA, hbB, hbC, hbD, hbE, hwy2, hA, hB, hC, hD]
  exact hsum

/-! ## The target -/

/-- **The easy case (`w·y ≤ N`) of the two-sided `S₃` cross estimate for `czCross`.**  For real
`1 ≤ w ≤ y ≤ N` with `w·y ≤ N`, `|czCross w y N − N·log(N/y)| ≤ C·N` with an absolute `C > 0`. -/
theorem CzSoftCrossAux : ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) → w * y ≤ (N : ℝ) →
      |Work.ZeroDensity.Jutila.czCross w y N - (N : ℝ) * Real.log ((N : ℝ) / y)| ≤ C * (N : ℝ) := by
  obtain ⟨C, hC, h⟩ := czBz_soft_bound
  refine ⟨C, hC, fun w y N hw hwy hyN hwyN => ?_⟩
  rw [← czCross_eq_soft w y N hw hwy hyN]
  exact h w y N hw hwy hyN hwyN

end

end Work.ZeroDensity.Jutila.LzAux
