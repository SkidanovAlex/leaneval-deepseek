import Mathlib
import Submission.Work.ChenPlan.H2.Level
import Submission.Work.ChenPlan.H2.Tab

/-!
# The cell decomposition of Chen's `h2` window sum

Vocabulary for bounding the window main term

`Σ_{q ∈ winPrimes M Y} Utab (sVal B x q) / (q - 1)`,

`M = siftM x`, `Y = winY x`, by splitting the window primes according to the grid cell of
the linear-sieve envelope `Utab`.  With `s_k = 3/2 + k/20` and the cell index
`kOf q = min (⌊(sVal B x q - 3/2)·20⌋₊) 70`, one has `Utab (sVal B x q) = utabQ (kOf q)`
whenever `sVal B x q ≥ 3/2`; a prime with cell index `k < 70` enjoys `s_k ≤ s_q < s_{k+1}`,
i.e. `q ∈ (L_{k+1}, L_k]` with `L_j = thrL B x j`, so the cell is contained in the integer
interval `Icc (cellLo B x k) (cellHi B x k)`.  The mass of that interval is bounded through
`Work.Sieve.RosserLinear.primeRecipsLocalUpper`.

The model sum `Σ_k utabQ k · max 0 (log (mnum k / mden k))` is the one estimated by
`Work.ChenPlan.H2.utab_table_sum_le`.
-/

open Finset Filter
open scoped BigOperators

namespace Work.ChenPlan.H2

noncomputable section

open Commons.NumberTheory.Chen.ChenEight

/-- The grid points of the linear-sieve envelope: `s_k = 3/2 + k/20`. -/
def sk (k : ℕ) : ℝ := 3 / 2 + (k : ℝ) / 20

/-- The cell index of a window prime `q`, so that `Utab (sVal B x q) = utabQ (kOf B x q)`
whenever `sVal B x q ≥ 3/2`. -/
def kOf (B : ℝ) (x q : ℕ) : ℕ := min (⌊(sVal B x q - 3 / 2) * 20⌋₊) 70

/-- The `k`-th cell of the window: the window primes with cell index `k`. -/
def cellF (B : ℝ) (x k : ℕ) : Finset ℕ :=
  (Submission.winPrimes (siftM x) (winY x)).filter (fun q => kOf B x q = k)

/-- The model numerator `min (7/2 - k/20) (10/3)` of the `k`-th window cell (the cap `10/3`
is the top `w = log (Y-1)/log M` of the window; `7/2 - k/20 = 5 - s_k`). -/
def mnum (k : ℕ) : ℝ := min ((7 : ℝ) / 2 - (k : ℝ) / 20) (10 / 3)

/-- The model denominator `max 1 (7/2 - (k+1)/20)` of the `k`-th window cell (the `1` is the
bottom `q ≥ M` of the window, `7/2 - (k+1)/20 = 5 - s_{k+1}`). -/
def mden (k : ℕ) : ℝ := max 1 ((7 : ℝ) / 2 - ((k : ℝ) + 1) / 20)

/-- The lower integer endpoint of the `k`-th cell: `max M (⌊L_{k+1}⌋₊ + 1)`. -/
def cellLo (B : ℝ) (x k : ℕ) : ℕ := max (siftM x) (⌊thrL B x (k + 1)⌋₊ + 1)

/-- The upper integer endpoint of the `k`-th cell: `min (Y-1) ⌊L_k⌋₊`. -/
def cellHi (B : ℝ) (x k : ℕ) : ℕ := min (winY x - 1) ⌊thrL B x k⌋₊

lemma mnum_eq (k : ℕ) : mnum k = min (5 - sk k) (10 / 3) := by
  unfold mnum sk
  congr 1
  ring

lemma mden_eq (k : ℕ) : mden k = max 1 (5 - sk (k + 1)) := by
  unfold mden sk
  congr 1
  push_cast
  ring

lemma sk_mono {j k : ℕ} (h : j ≤ k) : sk j ≤ sk k := by
  unfold sk
  have : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
  linarith

lemma sk_succ (k : ℕ) : sk (k + 1) = sk k + 1 / 20 := by
  unfold sk
  push_cast
  ring

@[simp] lemma mem_cellF {B : ℝ} {x k q : ℕ} :
    q ∈ cellF B x k ↔ q ∈ Submission.winPrimes (siftM x) (winY x) ∧ kOf B x q = k := by
  simp [cellF]

lemma kOf_le (B : ℝ) (x q : ℕ) : kOf B x q ≤ 70 := min_le_right _ _

lemma kOf_lt_iff {B : ℝ} {x q : ℕ} {k : ℕ} (hk : k < 70) :
    kOf B x q = k ↔ ⌊(sVal B x q - 3 / 2) * 20⌋₊ = k := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hne
    rcases lt_or_gt_of_ne hne with h1 | h1
    · rw [kOf, min_eq_left (le_trans (le_of_lt h1) (le_of_lt hk))] at h; omega
    · rcases le_or_gt ⌊(sVal B x q - 3 / 2) * 20⌋₊ 70 with hA | hA
      · rw [kOf, min_eq_left hA] at h; omega
      · rw [kOf, min_eq_right (le_of_lt hA)] at h; omega
  · rw [kOf, h, min_eq_left (le_of_lt hk)]

/-- The Bombieri–Vinogradov level is positive for `x ≥ 2`. -/
lemma lvlD_pos {B : ℝ} (hB : 0 < B) {x : ℕ} (hx : 2 ≤ x) : 0 < lvlD B x := by
  have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  exact div_pos (Real.sqrt_pos.mpr hx0) (Real.rpow_pos_of_pos hlog B)

/-! ## `Utab` is constant on a cell -/

/-- `Utab` is the table value on the cell of `q`, for `sVal ≥ 3/2`. -/
lemma Utab_sVal_eq_utabQ (B : ℝ) (x q : ℕ) (h : 3 / 2 ≤ sVal B x q) :
    Submission.ChenPlan.Utab (sVal B x q) = ((utabQ (kOf B x q) : ℚ) : ℝ) := by
  unfold Submission.ChenPlan.Utab kOf utabQ tabQ
  rw [if_neg (not_lt.mpr h)]

/-! ## The relation between the cell index and `thrL` -/

/-- `sVal B x q ≥ s_k` iff `q ≤ thrL B x k` (for `q > 0`, `M > 1`). -/
lemma sk_le_sVal_iff {B : ℝ} {x q k : ℕ} (hq : 0 < q) (hM : 1 < (siftM x : ℝ))
    (hlvl : 0 < lvlD B x) :
    sk k ≤ sVal B x q ↔ (q : ℝ) ≤ thrL B x k := by
  have hMpos : 0 < (siftM x : ℝ) := lt_trans zero_lt_one hM
  have hlogM : 0 < Real.log (siftM x : ℝ) := Real.log_pos hM
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hkey : Real.log ((siftM x : ℝ) ^ sk k) = sk k * Real.log (siftM x : ℝ) :=
    Real.log_rpow hMpos _
  rw [sVal, le_div_iff₀ hlogM, ← hkey,
    Real.log_le_log_iff (Real.rpow_pos_of_pos hMpos (sk k)) (div_pos hlvl hqpos),
    thrL, le_div_iff₀ hqpos,
    le_div_iff₀ (Real.rpow_pos_of_pos hMpos ((3 : ℝ) / 2 + (k : ℝ) / 20))]
  show (siftM x : ℝ) ^ sk k * (q : ℝ) ≤ lvlD B x ↔
    (q : ℝ) * (siftM x : ℝ) ^ sk k ≤ lvlD B x
  rw [mul_comm]

/-- `sVal B x q < s_k` iff `thrL B x k < q`. -/
lemma sVal_lt_sk_iff {B : ℝ} {x q k : ℕ} (hq : 0 < q) (hM : 1 < (siftM x : ℝ))
    (hlvl : 0 < lvlD B x) :
    sVal B x q < sk k ↔ thrL B x k < (q : ℝ) := by
  have hMpos : 0 < (siftM x : ℝ) := lt_trans zero_lt_one hM
  have hlogM : 0 < Real.log (siftM x : ℝ) := Real.log_pos hM
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hkey : Real.log ((siftM x : ℝ) ^ sk k) = sk k * Real.log (siftM x : ℝ) :=
    Real.log_rpow hMpos _
  rw [sVal, div_lt_iff₀ hlogM, ← hkey,
    Real.log_lt_log_iff (div_pos hlvl hqpos) (Real.rpow_pos_of_pos hMpos (sk k)),
    div_lt_iff₀ hqpos, thrL,
    div_lt_iff₀ (Real.rpow_pos_of_pos hMpos ((3 : ℝ) / 2 + (k : ℝ) / 20))]
  show lvlD B x < (siftM x : ℝ) ^ sk k * (q : ℝ) ↔
    lvlD B x < (q : ℝ) * (siftM x : ℝ) ^ sk k
  rw [mul_comm]

/-- `sVal` is at most `σ - 1` on the window (the prime `q ≥ M` costs at least a factor `M`). -/
lemma sVal_le_sigM_sub_one {B : ℝ} {x q : ℕ} (hqM : siftM x ≤ q) (hq : 0 < q)
    (hM : 1 < (siftM x : ℝ)) (hlvl : 0 < lvlD B x) :
    sVal B x q ≤ sigM B x - 1 := by
  have hMpos : 0 < (siftM x : ℝ) := lt_trans zero_lt_one hM
  have hlogM : 0 < Real.log (siftM x : ℝ) := Real.log_pos hM
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hle : (siftM x : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqM
  have hDq : Real.log (lvlD B x / (q : ℝ)) ≤ Real.log (lvlD B x / (siftM x : ℝ)) :=
    Real.log_le_log (div_pos hlvl hqpos)
      (div_le_div_of_nonneg_left hlvl.le hMpos hle)
  have hlog : Real.log (lvlD B x / (siftM x : ℝ)) = Real.log (lvlD B x) - Real.log (siftM x : ℝ) :=
    Real.log_div (ne_of_gt hlvl) (ne_of_gt hMpos)
  have h2 : Real.log (lvlD B x / (q : ℝ)) / Real.log (siftM x : ℝ)
      ≤ Real.log (lvlD B x / (siftM x : ℝ)) / Real.log (siftM x : ℝ) :=
    div_le_div_of_nonneg_right hDq hlogM.le
  rw [hlog] at h2
  have h3 : (Real.log (lvlD B x) - Real.log (siftM x : ℝ)) / Real.log (siftM x : ℝ)
      = Real.log (lvlD B x) / Real.log (siftM x : ℝ) - 1 := by
    field_simp
  rw [sVal, sigM]
  linarith [h2, h3.symm.le, h3.le]

/-- `M ≤ Y - 1` for `x ≥ 1`. -/
lemma siftM_le_winY_sub_one {x : ℕ} (hx : 1 ≤ x) : siftM x ≤ winY x - 1 := by
  have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  rw [siftM_eq, winY_sub_one_eq]
  have h : ⌊(x : ℝ) ^ ((1 : ℝ) / 10)⌋₊ ≤ ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num))
  omega

/-- `w = log (Y-1)/log M ≥ 1` for `x ≥ 2`. -/
lemma wVal_ge_one {x : ℕ} (hx : 2 ≤ x) : 1 ≤ wVal x := by
  have hMY := siftM_le_winY_sub_one (by omega : 1 ≤ x)
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hMpos : 0 < (siftM x : ℝ) := by
    rw [siftM_eq]; push_cast
    linarith [Nat.cast_nonneg (α := ℝ) ⌊(x : ℝ) ^ ((1 : ℝ) / 10)⌋₊]
  have hlogM : 0 < Real.log (siftM x : ℝ) := Real.log_pos (by
    rw [siftM_eq]; push_cast
    have h1 : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) := by
      have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt hx1)
        (by norm_num : (0 : ℝ) ≤ 1 / 10)
      rwa [Real.one_rpow] at h
    have h2 : (1 : ℕ) ≤ ⌊(x : ℝ) ^ ((1 : ℝ) / 10)⌋₊ := Nat.le_floor (by push_cast; exact h1)
    have h2' : (1 : ℝ) ≤ ((⌊(x : ℝ) ^ ((1 : ℝ) / 10)⌋₊ : ℕ) : ℝ) := by exact_mod_cast h2
    linarith)
  have hYpos : (0 : ℝ) < ((winY x - 1 : ℕ) : ℝ) := by
    have h1 : (1 : ℕ) ≤ siftM x := by
      rw [siftM_eq]; omega
    have : (0 : ℕ) < winY x - 1 := by omega
    exact_mod_cast this
  have hlog : Real.log (siftM x : ℝ) ≤ Real.log (((winY x - 1 : ℕ)) : ℝ) :=
    Real.log_le_log hMpos (by exact_mod_cast hMY)
  rw [wVal, le_div_iff₀ hlogM]
  linarith

/-- `sVal B x q ≥ σ - w` on the window (the smallest value is at `q = Y - 1`). -/
lemma sVal_ge_sigM_sub_wVal {B : ℝ} {x q : ℕ} (hq : 0 < q) (hqY : q ≤ winY x - 1)
    (hM : 1 < (siftM x : ℝ)) (hlvl : 0 < lvlD B x) (hY1 : 0 < winY x - 1) :
    sigM B x - wVal x ≤ sVal B x q := by
  have hMpos : 0 < (siftM x : ℝ) := lt_trans zero_lt_one hM
  have hlogM : 0 < Real.log (siftM x : ℝ) := Real.log_pos hM
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hYpos : (0 : ℝ) < ((winY x - 1 : ℕ) : ℝ) := by exact_mod_cast hY1
  have hle : (q : ℝ) ≤ ((winY x - 1 : ℕ) : ℝ) := by exact_mod_cast hqY
  have hD : Real.log (lvlD B x / ((winY x - 1 : ℕ) : ℝ)) ≤ Real.log (lvlD B x / (q : ℝ)) :=
    Real.log_le_log (div_pos hlvl hYpos) (div_le_div_of_nonneg_left hlvl.le hqpos hle)
  have h2 := div_le_div_of_nonneg_right hD hlogM.le
  have hlog : Real.log (lvlD B x / ((winY x - 1 : ℕ) : ℝ))
      = Real.log (lvlD B x) - Real.log (((winY x - 1 : ℕ)) : ℝ) :=
    Real.log_div (ne_of_gt hlvl) (ne_of_gt hYpos)
  rw [hlog] at h2
  have h3 : (Real.log (lvlD B x) - Real.log (((winY x - 1 : ℕ)) : ℝ)) / Real.log (siftM x : ℝ)
      = Real.log (lvlD B x) / Real.log (siftM x : ℝ)
        - Real.log (((winY x - 1 : ℕ)) : ℝ) / Real.log (siftM x : ℝ) := by
    field_simp
  rw [sVal, sigM, wVal]
  linarith [h2, h3.le, h3.symm.le]

/-- `σ ≤ 5` for `x ≥ 8`. -/
lemma sigM_le_five (B : ℝ) (hB : 0 < B) {x : ℕ} (hx : 8 ≤ x) : sigM B x ≤ 5 := by
  have hx1 : 1 ≤ x := by omega
  have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hx2 : (8 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hlogM : 0 < Real.log (siftM x : ℝ) := by
    have h := log_siftM_ge (x := x) hx1
    have h1 : 0 < Real.log (x : ℝ) := by
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 8) hx2
      have h2 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
      rw [h2] at this
      nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2), this]
    linarith
  have hlvlpos : 0 < lvlD B x := lvlD_pos hB (by omega)
  have h1 : Real.log (lvlD B x) ≤ Real.log (x : ℝ) / 2 := by
    have h := Real.log_le_log hlvlpos (lvlD_le_sqrt B hB.le hx)
    rwa [Real.log_sqrt hx0.le] at h
  have h2 : Real.log (x : ℝ) / 2 ≤ 5 * Real.log (siftM x : ℝ) := by
    have h := log_siftM_ge (x := x) hx1
    linarith
  rw [sigM, div_le_iff₀ hlogM]
  linarith

/-- `M ≥ 2` for `x ≥ 1`. -/
lemma siftM_two_le {x : ℕ} (hx : 1 ≤ x) : 2 ≤ siftM x := by
  rw [siftM_eq]
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have h : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10) := Real.one_le_rpow hx1 (by norm_num)
  have h2 : (1 : ℕ) ≤ ⌊(x : ℝ) ^ ((1 : ℝ) / 10)⌋₊ := Nat.le_floor (by exact_mod_cast h)
  omega

/-- `M > 1` for `x ≥ 1`. -/
lemma one_lt_siftM {x : ℕ} (hx : 1 ≤ x) : 1 < (siftM x : ℝ) := by
  have := siftM_two_le hx
  exact_mod_cast (by omega : 1 < siftM x)

/-- `Y - 1 > 0` for `x ≥ 1`. -/
lemma winY_sub_one_pos {x : ℕ} (hx : 1 ≤ x) : 0 < winY x - 1 := by
  have h := siftM_two_le hx
  have h2 := siftM_le_winY_sub_one hx
  omega

/-- The cell of index `k < 70` is contained in the integer interval `Icc (cellLo) (cellHi)`. -/
lemma cellF_subset_Icc {B : ℝ} {x k : ℕ} (hk : k < 70) (hM : 1 < (siftM x : ℝ))
    (hlvl : 0 < lvlD B x) {q : ℕ} (h32 : 3 / 2 ≤ sVal B x q) (hq : q ∈ cellF B x k) :
    q ∈ Finset.Icc (cellLo B x k) (cellHi B x k) := by
  rw [mem_cellF] at hq
  obtain ⟨hwq, hkq⟩ := hq
  obtain ⟨hqp, hq3, hqM, hqY⟩ := Submission.mem_winPrimes.mp hwq
  have hqpos : 0 < q := by omega
  have hfloor : ⌊(sVal B x q - 3 / 2) * 20⌋₊ = k := (kOf_lt_iff hk).mp hkq
  have hz0 : (0 : ℝ) ≤ (sVal B x q - 3 / 2) * 20 := by linarith
  have hz1 : (k : ℝ) ≤ (sVal B x q - 3 / 2) * 20 := by
    have := Nat.floor_le hz0
    rwa [hfloor] at this
  have hz2 : (sVal B x q - 3 / 2) * 20 < (k : ℝ) + 1 := by
    have := Nat.lt_floor_add_one ((sVal B x q - 3 / 2) * 20)
    rwa [hfloor] at this
  have hsk1 : sk k ≤ sVal B x q := by
    have : (k : ℝ) / 20 ≤ sVal B x q - 3 / 2 := by linarith
    unfold sk; linarith
  have hsk2 : sVal B x q < sk (k + 1) := by
    have h1 : sVal B x q - 3 / 2 < ((k : ℝ) + 1) / 20 := by linarith
    unfold sk
    push_cast
    linarith
  have hle : (q : ℝ) ≤ thrL B x k := (sk_le_sVal_iff hqpos hM hlvl).mp hsk1
  have hlt : thrL B x (k + 1) < (q : ℝ) := (sVal_lt_sk_iff hqpos hM hlvl).mp hsk2
  have hqi1 : q ≤ ⌊thrL B x k⌋₊ := Nat.le_floor hle
  have hqi2 : ⌊thrL B x (k + 1)⌋₊ + 1 ≤ q := by
    have h : ⌊thrL B x (k + 1)⌋₊ < q := (Nat.floor_lt' (by omega : q ≠ 0)).mpr hlt
    omega
  have hqi3 : q ≤ winY x - 1 := by omega
  rw [Finset.mem_Icc]
  exact ⟨by rw [cellLo]; exact max_le hqM hqi2, by rw [cellHi]; exact le_min hqi3 hqi1⟩

/-- Cell `70` is empty as soon as `σ ≤ 5`. -/
lemma cellF_seventy_empty {B : ℝ} {x : ℕ} (hσ : sigM B x ≤ 5) (hM : 1 < (siftM x : ℝ))
    (hlvl : 0 < lvlD B x) :
    cellF B x 70 = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨q, hq⟩
  rw [mem_cellF] at hq
  obtain ⟨hwq, hkq⟩ := hq
  obtain ⟨hqp, hq3, hqM, hqY⟩ := Submission.mem_winPrimes.mp hwq
  have hqpos : 0 < q := by omega
  have hsval := sVal_le_sigM_sub_one (B := B) hqM hqpos hM hlvl
  have hsval4 : sVal B x q ≤ 4 := by linarith
  have hz : (sVal B x q - 3 / 2) * 20 ≤ 50 := by linarith
  have hfloor : ⌊(sVal B x q - 3 / 2) * 20⌋₊ ≤ 50 := by
    have := Nat.floor_le_floor hz
    simpa using this
  have hk50 : kOf B x q ≤ 50 := by
    unfold kOf
    exact le_trans (min_le_left _ _) hfloor
  omega

/-! ## Splitting the window into the cells -/

/-- The window sum splits over the cells. -/
lemma sum_winPrimes_eq_sum_cellF (B : ℝ) (x : ℕ) (g : ℕ → ℝ) :
    (∑ q ∈ Submission.winPrimes (siftM x) (winY x), g q)
      = ∑ k ∈ Finset.range 71, ∑ q ∈ cellF B x k, g q := by
  rw [eq_comm]
  refine Finset.sum_fiberwise_of_maps_to ?_ g
  intro q hq
  simp only [Finset.mem_range]
  exact Nat.lt_succ_of_le (kOf_le B x q)

/-! ## The table is nonnegative and has small total mass -/

lemma List.getD_nonneg {l : List ℚ} (hl : ∀ a ∈ l, (0 : ℚ) ≤ a) (d : ℚ) (hd : 0 ≤ d) (n : ℕ) :
    0 ≤ l.getD n d := by
  induction l generalizing n with
  | nil => simpa using hd
  | cons a t ih =>
    cases n with
    | zero => simpa using hl a (by simp)
    | succ n => simpa using ih (fun b hb => hl b (by simp [hb])) n

lemma utabQ_nonneg (k : ℕ) : 0 ≤ (utabQ k : ℝ) := by
  rw [utabQ, tabQ]
  have h := List.getD_nonneg (l := Submission.ChenPlan.utabList)
    (by
      simp only [Submission.ChenPlan.utabList, List.mem_cons]
      norm_num) (0 : ℚ) le_rfl k
  exact_mod_cast h

lemma sum_utabQ_le : (∑ k ∈ Finset.range 71, (utabQ k : ℝ)) ≤ 100 := by
  simp only [utabQ, tabQ, Submission.ChenPlan.utabList,
    Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

end

end Work.ChenPlan.H2
