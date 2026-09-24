import Mathlib
import Submission.Work.ChenPlan.H2.WindowCells

/-!
# The cell endpoints of Chen's `h2` window are bounded by the model

`log_cellEndpoints_le_model` compares the `log log` of the cell mass of the linear-sieve
upper envelope with the model `log (mnum k / mden k)`.

With `M = siftM x`, `Y = winY x`, `L_j = thrL B x j = D · M^{-(3/2 + j/20)}` (`D = lvlD B x`),
`σ = log D / log M ≤ 5` and `s_k = 3/2 + k/20`,

* `cellHi k = min (Y-1) ⌊L_k⌋` so `log (cellHi k + 1) ≤ min (log Y) (log (L_k + 1)) ≤
  (min (10/3) (7/2 - k/20) + ε₁) · log M`,
* `cellLo k = max M (⌊L_{k+1}⌋ + 1)` so `log (cellLo k) ≥ max (log M) (log L_{k+1}) ≥
  (max 1 (7/2 - (k+1)/20) - ε₁) · log M`,

and the ratio of the two `log`s is at most
`min (7/2 - k/20) (10/3) / max 1 (7/2 - (k+1)/20) = mnum k / mden k` up to an error that tends
to `0`.  The constants below are chosen so that the error is eventually `< 10⁻⁷`.
-/

open Finset Filter
open scoped BigOperators

namespace Work.ChenPlan.H2

noncomputable section

/-! ## The model quantities -/

lemma mnum_eq_min (k : ℕ) : mnum k = min ((7:ℝ)/2 - (k:ℝ)/20) (10/3) := rfl

lemma mden_eq_max (k : ℕ) : mden k = max 1 ((7:ℝ)/2 - ((k:ℝ)+1)/20) := rfl

lemma mnum_nonneg {k : ℕ} (hk : k ≤ 70) : (0:ℝ) ≤ mnum k := by
  rw [mnum_eq_min]
  refine le_min ?_ ?_
  · have : (k:ℝ) ≤ 70 := by exact_mod_cast hk
    linarith
  · norm_num

lemma mnum_le_ten_thirds (k : ℕ) : mnum k ≤ 10/3 := by
  rw [mnum_eq_min]; exact min_le_right _ _

lemma mnum_le_linear (k : ℕ) : mnum k ≤ (7:ℝ)/2 - (k:ℝ)/20 := by
  rw [mnum_eq_min]; exact min_le_left _ _

lemma one_le_mden (k : ℕ) : (1:ℝ) ≤ mden k := by
  rw [mden_eq_max]; exact le_max_left _ _

lemma mden_le_seven_halves (k : ℕ) : mden k ≤ 7/2 := by
  rw [mden_eq_max]
  refine max_le ?_ ?_
  · norm_num
  · have : (0:ℝ) ≤ (k:ℝ) + 1 := by positivity
    linarith

lemma mnum_eq_zero_iff {k : ℕ} (hk : k ≤ 70) : mnum k = 0 ↔ k = 70 := by
  constructor
  · intro h
    rw [mnum_eq_min] at h
    have hle : (7:ℝ)/2 - (k:ℝ)/20 ≤ 0 := by
      by_contra hc
      push_neg at hc
      have : 0 < min ((7:ℝ)/2 - (k:ℝ)/20) (10/3) := lt_min hc (by norm_num)
      linarith
    have hk70 : (70:ℝ) ≤ (k:ℝ) := by linarith
    have : 70 ≤ k := by exact_mod_cast hk70
    omega
  · intro h
    rw [h, mnum_eq_min]
    norm_num

lemma one_twentieth_le_mnum_of_pos {k : ℕ} (hk : k ≤ 70) (h : 0 < mnum k) :
    (1:ℝ)/20 ≤ mnum k := by
  have hk69 : k ≤ 69 := by
    by_contra hc
    push_neg at hc
    have h70 : k = 70 := by omega
    rw [h70, mnum_eq_min] at h
    norm_num at h
  rw [mnum_eq_min]
  refine le_min ?_ ?_
  · have : (k:ℝ) ≤ 69 := by exact_mod_cast hk69
    linarith
  · norm_num

/-! ## The algebraic core -/

/-- If `α ≤ (mnum k + ε₁) u` and `β ≥ (mden k - ε₁) u` then
`log (α/β) ≤ log (mnum k / mden k) + ε` for the numerical constants below. -/
lemma log_model_le {α β u : ℝ} {k : ℕ} (hk : k ≤ 70) (hu : 0 < u)
    (hα : 0 < α) (hβ : 0 < β)
    (hαN : α ≤ (mnum k + 1 / 10000000000) * u)
    (hβD : (mden k - 1 / 10000000000) * u ≤ β) :
    Real.log (α / β) ≤ Real.log (mnum k / mden k) + 1 / 10000000 := by
  have hηpos : (0:ℝ) < 1 / 10000000000 := by norm_num
  have hD1 : (1:ℝ) ≤ mden k := one_le_mden k
  have hDηpos : (0:ℝ) < mden k - 1 / 10000000000 := by linarith
  have hN0 : (0:ℝ) ≤ mnum k := mnum_nonneg hk
  have hstep1 : α / β ≤ (mnum k + 1 / 10000000000) / (mden k - 1 / 10000000000) := by
    have h1 : α / β ≤ ((mnum k + 1/10000000000) * u) / ((mden k - 1/10000000000) * u) :=
      div_le_div₀ (mul_nonneg (by linarith) hu.le) hαN (mul_pos hDηpos hu) hβD
    rwa [mul_div_mul_right _ _ (ne_of_gt hu)] at h1
  rcases eq_or_lt_of_le hN0 with hN0' | hNpos
  · have hk70 : k = 70 := (mnum_eq_zero_iff hk).mp hN0'.symm
    have hmden : mden k = 1 := by rw [hk70, mden_eq_max]; norm_num
    have hlt1 : α / β < 1 := by
      have h2 : α / β ≤ (1/10000000000 : ℝ) / (1 - 1/10000000000) := by
        rw [← hN0', hmden] at hstep1
        norm_num at hstep1 ⊢
        exact hstep1
      have h3 : (1/10000000000 : ℝ) / (1 - 1/10000000000) < 1 := by norm_num
      linarith
    have hle0 : Real.log (α / β) ≤ 0 := Real.log_nonpos (le_of_lt (div_pos hα hβ)) hlt1.le
    have hz : Real.log (mnum k / mden k) = 0 := by rw [← hN0', hmden]; simp
    rw [hz]
    linarith
  · have hNge : (1:ℝ)/20 ≤ mnum k := one_twentieth_le_mnum_of_pos hk hNpos
    have hNle : mnum k ≤ 10/3 := mnum_le_ten_thirds k
    have hDle : mden k ≤ 7/2 := mden_le_seven_halves k
    have hDpos : (0:ℝ) < mden k := lt_of_lt_of_le zero_lt_one hD1
    have hcross' : (mnum k + 1/10000000000) * mden k
        ≤ mnum k * (1 + 1/10000000) * (mden k - 1/10000000000) := by
      have hkey : (1/10000000000 : ℝ) * (mden k + mnum k * (1 + 1/10000000))
          ≤ mnum k * mden k * (1/10000000) := by
        have h1 : (1/10000000000 : ℝ) * (mden k + mnum k * (1 + 1/10000000))
            ≤ (1/10000000000) * (7/2 + (10/3) * (1 + 1/10000000)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1/10000000000)
          nlinarith [hDle, hNle]
        have h2 : (1/10000000000 : ℝ) * (7/2 + (10/3) * (1 + 1/10000000))
            ≤ (1/20 : ℝ) * 1 * (1/10000000) := by norm_num
        have h3 : (1/20 : ℝ) * 1 * (1/10000000) ≤ mnum k * mden k * (1/10000000) := by
          have h4 : (1/20 : ℝ) * 1 ≤ mnum k * mden k :=
            mul_le_mul hNge hD1 (by norm_num) (le_of_lt hNpos)
          calc (1/20 : ℝ) * 1 * (1/10000000)
              = ((1/20) * 1) * (1/10000000) := by ring
            _ ≤ (mnum k * mden k) * (1/10000000) :=
                mul_le_mul_of_nonneg_right h4 (by norm_num)
            _ = mnum k * mden k * (1/10000000) := by ring
        linarith
      nlinarith [hkey]
    have hcross : (mnum k + 1/10000000000) / (mden k - 1/10000000000)
        ≤ mnum k * (1 + 1/10000000) / mden k := by
      rw [le_div_iff₀ hDpos, div_mul_eq_mul_div, div_le_iff₀ hDηpos]
      linarith [hcross']
    have h3 : Real.log (α / β) ≤ Real.log (mnum k * (1 + 1/10000000) / mden k) :=
      Real.log_le_log (div_pos hα hβ) (le_trans hstep1 hcross)
    have h4 : Real.log (mnum k * (1 + 1/10000000) / mden k)
        = Real.log (mnum k / mden k) + Real.log (1 + 1/10000000) := by
      rw [Real.log_div (mul_ne_zero (ne_of_gt hNpos) (by norm_num)) (ne_of_gt hDpos),
        Real.log_mul (ne_of_gt hNpos) (by norm_num), Real.log_div (ne_of_gt hNpos) (ne_of_gt hDpos)]
      ring
    have h5 : Real.log (1 + 1/10000000) ≤ 1/10000000 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 1/10000000 by norm_num)
      linarith
    linarith

/-! ## Eventual estimates -/

/-- `log Y ≤ (10/3 + 10⁻¹⁰) log M` eventually. -/
lemma eventually_log_winY_le :
    ∀ᶠ x : ℕ in Filter.atTop,
      Real.log (winY x) ≤ (10 / 3 + (1:ℝ) / 10000000000) * Real.log (siftM x) := by
  filter_upwards [eventually_log_ge (10 * Real.log 3 / ((1:ℝ) / 10000000000)),
    Filter.eventually_ge_atTop 1] with x hx hx1
  have hx0 : (0:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hx1' : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx1
  have hx13 : (1:ℝ) ≤ (x:ℝ) ^ ((1:ℝ)/3) := by
    have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hx1' (by norm_num : (0:ℝ) ≤ 1/3)
    rwa [Real.one_rpow] at h
  have hYle : ((winY x : ℕ) : ℝ) ≤ 3 * (x:ℝ) ^ ((1:ℝ)/3) := by
    rw [winY_eq]; push_cast
    have h := floor_rpow_three_le x
    linarith
  have hYpos : (0:ℝ) < ((winY x : ℕ) : ℝ) := by
    rw [winY_eq]; push_cast
    linarith [Nat.cast_nonneg (α := ℝ) ⌊(x : ℝ) ^ ((1:ℝ)/3)⌋₊]
  have hlogY : Real.log (((winY x : ℕ) : ℝ)) ≤ Real.log 3 + Real.log (x:ℝ)/3 := by
    have h := Real.log_le_log hYpos hYle
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0] at h
    linarith
  have hlog3 : Real.log 3 ≤ (1:ℝ)/10000000000 * Real.log (x:ℝ) / 10 := by
    have h := (div_le_iff₀ (show (0:ℝ) < 1/10000000000 by norm_num)).mp hx
    linarith
  have hu : Real.log (x:ℝ)/10 ≤ Real.log (siftM x : ℝ) := log_siftM_ge hx1
  have hc : (0:ℝ) ≤ 10/3 + 1/10000000000 := by norm_num
  have h1 : (10/3 + 1/10000000000) * (Real.log (x:ℝ)/10)
      ≤ (10/3 + 1/10000000000) * Real.log (siftM x : ℝ) :=
    mul_le_mul_of_nonneg_left hu hc
  have h2 : Real.log (x:ℝ)/3 + (1:ℝ)/10000000000 * Real.log (x:ℝ)/10
      = (10/3 + 1/10000000000) * (Real.log (x:ℝ)/10) := by ring
  linarith

/-- `log (L_k + 1) ≤ (7/2 - k/20 + 10⁻¹⁰) log M` eventually, for all `k ≤ 70`. -/
lemma eventually_log_thrL_add_one_le (B : ℝ) (hB : 0 < B) :
    ∀ᶠ x : ℕ in Filter.atTop, ∀ k : ℕ, k ≤ 70 →
      Real.log (thrL B x k + 1)
        ≤ ((7:ℝ)/2 - (k:ℝ)/20 + 1/10000000000) * Real.log (siftM x) := by
  have hc : (1:ℝ) ≤ Real.log 2 / (1/10000000000) := by
    rw [le_div_iff₀ (show (0:ℝ) < 1/10000000000 by norm_num)]
    have h := Real.log_two_gt_d9
    nlinarith
  filter_upwards [eventually_log_siftM_ge (c := Real.log 2 / (1/10000000000)) hc,
    Filter.eventually_ge_atTop 8] with x hx hx8
  intro k hk
  have hx2 : 2 ≤ x := by omega
  have hlvlD : 0 < lvlD B x := lvlD_pos hB hx2
  have hMpos : (0:ℝ) < (siftM x : ℝ) := by
    rw [siftM_eq]; push_cast
    linarith [Nat.cast_nonneg (α := ℝ) ⌊(x:ℝ)^((1:ℝ)/10)⌋₊]
  have hM1 : (1:ℝ) < (siftM x : ℝ) := by
    have h2 : (2:ℕ) ≤ siftM x := by
      rw [siftM_eq]
      have h1 : (1:ℕ) ≤ ⌊(x:ℝ)^((1:ℝ)/10)⌋₊ := by
        apply Nat.le_floor
        push_cast
        have hx1' : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
        have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hx1' (by norm_num : (0:ℝ) ≤ 1/10)
        rwa [Real.one_rpow] at h
      omega
    exact_mod_cast (by omega : 1 < siftM x)
  have hu : 0 < Real.log (siftM x : ℝ) := Real.log_pos hM1
  have hsig5 : sigM B x ≤ 5 := sigM_le_five B hB hx8
  have hlogD : Real.log (lvlD B x) = sigM B x * Real.log (siftM x : ℝ) := by
    rw [sigM]; field_simp
  have hTpos : 0 < thrL B x k := by
    rw [thrL]; exact div_pos hlvlD (Real.rpow_pos_of_pos hMpos _)
  have hlogT : Real.log (thrL B x k) ≤ ((7:ℝ)/2 - (k:ℝ)/20) * Real.log (siftM x) := by
    rw [thrL, Real.log_div (ne_of_gt hlvlD) (ne_of_gt (Real.rpow_pos_of_pos hMpos _)),
      Real.log_rpow hMpos]
    have h2 : Real.log (lvlD B x) ≤ 5 * Real.log (siftM x : ℝ) := by
      rw [hlogD]
      exact mul_le_mul_of_nonneg_right hsig5 hu.le
    nlinarith [h2, hu]
  have hlog2 : Real.log 2 ≤ (1:ℝ)/10000000000 * Real.log (siftM x) := by
    have h := (div_le_iff₀ (show (0:ℝ) < 1/10000000000 by norm_num)).mp hx
    linarith
  have hk20 : (0:ℝ) ≤ (7:ℝ)/2 - (k:ℝ)/20 := by
    have : (k:ℝ) ≤ 70 := by exact_mod_cast hk
    linarith
  have hgoal : ((7:ℝ)/2 - (k:ℝ)/20 + 1/10000000000) * Real.log (siftM x)
      = ((7:ℝ)/2 - (k:ℝ)/20) * Real.log (siftM x) + (1/10000000000) * Real.log (siftM x) := by
    ring
  rcases le_or_gt 1 (thrL B x k) with hT1 | hT1
  · have hle : thrL B x k + 1 ≤ 2 * thrL B x k := by linarith
    have h1 : Real.log (thrL B x k + 1) ≤ Real.log (2 * thrL B x k) :=
      Real.log_le_log (by linarith) hle
    rw [Real.log_mul (by norm_num) (ne_of_gt hTpos)] at h1
    rw [hgoal]
    linarith
  · have hle : thrL B x k + 1 ≤ 2 := by linarith
    have h1 : Real.log (thrL B x k + 1) ≤ Real.log 2 :=
      Real.log_le_log (by linarith) hle
    rw [hgoal]
    have hnn : 0 ≤ ((7:ℝ)/2 - (k:ℝ)/20) * Real.log (siftM x) := mul_nonneg hk20 hu.le
    linarith

/-! ## The main theorem -/

theorem log_cellEndpoints_le_model (B : ℝ) (hB : 0 < B) : ∀ᶠ x : ℕ in Filter.atTop, ∀ k : ℕ, k ≤ 70 → Real.log (Real.log (((Work.ChenPlan.H2.cellHi B x k) + 1 : ℕ) : ℝ) / Real.log ((Work.ChenPlan.H2.cellLo B x k : ℕ) : ℝ)) ≤ max 0 (Real.log (Work.ChenPlan.H2.mnum k / Work.ChenPlan.H2.mden k)) + ((1 : ℝ) / 10000000) := by
  have hsig : ∀ᶠ x : ℕ in Filter.atTop, 5 - 1/10000000000 ≤ sigM B x :=
    eventually_sigM_ge B hB (by norm_num) (by norm_num)
  filter_upwards [eventually_log_winY_le, eventually_log_thrL_add_one_le B hB, hsig,
    Filter.eventually_ge_atTop 8] with x hE1 hE2 hE3 hx8
  intro k hk
  have hx1 : 1 ≤ x := by omega
  have hx2 : 2 ≤ x := by omega
  have hM2 : (2:ℕ) ≤ siftM x := by
    rw [siftM_eq]
    have h1 : (1:ℝ) ≤ (x:ℝ)^((1:ℝ)/10) := by
      have hx1' : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx1
      have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hx1' (by norm_num : (0:ℝ) ≤ 1/10)
      rwa [Real.one_rpow] at h
    have h2 : (1:ℕ) ≤ ⌊(x:ℝ)^((1:ℝ)/10)⌋₊ := Nat.le_floor (by push_cast; exact h1)
    omega
  have hMpos : (0:ℝ) < (siftM x : ℝ) := by exact_mod_cast (by omega : 0 < siftM x)
  have hM1 : (1:ℝ) < (siftM x : ℝ) := by exact_mod_cast (by omega : 1 < siftM x)
  have hu : 0 < Real.log (siftM x : ℝ) := Real.log_pos hM1
  have hY1 : 1 ≤ winY x := by rw [winY_eq]; omega
  have hlvlD : 0 < lvlD B x := lvlD_pos hB hx2
  have hTpos : 0 < thrL B x k := by
    rw [thrL]; exact div_pos hlvlD (Real.rpow_pos_of_pos hMpos _)
  have hT'pos : 0 < thrL B x (k+1) := by
    rw [thrL]; exact div_pos hlvlD (Real.rpow_pos_of_pos hMpos _)
  -- endpoint inequalities
  have hhi1 : cellHi B x k ≤ winY x - 1 := by
    simp only [cellHi]; exact min_le_left _ _
  have hhi2 : cellHi B x k ≤ ⌊thrL B x k⌋₊ := by
    simp only [cellHi]; exact min_le_right _ _
  have hlo1 : siftM x ≤ cellLo B x k := by
    simp only [cellLo]; exact le_max_left _ _
  have hlo2 : ⌊thrL B x (k+1)⌋₊ + 1 ≤ cellLo B x k := by
    simp only [cellLo]; exact le_max_right _ _
  set a := Real.log (((cellHi B x k) + 1 : ℕ) : ℝ) with ha
  set b := Real.log ((cellLo B x k : ℕ) : ℝ) with hb
  have haY : a ≤ Real.log (winY x) := by
    rw [ha]
    refine Real.log_le_log (by positivity) ?_
    have h := Nat.add_le_add_right hhi1 1
    rw [Nat.sub_add_cancel hY1] at h
    exact_mod_cast h
  have haT : a ≤ Real.log (thrL B x k + 1) := by
    rw [ha]
    refine Real.log_le_log (by positivity) ?_
    have h1 : ((cellHi B x k : ℕ) : ℝ) ≤ ((⌊thrL B x k⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast hhi2
    have h2 : ((⌊thrL B x k⌋₊ : ℕ) : ℝ) ≤ thrL B x k := Nat.floor_le hTpos.le
    push_cast
    linarith
  have hbM : Real.log (siftM x) ≤ b := by
    rw [hb]
    refine Real.log_le_log (by exact_mod_cast (by omega : 0 < siftM x)) ?_
    exact_mod_cast hlo1
  have hbT : Real.log (thrL B x (k+1)) ≤ b := by
    rw [hb]
    refine Real.log_le_log hT'pos ?_
    have h3 : thrL B x (k+1) ≤ ((⌊thrL B x (k+1)⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast
      have := Nat.lt_floor_add_one (thrL B x (k+1))
      linarith
    have h4 : ((⌊thrL B x (k+1)⌋₊ + 1 : ℕ) : ℝ) ≤ ((cellLo B x k : ℕ) : ℝ) := by
      exact_mod_cast hlo2
    linarith
  have ha_le : a ≤ (mnum k + 1/10000000000) * Real.log (siftM x) := by
    have hmin : min (Real.log (winY x)) (Real.log (thrL B x k + 1))
        ≤ (mnum k + 1/10000000000) * Real.log (siftM x) := by
      have h3 : min (Real.log (winY x)) (Real.log (thrL B x k + 1))
          ≤ min ((10/3 + 1/10000000000) * Real.log (siftM x))
                (((7:ℝ)/2 - (k:ℝ)/20 + 1/10000000000) * Real.log (siftM x)) := by
        refine le_min ?_ ?_
        · exact le_trans (min_le_left _ _) hE1
        · exact le_trans (min_le_right _ _) (hE2 k hk)
      have h4 : min ((10/3 + 1/10000000000) * Real.log (siftM x))
                (((7:ℝ)/2 - (k:ℝ)/20 + 1/10000000000) * Real.log (siftM x))
          = (mnum k + 1/10000000000) * Real.log (siftM x) := by
        have hmm : min (10/3 + 1/10000000000) ((7:ℝ)/2 - (k:ℝ)/20 + 1/10000000000)
            = mnum k + 1/10000000000 := by
          rw [min_add_add_right, min_comm (10/3) ((7:ℝ)/2 - (k:ℝ)/20), ← mnum_eq_min]
        rw [← min_mul_of_nonneg (10/3 + 1/10000000000) ((7:ℝ)/2 - (k:ℝ)/20 + 1/10000000000) hu.le, hmm]
      linarith [h3, h4.le]
    exact le_trans (le_min haY haT) hmin
  have hb_ge : (mden k - 1/10000000000) * Real.log (siftM x) ≤ b := by
    have h3 : (((7:ℝ)/2 - (((k:ℝ)+1)/20)) - 1/10000000000) * Real.log (siftM x)
        ≤ Real.log (thrL B x (k+1)) := by
      have hT' : Real.log (thrL B x (k+1))
          = (sigM B x - ((3:ℝ)/2 + ((k:ℝ)+1)/20)) * Real.log (siftM x) := by
        rw [thrL, Real.log_div (ne_of_gt hlvlD) (ne_of_gt (Real.rpow_pos_of_pos hMpos _)),
          Real.log_rpow hMpos]
        have hlogD : Real.log (lvlD B x) = sigM B x * Real.log (siftM x : ℝ) := by
          rw [sigM]; field_simp
        push_cast
        rw [hlogD]
        ring
      rw [hT']
      apply mul_le_mul_of_nonneg_right _ hu.le
      linarith [hE3]
    have hm1 : max 1 ((7:ℝ)/2 - ((k:ℝ)+1)/20) - 1/10000000000
        ≤ max 1 (((7:ℝ)/2 - ((k:ℝ)+1)/20) - 1/10000000000) := by
      rcases le_or_gt 1 ((7:ℝ)/2 - ((k:ℝ)+1)/20) with h | h
      · rw [max_eq_right h]
        exact le_max_right (1:ℝ) ((7:ℝ)/2 - ((k:ℝ)+1)/20 - 1/10000000000)
      · rw [max_eq_left (le_of_lt h)]
        refine le_trans (by norm_num : (1:ℝ) - 1/10000000000 ≤ 1) ?_
        exact le_max_left (1:ℝ) ((7:ℝ)/2 - ((k:ℝ)+1)/20 - 1/10000000000)
    have hm2 : (mden k - 1/10000000000) * Real.log (siftM x)
        ≤ max (Real.log (siftM x))
            ((((7:ℝ)/2 - ((k:ℝ)+1)/20) - 1/10000000000) * Real.log (siftM x)) := by
      rw [mden_eq_max]
      have h1 : (max 1 ((7:ℝ)/2 - ((k:ℝ)+1)/20) - 1/10000000000) * Real.log (siftM x)
          ≤ max 1 (((7:ℝ)/2 - ((k:ℝ)+1)/20) - 1/10000000000) * Real.log (siftM x) :=
        mul_le_mul_of_nonneg_right hm1 hu.le
      have h2 : max 1 (((7:ℝ)/2 - ((k:ℝ)+1)/20) - 1/10000000000) * Real.log (siftM x)
          = max (1 * Real.log (siftM x))
              ((((7:ℝ)/2 - ((k:ℝ)+1)/20) - 1/10000000000) * Real.log (siftM x)) :=
        max_mul_of_nonneg _ _ hu.le
      rw [h2] at h1
      simpa using h1
    exact le_trans hm2 (max_le (by simpa using hbM) (le_trans h3 hbT))
  have ha0 : 0 ≤ a := by
    rw [ha]
    exact Real.log_nonneg (by exact_mod_cast (Nat.le_add_left 1 (cellHi B x k)))
  have hbpos : 0 < b := lt_of_lt_of_le hu hbM
  rcases eq_or_lt_of_le ha0 with haeq | hapos
  · rw [← haeq, zero_div, Real.log_zero]
    have := le_max_left (0:ℝ) (Real.log (mnum k / mden k))
    linarith
  · have hr : a / b ≤ (mnum k + 1 / 10000000000) / (mden k - 1 / 10000000000) := by
      have h1 : a / b ≤ ((mnum k + 1/10000000000) * Real.log (siftM x))
          / ((mden k - 1/10000000000) * Real.log (siftM x)) := by
        refine div_le_div₀ (mul_nonneg (add_nonneg (mnum_nonneg hk) (by norm_num)) hu.le) ha_le ?_ hb_ge
        have : (0:ℝ) < mden k - 1/10000000000 := by
          have := one_le_mden k
          linarith
        exact mul_pos this hu
      rwa [mul_div_mul_right _ _ (ne_of_gt hu)] at h1
    have h2 := log_model_le hk hu hapos hbpos ha_le hb_ge
    have h3 := le_max_right (0:ℝ) (Real.log (mnum k / mden k))
    linarith

end

end Work.ChenPlan.H2
