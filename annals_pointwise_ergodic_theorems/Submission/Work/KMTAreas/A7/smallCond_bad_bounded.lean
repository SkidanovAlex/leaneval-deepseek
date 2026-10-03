/-
# The "bad" (non-narrow) small scales are bounded

This module proves `Work.KMTAreas.A7.smallCond_bad_bounded`, the quantitative statement that
inside the §7 (small-scale) regime the *failure* of the narrowness inequality

  `max k₁ k₂ + 2·uScale ρ (smallL l₁ l₂ k₁ k₂) + 1 ≤ Log N`

can happen only for bounded scales `N = ⌊a n⌋` and bounded loss scale `L = smallL l₁ l₂ k₁ k₂`.

## The argument

Let `N = ⌊a n⌋`, `R = Log N = Nat.log 2 (max N 2)`, `L = smallL l₁ l₂ k₁ k₂` and
`u = uScale ρ L = ⌊2^{2ρL}⌋`.  The small-scale condition `smallCond` contains the admissibility
of the scale,

  `l₁, l₂, k₁, k₂ ≤ l_{(N)} = heightScale C₀ N = C₀ · Nat.log 2 (R + 2)`,

so `max k₁ k₂ ≤ C₀ · Nat.log 2 (R+2)` and `L ≤ C₀ · Nat.log 2 (R+2)`.  The failure of the
narrowness inequality says `R ≤ max k₁ k₂ + 2u`, and the scale count obeys

  `u = ⌊2^{2ρL}⌋ ≤ 2^{2ρL} ≤ 2^{(1/2) log₂(R+2)} = (R+2)^{1/2}`

(the exponent bound is `Work.KMTAreas.A7.scaleCount_le_sqrt`, which needs `ρ ≤ 1/(4C₀)`; our
hypothesis `ρ ≤ 1/(8C₀)` is stronger).  Altogether

  `R ≤ C₀ · log₂(R+2) + 2 (R+2)^{1/2}`,

and the numeric core proved below (the private lemma `logN_bound_sqrt_aux`) converts this super-linear
inequality on an integer `R` into the explicit bound `R ≤ (2C₀+4)²`: with `s = √(R+2)` the
inequality reads `s² - 2 ≤ 2C₀ log₂ s + 2s ≤ 2C₀(s-1) + 2s`, so `s ≤ 2C₀+2+2/s < 2C₀+3`, while
`R > (2C₀+4)²` would force `s > 2C₀+4`.

The two conclusions follow: `N < 2^{R+1}` and `L ≤ C₀ · Nat.log 2 (R+2) ≤ C₀ ((2C₀+4)²+2)`.

Note that the main-regime conjunct of `smallCond` is *not* used: the narrowness hypothesis of
this file is the one with the auxiliary scale computed at `L = smallL l₁ l₂ k₁ k₂`, which
dominates `max k₁ k₂`, the scale used by `mainRegime`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.SmallDefs
import Submission.Work.KMTAreas.A7.logb_sqrt_core
import Submission.Work.KMTAreas.A7.scaleCount_le_sqrt

namespace Work.KMTAreas.A7

/-- **Numeric core.**  If `c ≥ 1` and the integer `R` satisfies
`R ≤ c·log₂(R+2) + 2√(R+2)`, then `R ≤ (2c+4)²`.

Assume `R > (2c+4)²` and put `t = R+2`, `s = √t`, so that `t = s²`, `R = s²-2`,
`s > 2c+4 ≥ 6` and `log₂ t = 2 log₂ s ≤ 2(s-1)`.  The hypothesis becomes
`s² - 2 ≤ 2c(s-1) + 2s`, i.e. `s² ≤ (2c+2)s + 2`; dividing by `s > 0` gives
`s ≤ 2c+2+2/s < 2c+3`, contradicting `s > 2c+4`. -/
private theorem logN_bound_sqrt_aux (C₀ R : ℕ) (hC₀ : 1 ≤ C₀)
    (h : (R : ℝ) ≤ (C₀ : ℝ) * Real.logb 2 ((R : ℝ) + 2)
      + 2 * ((R : ℝ) + 2) ^ ((1 : ℝ) / 2)) :
    R ≤ (2 * C₀ + 4) ^ 2 := by
  by_contra hcon
  rw [not_le] at hcon
  have hk2 : ((2 * C₀ + 4 : ℕ) : ℝ) ^ 2 < (R : ℝ) := by
    have h1 : (((2 * C₀ + 4) ^ 2 : ℕ) : ℝ) < (R : ℝ) := by exact_mod_cast hcon
    simpa only [Nat.cast_pow] using h1
  have hk : ((2 * C₀ + 4 : ℕ) : ℝ) = 2 * (C₀ : ℝ) + 4 := by push_cast; ring
  rw [hk] at hk2
  set s : ℝ := Real.sqrt ((R : ℝ) + 2) with hs
  have hs_sq : s ^ 2 = (R : ℝ) + 2 := by rw [hs]; exact Real.sq_sqrt (by positivity)
  have hrpow : ((R : ℝ) + 2) ^ ((1 : ℝ) / 2) = s := by
    rw [← Real.sqrt_eq_rpow]
  have hlogb : Real.logb 2 ((R : ℝ) + 2) = 2 * Real.logb 2 s := by
    rw [← hs_sq, Real.logb_pow]
    norm_num
  have hsgt : 2 * (C₀ : ℝ) + 4 < s := by
    rw [hs, Real.lt_sqrt (by positivity : (0 : ℝ) ≤ 2 * (C₀ : ℝ) + 4)]
    linarith
  have hc1 : (1 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
  have hs2 : 2 ≤ s := by linarith
  have hlogbs : Real.logb 2 s ≤ s - 1 := logb_two_le_sub_one hs2
  have hmain : s ^ 2 - 2 ≤ 2 * (C₀ : ℝ) * (s - 1) + 2 * s := by
    have h' := h
    rw [hlogb, hrpow] at h'
    have hR : (R : ℝ) = s ^ 2 - 2 := by rw [hs_sq]; ring
    rw [hR] at h'
    have hstep : (C₀ : ℝ) * (2 * Real.logb 2 s) ≤ 2 * (C₀ : ℝ) * (s - 1) := by
      have h2 := mul_le_mul_of_nonneg_left hlogbs (show (0 : ℝ) ≤ (C₀ : ℝ) by positivity)
      linarith
    linarith [h', hstep]
  have hquad : s ^ 2 ≤ (2 * (C₀ : ℝ) + 2) * s + 2 := by nlinarith [hmain]
  have hsne : s ≠ 0 := by linarith
  have hdiv : s ≤ 2 * (C₀ : ℝ) + 2 + 2 / s := by
    have h1 : s ^ 2 / s ≤ ((2 * (C₀ : ℝ) + 2) * s + 2) / s :=
      div_le_div_of_nonneg_right hquad (by linarith : (0 : ℝ) ≤ s)
    have e1 : s ^ 2 / s = s := by rw [sq, mul_div_cancel_right₀ _ hsne]
    have e2 : ((2 * (C₀ : ℝ) + 2) * s + 2) / s = (2 * (C₀ : ℝ) + 2) + 2 / s := by
      rw [add_div, mul_div_cancel_right₀ _ hsne]
    rw [e1, e2] at h1
    exact h1
  have h2s : 2 / s < 1 := by
    rw [div_lt_iff₀ (by linarith : (0 : ℝ) < s)]
    linarith
  linarith [hdiv, h2s, hsgt]

theorem smallCond_bad_bounded (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1 / (8 * (C₀ : ℝ))) :
    ∃ D : ℕ, ∀ (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ n : ℕ),
      Work.KMTAreas.A7.smallCond ρ C₀ a l₁ l₂ k₁ k₂ n →
      ¬ ((max k₁ k₂ + 2 * Work.KMTAreas.A7.uScale ρ (Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂) + 1)
          ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat) →
      Nat.floor (a n) ≤ D ∧ Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂ ≤ D := by
  refine ⟨max (2 ^ ((2 * C₀ + 4) ^ 2 + 1)) (C₀ * ((2 * C₀ + 4) ^ 2 + 2)), ?_⟩
  intro a l₁ l₂ k₁ k₂ n hcond hbad
  set N : ℕ := Nat.floor (a n) with hN
  set R : ℕ := Nat.log 2 (max N 2) with hR
  have hlogN : (Work.Analysis.EndVar.logN N).toNat = R := by
    simp only [Work.Analysis.EndVar.logN, hR, Int.toNat_natCast]
  -- unpack the small-scale condition
  have hcond' := hcond
  unfold Work.KMTAreas.A7.smallCond at hcond'
  obtain ⟨hindex, -, -⟩ := hcond'
  simp only [Work.Analysis.EndVar.inIndexSet] at hindex
  obtain ⟨hlmax, hk₁, hk₂⟩ := hindex
  have hhs : Work.Analysis.EndVar.heightScale C₀ N = C₀ * Nat.log 2 (R + 2) := by
    unfold Work.Analysis.EndVar.heightScale Work.Analysis.EndVar.logLogN
    rw [← hR]
  have hl : max l₁ l₂ ≤ Work.Analysis.EndVar.heightScale C₀ N := by
    have h := hlmax
    rw [← Nat.cast_max] at h
    exact_mod_cast h
  have hk₁n : k₁ ≤ Work.Analysis.EndVar.heightScale C₀ N := by exact_mod_cast hk₁
  have hk₂n : k₂ ≤ Work.Analysis.EndVar.heightScale C₀ N := by exact_mod_cast hk₂
  have hL : Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂
      ≤ Work.Analysis.EndVar.heightScale C₀ N := by
    rw [Work.KMTAreas.A7.smallL]
    exact max_le hl (max_le hk₁n hk₂n)
  have hM : max k₁ k₂ ≤ Work.Analysis.EndVar.heightScale C₀ N := max_le hk₁n hk₂n
  have hLr : Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂ ≤ C₀ * Nat.log 2 (R + 2) := by
    rw [← hhs]; exact hL
  have hMr : max k₁ k₂ ≤ C₀ * Nat.log 2 (R + 2) := by
    rw [← hhs]; exact hM
  -- the failure of the narrowness inequality
  have hbad' : R ≤ max k₁ k₂
      + 2 * Work.KMTAreas.A7.uScale ρ (Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂) := by
    have h := Nat.lt_of_not_le hbad
    rw [hlogN] at h
    omega
  -- the auxiliary scale is at most `√(R+2)`
  have hρ4 : ρ ≤ 1 / (4 * (C₀ : ℝ)) := by
    have h4 : (0 : ℝ) < 4 * (C₀ : ℝ) := by
      have h0 : (0 : ℝ) < (C₀ : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hC₀)
      linarith
    have h8 : (0 : ℝ) < 8 * (C₀ : ℝ) := by linarith
    have h8' : ρ * (8 * (C₀ : ℝ)) ≤ 1 := (le_div_iff₀ h8).mp hρ1
    rw [le_div_iff₀ h4]
    nlinarith
  have hu : (Work.KMTAreas.A7.uScale ρ (Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂) : ℝ)
      ≤ ((R : ℝ) + 2) ^ ((1 : ℝ) / 2) := by
    have h := scaleCount_le_sqrt ρ C₀ (Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂) R
      hC₀ hρ hρ4 hLr
    simpa [Work.KMTAreas.A7.uScale] using h
  -- the real inequality
  have hC0nn : (0 : ℝ) ≤ (C₀ : ℝ) := by positivity
  have hlogb : ((Nat.log 2 (R + 2) : ℕ) : ℝ) ≤ Real.logb 2 ((R : ℝ) + 2) := by
    have h := Real.natLog_le_logb (R + 2) 2
    simpa using h
  have hMr' : (max k₁ k₂ : ℝ) ≤ (C₀ : ℝ) * Real.logb 2 ((R : ℝ) + 2) := by
    have h1 : ((max k₁ k₂ : ℕ) : ℝ) ≤ ((C₀ * Nat.log 2 (R + 2) : ℕ) : ℝ) := by
      exact_mod_cast hMr
    have h2 : ((C₀ * Nat.log 2 (R + 2) : ℕ) : ℝ)
        = (C₀ : ℝ) * ((Nat.log 2 (R + 2) : ℕ) : ℝ) := by push_cast; ring
    rw [h2] at h1
    rw [Nat.cast_max] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_left hlogb hC0nn)
  have hreal : (R : ℝ) ≤ (C₀ : ℝ) * Real.logb 2 ((R : ℝ) + 2)
      + 2 * ((R : ℝ) + 2) ^ ((1 : ℝ) / 2) := by
    have h1 : (R : ℝ) ≤ ((max k₁ k₂
        + 2 * Work.KMTAreas.A7.uScale ρ (Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂) : ℕ) : ℝ) := by
      exact_mod_cast hbad'
    have h2 : ((max k₁ k₂
        + 2 * Work.KMTAreas.A7.uScale ρ (Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂) : ℕ) : ℝ)
        = (max k₁ k₂ : ℝ)
          + 2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂) : ℝ) := by
      push_cast; ring
    rw [h2] at h1
    have h3 : 2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂) : ℝ)
        ≤ 2 * ((R : ℝ) + 2) ^ ((1 : ℝ) / 2) := by linarith [hu]
    linarith [h1, hMr', h3]
  -- the numeric core
  have hnum : R ≤ (2 * C₀ + 4) ^ 2 := logN_bound_sqrt_aux C₀ R hC₀ hreal
  -- bounds on `N` and on `L`
  have hNbound : N ≤ 2 ^ ((2 * C₀ + 4) ^ 2 + 1) := by
    have h1 : max N 2 < 2 ^ (R + 1) := by
      have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (max N 2)
      rw [← hR] at h
      simpa only [Nat.succ_eq_add_one] using h
    have h2 : N ≤ 2 ^ (R + 1) := le_trans (le_max_left N 2) h1.le
    exact le_trans h2 (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hLbound : Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂
      ≤ C₀ * ((2 * C₀ + 4) ^ 2 + 2) := by
    have hlog : Nat.log 2 (R + 2) ≤ (2 * C₀ + 4) ^ 2 + 2 := by
      calc Nat.log 2 (R + 2) ≤ Nat.log 2 ((2 * C₀ + 4) ^ 2 + 2) :=
            Nat.log_mono_right (by omega)
        _ ≤ (2 * C₀ + 4) ^ 2 + 2 := Nat.log_le_self 2 _
    calc Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂ ≤ C₀ * Nat.log 2 (R + 2) := hLr
      _ ≤ C₀ * ((2 * C₀ + 4) ^ 2 + 2) := Nat.mul_le_mul_left C₀ hlog
  exact ⟨le_trans hNbound (le_max_left _ _), le_trans hLbound (le_max_right _ _)⟩

end Work.KMTAreas.A7
