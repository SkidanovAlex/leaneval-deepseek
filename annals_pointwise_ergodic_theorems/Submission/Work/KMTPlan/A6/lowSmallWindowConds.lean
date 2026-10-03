/-
# The window conditions of the small-scale low case

`Work.KMTPlan.A6.LowSmallDefs` documents two arithmetic conditions which make the narrow window
`m_* = η_{≤-2u} ⊗ η_{≤-2du}` (`u = uScale ρ L`, `L = lcL l₁ l₂ k₁ k₂`) the correct one for the
small-scale model of §6:

* **the window contains the bumps**: `max k₁ k₂ + 2u ≤ Log N` (the main regime);
* **the window is finer than the spacing of the arithmetic frequencies**: `L ≤ 2u`.

This module proves that on the admissible index set `I^{max(l₁,l₂),k₁,k₂}` both conditions hold
as soon as `L = lcL l₁ l₂ k₁ k₂` is large enough (the threshold depending on `ρ` and `C₀` only).

## The mathematics

Write `R = Log N = ⌊log₂ N⌋` and `q = LogLog N = ⌊log₂ (R+2)⌋`, so `2^q ≤ R + 2`.

*First condition.*  Admissibility gives `max k₁ k₂ ≤ L ≤ C₀ q`, and (because the window radius is
`2^{2ρL}`, i.e. `ρC₀ ≤ 1/8`)

  `uScale ρ L ≤ 2^{2ρL} ≤ 2^{q/4} ≤ 2^{q/2}`,

so `mainRegimeArith` (`max k₁ k₂ + 2·2^{q/2} ≤ 2^q - 2` for `C₀ ≤ q`, `q ≥ 8`) gives
`max k₁ k₂ + 2 uScale ρ L ≤ 2^q - 2 ≤ R`.  Finally `L ≥ C₀ · max C₀ 8` with `L ≤ C₀ q` forces
`q ≥ max C₀ 8`; this is where the threshold comes from.

*Second condition.*  Here `N` plays no role: one needs `L ≤ 2 ⌊2^{2ρL}⌋` for all `L ≥ B₂`, and any
`B₂ ≥ 1/(2ρ²)` works.  Indeed with `t = 2ρL ≥ 1/ρ ≥ 8` and `m = ⌊t⌋ ≥ 4` one has
`L = t/(2ρ)`, `2(t-1)^2 ≥ t/(2ρ) = L` (from `4ρ(t-1)^2 ≥ 4ρ t^2/4 = ρt^2 ≥ ρt·(1/ρ) = t`) and
`t - 1 ≤ m`, `m^2 ≤ 2^m`; hence `L ≤ 2m^2 ≤ 2·2^m ≤ 2 ⌊2^t⌋ = 2 uScale ρ L`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.LowSmallDefs
import Submission.Work.KMTPlan.A6.mainRegimeArith
import Submission.Work.KMTPlan.A6.uScaleHalfPow

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open Work.Analysis.EndVar

/-! ## Two elementary exponentials -/

/-- Linear beats exponential: `2m + 1 ≤ 2^m` for `m ≥ 4`. -/
private lemma two_mul_add_one_le_two_pow (m : ℕ) (hm : 4 ≤ m) : 2 * m + 1 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    calc 2 * (m + 1) + 1 = 2 * m + 3 := by ring
      _ ≤ 2 * (2 * m + 1) := by omega
      _ ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (m + 1) := by rw [pow_succ']

/-- Quadratic beats exponential: `m^2 ≤ 2^m` for `m ≥ 4`. -/
private lemma sq_le_two_pow (m : ℕ) (hm : 4 ≤ m) : m ^ 2 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have h1 : 2 * m + 1 ≤ 2 ^ m := two_mul_add_one_le_two_pow m hm
    calc (m + 1) ^ 2 = m ^ 2 + (2 * m + 1) := by ring
      _ ≤ 2 ^ m + 2 ^ m := Nat.add_le_add ih h1
      _ = 2 ^ (m + 1) := by rw [pow_succ']; ring

/-! ## The main theorem -/

theorem lowSmallWindowConds (ρ : ℝ) (hρ : 0 < ρ) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (hρC₀ : ρ * (C₀ : ℝ) ≤ 1 / 8) :
    ∃ B₀ : ℕ, ∀ (l₁ l₂ k₁ k₂ N : ℕ),
      Work.Analysis.EndVar.inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) N →
      B₀ ≤ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ →
      (max k₁ k₂ + 2 * Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)
          ≤ (Work.Analysis.EndVar.logN N).toNat) ∧
        Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂
          ≤ 2 * Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) := by
  refine ⟨max (C₀ * max C₀ 8) (Nat.ceil ((1 : ℝ) / (2 * ρ ^ 2)) + 1), ?_⟩
  intro l₁ l₂ k₁ k₂ N hidx hB
  have hC₀R : (1 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
  have hρ8 : ρ ≤ 1 / 8 := by nlinarith
  have hρC : ρ * (C₀ : ℝ) ≤ 1 / 4 := by linarith
  set L : ℕ := lcL l₁ l₂ k₁ k₂ with hLdef
  have hB₁ : C₀ * max C₀ 8 ≤ L := le_trans (le_max_left _ _) hB
  have hB₂ : Nat.ceil ((1 : ℝ) / (2 * ρ ^ 2)) + 1 ≤ L := le_trans (le_max_right _ _) hB
  obtain ⟨hl₁, hl₂, hk₁, hk₂⟩ :=
    (inIndexSet_iff_le (C₀ := C₀) (l₁ := l₁) (l₂ := l₂) (k₁ := k₁) (k₂ := k₂) (N := N)).mp hidx
  constructor
  · -- ## the first condition: the main regime
    set n : ℕ := Nat.log 2 (max N 2) with hn
    set q : ℕ := Work.Analysis.EndVar.logLogN N with hqdef
    have hq : q = Nat.log 2 (n + 2) := by rw [hqdef, hn]; rfl
    have hheight : heightScale C₀ N = C₀ * q := by rw [heightScale, hqdef]
    have hLle : L ≤ C₀ * q := by
      have h : L ≤ heightScale C₀ N := by
        rw [hLdef, lcL]
        exact max_le (max_le hl₁ hl₂) (max_le hk₁ hk₂)
      rwa [hheight] at h
    have hQle : max C₀ 8 ≤ q :=
      Nat.le_of_mul_le_mul_left (le_trans hB₁ hLle) (by omega)
    have hCq : C₀ ≤ q := le_trans (le_max_left _ _) hQle
    have hq8 : 8 ≤ q := le_trans (le_max_right _ _) hQle
    have hpow : 2 ^ q ≤ n + 2 := by
      rw [hq]
      exact Nat.pow_log_le_self 2 (by omega)
    have hmL : max k₁ k₂ ≤ L := by rw [hLdef, lcL]; exact le_max_right _ _
    have hkq : max k₁ k₂ ≤ C₀ * q := le_trans hmL hLle
    have hy : (Work.KMTAreas.A7.uScale ρ L : ℝ) ≤ (2 : ℝ) ^ ((q : ℝ) / 2) :=
      uScaleHalfPow ρ hρ C₀ q L L hρC le_rfl hLle
    have h1 : max (k₁ : ℝ) (k₂ : ℝ) + 2 * (Work.KMTAreas.A7.uScale ρ L : ℝ)
        ≤ (2 : ℝ) ^ q - 2 := by
      have h := mainRegimeArith C₀ q (max k₁ k₂) _ hC₀ hCq hq8 hkq hy
      rwa [Nat.cast_max] at h
    have h2 : (2 : ℝ) ^ q - 2 ≤ (n : ℝ) := by
      have h3 : (2 : ℝ) ^ q ≤ (n : ℝ) + 2 := by exact_mod_cast hpow
      linarith
    have h4 : (((max k₁ k₂) + 2 * Work.KMTAreas.A7.uScale ρ L : ℕ) : ℝ) ≤ (n : ℝ) := by
      push_cast
      linarith
    have h5 : max k₁ k₂ + 2 * Work.KMTAreas.A7.uScale ρ L ≤ n := by exact_mod_cast h4
    have hlog : (logN N).toNat = n := by simp only [logN, hn, Int.toNat_natCast]
    rw [hlog]
    exact h5
  · -- ## the second condition: the window is finer than the arithmetic spacing
    set m : ℕ := Nat.floor (2 * ρ * (L : ℝ)) with hm
    have hceil : (1 : ℝ) / (2 * ρ ^ 2) ≤ (L : ℝ) := by
      have h1 : (1 : ℝ) / (2 * ρ ^ 2) ≤ (Nat.ceil ((1 : ℝ) / (2 * ρ ^ 2)) : ℝ) :=
        Nat.le_ceil _
      have h2 : ((Nat.ceil ((1 : ℝ) / (2 * ρ ^ 2)) + 1 : ℕ) : ℝ) ≤ (L : ℝ) := by
        exact_mod_cast hB₂
      push_cast at h2
      linarith
    have ht_ge : (1 : ℝ) / ρ ≤ 2 * ρ * (L : ℝ) := by
      have h3 : 2 * ρ * ((1 : ℝ) / (2 * ρ ^ 2)) ≤ 2 * ρ * (L : ℝ) :=
        mul_le_mul_of_nonneg_left hceil (by positivity)
      have h4 : 2 * ρ * ((1 : ℝ) / (2 * ρ ^ 2)) = 1 / ρ := by
        field_simp
      linarith
    have ht8 : (8 : ℝ) ≤ 2 * ρ * (L : ℝ) := by
      have h5 : (8 : ℝ) ≤ (1 : ℝ) / ρ := by
        rw [le_div_iff₀ hρ]
        nlinarith
      linarith
    have hm4 : 4 ≤ m := by
      rw [hm]
      apply Nat.le_floor
      push_cast
      linarith
    have hmsq : m ^ 2 ≤ 2 ^ m := sq_le_two_pow m hm4
    have htm : 2 * ρ * (L : ℝ) - 1 ≤ (m : ℝ) := by
      have h := Nat.lt_floor_add_one (2 * ρ * (L : ℝ))
      rw [← hm] at h
      linarith
    have hLsq : (L : ℝ) ≤ 2 * (m : ℝ) ^ 2 := by
      set t : ℝ := 2 * ρ * (L : ℝ) with ht
      have ht1 : (1 : ℝ) / ρ ≤ t := ht_ge
      have ht8' : (8 : ℝ) ≤ t := ht8
      have htm' : t - 1 ≤ (m : ℝ) := htm
      have hLt : (L : ℝ) = t / (2 * ρ) := by
        rw [ht]
        field_simp
      have h1 : 1 ≤ ρ * t := by
        rw [div_le_iff₀ hρ] at ht1
        linarith
      have h2 : t ^ 2 / 4 ≤ (t - 1) ^ 2 := by nlinarith
      have h3 : t ≤ ρ * t ^ 2 := by nlinarith
      have hstep : t ≤ 4 * ρ * (t - 1) ^ 2 := by nlinarith
      have hm2 : (t - 1) ^ 2 ≤ (m : ℝ) ^ 2 := by
        have h0 : (0 : ℝ) ≤ t - 1 := by linarith
        have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        nlinarith [htm', h0, hm0]
      rw [hLt, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ρ)]
      nlinarith
    have hfloor : 2 ^ m ≤ Work.KMTAreas.A7.uScale ρ L := by
      have hu : Work.KMTAreas.A7.uScale ρ L = Nat.floor ((2 : ℝ) ^ (2 * ρ * (L : ℝ))) := by
        simp [Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount, Int.floor_toNat]
      rw [hu]
      have hmle : ((m : ℕ) : ℝ) ≤ 2 * ρ * (L : ℝ) := by
        have h := Nat.floor_le (show (0 : ℝ) ≤ 2 * ρ * (L : ℝ) by positivity)
        rwa [← hm] at h
      have hmm : (2 : ℝ) ^ ((m : ℝ)) ≤ (2 : ℝ) ^ (2 * ρ * (L : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num) hmle
      rw [Real.rpow_natCast] at hmm
      refine Nat.le_floor ?_
      rw [Nat.cast_pow]
      norm_num
      exact hmm
    have h1 : L ≤ 2 * m ^ 2 := by exact_mod_cast hLsq
    have h2 : 2 * m ^ 2 ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 hmsq
    have h3 : 2 * 2 ^ m ≤ 2 * Work.KMTAreas.A7.uScale ρ L := Nat.mul_le_mul_left 2 hfloor
    omega

end Work.KMTPlan.A6
