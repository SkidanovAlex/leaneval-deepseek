/-
# Narrowness of the modulated bump on the core of the model tuple

This module proves the *threshold comparison* that turns the height bound contained in the core
of the model tuple (`Work.KMTAreas.A7.core`) into the **narrowness** of the symbol
`varphiNt N k₁ t`: on the core, a nonzero value of the bump forces `|ξ|` to be as small as
`2^{⌊-Cρ·2^{ρl₁}⌋}`, i.e. the bump is `GoodMajorArcs ρ Cρ l₁ ·`-narrow.

The two inputs are

* the support of the bump, `varphiNt_support_le` (here in the form valid for *all* heights `k₁`,
  the case `k₁ = 0` included): `varphiNt N k₁ t ξ ≠ 0 → |ξ| ≤ 2^{k₁ - Log N}`;
* the height bound of the core, `inIndexSet C₀ (max l₁ l₂) k₁ k₂ N`, i.e.
  `L ≤ heightScale C₀ N = C₀ · LogLog N` with `L = max (max l₁ l₂) (max k₁ k₂)`, which gives

      `2 ^ (L / C₀ - 2) ≤ Log N + 2`     (`two_rpow_div_sub_two_le`)

  (because `2 ^ (L/C₀) ≤ 2 ^ LogLog N ≤ Log N + 2`).

Combining these with the explicit threshold hypothesis

      `k₁ + Cρ · 2^{ρ l₁} + 2 ≤ 2 ^ (L / C₀ - 2)`

yields `k₁ + Cρ · 2^{ρ l₁} ≤ Log N`, whence `k₁ - Log N ≤ ⌊-Cρ · 2^{ρ l₁}⌋` (an integer
comparison), and the support bound gives the claim with the floor exponent.

Only the `inIndexSet` conjunct of `core` is used; `splitCut` and `mainRegime` play no role here.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.varphiNt_support_le

namespace Work.KMTAreas.A7

open Work.Analysis.EndVar

/-! ## The support of the modulated bump at an arbitrary height -/

/-- **The support of the modulated bump `φ_{N,t}` at an arbitrary height `k₁ : ℕ`** (the case
`k₁ = 0` included, where `φ_N = η(2^{Log N}·)` and the support is `|ξ| < 2^{-Log N}`): a nonzero
value of `varphiNt N k₁ t` forces `|ξ| ≤ 2^{k₁ - Log N}`.

For `k₁ ≥ 1` this is `varphiNt_support_le`; for `k₁ = 0` the modulation `e(Nt·)` is nowhere zero
and `kmtEta_zero` bounds the argument of the cutoff by `1`. -/
lemma varphiNt_support_le_all (k₁ N : ℕ) (t : ℝ) :
    ∀ ξ : ℝ, varphiNt N k₁ t ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ ((k₁ : ℝ) - (logN N : ℝ)) := by
  intro ξ hξ
  rcases Nat.eq_zero_or_pos k₁ with hk | hk
  · -- the bottom height `k₁ = 0`
    subst hk
    have hprod : varphiN N 0 ξ * ee ((N : ℝ) * t * ξ) ≠ 0 := by
      simpa only [varphiNt] using hξ
    have h1 : varphiN N 0 ξ ≠ 0 := (mul_ne_zero_iff.mp hprod).1
    have h2 : Work.KMTContract.kmtEta ((2 : ℝ) ^ (logN N : ℝ) * ξ) ≠ 0 := by
      simpa only [varphiN, if_true] using h1
    have h3 : ¬ (1 ≤ |(2 : ℝ) ^ (logN N : ℝ) * ξ|) :=
      fun hc => h2 (Work.KMTContract.kmtEta_zero hc)
    have h4 : |(2 : ℝ) ^ (logN N : ℝ) * ξ| < 1 := lt_of_not_ge h3
    have hp : (0 : ℝ) < (2 : ℝ) ^ (logN N : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    rw [abs_mul, abs_of_pos hp] at h4
    have h7 : |ξ| < ((2 : ℝ) ^ (logN N : ℝ))⁻¹ := by
      rw [inv_eq_one_div, lt_div_iff₀ hp]
      linarith
    rw [← Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num) (logN N : ℝ)] at h7
    simpa only [Nat.cast_zero, zero_sub] using le_of_lt h7
  · -- the heights `k₁ ≥ 1`
    exact varphiNt_support_le k₁ hk N t ξ hξ

/-! ## The threshold arithmetic -/

/-- **The height bound of the core dominates the threshold.**  If `L ≤ heightScale C₀ N` and
`1 ≤ C₀`, then `2 ^ (L / C₀ - 2) ≤ Log N + 2`.  Indeed `L / C₀ ≤ LogLog N`, so
`2 ^ (L / C₀) ≤ 2 ^ LogLog N ≤ Log N + 2`; this is precisely the amount of room that the
threshold hypothesis of `narrow_of_core` is allowed to consume. -/
lemma two_rpow_div_sub_two_le (C₀ L N : ℕ) (hC₀ : 1 ≤ C₀) (hL : L ≤ heightScale C₀ N) :
    (2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ) - 2) ≤ (logN N : ℝ) + 2 := by
  have hC₀pos : (0 : ℝ) < C₀ := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hC₀)
  have hcast : (L : ℝ) ≤ (C₀ : ℝ) * (logLogN N : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr hL
    simpa only [heightScale, Nat.cast_mul] using this
  have hdiv : (L : ℝ) / (C₀ : ℝ) ≤ (logLogN N : ℝ) := by
    rw [div_le_iff₀ hC₀pos]; linarith
  have h1 : (2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ) - 2) ≤ (2 : ℝ) ^ ((logLogN N : ℝ) - 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h2 : (2 : ℝ) ^ ((logLogN N : ℝ) - 2) ≤ (2 : ℝ) ^ (logLogN N : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h3 : (2 : ℝ) ^ (logLogN N : ℝ) ≤ (logN N : ℝ) + 2 := by
    have hnat : 2 ^ logLogN N ≤ Nat.log 2 (max N 2) + 2 := by
      have hlog : logLogN N = Nat.log 2 (Nat.log 2 (max N 2) + 2) := rfl
      rw [hlog]
      exact Nat.pow_log_le_self 2 (by omega)
    calc (2 : ℝ) ^ (logLogN N : ℝ) = ((2 ^ logLogN N : ℕ) : ℝ) := by
          rw [Real.rpow_natCast, Nat.cast_pow]; norm_num
      _ ≤ ((Nat.log 2 (max N 2) + 2 : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = (logN N : ℝ) + 2 := by rw [logN]; push_cast; ring
  linarith

/-- **The real–integer comparison behind the floor.**  If `k + x ≤ Log N` with `k : ℕ` and
`x : ℝ`, then `k - Log N ≤ ⌊-x⌋`: the left-hand side is an integer and
`k - Log N ≤ -x`, so it is at most the greatest integer below `-x`. -/
lemma int_sub_le_floor_neg {N k : ℕ} {x : ℝ}
    (h : (k : ℝ) + x ≤ (logN N : ℝ)) : (k : ℤ) - logN N ≤ ⌊-x⌋ := by
  rw [Int.le_floor]
  simp only [logN, Int.cast_sub, Int.cast_natCast] at h ⊢
  linarith

/-! ## The threshold comparison -/

theorem narrow_of_core (ρ : ℝ) (Cρ : ℝ) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    {l₁ l₂ k₁ k₂ : ℕ} {a : ℕ → NNReal} {n : ℕ} {t : ℝ}
    (hcore : Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n)
    (hthr : (k₁ : ℝ) + Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) + 2 ≤
      (2 : ℝ) ^ (((max (max l₁ l₂) (max k₁ k₂) : ℕ) : ℝ) / (C₀ : ℝ) - 2)) :
    ∀ ξ : ℝ, Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ (⌊-Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ))⌋ : ℤ) := by
  intro ξ hξ
  -- only the `inIndexSet` conjunct of the core is used
  have hindex : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)) :=
    hcore.1
  have hLh : max (max l₁ l₂) (max k₁ k₂) ≤ heightScale C₀ (Nat.floor (a n)) := by
    have h1 : max (l₁ : ℤ) (l₂ : ℤ) ≤ (heightScale C₀ (Nat.floor (a n)) : ℤ) := hindex.1
    have h2 : (k₁ : ℤ) ≤ (heightScale C₀ (Nat.floor (a n)) : ℤ) := hindex.2.1
    have h3 : (k₂ : ℤ) ≤ (heightScale C₀ (Nat.floor (a n)) : ℤ) := hindex.2.2
    omega
  -- the threshold comparison `k₁ + Cρ 2^{ρl₁} ≤ Log N`
  have hkey : (k₁ : ℝ) + Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) ≤ (logN (Nat.floor (a n)) : ℝ) := by
    have h := two_rpow_div_sub_two_le C₀ (max (max l₁ l₂) (max k₁ k₂)) (Nat.floor (a n)) hC₀ hLh
    linarith
  -- the integer form of the comparison, with the floor
  have hfloor : (k₁ : ℤ) - logN (Nat.floor (a n)) ≤ ⌊-Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ))⌋ := by
    have h := int_sub_le_floor_neg (N := Nat.floor (a n)) (k := k₁)
      (x := Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) hkey
    have hx : -(Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) =
        -Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) := by ring
    rwa [hx] at h
  -- the support bound at the height `k₁` and the monotonicity of the integer power
  calc |ξ| ≤ (2 : ℝ) ^ ((k₁ : ℝ) - (logN (Nat.floor (a n)) : ℝ)) :=
        varphiNt_support_le_all k₁ (Nat.floor (a n)) t ξ hξ
    _ = (2 : ℝ) ^ ((k₁ : ℤ) - logN (Nat.floor (a n))) := by
        rw [← Real.rpow_intCast]
        congr 1
        simp only [logN, Int.cast_sub, Int.cast_natCast]
    _ ≤ (2 : ℝ) ^ (⌊-Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ))⌋ : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) hfloor

end Work.KMTAreas.A7
