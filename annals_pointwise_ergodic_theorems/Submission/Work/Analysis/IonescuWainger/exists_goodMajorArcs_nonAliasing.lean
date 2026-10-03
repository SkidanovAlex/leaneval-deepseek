/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Analysis.IonescuWainger.MajorArcs
import Submission.Work.Analysis.IonescuWainger.iw_height_separated

/-!
# Good major arcs are non-aliasing

This file proves the first assertion of Theorem `thm:iw` of Krause–Mirek–Tao,
*Pointwise ergodic theorems for non-conventional bilinear polynomial averages*
(Annals of Math. 195 (2022)), at the level of the arithmetic frequency set
`(ℚ/ℤ)_{≤l}` of Appendix A: **for `C_ρ` large enough, every *good* pair of major
arcs is non-aliasing.**

Concretely, with `ℝ_{≤k} = [-2^k, 2^k]` (the file's `realArc`) and
`(ℚ/ℤ)_{≤l}` (the file's `iwArithFreqs ρ l`), the statement is that there is a
constant `Cρ > 0` such that whenever `k ≤ -Cρ · 2^{ρl}` (the file's
`GoodMajorArcs`), the addition map `(θ, α) ↦ θ + α` is injective on
`ℝ_{≤k} × (ℚ/ℤ)_{≤l}` (the file's `NonAliasing`).

## The argument

The only input is the separation of the arithmetic frequencies proved in
`Work.Analysis.IonescuWainger.iw_height_separated`: distinct elements `α ≠ β` of
`(ℚ/ℤ)_{≤l}` have circle distance at least `2^{-C 2^{ρl}}` for some `C = C(ρ) > 0`.
Taking `Cρ = C + 2` one gets the strict inequality

`2^{k+1} < 2^{-C 2^{ρl}}`  (`two_pow_le_of_goodMajorArcs` below),

because `k ≤ -(C+2) 2^{ρl}` gives `k + 1 ≤ -(C+2) 2^{ρl} + 1 ≤ -C 2^{ρl} - 1`.

Now suppose `α + θ = β + θ'` in `ℝ/ℤ` with `α, β ∈ (ℚ/ℤ)_{≤l}` and
`θ, θ' ∈ ℝ_{≤k}`.  Then `α - β` is the class of `θ' - θ`, with
`|θ' - θ| ≤ 2·2^k = 2^{k+1} < 2^{-C 2^{ρl}}`.

* If `α ≠ β`, the separation bound gives
  `2^{-C 2^{ρl}} ≤ ‖α - β‖ ≤ |θ' - θ|`, a contradiction.
* Hence `α = β` and the class of `θ' - θ` vanishes, i.e. `θ' - θ ∈ ℤ`; as
  `|θ' - θ| ≤ 2^{k+1} < 1`, necessarily `θ = θ'`.

Both uses of `2^{k+1}` combine the integer power appearing in `realArc` with the
real power appearing in the good-major-arcs condition; this is the (only) reason
for the helper `zpow_two_eq_rpow`.

## Main result

* `Work.Analysis.IonescuWainger.exists_goodMajorArcs_nonAliasing`
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Analysis.IonescuWainger

/-- The integer power `2^k` and the real power `2^{k : ℝ}` agree, so that the
`zpow`-bounds coming from `realArc` can be compared with the `rpow`-bounds coming
from the good-major-arcs condition. -/
private lemma zpow_two_eq_rpow (k : ℤ) : (2 : ℝ) ^ k = (2 : ℝ) ^ (k : ℝ) :=
  (Real.rpow_intCast 2 k).symm

/-- The class in `ℝ/ℤ` of a real number `u` has norm at most `|u|`; this is the
quotient-norm inequality `‖(u : ℝ ⧸ ℤ)‖ ≤ ‖u‖` transported to `Circle = ℝ/ℤ`. -/
private lemma norm_coe_circle_le_abs (u : ℝ) : ‖((u : ℝ) : Circle)‖ ≤ |u| := by
  have h := QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (1 : ℝ)) (m := u)
  simpa only [Circle, AddCircle, Real.norm_eq_abs] using h

/-- **Good major arcs do not alias the Ionescu–Wainger arithmetic frequencies**
(Theorem `thm:iw`, first assertion).  There is a constant `Cρ > 0` depending only on `ρ > 0` such
that whenever `k ≤ -Cρ · 2^{ρl}` the addition map `(θ, α) ↦ θ + α` is injective on
`ℝ_{≤k} × (ℚ/ℤ)_{≤l}`, i.e. the major arcs `α + ℝ_{≤k}`, `α ∈ (ℚ/ℤ)_{≤l}`, are pairwise
disjoint. -/
theorem exists_goodMajorArcs_nonAliasing {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∀ l k, GoodMajorArcs ρ Cρ l k → NonAliasing k (iwArithFreqs ρ l) := by
  obtain ⟨C, hCpos, hsep⟩ := iw_height_separated hρ
  refine ⟨C + 2, by linarith, ?_⟩
  intro l k hgood
  set S : ℝ := (2 : ℝ) ^ (ρ * (l : ℝ)) with hS
  -- `S ≥ 1`, so `C ≤ C * S` and hence `-(C * S) ≤ -C < 0`.
  have hS1 : (1 : ℝ) ≤ S := by
    rw [hS]
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hCS : C ≤ C * S := by
    have h : (1 : ℝ) * C ≤ S * C := mul_le_mul_of_nonneg_right hS1 hCpos.le
    linarith
  -- The good-major-arcs condition, in terms of `S`.
  have hk2 : (k : ℝ) + 2 * S ≤ -(C * S) := by
    have h : (k : ℝ) ≤ -(C + 2) * S := by
      have h' : (k : ℝ) ≤ -(C + 2) * (2 : ℝ) ^ (ρ * (l : ℝ)) := hgood
      rwa [← hS] at h'
    have h'' : -(C + 2) * S = -(C * S) - 2 * S := by ring
    linarith
  -- Key numerical consequence: `k + 1 < -C * S` (and hence `2^{k+1} < 2^{-C·2^{ρl}}`).
  have hk1 : (k : ℝ) + 1 < -(C * S) := by linarith
  have hneg : (k : ℝ) + 1 < 0 := by linarith
  have hpow : (2 : ℝ) ^ ((k : ℝ) + 1) < (2 : ℝ) ^ (-(C * S)) :=
    (Real.rpow_lt_rpow_left_iff (by norm_num)).mpr hk1
  have hpow1 : (2 : ℝ) ^ ((k : ℝ) + 1) < 1 := by
    have h := (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr hneg
    simpa using h
  intro α hα β hβ θ hθ θ' hθ' heq
  -- `α - β` is the class of `θ' - θ`.
  have hsub : α - β = ((θ' - θ : ℝ) : Circle) := by
    rw [AddCircle.coe_sub (1 : ℝ) θ' θ, sub_eq_sub_iff_add_eq_add, heq, add_comm]
  -- `θ, θ' ∈ ℝ_{≤k}` give `|θ' - θ| ≤ 2^{k+1}` (in real powers).
  have hθr : |θ| ≤ (2 : ℝ) ^ (k : ℝ) := by
    have h := hθ
    rw [realArc, Set.mem_Icc] at h
    have hb : |θ| ≤ (2 : ℝ) ^ k := abs_le.mpr h
    rwa [zpow_two_eq_rpow k] at hb
  have hθ'r : |θ'| ≤ (2 : ℝ) ^ (k : ℝ) := by
    have h := hθ'
    rw [realArc, Set.mem_Icc] at h
    have hb : |θ'| ≤ (2 : ℝ) ^ k := abs_le.mpr h
    rwa [zpow_two_eq_rpow k] at hb
  have hdd : |θ' - θ| ≤ 2 * (2 : ℝ) ^ (k : ℝ) := by
    calc |θ' - θ| ≤ |θ'| + |θ| := abs_sub θ' θ
      _ ≤ (2 : ℝ) ^ (k : ℝ) + (2 : ℝ) ^ (k : ℝ) := add_le_add hθ'r hθr
      _ = 2 * (2 : ℝ) ^ (k : ℝ) := by ring
  have hdd' : |θ' - θ| ≤ (2 : ℝ) ^ ((k : ℝ) + 1) := by
    calc |θ' - θ| ≤ 2 * (2 : ℝ) ^ (k : ℝ) := hdd
      _ = (2 : ℝ) ^ ((k : ℝ) + 1) := by
          rw [Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)]
          ring
  have hdd'' : |θ' - θ| < (2 : ℝ) ^ (-(C * S)) := lt_of_le_of_lt hdd' hpow
  have hdd1 : |θ' - θ| < 1 := lt_of_le_of_lt hdd' hpow1
  rcases eq_or_ne α β with hAB | hAB
  · -- `α = β`: then `θ' - θ` is an integer of absolute value `< 1`, so `θ = θ'`.
    refine ⟨hAB, ?_⟩
    have h0 : ((θ' - θ : ℝ) : Circle) = 0 := by rw [← hsub, hAB, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h0
    have hnR : θ' - θ = (n : ℝ) := by rw [← hn, zsmul_one]
    have hnabs : |(n : ℝ)| < 1 := by rw [← hnR]; exact hdd1
    have hn0 : n = 0 := by
      obtain ⟨h1, h2⟩ := abs_lt.mp hnabs
      have h1' : (-1 : ℤ) < n := by exact_mod_cast h1
      have h2' : n < (1 : ℤ) := by exact_mod_cast h2
      omega
    have hθθ' : θ = θ' := by
      have hz : θ' - θ = 0 := by rw [hnR, hn0]; norm_num
      linarith
    exact hθθ'
  · -- `α ≠ β`: separation of the arithmetic frequencies contradicts `|θ' - θ| < 2^{-C·2^{ρl}}`.
    exfalso
    have hsep' : (2 : ℝ) ^ (-(C * S)) ≤ ‖α - β‖ := by
      have h := hsep l hα hβ hAB
      rwa [← hS] at h
    have hnorm : ‖α - β‖ ≤ |θ' - θ| := by
      rw [hsub]
      exact norm_coe_circle_le_abs (θ' - θ)
    linarith [hsep', hnorm, hdd'']

end Work.Analysis.IonescuWainger
