import Mathlib
import Submission.Work.Maximal.mstWide_defs
import Submission.Work.BourgainPlan.Maximal.mstQ_le_two_pow
import Submission.Work.Maximal.mstKappa_chi_le

/-!
# The wide scale `c_s = (Q_s)^{3d}` is dominated by the MST threshold tower

The wide-scale half of the level-`s` maximal estimate (MST arXiv:1512.07518, §4.4) uses the *wide*
bump `ϱ_s(ξ) = η(c_s · iwRep ξ)` with `c_s = (Q_s)^{3d}` (see `mstWide_defs`).  The two scales that
`c_s` has to be compared with are

* the *narrow* level-`s` ball of radius `2^{-s(d-χ)}`, whose own scale is the number `2^{s(d-χ)}`, and
* the MST threshold `2^{κ_s}`, `κ_s = mstKappa P s = 20 d (⌊(s+1)^{1/10}⌋ + 1)`, which separates the
  small from the large scales in the level estimate.

Both are much smaller than the doubly exponential tower `2^{2^{κ_s}/(2d)}`: this file proves

`2^{s(d-χ)} + c_s ≤ 2^{2^{κ_s}/(2d)}` for all `s ≥ s₀(χ)`.

The proof splits the right-hand side at the half exponent `Y = 2^{κ_s}/(4d)` and shows each summand
is at most `2^Y`; `2^Y + 2^Y = 2·2^Y ≤ 2^Y·2^Y = 2^{2Y}` finishes, using `1 ≤ Y`.

The estimate for `c_s` is the elementary `12 d² 2^{5m} ≤ 2^{20dm}` (`m = ⌊(s+1)^{1/10}⌋+1`) combined
with `Q_s = ⌈e^{(s+1)^{1/10}}⌉! ≤ 2^{2^{5m}}` (`mstQ_le_two_pow`); the estimate for `2^{s(d-χ)}` uses
`s < m^{10} ≤ 2^{10m}` together with a threshold `2^{10m} ≥ 4d·max 0 (d-χ)`, which exists because
`m → ∞`.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.Maximal

noncomputable section

/-! ## The elementary power estimates -/

/-- `12 d² ≤ 2^{4+2d}` (from `2^4 = 16 ≥ 12` and `d² ≤ (2^d)² = 2^{2d}`). -/
private lemma twelve_mul_sq_le (d : ℕ) : 12 * d ^ 2 ≤ 2 ^ (4 + 2 * d) := by
  have h1 : 12 ≤ 2 ^ 4 := by norm_num
  have h2 : d ^ 2 ≤ 2 ^ (2 * d) := by
    calc d ^ 2 ≤ (2 ^ d) ^ 2 := Nat.pow_le_pow_left (Nat.le_of_lt Nat.lt_two_pow_self) 2
      _ = 2 ^ (d * 2) := (pow_mul 2 d 2).symm
      _ = 2 ^ (2 * d) := by rw [mul_comm]
  calc 12 * d ^ 2 ≤ 2 ^ 4 * 2 ^ (2 * d) := Nat.mul_le_mul h1 h2
    _ = 2 ^ (4 + 2 * d) := (pow_add 2 4 (2 * d)).symm

/-- `m^{10} ≤ 2^{10m}`. -/
private lemma pow_ten_le_two_pow_ten_mul (m : ℕ) : m ^ 10 ≤ 2 ^ (10 * m) := by
  calc m ^ 10 ≤ (2 ^ m) ^ 10 := Nat.pow_le_pow_left (Nat.le_of_lt Nat.lt_two_pow_self) 10
    _ = 2 ^ (m * 10) := (pow_mul 2 m 10).symm
    _ = 2 ^ (10 * m) := by rw [mul_comm]

/-- `4 d ≤ 2^{2d}` for `d ≥ 2` (from `d ≤ 2^d`). -/
private lemma four_mul_le_two_pow_two_mul (d : ℕ) (hd : 2 ≤ d) : 4 * d ≤ 2 ^ (2 * d) := by
  have h1 : d ≤ 2 ^ d := Nat.le_of_lt Nat.lt_two_pow_self
  calc 4 * d ≤ 4 * 2 ^ d := Nat.mul_le_mul_left 4 h1
    _ = 2 ^ 2 * 2 ^ d := by norm_num
    _ = 2 ^ (2 + d) := (pow_add 2 2 d).symm
    _ ≤ 2 ^ (2 * d) := by
        have h2d : 2 + d ≤ 2 * d := by omega
        exact Nat.pow_le_pow_right (by norm_num) h2d

/-- `12 d² 2^{5m} ≤ 2^{20dm}` for `d ≥ 2`, `m ≥ 1`. -/
private lemma key_pow_ineq (d m : ℕ) (hd : 2 ≤ d) (hm : 1 ≤ m) :
    12 * d ^ 2 * 2 ^ (5 * m) ≤ 2 ^ (20 * d * m) := by
  calc 12 * d ^ 2 * 2 ^ (5 * m)
      ≤ 2 ^ (4 + 2 * d) * 2 ^ (5 * m) := Nat.mul_le_mul_right _ (twelve_mul_sq_le d)
    _ = 2 ^ (4 + 2 * d + 5 * m) := (pow_add 2 (4 + 2 * d) (5 * m)).symm
    _ ≤ 2 ^ (20 * d * m) := Nat.pow_le_pow_right (by norm_num) (by nlinarith [hd, hm])

/-- **The wide-scale bound, elementary form.**  If `Q ≤ 2^{2^{5m}}`, `d ≥ 2` and `m ≥ 1` then
`Q^{3d} ≤ 2^{2^{20dm}/(4d)}`. -/
private lemma pow_le_two_pow_quarter (Q d m : ℕ) (hd : 2 ≤ d) (hm : 1 ≤ m)
    (hQ : Q ≤ 2 ^ (2 ^ (5 * m))) :
    (Q : ℝ) ^ (3 * d)
      ≤ (2 : ℝ) ^ (((2 ^ (20 * d * m) : ℕ) : ℝ) / (4 * (d : ℝ))) := by
  have hcore : 12 * d ^ 2 * 2 ^ (5 * m) ≤ 2 ^ (20 * d * m) := key_pow_ineq d m hd hm
  have hstep : Q ^ (3 * d) ≤ 2 ^ (2 ^ (5 * m) * 3 * d) := by
    calc Q ^ (3 * d) ≤ (2 ^ (2 ^ (5 * m))) ^ (3 * d) := Nat.pow_le_pow_left hQ _
      _ = 2 ^ (2 ^ (5 * m) * (3 * d)) := (pow_mul 2 (2 ^ (5 * m)) (3 * d)).symm
      _ = 2 ^ (2 ^ (5 * m) * 3 * d) := by rw [mul_assoc]
  have hcast : (2 ^ (5 * m) * 3 * d) * (4 * d) ≤ 2 ^ (20 * d * m) := by
    have heq : (2 ^ (5 * m) * 3 * d) * (4 * d) = 12 * d ^ 2 * 2 ^ (5 * m) := by ring
    rw [heq]; exact hcore
  have hreal : ((2 ^ (5 * m) * 3 * d : ℕ) : ℝ) * (4 * (d : ℝ)) ≤ ((2 ^ (20 * d * m) : ℕ) : ℝ) := by
    have h := Nat.cast_le (α := ℝ).mpr hcast
    push_cast at h ⊢
    exact h
  have hd0 : (0 : ℝ) < 4 * (d : ℝ) := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    linarith
  have hdiv : ((2 ^ (5 * m) * 3 * d : ℕ) : ℝ)
      ≤ ((2 ^ (20 * d * m) : ℕ) : ℝ) / (4 * (d : ℝ)) := (le_div_iff₀ hd0).mpr hreal
  have hfirst : (Q : ℝ) ^ (3 * d) ≤ (2 : ℝ) ^ (((2 ^ (5 * m) * 3 * d : ℕ)) : ℝ) := by
    have h := Nat.cast_le (α := ℝ).mpr hstep
    push_cast at h
    simp only [← Real.rpow_natCast] at h ⊢
    exact h
  exact hfirst.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hdiv)

/-- **The wide scale against the quarter tower**: `c_s ≤ 2^{2^{κ_s}/(4d)}`, where `c_s = mstWideC P s`
and `κ_s = mstKappa P s`. -/
private theorem mstWideC_le_quarter (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (s : ℕ) :
    mstWideC P s
      ≤ (2 : ℝ) ^ (((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
          / (4 * (P.natDegree : ℝ))) := by
  have hm : 1 ≤ ⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ + 1 := by omega
  have hQ : Work.BourgainPlan.Maximal.mstQ' s
      ≤ 2 ^ (2 ^ (5 * (⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ + 1))) := by
    have h := Work.BourgainPlan.Maximal.mstQ_le_two_pow s
    exact_mod_cast h
  have hmain := pow_le_two_pow_quarter (Work.BourgainPlan.Maximal.mstQ' s) P.natDegree
    (⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ + 1) hd hm hQ
  rw [mstWideC]
  exact hmain

/-- `1 ≤ 2^{κ_s}/(4d)`: the exponent `2^{κ_s}/(4d)` of the tower is at least `1`. -/
private theorem one_le_quarter (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (s : ℕ) :
    1 ≤ (((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
          / (4 * (P.natDegree : ℝ))) := by
  have hd1 : 1 ≤ P.natDegree := by omega
  have hm : 1 ≤ ⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ + 1 := by omega
  have h4 : 4 * P.natDegree ≤ 2 ^ (2 * P.natDegree) :=
    four_mul_le_two_pow_two_mul P.natDegree hd
  have h2 : 2 * P.natDegree ≤ 20 * P.natDegree * (⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ + 1) := by
    nlinarith [hd1, hm]
  have hpow : 4 * P.natDegree ≤ 2 ^ Work.BourgainPlan.Maximal.mstKappa P s := h4.trans (by
    rw [Work.BourgainPlan.Maximal.mstKappa]
    exact Nat.pow_le_pow_right (by norm_num) h2)
  have hd0 : (0 : ℝ) < 4 * (P.natDegree : ℝ) := by
    have : (0 : ℝ) < (P.natDegree : ℝ) := by exact_mod_cast (by omega : 0 < P.natDegree)
    linarith
  rw [le_div_iff₀ hd0, one_mul]
  exact_mod_cast hpow

theorem mstWideC_le_two_pow_kappa (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (χ : ℝ) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
      (2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)) + Work.Maximal.mstWideC P s
        ≤ (2 : ℝ) ^ (((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
            / (2 * (P.natDegree : ℝ))) := by
  obtain ⟨s₀, hs₀⟩ := Work.Maximal.mstKappa_chi_le P hd χ
  refine ⟨s₀, fun s hs => ?_⟩
  have hA := hs₀ s hs
  have hW := mstWideC_le_quarter P hd s
  have hY1 := one_le_quarter P hd s
  have hd0 : (P.natDegree : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (P.natDegree : ℝ) := by exact_mod_cast (by omega : 0 < P.natDegree)
    exact ne_of_gt this
  have hsum : (2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)) + Work.Maximal.mstWideC P s
      ≤ (2 : ℝ) ^ (((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
            / (4 * (P.natDegree : ℝ)))
        + (2 : ℝ) ^ (((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
            / (4 * (P.natDegree : ℝ))) := add_le_add hA hW
  refine hsum.trans ?_
  have htwo : (2 : ℝ)
      ≤ (2 : ℝ) ^ (((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
            / (4 * (P.natDegree : ℝ))) := by
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ (2 : ℝ) ^ (((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
            / (4 * (P.natDegree : ℝ))) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hY1
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
            / (4 * (P.natDegree : ℝ))) := Real.rpow_pos_of_pos (by norm_num) _
  have hQ : (((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
            / (4 * (P.natDegree : ℝ)))
          + (((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
            / (4 * (P.natDegree : ℝ)))
        = ((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
            / (2 * (P.natDegree : ℝ)) := by
    field_simp
    ring
  calc (2 : ℝ) ^ (((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
            / (4 * (P.natDegree : ℝ)))
        + (2 : ℝ) ^ (((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
            / (4 * (P.natDegree : ℝ)))
      = 2 * (2 : ℝ) ^ (((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
            / (4 * (P.natDegree : ℝ))) := by ring
    _ ≤ (2 : ℝ) ^ (((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
            / (4 * (P.natDegree : ℝ)))
        * (2 : ℝ) ^ (((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
            / (4 * (P.natDegree : ℝ))) := mul_le_mul_of_nonneg_right htwo (le_of_lt hpos)
    _ = (2 : ℝ) ^ ((((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
            / (4 * (P.natDegree : ℝ)))
          + (((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
            / (4 * (P.natDegree : ℝ)))) := (Real.rpow_add (by norm_num) _ _).symm
    _ = (2 : ℝ) ^ (((2 ^ Work.BourgainPlan.Maximal.mstKappa P s : ℕ) : ℝ)
            / (2 * (P.natDegree : ℝ))) := by rw [hQ]

end

end Work.Maximal
