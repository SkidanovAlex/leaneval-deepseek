import Mathlib
import Submission.Work.CNum.SerUpDefs
import Submission.Work.CNum.LgInfra

namespace Work.CNum

open Work.ANum

/-!
# `Work.CNum.SerStepScale` — the scale step of the `serUp` invariant

The invariant `SerInv x y e σ k px py pe sg` carried by the recursion `serAuxB` keeps
`R^k ≤ m2r sg ≤ 2`, where `R = srad x y e = ‖c‖ + ρ` is the radius of the disc.  One step of the
recursion replaces `sg` by `snsg σ sg = mulU sg σ = ⌈sg·σ/SC⌉`; this file proves that the two
inequalities survive that step:

* `m2r sg · m2r σ ≤ m2r (mulU sg σ)` (upward rounding of the product), so the first inequality
  follows from `srad^k ≤ m2r sg` and `srad ≤ m2r σ`;
* the second inequality is the integer statement `mulU sg σ ≤ 2·SC`, which reduces to
  `sg·σ ≤ 2·SC²` and holds because `sg ≤ 2·SC`, `σ ≤ SC`, `sg, σ ≥ 0`.

The two mantissa facts `m2r a ≤ m2r b ↔ a ≤ b` and `a ≤ b/c ↔ a·c ≤ b` (for `c > 0`) are the
integer-level tools used throughout; the latter is stated here for `Int.ediv`, the function that
`mulU` is built from.
-/

/-! ## Order reflection for the mantissa embedding -/

lemma m2r_le_iff {a b : ℤ} : m2r a ≤ m2r b ↔ a ≤ b := by
  refine ⟨?_, m2r_le⟩
  intro h
  by_contra hc
  rw [not_le] at hc
  exact absurd h (not_le.mpr (m2r_lt hc))

lemma m2r_lt_iff {a b : ℤ} : m2r a < m2r b ↔ a < b := by
  refine ⟨?_, m2r_lt⟩
  intro h
  by_contra hc
  rw [not_lt] at hc
  exact absurd h (not_lt.mpr (m2r_le hc))

/-- `Int.ediv` form of `Int.le_ediv_iff_mul_le`, matching the function used by `mulU`. -/
lemma le_ediv_iff_mul_le' (a b : ℤ) {c : ℤ} (hc : 0 < c) :
    a ≤ Int.ediv b c ↔ a * c ≤ b := by
  rw [show Int.ediv b c = b / c from rfl]
  exact Int.le_ediv_iff_mul_le hc

/-- The upward-rounded product `mulU a b = ⌈a·b/SC⌉` is `≤ n` exactly when `a·b ≤ n·SC`. -/
lemma mulU_le_iff (a b n : ℤ) : mulU a b ≤ n ↔ a * b ≤ n * SC := by
  have h₁ : (-n) ≤ Int.ediv (-(a * b)) SC ↔ a * b ≤ n * SC := by
    rw [le_ediv_iff_mul_le' (-n) (-(a * b)) SC_pos]
    constructor <;> intro h <;> linarith
  have h₂ : mulU a b = -Int.ediv (-(a * b)) SC := rfl
  rw [h₂]
  constructor
  · intro h
    exact h₁.mp (by linarith)
  · intro h
    have := h₁.mpr h
    linarith

/-- `srad` is nonnegative whenever the ball radius is. -/
lemma srad_nonneg {x y e : ℤ} (he : 0 ≤ e) : 0 ≤ srad x y e := by
  rw [srad]
  exact add_nonneg (norm_nonneg _) (m2r_nonneg_NrmSpec he)

/-- One step of the `σ`-scale: multiplying the running bound `sg ≥ R^k` by `σ ≥ R` keeps
`R^(k+1)` below the new bound and keeps the new bound below `2`. -/
theorem SerStepScale {x y e σ : ℤ} {k : ℕ} {sg : ℤ} (he : 0 ≤ e) (hσlt : Work.ANum.m2r σ < 1) (hRσ : Work.CNum.srad x y e ≤ Work.ANum.m2r σ) (hk : Work.CNum.srad x y e ^ k ≤ Work.ANum.m2r sg) (hsg2 : Work.ANum.m2r sg ≤ 2) : Work.CNum.srad x y e ^ (k + 1) ≤ Work.ANum.m2r (Work.CNum.snsg σ sg) ∧ Work.ANum.m2r (Work.CNum.snsg σ sg) ≤ 2 := by
  have hsrad0 : 0 ≤ srad x y e := srad_nonneg he
  have hσ0r : 0 ≤ m2r σ := le_trans hsrad0 hRσ
  have hσ0 : 0 ≤ σ := (m2r_nonneg_iff σ).mp hσ0r
  have hsg0r : 0 ≤ m2r sg := le_trans (pow_nonneg hsrad0 k) hk
  have hsg0 : 0 ≤ sg := (m2r_nonneg_iff sg).mp hsg0r
  -- integer-level consequences of the two mantissa bounds
  have hσltZ : σ < SC := by
    have h := hσlt
    rw [← m2r_SC] at h
    exact m2r_lt_iff.mp h
  have hsg2Z : sg ≤ 2 * SC := by
    have h := hsg2
    rw [← m2r_two] at h
    exact m2r_le_iff.mp h
  have hσle : σ ≤ SC := hσltZ.le
  have hprod : sg * σ ≤ (2 * SC) * SC :=
    mul_le_mul hsg2Z hσle hσ0 (by linarith [SC_pos])
  constructor
  · -- `R^(k+1) ≤ m2r (mulU sg σ)`
    have hstep : srad x y e ^ k * srad x y e ≤ m2r sg * m2r σ :=
      calc srad x y e ^ k * srad x y e ≤ m2r sg * srad x y e :=
            mul_le_mul_of_nonneg_right hk hsrad0
        _ ≤ m2r sg * m2r σ := mul_le_mul_of_nonneg_left hRσ hsg0r
    have hle : m2r sg * m2r σ ≤ m2r (snsg σ sg) := by
      have h := le_mulU sg σ
      simpa only [snsg] using h
    rw [pow_succ]
    exact le_trans hstep hle
  · -- `m2r (mulU sg σ) ≤ 2`
    have hceil : mulU sg σ ≤ 2 * SC := (mulU_le_iff sg σ (2 * SC)).mpr hprod
    have h := m2r_le hceil
    rw [m2r_two] at h
    simpa only [snsg] using h

end Work.CNum
