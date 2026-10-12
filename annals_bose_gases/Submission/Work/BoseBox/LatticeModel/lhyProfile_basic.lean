import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBox.LatticeModel.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Basic properties of the Bogoliubov bracket `lhyProfile`

`lhyProfile c r` is the rationalised Bogoliubov bracket
`c²/((r²+c) + r√(r²+2c)) − c²/(2r²)` (see `Defs.lhyProfile`).

For `c > 0` and `r ≥ 0` we prove:

* the rationalised form equals the original form
  `(r²+c) − √((r²+c)²−c²) − c²/(2r²)` (using `√((r²+c)²−c²) = r√(r²+2c)`);
* the coarse bound `|lhyProfile c r| ≤ c + c²/(2r²)`;
* the sharp decay bound `|lhyProfile c r| ≤ c³/(2r⁴)` for `r > 0`, obtained from the
  exact identity `(s+r)(2r² − D) = −c(3r+s)` with `s = √(r²+2c)`, `D = r²+c+rs`.
-/

namespace Work.BoseBox.LatticeModel

theorem lhyProfile_basic {c : ℝ} (hc : 0 < c) :
    (∀ r : ℝ, 0 ≤ r → lhyProfile c r
        = (r ^ 2 + c) - Real.sqrt ((r ^ 2 + c) ^ 2 - c ^ 2) - c ^ 2 / (2 * r ^ 2)) ∧
    (∀ r : ℝ, 0 ≤ r → |lhyProfile c r| ≤ c + c ^ 2 / (2 * r ^ 2)) ∧
    (∀ r : ℝ, 0 < r → |lhyProfile c r| ≤ c ^ 3 / (2 * r ^ 4)) := by
  -- `√(r²+2c)` is nonnegative with square `r²+2c`, and `(r²+c)² - c² = r²(r²+2c)`.
  have hsq_ne : ∀ r : ℝ, 0 ≤ r →
      Real.sqrt ((r ^ 2 + c) ^ 2 - c ^ 2) = r * Real.sqrt (r ^ 2 + 2 * c) := by
    intro r hr
    have h2 : 0 ≤ r ^ 2 + 2 * c := by nlinarith [sq_nonneg r]
    have h1 : (r ^ 2 + c) ^ 2 - c ^ 2 = r ^ 2 * (r ^ 2 + 2 * c) := by ring
    rw [h1, Real.sqrt_mul (sq_nonneg r) (r ^ 2 + 2 * c), Real.sqrt_sq hr]
  -- the denominator `D = (r²+c) + r√(r²+2c)` is positive and at least `c`.
  have hden_pos : ∀ r : ℝ, 0 ≤ r → 0 < (r ^ 2 + c) + r * Real.sqrt (r ^ 2 + 2 * c) := by
    intro r hr
    have hss : 0 ≤ Real.sqrt (r ^ 2 + 2 * c) := Real.sqrt_nonneg _
    have hrs : 0 ≤ r * Real.sqrt (r ^ 2 + 2 * c) := mul_nonneg hr hss
    have hc' : 0 < r ^ 2 + c := by nlinarith [sq_nonneg r]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: the two forms of the bracket agree.
    intro r hr
    have h2 : 0 ≤ r ^ 2 + 2 * c := by nlinarith [sq_nonneg r]
    have hs2 : (Real.sqrt (r ^ 2 + 2 * c)) ^ 2 = r ^ 2 + 2 * c := Real.sq_sqrt h2
    have hDne : ((r ^ 2 + c) + r * Real.sqrt (r ^ 2 + 2 * c)) ≠ 0 :=
      ne_of_gt (hden_pos r hr)
    have hmain : c ^ 2 / (r ^ 2 + c + r * Real.sqrt (r ^ 2 + 2 * c))
        = (r ^ 2 + c) - r * Real.sqrt (r ^ 2 + 2 * c) := by
      rw [div_eq_iff hDne]
      nlinarith [hs2]
    simp only [lhyProfile, hsq_ne r hr, hmain]
  · -- Part 2: the coarse bound.
    intro r hr
    have hss : 0 ≤ Real.sqrt (r ^ 2 + 2 * c) := Real.sqrt_nonneg _
    have hrs : 0 ≤ r * Real.sqrt (r ^ 2 + 2 * c) := mul_nonneg hr hss
    have hDc : c ≤ (r ^ 2 + c) + r * Real.sqrt (r ^ 2 + 2 * c) := by
      nlinarith [sq_nonneg r, hrs]
    have hA : c ^ 2 / ((r ^ 2 + c) + r * Real.sqrt (r ^ 2 + 2 * c)) ≤ c := by
      rw [div_le_iff₀ (hden_pos r hr)]
      nlinarith [hDc, hc]
    have hA0 : 0 ≤ c ^ 2 / ((r ^ 2 + c) + r * Real.sqrt (r ^ 2 + 2 * c)) :=
      div_nonneg (sq_nonneg c) (hden_pos r hr).le
    have hB0 : 0 ≤ c ^ 2 / (2 * r ^ 2) := div_nonneg (sq_nonneg c) (by positivity)
    simp only [lhyProfile]
    rw [abs_le]
    exact ⟨by nlinarith [hA, hA0, hB0], by nlinarith [hA, hA0, hB0]⟩
  · -- Part 3: the sharp bound, via the identity `(s+r)(2r²-D) = -c(3r+s)`.
    intro r hr
    simp only [lhyProfile]
    set s := Real.sqrt (r ^ 2 + 2 * c) with hsdef
    have h2 : 0 ≤ r ^ 2 + 2 * c := by nlinarith [sq_nonneg r]
    have hs2 : s ^ 2 = r ^ 2 + 2 * c := by rw [hsdef]; exact Real.sq_sqrt h2
    have hsnn : 0 ≤ s := by rw [hsdef]; exact Real.sqrt_nonneg _
    have hsge : r ≤ s := by
      have h : Real.sqrt (r ^ 2) ≤ Real.sqrt (r ^ 2 + 2 * c) := Real.sqrt_le_sqrt (by linarith)
      rwa [Real.sqrt_sq hr.le, ← hsdef] at h
    have hrs : 0 ≤ r * s := mul_nonneg hr.le hsnn
    have hDpos : 0 < r ^ 2 + c + r * s := by nlinarith [sq_nonneg r, hrs]
    have hspos : 0 < s + r := by linarith
    have hid : (s + r) * (2 * r ^ 2 - (r ^ 2 + c + r * s)) = -c * (3 * r + s) := by
      nlinarith [hs2]
    have hD2 : (r ^ 2 + c + r * s) - 2 * r ^ 2 = c * (3 * r + s) / (s + r) := by
      rw [eq_div_iff hspos.ne']
      nlinarith [hid]
    have hDgt2 : 2 * r ^ 2 ≤ r ^ 2 + c + r * s := by
      have hnn : 0 ≤ c * (3 * r + s) / (s + r) :=
        div_nonneg (mul_nonneg hc.le (by linarith)) hspos.le
      linarith [hD2]
    -- `r²(3r+s) ≤ D(s+r)`, the core inequality, from `D(s+r) - r²(3r+s) = r²(s-r)+c(s+3r)`.
    have hkey2 : r ^ 2 * (3 * r + s) ≤ (r ^ 2 + c + r * s) * (s + r) := by
      have hDdiff : (r ^ 2 + c + r * s) * (s + r) - r ^ 2 * (3 * r + s)
          = r ^ 2 * (s - r) + c * (s + 3 * r) := by nlinarith [hs2]
      have h1 : 0 ≤ r ^ 2 * (s - r) := mul_nonneg (sq_nonneg r) (by linarith)
      have h2' : 0 ≤ c * (s + 3 * r) := mul_nonneg hc.le (by linarith)
      linarith [hDdiff, h1, h2']
    have hkey2b : r ^ 2 * ((r ^ 2 + c + r * s) - 2 * r ^ 2) ≤ c * (r ^ 2 + c + r * s) := by
      rw [hD2, ← mul_div_assoc, div_le_iff₀ hspos]
      have hm := mul_le_mul_of_nonneg_left hkey2 hc.le
      nlinarith [hm]
    have hX : c ^ 2 / (r ^ 2 + c + r * s) - c ^ 2 / (2 * r ^ 2)
        = c ^ 2 * (2 * r ^ 2 - (r ^ 2 + c + r * s)) / (2 * r ^ 2 * (r ^ 2 + c + r * s)) := by
      field_simp
    rw [hX, abs_le]
    have hden : 0 < 2 * r ^ 2 * (r ^ 2 + c + r * s) := by positivity
    have hB : c ^ 2 * ((r ^ 2 + c + r * s) - 2 * r ^ 2) / (2 * r ^ 2 * (r ^ 2 + c + r * s))
        ≤ c ^ 3 / (2 * r ^ 4) := by
      rw [div_le_iff₀ hden, div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < 2 * r ^ 4)]
      have hm := mul_le_mul_of_nonneg_left hkey2b (by positivity : (0:ℝ) ≤ c ^ 2 * r ^ 2)
      nlinarith [hm]
    constructor
    · have hneg : c ^ 2 * (2 * r ^ 2 - (r ^ 2 + c + r * s)) / (2 * r ^ 2 * (r ^ 2 + c + r * s))
          = -(c ^ 2 * ((r ^ 2 + c + r * s) - 2 * r ^ 2)
              / (2 * r ^ 2 * (r ^ 2 + c + r * s))) := by
        ring
      rw [hneg]
      linarith [hB]
    · have hnum : c ^ 2 * (2 * r ^ 2 - (r ^ 2 + c + r * s)) ≤ 0 := by
        have h : 2 * r ^ 2 - (r ^ 2 + c + r * s) ≤ 0 := by linarith [hDgt2]
        nlinarith [sq_nonneg c]
      have h := div_nonpos_of_nonpos_of_nonneg hnum hden.le
      linarith [h, show (0:ℝ) ≤ c ^ 3 / (2 * r ^ 4) by positivity]

end Work.BoseBox.LatticeModel
