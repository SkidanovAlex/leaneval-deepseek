import Mathlib
import Submission.Work.OROneRel.gaugeExtWindowDefs

namespace Work.OROneRel

/-- Integer division with a nonnegative remainder strictly below the (positive) divisor:
if `0 ≤ r < d` then `r + m * d` has quotient `m` and remainder `r` on division by `d`. -/
theorem int_ediv_emod_add_mul (d r m : ℤ) (hd : 0 < d) (hr0 : 0 ≤ r) (hrd : r < d) :
    (r + m * d) / d = m ∧ (r + m * d) % d = r :=
  (Int.ediv_emod_unique (a := r + m * d) (b := d) (q := m) (r := r) hd).mpr
    ⟨by ring, hr0, hrd⟩

/-- The base level of the downward `x₀`-chain has the claimed arithmetic properties: it is
congruent to `j` modulo `d`, lies in the half-open window `[lo, lo + d - 1]`, is fixed by
repeatedly subtracting multiples of `d` (and the exponent of those steps is recovered as the
number of subtracted multiples), and the exponent is at least `1` below the window. -/
theorem gxDnBase_arith {d lo j : ℤ} (hd : 0 < d) :
    (Work.OROneRel.gxDnBase d lo j - Work.OROneRel.gxDnExp d lo j * d = j) ∧
    (lo ≤ Work.OROneRel.gxDnBase d lo j ∧ Work.OROneRel.gxDnBase d lo j ≤ lo + d - 1) ∧
    (∀ m : ℤ, 0 ≤ m → Work.OROneRel.gxDnBase d lo (Work.OROneRel.gxDnBase d lo j - m * d)
      = Work.OROneRel.gxDnBase d lo j) ∧
    (∀ m : ℤ, 0 ≤ m → Work.OROneRel.gxDnExp d lo (Work.OROneRel.gxDnBase d lo j - m * d) = m) ∧
    (j < lo → 1 ≤ Work.OROneRel.gxDnExp d lo j) := by
  have hd0 : d ≠ 0 := ne_of_gt hd
  -- Closed form: the base level is `lo + d - 1 - r` where `r` is the remainder of `lo - j - 1` by `d`.
  have key : ∀ k : ℤ, gxDnBase d lo k = lo + d - 1 - ((lo - k - 1) % d) := by
    intro k
    unfold gxDnBase gxDnExp
    rw [Int.emod_def]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold gxDnBase; ring
  · have h0 : 0 ≤ (lo - j - 1) % d := Int.emod_nonneg _ hd0
    have h1 : (lo - j - 1) % d < d := Int.emod_lt_of_pos _ hd
    rw [key j]; constructor <;> omega
  · intro m hm
    set r : ℤ := (lo - j - 1) % d with hr
    set b : ℤ := gxDnBase d lo j with hb_def
    have hb : b = lo + d - 1 - r := by rw [hb_def, key j, hr]
    have hr0 : 0 ≤ r := by rw [hr]; exact Int.emod_nonneg _ hd0
    have hrd : r < d := by rw [hr]; exact Int.emod_lt_of_pos _ hd
    have hnum : lo - (b - m * d) - 1 = r + (m - 1) * d := by rw [hb]; ring
    have h1 := (int_ediv_emod_add_mul d r (m - 1) hd hr0 hrd).2
    rw [key (b - m * d), hnum, h1, ← hb]
  · intro m hm
    set r : ℤ := (lo - j - 1) % d with hr
    set b : ℤ := gxDnBase d lo j with hb_def
    have hb : b = lo + d - 1 - r := by rw [hb_def, key j, hr]
    have hr0 : 0 ≤ r := by rw [hr]; exact Int.emod_nonneg _ hd0
    have hrd : r < d := by rw [hr]; exact Int.emod_lt_of_pos _ hd
    have hnum : lo - (b - m * d) - 1 = r + (m - 1) * d := by rw [hb]; ring
    have h1 := (int_ediv_emod_add_mul d r (m - 1) hd hr0 hrd).1
    unfold gxDnExp
    rw [hnum, h1]
    ring
  · intro h
    unfold gxDnExp
    have hle : 0 ≤ lo - j - 1 := by omega
    have hdnn : 0 ≤ d := le_of_lt hd
    have := Int.ediv_nonneg hle hdnn
    omega

end Work.OROneRel
