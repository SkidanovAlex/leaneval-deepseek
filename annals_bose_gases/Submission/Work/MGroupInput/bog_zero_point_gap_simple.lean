import Mathlib.Algebra.Order.Star.Real
import Submission.Work.MGroupInput.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.MGroupInput

/-- **Zero-point gap in the small-`|B|` regime.**  For `0 < A`, `0 < ε ≤ 1`
and `|B| ≤ (ε/2) A`, the Bogoliubov zero-point constant `A − √(A²−B²)`
(`Submission.BoseGases.bogS`) is at most `½ (1 + ε/2) B²/A`.

The constants are chosen so that the coarse split
`A − s ≤ B²/(2A) + B⁴/A³` (`bog_zero_point_gap_split`) plus the regime
bound `B²/A² ≤ ε²/4 ≤ ε/4` together give the claimed `(1 + ε/2)/2`
factor: the residual `B⁴/A³ = (B²/A²)(B²/A)` is absorbed by
`ε·B²/(4A)`. -/
theorem bog_zero_point_gap_simple {A B ε : ℝ} (hA : 0 < A) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hB : |B| ≤ ε / 2 * A) :
    A - Submission.BoseGases.bogS A B ≤ (1 / 2) * (1 + ε / 2) * B ^ 2 / A := by
  -- the regime forces `|B| ≤ A`, so the split lemma applies
  have hBleA : |B| ≤ A := by
    have h1 : ε / 2 * A ≤ A := by nlinarith [hA, hε0, hε1]
    linarith
  -- `B² ≤ ε A²/4`
  have hBsq : B ^ 2 ≤ ε * A ^ 2 / 4 := by
    have h2 : B ^ 2 ≤ (ε / 2 * A) ^ 2 := by
      have hb := abs_le.mp hB
      exact sq_le_sq' hb.1 hb.2
    have h3 : (ε / 2 * A) ^ 2 = ε ^ 2 * A ^ 2 / 4 := by ring
    have h4 : ε ^ 2 ≤ ε := by nlinarith [hε0, hε1]
    have h5 : ε ^ 2 * A ^ 2 / 4 ≤ ε * A ^ 2 / 4 := by
      have hh : ε ^ 2 * (A ^ 2 / 4) ≤ ε * (A ^ 2 / 4) :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
      linarith
    linarith
  -- hence `B²/A² ≤ ε/4`
  have hu : B ^ 2 / A ^ 2 ≤ ε / 4 := by
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < A ^ 2) (by norm_num : (0:ℝ) < 4)]
    linarith [hBsq]
  -- and multiplying by the nonnegative `B²/A` absorbs the `B⁴/A³` tail
  have hkey : B ^ 4 / A ^ 3 ≤ ε * B ^ 2 / (4 * A) := by
    have hmult := mul_le_mul_of_nonneg_right hu (by positivity : (0:ℝ) ≤ B ^ 2 / A)
    have h1 : B ^ 2 / A ^ 2 * (B ^ 2 / A) = B ^ 4 / A ^ 3 := by field_simp
    have h2 : ε / 4 * (B ^ 2 / A) = ε * B ^ 2 / (4 * A) := by ring
    rw [h1, h2] at hmult
    exact hmult
  have hsplit := Submission.BoseGases.bog_zero_point_gap_split hA hBleA
  have hfin : B ^ 2 / (2 * A) + B ^ 4 / A ^ 3 ≤ (1 / 2) * (1 + ε / 2) * B ^ 2 / A := by
    have heq : (1 / 2) * (1 + ε / 2) * B ^ 2 / A
        = B ^ 2 / (2 * A) + ε * B ^ 2 / (4 * A) := by
      field_simp; ring
    rw [heq]
    linarith [hkey]
  linarith [hsplit, hfin]

end Work.MGroupInput
