import Mathlib
import Submission.Work.WilC5.Values
import Submission.Work.WilC5.ValuesLemmas

namespace Work.WilC5

section Aux

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The multiplier `1` (`N = 0`) already witnesses `VLe x y` whenever `|y| ≤ |x|`. -/
private lemma VLe_of_abs_le {x y : K} (h : |y| ≤ |x|) : VLe x y :=
  ⟨0, by simpa using h⟩

end Aux

/-- **The order and the value order disagree exactly when the elements lie in different
archimedean classes.**  For positive `w, t` with `¬ SameArch w t`, the smaller of the two is
dominated by the larger but not conversely: `w < t` iff `t` dominates `w` and `w` does not dominate
`t`, and dually for `t < w`.

Indeed, for `0 < w < t` one has `|w| = w ≤ t = |t|`, so `VLe t w` holds with multiplier `1`; if also
`VLe w t` held then `SameArch w t` by `SameArch_iff_VLe`, contradicting the hypothesis.  Conversely,
`VLe t w ∧ ¬ VLe w t` forces `w < t`, since `t ≤ w` would give `|t| = t ≤ w = |w|`, i.e. `VLe w t`. -/
theorem lt_iff_VLe_of_not_SameArch {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {w t : K} (hw : 0 < w) (ht : 0 < t) (h : ¬ Work.WilC5.SameArch w t) :
    (w < t ↔ (Work.WilC5.VLe t w ∧ ¬ Work.WilC5.VLe w t)) ∧
    (t < w ↔ (Work.WilC5.VLe w t ∧ ¬ Work.WilC5.VLe t w)) := by
  constructor
  · refine ⟨fun hlt => ?_, fun ⟨hvt, hnt⟩ => ?_⟩
    · -- `w < t` ⟹ `VLe t w`, and `VLe w t` would put `w`, `t` in the same class
      have hle : |w| ≤ |t| := by rw [abs_of_pos hw, abs_of_pos ht]; exact le_of_lt hlt
      exact ⟨VLe_of_abs_le hle,
        fun hvw => h ((SameArch_iff_VLe w t).mpr ⟨hvw, VLe_of_abs_le hle⟩)⟩
    · -- `t ≤ w` would give `VLe w t`, contradicting the second conjunct
      by_contra hcon
      have htw : t ≤ w := not_lt.mp hcon
      have hle : |t| ≤ |w| := by rw [abs_of_pos ht, abs_of_pos hw]; exact htw
      exact hnt (VLe_of_abs_le hle)
  · refine ⟨fun hlt => ?_, fun ⟨hwt, hnt⟩ => ?_⟩
    · -- `t < w` ⟹ `VLe w t`, and `VLe t w` would put `w`, `t` in the same class
      have hle : |t| ≤ |w| := by rw [abs_of_pos ht, abs_of_pos hw]; exact le_of_lt hlt
      exact ⟨VLe_of_abs_le hle,
        fun hvt => h ((SameArch_iff_VLe w t).mpr ⟨VLe_of_abs_le hle, hvt⟩)⟩
    · -- `w ≤ t` would give `VLe t w`, contradicting the second conjunct
      by_contra hcon
      have hwt' : w ≤ t := not_lt.mp hcon
      have hle : |w| ≤ |t| := by rw [abs_of_pos hw, abs_of_pos ht]; exact hwt'
      exact hnt (VLe_of_abs_le hle)

end Work.WilC5
