/-
# `Work.FIArea5.S16Hecke.thetaHol_twist_eq`

The twist `twist χ m` of a character `χ` by the unit character `twistChar χ m` (a character of
`(ℤ[i]/4d)∗` which is trivial on the primary coset `1 + (1+i)³ℤ[i]`) does not change the
primary-coset holomorphic theta series `thetaHol`:

  `thetaHol (twist χ m) m u = thetaHol χ m u`.

The proof is pointwise on the primary coset: for primary `z` we have
`twist χ m z = χ(z)·twistChar χ m z = χ(z)`, because

* primary `z` is *odd* (`IsPrimary z` gives `z.re` odd and `z.im` even, so `z.re + z.im` is odd,
  and `isOddG z ↔ Odd (z.re + z.im)`), so `twistChar` takes its non-zero branch, and
* primary `z` lies in the coset `1 + (1+i)³ℤ[i]` (`isPrimary_iff_coset`), so `(1+i)³ ∣ z - 1` and
  `primaryUnit z = 1`; hence `twistChar χ m z = 1^-(j) = 1`.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.h1166TwistDefs
import Submission.Work.FIArea5.S16Hecke.isPrimary_iff_coset
import Submission.Work.FIArea5.S16Hecke.GaussBasic

set_option linter.unusedVariables false

namespace Work.FIArea5.S16Hecke

open Work.FIPlan

noncomputable section

/-- **A primary Gaussian integer is odd**: `z.re` is odd and `z.im` even, so `z.re + z.im` is odd,
and oddness in `ℤ[i]` (non-divisibility by `1+i`) is exactly the oddness of `z.re + z.im`. -/
lemma isOddG_of_isPrimary {z : GaussianInt} (hz : IsPrimary z) : isOddG z :=
  (GaussBasic.isOddG_iff_odd z).mpr (hz.1.add_even hz.2.1)

/-- **`(1+i)³` divides `z - 1` for primary `z`**: the primary coset is `1 + (1+i)³ℤ[i]`. -/
lemma c3_dvd_sub_one_of_isPrimary {z : GaussianInt} (hz : IsPrimary z) : c3 ∣ z - 1 := by
  obtain ⟨w, hw⟩ := (isPrimary_iff_coset z).mp hz
  refine ⟨w, ?_⟩
  rw [hw]
  simp only [c3]
  ring

/-- **`primaryUnit z = 1` for primary `z`**, since the first branch `(1+i)³ ∣ z - 1` applies. -/
lemma primaryUnit_of_isPrimary {z : GaussianInt} (hz : IsPrimary z) : primaryUnit z = 1 := by
  rw [primaryUnit, if_pos (c3_dvd_sub_one_of_isPrimary hz)]

/-- **The twisting character is trivial on the primary coset**: `twistChar χ m z = 1` for
primary `z`.  Indeed `z` is odd, so the non-zero branch is taken, and `primaryUnit z = 1`. -/
lemma twistChar_eq_one_of_isPrimary (chi : GaussianInt → ℂ) (m : ℕ) {z : GaussianInt}
    (hz : IsPrimary z) : twistChar chi m z = 1 := by
  classical
  show (if isOddG z then ((primaryUnit z).toComplex) ^ (-(twistExp chi m : ℤ)) else 0) = 1
  rw [if_pos (isOddG_of_isPrimary hz), primaryUnit,
    if_pos (c3_dvd_sub_one_of_isPrimary hz), GaussianInt.toComplex_one, one_zpow]

/-- **The twisted character agrees with `χ` on the primary coset**: `twist χ m z = χ z` for
primary `z`. -/
lemma twist_eq_of_isPrimary (chi : GaussianInt → ℂ) (m : ℕ) {z : GaussianInt}
    (hz : IsPrimary z) : twist chi m z = chi z := by
  rw [twist, twistChar_eq_one_of_isPrimary chi m hz, mul_one]

theorem thetaHol_twist_eq (d : ℕ) (chi : GaussianInt → ℂ) (m : ℕ) (u : ℝ) :
    thetaHol (twist chi m) m u = thetaHol chi m u := by
  classical
  rw [thetaHol, thetaHol]
  refine tsum_congr fun z => ?_
  by_cases hz : IsPrimary z
  · rw [if_pos hz, if_pos hz, twist_eq_of_isPrimary chi m hz]
  · rw [if_neg hz, if_neg hz]

end

end Work.FIArea5.S16Hecke
