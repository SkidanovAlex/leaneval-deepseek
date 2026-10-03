import Mathlib
import Submission.Work.FIArea7.Bridge17Defs
import Submission.Work.FIArea7.chiOf_eq_unitInd_mul

namespace Work.FIArea7

/-- **The class-eight indicator commutes with the deep bilinear form.**

The two hypotheses `hsum1`/`hsum0` say that for every *primary* `z`, the coefficient vector
`(c z0 i)_i` reproduces the class-eight indicator `1_{SameClass8 z z0}` against the vector
`(a i z)_i`:
`∑ i, c z0 i * a i z = if SameClass8 z z0 then 1 else 0`.

The point of the lemma is that this pointwise identity may be pulled *through* the radial
coefficient `radBeta` of (17.15).  Indeed `radBeta Pa p Pa.C z` vanishes off the primary
`z`, so multiplying it against the pointwise identity is legitimate, and the weighted sum
`∑_z [z] χ(z) (z/|z|)^m (1_{SameClass8 z z0} · radBeta z)` of the left hand side equals
`∑_i c z0 i · SChiRad Pa p Pa.C (χ̄ · a i) m`.  In other words the indicator `radBetaCls`
(5.7) on the *source* side is the same thing as the coefficient vector `c z0` on the
*target* side. -/
theorem cls8_indicator_mul_radBeta {N : ℕ} {a : Fin N → GaussianInt → ℂ} {c : GaussianInt → Fin N → ℂ}
    (hsum1 : ∀ z z0 : GaussianInt, Work.FIPlan.IsPrimary z → Work.FITop4.SameClass8 z z0 →
      (1 : ℂ) = ∑ i, c z0 i * a i z)
    (hsum0 : ∀ z z0 : GaussianInt, Work.FIPlan.IsPrimary z → ¬ Work.FITop4.SameClass8 z z0 →
      (0 : ℂ) = ∑ i, c z0 i * a i z)
    (Pa : Work.FITop.Params) (p : ℝ → ℝ) (z0 : GaussianInt) (m : ℤ) (Q : ℕ) [NeZero Q]
    (χ : AddChar (Additive (Work.FIArea7.GaussUnit Q)) ℂ) :
    (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
        Work.FIArea7.JKSym z * Work.FIArea7.uniPow z m * star (Work.FIArea7.chiOf Q χ z)
          * Work.FIArea7.radBetaCls Pa p z0 z)
      = ∑ i, c z0 i * Work.FIArea7.SChiRad Pa p Pa.C
          (fun z => star (Work.FIArea7.chiOf Q χ z) * a i z) m := by
  classical
  -- The pointwise identity, valid because `radBeta` vanishes off the primary `z`.
  have hkey : ∀ z : GaussianInt,
      Work.FIArea7.radBeta Pa p Pa.C z * (∑ i, c z0 i * a i z)
        = (if Work.FITop4.SameClass8 z z0 then (1 : ℂ) else 0) * Work.FIArea7.radBeta Pa p Pa.C z := by
    intro z
    by_cases h : Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z
    · rw [Work.FIArea7.radBeta, if_pos h]
      by_cases hc : Work.FITop4.SameClass8 z z0
      · rw [if_pos hc, ← hsum1 z z0 h.1 hc]; ring
      · rw [if_neg hc, ← hsum0 z z0 h.1 hc]; ring
    · rw [Work.FIArea7.radBeta, if_neg h]; simp
  -- Left hand side, put into a common normal form.
  have hA : (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
        Work.FIArea7.JKSym z * Work.FIArea7.uniPow z m * star (Work.FIArea7.chiOf Q χ z)
          * Work.FIArea7.radBetaCls Pa p z0 z)
      = ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          (if Work.FITop4.SameClass8 z z0 then (1 : ℂ) else 0)
            * Work.FIArea7.radBeta Pa p Pa.C z
            * (Work.FIArea7.JKSym z * star (Work.FIArea7.chiOf Q χ z) * Work.FIArea7.uniPow z m) := by
    apply Finset.sum_congr rfl
    intro z _
    rw [Work.FIArea7.radBetaCls]
    ring
  -- Right hand side, expanded and put into the same normal form.
  have hR : (∑ i, c z0 i * Work.FIArea7.SChiRad Pa p Pa.C
          (fun z => star (Work.FIArea7.chiOf Q χ z) * a i z) m)
      = ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          (Work.FIArea7.radBeta Pa p Pa.C z * (∑ i, c z0 i * a i z))
            * (Work.FIArea7.JKSym z * star (Work.FIArea7.chiOf Q χ z) * Work.FIArea7.uniPow z m) := by
    simp only [Work.FIArea7.SChiRad]
    trans ∑ i, ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
        c z0 i * (Work.FIArea7.radBeta Pa p Pa.C z * Work.FIArea7.JKSym z
          * (star (Work.FIArea7.chiOf Q χ z) * a i z) * Work.FIArea7.uniPow z m)
    · apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      trans ∑ i, (Work.FIArea7.radBeta Pa p Pa.C z * (c z0 i * a i z))
              * (Work.FIArea7.JKSym z * star (Work.FIArea7.chiOf Q χ z) * Work.FIArea7.uniPow z m)
      · apply Finset.sum_congr rfl
        intro i _
        ring
      · rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [hA, hR]
  apply Finset.sum_congr rfl
  intro z _
  rw [hkey z]

end Work.FIArea7
