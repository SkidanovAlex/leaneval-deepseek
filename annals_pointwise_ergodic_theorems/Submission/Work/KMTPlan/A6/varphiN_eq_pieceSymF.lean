/-
# The §6 bump `varphiN` is the §7 piece symbol `pieceSymF`

The paper's §6 bump `φ_N` at the continuous scale `k₁`
(`Work.KMTAreas.A7.varphiN`) is a difference of two Littlewood–Paley cutoffs
`η(2^{Log N - k₁}·)`, i.e. the cutoff `η` evaluated at the *frequency* rescaled by
`2^{Log N - k₁}`.  The §7 piece symbol `Work.KMTAreas.A7.pieceSymF s N` is the same object
written as a difference of `Work.Analysis.IonescuWainger.etaCut`s, i.e. as `η(·/2^{a})` with
`a` the *exponent of the reciprocal* rescaling.

The only content of the identification is therefore the elementary rewriting
`η (2^m · ξ) = etaCut η (-m) ξ`, i.e. `ξ / 2^{-m} = 2^m ξ`, together with the identification of
the real power `2^{(Log N - k₁ : ℝ)}` with the integer power `2^{Log N - k₁}` (the exponent is
the cast of an integer, so `Real.rpow_intCast` applies).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.LowSmallSymDefs

namespace Work.KMTPlan.A6

open Work.Analysis.IonescuWainger

noncomputable section

/-- `etaCut η (-m)` is `η` precomposed with the scaling by `2^m`: `η (2^m ξ)`. -/
private lemma etaCut_neg_eq (η : ℝ → ℂ) (m : ℤ) (ξ : ℝ) :
    etaCut η (-m) ξ = η ((2 : ℝ) ^ m * ξ) := by
  simp only [etaCut]
  rw [div_eq_mul_inv, zpow_neg, inv_inv, mul_comm]

/-- The same rewriting with the cutoff exponent kept general:
`etaCut η a ξ = η (2^{-a} ξ)`. -/
private lemma etaCut_eq (η : ℝ → ℂ) (a : ℤ) (ξ : ℝ) :
    etaCut η a ξ = η ((2 : ℝ) ^ (-a) * ξ) := by
  simp only [etaCut]
  rw [div_eq_mul_inv, ← zpow_neg, mul_comm]

/-- The top exponent of `varphiN` (`k ≠ 0` case) as a cast of an integer. -/
private lemma two_rpow_sub_natCast_add_one (L : ℤ) (k : ℕ) :
    (2 : ℝ) ^ ((L : ℝ) - (k : ℝ) + 1)
      = (2 : ℝ) ^ (((L - (k : ℤ)) + 1 : ℤ) : ℝ) := by
  congr 1
  push_cast
  ring

/-- The bottom exponent of `varphiN` (`k ≠ 0` case) as a cast of an integer. -/
private lemma two_rpow_sub_natCast (L : ℤ) (k : ℕ) :
    (2 : ℝ) ^ ((L : ℝ) - (k : ℝ)) = (2 : ℝ) ^ (((L - (k : ℤ)) : ℤ) : ℝ) := by
  congr 1
  push_cast
  ring

theorem varphiN_eq_pieceSymF (N k : ℕ) :
    Work.KMTAreas.A7.varphiN N k = Work.KMTAreas.A7.pieceSymF k N := by
  funext ξ
  by_cases hk : k = 0
  · subst hk
    simp only [Work.KMTAreas.A7.varphiN, Work.KMTAreas.A7.pieceSymF, if_true]
    rw [etaCut_neg_eq, Real.rpow_intCast]
  · simp only [Work.KMTAreas.A7.varphiN, Work.KMTAreas.A7.pieceSymF, if_neg hk]
    rw [show (-Work.Analysis.EndVar.logN N + ((k : ℕ) : ℤ) - 1)
          = -((Work.Analysis.EndVar.logN N - ((k : ℕ) : ℤ)) + 1) from by ring]
    rw [show (-Work.Analysis.EndVar.logN N + ((k : ℕ) : ℤ))
          = -(Work.Analysis.EndVar.logN N - ((k : ℕ) : ℤ)) from by ring]
    rw [etaCut_eq, etaCut_eq, neg_neg, neg_neg]
    rw [two_rpow_sub_natCast_add_one, two_rpow_sub_natCast,
      Real.rpow_intCast, Real.rpow_intCast]

end

end Work.KMTPlan.A6
