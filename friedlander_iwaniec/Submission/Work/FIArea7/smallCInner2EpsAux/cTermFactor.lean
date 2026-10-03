import Mathlib
import Submission.Work.FIArea7.smallCInner2EpsAux.sepLHSDefs
import Submission.Work.FIArea7.smallCInnerAux.sepPairCoprime

set_option autoImplicit false

namespace Work.FIArea7.smallCInner2EpsAux

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `smoothInd` is `ind` of the smoothness condition, definitionally. -/
lemma smoothInd_eq_ind (z n : ℕ) :
    smoothInd z n = ind (∀ p : ℕ, p.Prime → p ∣ n → p ≤ z) := rfl

/-- The defining `if` of `cTerm` written as an `ind`. -/
lemma cTerm_eq_ind (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (k : ℤ) (c : ℕ)
    (P : ℝ → ℝ) (ℓ : ℕ) :
    cTerm Pa chi k c P ℓ
      = ind (Nat.Coprime c ℓ)
        * (Work.FIArea7.nspInd Pa ℓ * ((ArithmeticFunction.moebius ℓ : ℤ) : ℂ)
            * ((P ((c : ℝ) * (ℓ : ℝ)) : ℝ) : ℂ)
            * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * ℓ)) := by
  unfold cTerm ind
  by_cases h : Nat.Coprime c ℓ <;> simp [h]

/-- The defining `if`s of `cCoeff` written as `ind`s. -/
lemma cCoeff_eq_ind (Pa : Work.FITop.Params) (c z n : ℕ) :
    cCoeff Pa c z n
      = ind (Nat.Coprime c n)
        * (smoothInd z n * (Work.FIArea7.nspInd Pa n * ((ArithmeticFunction.moebius n : ℤ) : ℂ))) := by
  unfold cCoeff ind smoothInd
  by_cases h1 : Nat.Coprime c n <;>
    by_cases h2 : (∀ p : ℕ, p.Prime → p ∣ n → p ≤ z) <;>
      simp [h1, h2]

/-- The smoothness indicator of a product factors over the three factors: a prime divides
`d·m·n` iff it divides one of `d, m, n`. -/
lemma ind_smooth_mul (z d m n : ℕ) :
    ind (∀ p : ℕ, p.Prime → p ∣ d * m * n → p ≤ z)
      = smoothInd z d * smoothInd z m * smoothInd z n := by
  rw [smoothInd_eq_ind (z := z) (n := d), smoothInd_eq_ind (z := z) (n := m),
    smoothInd_eq_ind (z := z) (n := n)]
  have hprod : ind (∀ p : ℕ, p.Prime → p ∣ d → p ≤ z) * ind (∀ p : ℕ, p.Prime → p ∣ m → p ≤ z)
        * ind (∀ p : ℕ, p.Prime → p ∣ n → p ≤ z)
      = ind ((∀ p : ℕ, p.Prime → p ∣ d → p ≤ z)
          ∧ (∀ p : ℕ, p.Prime → p ∣ m → p ≤ z)
          ∧ (∀ p : ℕ, p.Prime → p ∣ n → p ≤ z)) := by
    simp only [ind_and]
    ring
  rw [hprod]
  exact congrArg ind (propext <| by
    constructor
    · intro hc
      exact ⟨fun p hp hpd => hc p hp ((dvd_mul_of_dvd_left hpd m).trans (dvd_mul_right (d * m) n)),
        fun p hp hpm => hc p hp ((dvd_mul_of_dvd_right hpm d).trans (dvd_mul_right (d * m) n)),
        fun p hp hpn => hc p hp (dvd_mul_of_dvd_right hpn (d * m))⟩
    · rintro ⟨hd, hm, hn⟩ p hp hpdvd
      rcases (hp.dvd_mul.mp hpdvd) with h1 | h1
      · rcases (hp.dvd_mul.mp h1) with h2 | h2
        · exact hd p hp h2
        · exact hm p hp h2
      · exact hn p hp h1)

/-- The indicator of `(c, ·) = 1` factors over the three factors. -/
lemma ind_coprime_mul (c d m n : ℕ) :
    ind (Nat.Coprime c (d * m * n))
      = ind (Nat.Coprime c d) * ind (Nat.Coprime c m) * ind (Nat.Coprime c n) := by
  have hiff : Nat.Coprime c (d * m * n)
      ↔ (Nat.Coprime c d ∧ Nat.Coprime c m) ∧ Nat.Coprime c n := by
    rw [Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_right]
  have hprod : ind (Nat.Coprime c d) * ind (Nat.Coprime c m) * ind (Nat.Coprime c n)
      = ind ((Nat.Coprime c d ∧ Nat.Coprime c m) ∧ Nat.Coprime c n) := by
    simp only [ind_and]
  rw [hprod]
  exact congrArg ind (propext hiff)

/-- `nspInd` is multiplicative over a pairwise coprime triple. -/
lemma nspInd_triple (Pa : Work.FITop.Params) {d m n : ℕ}
    (hdm : Nat.Coprime d m) (hmn : Nat.Coprime m n) (hdn : Nat.Coprime d n) :
    Work.FIArea7.nspInd Pa (d * m * n)
      = Work.FIArea7.nspInd Pa d * Work.FIArea7.nspInd Pa m * Work.FIArea7.nspInd Pa n := by
  rw [Work.FIArea7.nspInd_mul Pa (hdn.mul_left hmn), Work.FIArea7.nspInd_mul Pa hdm]

/-- Möbius is multiplicative over a pairwise coprime triple. -/
lemma moebius_triple {d m n : ℕ}
    (hdm : Nat.Coprime d m) (hmn : Nat.Coprime m n) (hdn : Nat.Coprime d n) :
    ((ArithmeticFunction.moebius (d * m * n) : ℤ) : ℂ)
      = ((ArithmeticFunction.moebius d : ℤ) : ℂ) * ((ArithmeticFunction.moebius m : ℤ) : ℂ)
        * ((ArithmeticFunction.moebius n : ℤ) : ℂ) := by
  have h1 := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
    (hdn.mul_left hmn : Nat.Coprime (d * m) n)
  have h2 := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (hdm : Nat.Coprime d m)
  rw [h1, h2]
  push_cast
  ring

theorem cTermFactor {r d m n : ℕ} (hr : 2 ≤ r) (h : Work.FIArea7.IsSepPair r d m n)
    (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (k : ℤ) (c z : ℕ) (P : ℝ → ℝ) :
    Work.FIArea7.smallCInner2EpsAux.ind (∀ p : ℕ, p.Prime → p ∣ d * m * n → p ≤ z)
        * Work.FIArea7.smallCInner2EpsAux.cTerm Pa chi k c P (d * m * n)
      = Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z d
        * Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z m
        * Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z n
        * ((P ((c : ℝ) * ((d * m * n : ℕ) : ℝ)) : ℝ) : ℂ)
        * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (d * m * n)) := by
  obtain ⟨_, _, _, hcdm, hcdn, hcmn, _, _, _, _⟩ :=
    Work.FIArea7.smallCInnerAux.sepPairCoprime hr h
  rw [cTerm_eq_ind, cCoeff_eq_ind, cCoeff_eq_ind, cCoeff_eq_ind]
  rw [ind_smooth_mul, ind_coprime_mul, nspInd_triple Pa hcdm hcmn hcdn,
    moebius_triple hcdm hcmn hcdn]
  ring

end

end Work.FIArea7.smallCInner2EpsAux
