import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Submission.Commons.NumberTheory.DirichletCharacter.changeLevel_congr

namespace Commons.NumberTheory.DirichletCharacter

theorem changeLevel_stable_nat {q : ℕ} [NeZero q] {c : ℕ} (h : c ∣ q)
    (χ : DirichletCharacter ℂ c) {n : ℕ} (hcn : n.Coprime q) :
    (DirichletCharacter.changeLevel h χ) (n : ZMod q) = χ (n : ZMod c) := by
  have hcop : IsCoprime (n : ℤ) q := Nat.isCoprime_iff_coprime.mpr hcn
  have key := DirichletCharacter.changeLevel_eq_cast_of_dvd' (χ := χ) h hcop
  simpa using key

end Commons.NumberTheory.DirichletCharacter