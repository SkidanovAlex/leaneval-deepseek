import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.NumberTheory.BombieriVinogradov.bilinear_error_sum_bound

open scoped BigOperators

namespace Commons.NumberTheory.BombieriVinogradov

lemma indicator_char (q : ℕ) [NeZero q] (a : ℕ) (ha : a.Coprime q) (n : ℕ) :
    (if n % q = a % q then (1 : ℂ) else 0) =
      ((q.totient : ℂ)⁻¹) * (∑ χ : DirichletCharacter ℂ q,
        χ ((a : ZMod q)⁻¹) * χ (n : ZMod q)) := by
  have hsum : (∑ χ : DirichletCharacter ℂ q,
        χ ((a : ZMod q)⁻¹) * χ (n : ZMod q)) =
      if (a : ZMod q) = (n : ZMod q) then (q.totient : ℂ) else 0 := by
    simpa using (DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) (n := q)
      ((ZMod.isUnit_iff_coprime a q).mpr ha) (n : ZMod q))
  rw [hsum]
  have hne : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.neZero_totient (n := q)).out
  by_cases h : n % q = a % q
  · have hz : (a : ZMod q) = (n : ZMod q) := (ZMod.natCast_eq_natCast_iff' a n q).mpr h.symm
    simp [h, hz, inv_mul_cancel₀ hne]
  · have hz : ¬ (a : ZMod q) = (n : ZMod q) := by
      intro he
      exact h ((ZMod.natCast_eq_natCast_iff' a n q).mp he).symm
    simp [h, hz]

end Commons.NumberTheory.BombieriVinogradov