import Mathlib
import Submission.Work.ZeroFreeTables.P9.SigmaP3LChangeLevelAux
import Submission.Work.ZeroFreeTables.P9.changeLevel_norm_sub_le

open DirichletCharacter
open scoped BigOperators

namespace Work.ZeroFreeTables.P9

/-- The character-level estimate behind `norm_sigmaTerm_changeLevel_sub_le`:
`changeLevel` differs from the original character only at `n` that are coprime to the lower
level `N` but not to the higher level `q`, where the difference has norm at most `1`. -/
lemma changeLevel_norm_sub_le_aux {N q : ℕ} [NeZero N] [NeZero q] (hNq : N ∣ q)
    (ψ : DirichletCharacter ℂ N) (n : ℕ) :
    ‖(DirichletCharacter.changeLevel hNq ψ) (n : ZMod q) - ψ (n : ZMod N)‖
      ≤ (if Nat.Coprime n N ∧ ¬ Nat.Coprime n q then (1:ℝ) else 0) := by
  by_cases hq : IsUnit (n : ZMod q)
  · have hcq : Nat.Coprime n q := (ZMod.isUnit_iff_coprime n q).mp hq
    have hv : (DirichletCharacter.changeLevel hNq ψ) (n : ZMod q) = ψ (n : ZMod N) := by
      have h := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ hNq hq.unit
      have hu : ((hq.unit : (ZMod q)ˣ) : ZMod q) = (n : ZMod q) := hq.unit_spec
      rw [hu] at h
      rw [ZMod.cast_natCast hNq n] at h
      exact h
    rw [hv, sub_self, norm_zero]
    simp [hcq]
  · have hcq : ¬ Nat.Coprime n q := fun h => hq ((ZMod.isUnit_iff_coprime n q).mpr h)
    have hv : (DirichletCharacter.changeLevel hNq ψ) (n : ZMod q) = 0 :=
      MulChar.map_nonunit _ hq
    rw [hv, zero_sub, norm_neg]
    by_cases hN : IsUnit (n : ZMod N)
    · have hcN : Nat.Coprime n N := (ZMod.isUnit_iff_coprime n N).mp hN
      rw [if_pos ⟨hcN, hcq⟩]
      have : ‖ψ (n : ZMod N)‖ = 1 := by
        have hu : ((hN.unit : (ZMod N)ˣ) : ZMod N) = (n : ZMod N) := hN.unit_spec
        rw [← hu]
        exact DirichletCharacter.unit_norm_eq_one ψ hN.unit
      rw [this]
    · have hcN : ¬ Nat.Coprime n N := fun h => hN ((ZMod.isUnit_iff_coprime n N).mpr h)
      rw [if_neg (by tauto), MulChar.map_nonunit ψ hN, norm_zero]

theorem norm_sigmaTerm_changeLevel_sub_le {N q : ℕ} [NeZero N] [NeZero q] (hNq : N ∣ q) (ψ : DirichletCharacter ℂ N) (L : ℝ) (s : ℂ) (a lam₁ : ℝ) (ha : 0 < a) (hlam₁ : 0 ≤ lam₁) (hL : 0 < L) (n : ℕ) :
    ‖Work.ZeroFreeTables.P9.sigmaTerm q L (DirichletCharacter.changeLevel hNq ψ) s a lam₁ n - Work.ZeroFreeTables.P9.sigmaTerm N L ψ s a lam₁ n‖ ≤ (if Nat.Coprime n N ∧ ¬ Nat.Coprime n q then (1:ℝ) else 0) * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re) * Work.ZeroFreeTables.hbWL L a lam₁ n := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    simp [sigmaTerm]
  · have hvm : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
    have hU : 0 ≤ hbWL L a lam₁ n := by
      have hy : 0 ≤ Real.log (n:ℝ) / L := div_nonneg (Real.log_natCast_nonneg n) hL.le
      simp only [hbWL]
      have h1 : 0 ≤ (a + lam₁) ^ 2 * (Real.log (n:ℝ) / L) := mul_nonneg (sq_nonneg _) hy
      have h2 : 0 ≤ (1/3 : ℝ) * (a + lam₁) ^ 3 * (Real.log (n:ℝ) / L) ^ 2 := by positivity
      linarith [h1, h2]
    have hw : 0 ≤ (n : ℝ) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hΔ : ‖(DirichletCharacter.changeLevel hNq ψ) (n : ZMod q) - ψ (n : ZMod N)‖ ≤ (if Nat.Coprime n N ∧ ¬ Nat.Coprime n q then (1:ℝ) else 0) := changeLevel_norm_sub_le_aux hNq ψ n
    have hid : sigmaTerm q L (DirichletCharacter.changeLevel hNq ψ) s a lam₁ n - sigmaTerm N L ψ s a lam₁ n
        = (ArithmeticFunction.vonMangoldt n : ℝ) * (((DirichletCharacter.changeLevel hNq ψ) (n : ZMod q) - ψ (n : ZMod N)) / (n : ℂ) ^ s).re * hbWL L a lam₁ n := by
      simp only [sigmaTerm]
      rw [← sub_mul, ← mul_sub]
      congr 1
      rw [← Complex.sub_re, div_sub_div_same]
    rw [hid]
    have hX : |(((DirichletCharacter.changeLevel hNq ψ) (n : ZMod q) - ψ (n : ZMod N)) / (n : ℂ) ^ s).re| ≤ (if Nat.Coprime n N ∧ ¬ Nat.Coprime n q then (1:ℝ) else 0) * (n : ℝ) ^ (-s.re) := by
      calc |(((DirichletCharacter.changeLevel hNq ψ) (n : ZMod q) - ψ (n : ZMod N)) / (n : ℂ) ^ s).re|
          ≤ ‖((DirichletCharacter.changeLevel hNq ψ) (n : ZMod q) - ψ (n : ZMod N)) / (n : ℂ) ^ s‖ := Complex.abs_re_le_norm _
        _ = ‖(DirichletCharacter.changeLevel hNq ψ) (n : ZMod q) - ψ (n : ZMod N)‖ / ‖(n : ℂ) ^ s‖ := norm_div _ _
        _ = ‖(DirichletCharacter.changeLevel hNq ψ) (n : ZMod q) - ψ (n : ZMod N)‖ / ((n : ℝ) ^ s.re) := by rw [Complex.norm_natCast_cpow_of_pos hn]
        _ = ‖(DirichletCharacter.changeLevel hNq ψ) (n : ZMod q) - ψ (n : ZMod N)‖ * ((n : ℝ) ^ s.re)⁻¹ := by rw [div_eq_mul_inv]
        _ = ‖(DirichletCharacter.changeLevel hNq ψ) (n : ZMod q) - ψ (n : ZMod N)‖ * ((n : ℝ) ^ (-s.re)) := by rw [Real.rpow_neg (Nat.cast_nonneg n) (s.re)]
        _ ≤ (if Nat.Coprime n N ∧ ¬ Nat.Coprime n q then (1:ℝ) else 0) * (n : ℝ) ^ (-s.re) := by
              apply mul_le_mul_of_nonneg_right hΔ
              exact Real.rpow_nonneg (Nat.cast_nonneg n) _
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hvm, abs_of_nonneg hU]
    calc (ArithmeticFunction.vonMangoldt n : ℝ) * |(((DirichletCharacter.changeLevel hNq ψ) (n : ZMod q) - ψ (n : ZMod N)) / (n : ℂ) ^ s).re| * hbWL L a lam₁ n
        ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * ((if Nat.Coprime n N ∧ ¬ Nat.Coprime n q then (1:ℝ) else 0) * (n : ℝ) ^ (-s.re)) * hbWL L a lam₁ n := by
            apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX hvm) hU
      _ = (if Nat.Coprime n N ∧ ¬ Nat.Coprime n q then (1:ℝ) else 0) * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re) * hbWL L a lam₁ n := by ring

end Work.ZeroFreeTables.P9
