import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.NumberTheory.NumberField

theorem differentIdeal_eq_top_of_rootDiscr_eq {E K : Type*} [Field E]
    [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (h : NumberField.rootDiscr K = NumberField.rootDiscr E) :
    differentIdeal (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers K) = ⊤ := by
  have hN : Ideal.absNorm (differentIdeal (NumberField.RingOfIntegers E)
      (NumberField.RingOfIntegers K)) = 1 := by
    let m := Module.finrank ℚ E
    let n := Module.finrank E K
    let N := Ideal.absNorm (differentIdeal (NumberField.RingOfIntegers E)
      (NumberField.RingOfIntegers K))
    have hfin : m * n = Module.finrank ℚ K := by
      dsimp [m, n]
      exact Module.finrank_mul_finrank ℚ E K
    have hm_pos : 0 < m := by
      dsimp [m]
      exact Module.finrank_pos
    have hn_pos : 0 < n := by
      dsimp [n]
      exact Module.finrank_pos
    have hm : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm_pos
    have hn : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn_pos
    have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
    have hmE : Module.finrank ℚ E ≠ 0 := by
      simpa [m] using hm
    have hdisc : (NumberField.discr K).natAbs = N * (NumberField.discr E).natAbs ^ n := by
      dsimp [N, n]
      exact NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
        E (NumberField.RingOfIntegers E) K (NumberField.RingOfIntegers K)
    have hdisc_real : ((NumberField.discr K).natAbs : ℝ) =
        (N : ℝ) * ((NumberField.discr E).natAbs : ℝ) ^ n := by
      exact_mod_cast hdisc
    have hK_abs : (↑|NumberField.discr K| : ℝ) =
        (N : ℝ) * ((↑|NumberField.discr E| : ℝ) ^ n) := by
      rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]
      simpa [Nat.cast_pow] using hdisc_real
    have hxK : 0 ≤ (↑|NumberField.discr K| : ℝ) := by
      exact Int.cast_nonneg (abs_nonneg (NumberField.discr K))
    have hxE : 0 ≤ (↑|NumberField.discr E| : ℝ) := by
      exact Int.cast_nonneg (abs_nonneg (NumberField.discr E))
    have hrootK_pow : (NumberField.rootDiscr K) ^ (m * n) =
        (↑|NumberField.discr K| : ℝ) := by
      rw [NumberField.rootDiscr_def]
      rw [← hfin]
      simpa using Real.rpow_inv_natCast_pow (x := (↑|NumberField.discr K| : ℝ))
        (n := m * n) hxK hmn
    have hrootE_pow : (NumberField.rootDiscr E) ^ (m * n) =
        ((↑|NumberField.discr E| : ℝ) ^ n) := by
      rw [NumberField.rootDiscr_def]
      rw [← Real.rpow_natCast, ← Real.rpow_natCast]
      rw [← Real.rpow_mul hxE]
      congr 1
      dsimp [m]
      field_simp [Nat.cast_ne_zero.mpr hmE]
      norm_num
    have hK_eq : (↑|NumberField.discr K| : ℝ) =
        ((↑|NumberField.discr E| : ℝ) ^ n) := by
      calc
        (↑|NumberField.discr K| : ℝ) = (NumberField.rootDiscr K) ^ (m * n) := by
          rw [hrootK_pow]
        _ = (NumberField.rootDiscr E) ^ (m * n) := by rw [h]
        _ = ((↑|NumberField.discr E| : ℝ) ^ n) := by rw [hrootE_pow]
    have hE_cast_ne : (NumberField.discr E : ℝ) ≠ 0 :=
      Int.cast_ne_zero.mpr (NumberField.discr_ne_zero E)
    have hE_abs_pos : 0 < (↑|NumberField.discr E| : ℝ) := by
      rw [Int.cast_abs]
      exact abs_pos.mpr hE_cast_ne
    have hbase_pos : 0 < ((↑|NumberField.discr E| : ℝ) ^ n) :=
      pow_pos hE_abs_pos n
    have hbase_ne : ((↑|NumberField.discr E| : ℝ) ^ n) ≠ 0 := ne_of_gt hbase_pos
    have hN_mul : (N : ℝ) * ((↑|NumberField.discr E| : ℝ) ^ n) =
        ((↑|NumberField.discr E| : ℝ) ^ n) := by
      rw [← hK_abs]
      exact hK_eq
    have hN_one : (N : ℝ) = 1 :=
      (mul_left_eq_self₀.mp hN_mul).resolve_right hbase_ne
    have hN_nat : N = 1 := Nat.cast_eq_one.mp hN_one
    simpa [N] using hN_nat
  exact (Ideal.absNorm_eq_one_iff).mp hN

end Commons.NumberTheory.NumberField