/-
  WilC5 — the arithmetic of the standard real valuation of vdDMM (1.1).

  The valuation itself is the quotient `K^× → K^×/Un(K)`, so all the computations of vdDMM §3
  are computations with the *unit* predicate `IsUnitVal` and the archimedean class relation
  `SameArch` of `Values.lean`.  This module provides the arithmetic of those predicates:

  * `IsUnitVal` is multiplicative and inversion-stable (`IsUnitVal_mul`, `IsUnitVal_inv`,
    `IsUnitVal_div`), hence closed under natural and integer powers (`IsUnitVal_pow`,
    `IsUnitVal_zpow`) and under `n`-th roots of powers (`IsUnitVal_of_pow`);
  * `IsUnitVal x ↔ SameArch x 1` (`ValuesLemmas.lean`), so these transport to `SameArch`.

  They are the lemmas that vdDMM Lemmas 4.2–4.4 consume when they write `v(w) = v(z)`,
  `v(ε) > 0`, or `v(F(x)^×) = v(F^×)` in the course of the extension argument.

  Everything is stated in the typeclass context of the frozen `IsUnitVal` — an ordered field —
  with the `TR`-model hypotheses added by callers.
-/
import Mathlib
import Submission.Work.WilC5.Values
import Submission.Work.WilC5.ValuesLemmas

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG

section ValArith

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The natural multiplier of a product of two natural multipliers, read backwards: the shape in
which compositions of `IsUnitVal` bounds are added up. -/
private lemma mul_succ_eq (N M : ℕ) :
    (((N * M + N + M : ℕ)) : K) + 1 = ((N : K) + 1) * ((M : K) + 1) := by
  push_cast; ring

/-- `1` is a unit (`v(1) = 0`). -/
theorem IsUnitVal_one : IsUnitVal (1 : K) := by
  refine ⟨1, ?_, ?_⟩
  · show (((1 : ℕ) : K) + 1)⁻¹ ≤ |(1 : K)|
    rw [abs_one, Nat.cast_one]
    exact inv_le_one_of_one_le₀ (le_add_of_nonneg_right zero_le_one)
  · show |(1 : K)| ≤ ((1 : ℕ) : K) + 1
    rw [abs_one, Nat.cast_one]
    exact le_add_of_nonneg_right zero_le_one

/-- `IsUnitVal` depends only on `|x|`. -/
theorem isUnitVal_abs_iff (x : K) : IsUnitVal |x| ↔ IsUnitVal x := by
  unfold IsUnitVal; rw [abs_abs]

/-- `v(-x) = v(x)`: the valuation is insensitive to sign. -/
theorem isUnitVal_neg_iff (x : K) : IsUnitVal (-x) ↔ IsUnitVal x := by
  unfold IsUnitVal; rw [abs_neg]

/-- The units are closed under negation. -/
theorem IsUnitVal.neg {x : K} (hx : IsUnitVal x) : IsUnitVal (-x) :=
  (isUnitVal_neg_iff x).mpr hx

/-- The units are closed under multiplication: `Un(K)` is a subgroup of `K^×`. -/
theorem IsUnitVal_mul {x y : K} (hx : IsUnitVal x) (hy : IsUnitVal y) : IsUnitVal (x * y) := by
  obtain ⟨N, hN1, hN2⟩ := hx
  obtain ⟨M, hM1, hM2⟩ := hy
  refine ⟨N * M + N + M, ?_, ?_⟩
  · show ((((N * M + N + M : ℕ)) : K) + 1)⁻¹ ≤ |x * y|
    rw [abs_mul, mul_succ_eq, mul_inv]
    exact mul_le_mul hN1 hM1 (by positivity) (abs_nonneg x)
  · show |x * y| ≤ (((N * M + N + M : ℕ)) : K) + 1
    rw [abs_mul, mul_succ_eq]
    exact mul_le_mul hN2 hM2 (abs_nonneg y) (by positivity)

/-- The units are closed under inversion. -/
theorem IsUnitVal_inv {x : K} (hx : IsUnitVal x) : IsUnitVal x⁻¹ := by
  obtain ⟨N, hN1, hN2⟩ := hx
  have hx0 : 0 < |x| := lt_of_lt_of_le (by positivity) hN1
  refine ⟨N, ?_, ?_⟩
  · show (((N : ℕ) : K) + 1)⁻¹ ≤ |x⁻¹|
    rw [abs_inv]
    rw [inv_le_inv₀ (by positivity) hx0]
    exact hN2
  · show |x⁻¹| ≤ ((N : ℕ) : K) + 1
    rw [abs_inv, inv_le_iff_one_le_mul₀ hx0]
    calc (1 : K) = ((N : K) + 1)⁻¹ * ((N : K) + 1) := (inv_mul_cancel₀ (by positivity)).symm
      _ ≤ |x| * ((N : K) + 1) := mul_le_mul_of_nonneg_right hN1 (by positivity)
      _ = ((N : K) + 1) * |x| := mul_comm _ _

/-- The units are closed under division. -/
theorem IsUnitVal_div {x y : K} (hx : IsUnitVal x) (hy : IsUnitVal y) : IsUnitVal (x / y) := by
  rw [div_eq_mul_inv]
  exact IsUnitVal_mul hx (IsUnitVal_inv hy)

/-- A quotient of units: `v(x/y) = 0` when `v(x) = v(y) = 0`. -/
theorem isUnitVal_div_iff {x y : K} (hx : IsUnitVal x) (hy : IsUnitVal y) :
    IsUnitVal (x / y) := IsUnitVal_div hx hy

/-- The units are closed under natural powers. -/
theorem IsUnitVal_pow {x : K} (hx : IsUnitVal x) (n : ℕ) : IsUnitVal (x ^ n) := by
  induction n with
  | zero => simpa using IsUnitVal_one
  | succ n ih => rw [pow_succ]; exact IsUnitVal_mul ih hx

/-- The units are closed under integer powers. -/
theorem IsUnitVal_zpow {x : K} (hx : IsUnitVal x) (n : ℤ) : IsUnitVal (x ^ n) := by
  cases n with
  | ofNat n => simpa [zpow_natCast] using IsUnitVal_pow hx n
  | negSucc n => rw [zpow_negSucc]; exact IsUnitVal_inv (IsUnitVal_pow hx (n + 1))

/-- **A positive power of a unit is a unit only if the base is.**  This is the "`v(x)/n ∈ v(K^×)`"
step of vdDMM (3.5): if `v(x^n) ∈ v(K^×)` then `v(x) ∈ v(K^×)`. -/
theorem IsUnitVal_of_pow {x : K} {n : ℕ} (hn : 1 ≤ n) (h : IsUnitVal (x ^ n)) : IsUnitVal x := by
  obtain ⟨N, hN1, hN2⟩ := h
  rw [abs_pow] at hN1 hN2
  rcases Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega) with ⟨k, rfl⟩
  simp only [pow_succ] at hN1 hN2
  have hA : (0 : K) ≤ |x| := abs_nonneg x
  refine ⟨N, ?_, ?_⟩
  · -- `((N : K) + 1)⁻¹ ≤ |x|`
    by_cases h1 : (1 : K) ≤ |x|
    · refine le_trans (inv_le_one_of_one_le₀ ?_) h1
      exact le_add_of_nonneg_left (Nat.cast_nonneg N : (0 : K) ≤ ↑N)
    · have hlt : |x| < 1 := not_le.mp h1
      have hle1 : |x| ^ k * |x| ≤ |x| := by
        have h1' : |x| ^ k ≤ 1 := pow_le_one₀ hA (le_of_lt hlt)
        calc |x| ^ k * |x| ≤ 1 * |x| := mul_le_mul_of_nonneg_right h1' hA
          _ = |x| := one_mul _
      exact le_trans hN1 hle1
  · -- `|x| ≤ (N : K) + 1`
    by_cases h1 : (1 : K) ≤ |x|
    · have hle : |x| ≤ |x| ^ k * |x| := by
        have h1' : (1 : K) ≤ |x| ^ k := one_le_pow₀ h1
        calc |x| = 1 * |x| := (one_mul _).symm
          _ ≤ |x| ^ k * |x| := mul_le_mul_of_nonneg_right h1' hA
      exact le_trans hle hN2
    · refine le_trans (le_of_lt (not_le.mp h1)) ?_
      exact le_add_of_nonneg_left (Nat.cast_nonneg N : (0 : K) ≤ ↑N)

end ValArith

section SameArchAlg

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **`v(x) = v(y)` is `x / y ∈ Un(K)`.**  This is the form in which vdDMM write the value
computations of §3 (`v(F(x)^×) = v(F^×)` becomes "every quotient of elements of `F(x)` and `F` is
a unit"), and it is how the frozen `ValIneq`'s independence hypothesis is read. -/
theorem SameArch_iff_IsUnitVal_div {x y : K} (hy : y ≠ 0) :
    SameArch x y ↔ IsUnitVal (x / y) := by
  have hy0 : 0 < |y| := abs_pos.mpr hy
  unfold SameArch IsUnitVal
  rw [abs_div]
  constructor
  · -- `v(x) = v(y) → v(x/y) = 0`
    rintro ⟨N, h1, h2⟩
    refine ⟨N, ?_, ?_⟩
    · rw [le_div_iff₀ hy0]
      calc ((N : K) + 1)⁻¹ * |y| ≤ ((N : K) + 1)⁻¹ * (((N : K) + 1) * |x|) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = |x| := by rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    · rw [div_le_iff₀ hy0]
      exact h1
  · -- `v(x/y) = 0 → v(x) = v(y)`
    rintro ⟨N, h1, h2⟩
    refine ⟨N, ?_, ?_⟩
    · rw [div_le_iff₀ hy0] at h2
      exact h2
    · rw [le_div_iff₀ hy0] at h1
      calc |y| = ((N : K) + 1) * (((N : K) + 1)⁻¹ * |y|) := by
            rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
        _ ≤ ((N : K) + 1) * |x| := mul_le_mul_of_nonneg_left h1 (by positivity)

/-- The same, in the multiplicative form used when the value of a quotient is computed as a
product. -/
theorem SameArch_iff_IsUnitVal_mul_inv {x y : K} (hy : y ≠ 0) :
    SameArch x y ↔ IsUnitVal (x * y⁻¹) := by
  rw [SameArch_iff_IsUnitVal_div hy, div_eq_mul_inv]

/-- `SameArch` only depends on absolute values. -/
theorem SameArch_abs_iff (x y : K) : SameArch |x| |y| ↔ SameArch x y := by
  unfold SameArch; rw [abs_abs, abs_abs]

/-- The archimedean class is multiplicative. -/
theorem SameArch_mul {x y x' y' : K} (hx : SameArch x x') (hy : SameArch y y') :
    SameArch (x * y) (x' * y') := by
  obtain ⟨N, hN1, hN2⟩ := hx
  obtain ⟨M, hM1, hM2⟩ := hy
  refine ⟨N * M + N + M, ?_, ?_⟩
  · rw [abs_mul, abs_mul, mul_succ_eq]
    calc |x| * |y| ≤ (((N : K) + 1) * |x'|) * (((M : K) + 1) * |y'|) :=
          mul_le_mul hN1 hM1 (abs_nonneg y) (by positivity)
      _ = (((N : K) + 1) * ((M : K) + 1)) * (|x'| * |y'|) := by ring
  · rw [abs_mul, abs_mul, mul_succ_eq]
    calc |x'| * |y'| ≤ (((N : K) + 1) * |x|) * (((M : K) + 1) * |y|) :=
          mul_le_mul hN2 hM2 (abs_nonneg y') (by positivity)
      _ = (((N : K) + 1) * ((M : K) + 1)) * (|x| * |y|) := by ring

/-- The archimedean class is inversion-stable. -/
theorem SameArch_inv {x y : K} (h : SameArch x y) : SameArch x⁻¹ y⁻¹ := by
  rcases eq_or_ne y 0 with rfl | hy
  · have hx : x = 0 := by
      obtain ⟨N, h1, _⟩ := h
      exact abs_eq_zero.mp (le_antisymm (by simpa using h1) (abs_nonneg x))
    subst hx
    exact SameArch_equiv.refl _
  · have hx : x ≠ 0 := by
      intro hx0
      obtain ⟨N, _, h2⟩ := h
      exact hy (abs_eq_zero.mp (le_antisymm (by simpa [hx0] using h2) (abs_nonneg y)))
    rw [SameArch_iff_IsUnitVal_div (inv_ne_zero hy), div_eq_mul_inv]
    have key : IsUnitVal (x * y⁻¹) :=
      (SameArch_iff_IsUnitVal_mul_inv hy).mp h
    have key2 : IsUnitVal ((x * y⁻¹)⁻¹) := IsUnitVal_inv key
    rw [mul_inv_rev, inv_inv] at key2
    simpa [mul_comm, inv_inv] using key2

/-- The archimedean class is power-stable. -/
theorem SameArch_pow {x y : K} (h : SameArch x y) (n : ℕ) :
    SameArch (x ^ n) (y ^ n) := by
  induction n with
  | zero => simpa using (SameArch_equiv.refl (1 : K))
  | succ n ih => rw [pow_succ, pow_succ]; exact SameArch_mul ih h

end SameArchAlg

end Work.WilC5
