import Mathlib
import Submission.Work.MotK.TGen.ZPlaneDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TGen

open MvPolynomial

/-- The `x₁`-degree of the elimination coefficient `zpA = b³h·x₀ − a³h·x₁²` is `2`: the `x₁²`
term dominates the `x₁⁰` term `b³h·x₀`. -/
private lemma degreeOf_one_zpA (K : Type) [Field K] (a b h : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    MvPolynomial.degreeOf (1 : Fin 2) (zpA K a b h) = 2 := by
  have hP : MvPolynomial.degreeOf (1 : Fin 2)
      (MvPolynomial.C (b ^ 3 * h) * MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K) = 0 := by
    rw [MvPolynomial.degreeOf_mul_eq
      (MvPolynomial.C_ne_zero.mpr (mul_ne_zero (pow_ne_zero 3 hb) hh))
      (MvPolynomial.X_ne_zero 0)]
    rw [MvPolynomial.degreeOf_C, MvPolynomial.degreeOf_X_of_ne (by decide)]
  have hQ : MvPolynomial.degreeOf (1 : Fin 2)
      (MvPolynomial.C (a ^ 3 * h) * MvPolynomial.X (1 : Fin 2) ^ 2 : MvPolynomial (Fin 2) K) = 2 := by
    rw [MvPolynomial.degreeOf_mul_eq
      (MvPolynomial.C_ne_zero.mpr (mul_ne_zero (pow_ne_zero 3 ha) hh))
      (pow_ne_zero 2 (MvPolynomial.X_ne_zero 1))]
    rw [MvPolynomial.degreeOf_C, MvPolynomial.degreeOf_X_self_pow, zero_add]
  have hQneg : MvPolynomial.degreeOf (1 : Fin 2)
      (-(MvPolynomial.C (a ^ 3 * h) * MvPolynomial.X (1 : Fin 2) ^ 2) :
        MvPolynomial (Fin 2) K) = 2 := by
    rw [MvPolynomial.degreeOf_neg, hQ]
  have hsplit : zpA K a b h
      = -(MvPolynomial.C (a ^ 3 * h) * MvPolynomial.X (1 : Fin 2) ^ 2)
        + MvPolynomial.C (b ^ 3 * h) * MvPolynomial.X (0 : Fin 2) := by
    rw [zpA]; ring
  rw [hsplit,
    MvPolynomial.degreeOf_add_eq_of_degreeOf_lt
      (p := -(MvPolynomial.C (a ^ 3 * h) * MvPolynomial.X (1 : Fin 2) ^ 2))
      (q := MvPolynomial.C (b ^ 3 * h) * MvPolynomial.X (0 : Fin 2))
      (by rw [hP, hQneg]; norm_num)]
  exact hQneg

/-- The `x₁`-degree of the plane eliminant `ZElim2` is `5`: the term `−a⁶b²h·x₁⁵` dominates the
remaining terms, whose `x₁`-degrees are at most `3` (and the coefficient `a⁶b²h` is nonzero). -/
private lemma degreeOf_one_ZElim2 (K : Type) [Field K] (a b h : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    MvPolynomial.degreeOf (1 : Fin 2) (Work.MotK.TwCensus.ZElim2 a b h) = 5 := by
  set B1 : MvPolynomial (Fin 2) K :=
    MvPolynomial.C (a * b ^ 7 * h ^ 2) * (MvPolynomial.X (0 : Fin 2)) ^ 5 with hB1
  set B2 : MvPolynomial (Fin 2) K :=
    MvPolynomial.C (b ^ 3 * h * (3 * a ^ 5 + b ^ 5)) * (MvPolynomial.X (0 : Fin 2)) ^ 2
      * MvPolynomial.X (1 : Fin 2) with hB2
  set B3 : MvPolynomial (Fin 2) K :=
    MvPolynomial.C (a ^ 3 * h * (a ^ 5 + 2 * b ^ 5)) * MvPolynomial.X (0 : Fin 2)
      * (MvPolynomial.X (1 : Fin 2)) ^ 3 with hB3
  set B4 : MvPolynomial (Fin 2) K := MvPolynomial.C (a ^ 6 * b ^ 2) with hB4
  set T4 : MvPolynomial (Fin 2) K :=
    MvPolynomial.C (a ^ 6 * b ^ 2 * h) * (MvPolynomial.X (1 : Fin 2)) ^ 5 with hT4def
  have hT4 : MvPolynomial.degreeOf (1 : Fin 2) T4 = 5 := by
    rw [hT4def, MvPolynomial.degreeOf_mul_eq
      (MvPolynomial.C_ne_zero.mpr
        (mul_ne_zero (mul_ne_zero (pow_ne_zero 6 ha) (pow_ne_zero 2 hb)) hh))
      (pow_ne_zero 5 (MvPolynomial.X_ne_zero 1))]
    rw [MvPolynomial.degreeOf_C, MvPolynomial.degreeOf_X_self_pow, zero_add]
  have b1 : MvPolynomial.degreeOf (1 : Fin 2) B1 ≤ 3 := by
    rw [hB1]
    refine le_trans (MvPolynomial.degreeOf_C_mul_le _ 1 (a * b ^ 7 * h ^ 2)) ?_
    rw [MvPolynomial.degreeOf_X_pow_of_ne 5 (by decide)]
    norm_num
  have b2 : MvPolynomial.degreeOf (1 : Fin 2) B2 ≤ 3 := by
    rw [hB2]
    refine le_trans (MvPolynomial.degreeOf_mul_le 1 _ (MvPolynomial.X (1 : Fin 2))) ?_
    have h1 : MvPolynomial.degreeOf (1 : Fin 2)
        (MvPolynomial.C (b ^ 3 * h * (3 * a ^ 5 + b ^ 5)) *
          (MvPolynomial.X (0 : Fin 2)) ^ 2 : MvPolynomial (Fin 2) K) ≤ 0 := by
      refine le_trans (MvPolynomial.degreeOf_C_mul_le _ 1 _) ?_
      rw [MvPolynomial.degreeOf_X_pow_of_ne 2 (by decide)]
    have h2 : MvPolynomial.degreeOf (1 : Fin 2)
        (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) = 1 :=
      MvPolynomial.degreeOf_X_self _
    omega
  have b3 : MvPolynomial.degreeOf (1 : Fin 2) B3 ≤ 3 := by
    rw [hB3]
    refine le_trans (MvPolynomial.degreeOf_mul_le 1 _ ((MvPolynomial.X (1 : Fin 2)) ^ 3)) ?_
    have h1 : MvPolynomial.degreeOf (1 : Fin 2)
        (MvPolynomial.C (a ^ 3 * h * (a ^ 5 + 2 * b ^ 5)) *
          (MvPolynomial.X (0 : Fin 2)) : MvPolynomial (Fin 2) K) ≤ 0 := by
      refine le_trans (MvPolynomial.degreeOf_C_mul_le _ 1 _) ?_
      rw [MvPolynomial.degreeOf_X_of_ne (by decide : (1 : Fin 2) ≠ 0)]
    have h2 : MvPolynomial.degreeOf (1 : Fin 2)
        ((MvPolynomial.X (1 : Fin 2)) ^ 3 : MvPolynomial (Fin 2) K) = 3 :=
      MvPolynomial.degreeOf_X_self_pow _ _
    omega
  have b4 : MvPolynomial.degreeOf (1 : Fin 2) B4 ≤ 3 := by
    rw [hB4, MvPolynomial.degreeOf_C]
    norm_num
  have hAB : MvPolynomial.degreeOf (1 : Fin 2) (B1 - B2 + B3 + B4) ≤ 3 := by
    have e1 : MvPolynomial.degreeOf (1 : Fin 2) (B1 - B2) ≤ 3 := by
      refine le_trans (MvPolynomial.degreeOf_sub_le 1 B1 B2) ?_
      rw [max_le_iff]
      exact ⟨b1, b2⟩
    have e2 : MvPolynomial.degreeOf (1 : Fin 2) ((B1 - B2) + B3) ≤ 3 := by
      refine le_trans (MvPolynomial.degreeOf_add_le 1 _ _) ?_
      rw [max_le_iff]
      exact ⟨e1, b3⟩
    have e3 : MvPolynomial.degreeOf (1 : Fin 2) (((B1 - B2) + B3) + B4) ≤ 3 := by
      refine le_trans (MvPolynomial.degreeOf_add_le 1 _ _) ?_
      rw [max_le_iff]
      exact ⟨e2, b4⟩
    exact e3
  have hdef : Work.MotK.TwCensus.ZElim2 a b h = (B1 - B2 + B3 + B4) - T4 := by
    rw [Work.MotK.TwCensus.ZElim2, hB1, hB2, hB3, hB4, hT4def]
    first | refl_ring1 | ring
  rw [hdef, sub_eq_add_neg, add_comm,
    MvPolynomial.degreeOf_add_eq_of_degreeOf_lt
      (p := -T4) (q := B1 - B2 + B3 + B4)
      (by rw [MvPolynomial.degreeOf_neg, hT4]; omega)]
  rw [MvPolynomial.degreeOf_neg, hT4]

theorem zpA_notMem_span (K : Type) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) : zpA K a b h ∉ Ideal.span ({Work.MotK.TwCensus.ZElim2 a b h} : Set (MvPolynomial (Fin 2) K)) := by
  have hzpA : MvPolynomial.degreeOf (1 : Fin 2) (zpA K a b h) = 2 :=
    degreeOf_one_zpA K a b h ha hb hh
  have hZ : MvPolynomial.degreeOf (1 : Fin 2) (Work.MotK.TwCensus.ZElim2 a b h) = 5 :=
    degreeOf_one_ZElim2 K a b h ha hb hh
  intro hmem
  rw [Ideal.mem_span_singleton] at hmem
  obtain ⟨q, hq⟩ := hmem
  have hZne : Work.MotK.TwCensus.ZElim2 a b h ≠ 0 :=
    MvPolynomial.ne_zero_of_degreeOf_ne_zero (by rw [hZ]; norm_num)
  have hzne : zpA K a b h ≠ 0 :=
    MvPolynomial.ne_zero_of_degreeOf_ne_zero (by rw [hzpA]; norm_num)
  have hqne : q ≠ 0 := by
    rintro rfl
    simp at hq
    exact hzne hq
  have hmul := MvPolynomial.degreeOf_mul_eq (n := (1 : Fin 2))
    (p := Work.MotK.TwCensus.ZElim2 a b h) (q := q) hZne hqne
  rw [← hq, hzpA, hZ] at hmul
  omega

end Work.MotK.TGen
