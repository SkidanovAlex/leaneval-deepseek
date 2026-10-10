import Mathlib
import Submission.Work.MotK.TwCensus.Defs
import Submission.Work.MotK.TwCensus.ZTwist
import Submission.Work.MotK.TwCensus.TrdegQuotientTwo
import Submission.Work.MotV.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

set_option maxHeartbeats 4000000

namespace Work.MotK.TGen

open MvPolynomial

abbrev zEmb : Fin 2 → Fin 3 := ![(1 : Fin 3), (2 : Fin 3)]

noncomputable def zpA (K : Type) [Field K] (a b h : K) : MvPolynomial (Fin 2) K :=
  C (b ^(3:ℕ) * h) * X 0 - C (a ^(3:ℕ) * h) * (X 1) ^(2:ℕ)

noncomputable def zpC (K : Type) [Field K] (a b h : K) : MvPolynomial (Fin 2) K :=
  C (a ^(2:ℕ) * b) - C (a * b ^(2:ℕ) * h) * (X 0) ^(2:ℕ) * X 1

noncomputable def zA (K : Type) [Field K] (a b h : K) : MvPolynomial (Fin 3) K :=
  C (b ^(3:ℕ) * h) * X 1 - C (a ^(3:ℕ) * h) * (X 2) ^(2:ℕ)

noncomputable def zC (K : Type) [Field K] (a b h : K) : MvPolynomial (Fin 3) K :=
  C (a ^(2:ℕ) * b) - C (a * b ^(2:ℕ) * h) * (X 1) ^(2:ℕ) * X 2

noncomputable def zB (K : Type) [Field K] (a b h : K) : MvPolynomial (Fin 3) K :=
  zA K a b h * X 0 - zC K a b h

noncomputable def zg (K : Type) [Field K] (a b h : K) : MvPolynomial (Fin 3) K :=
  MvPolynomial.rename zEmb (Work.MotK.TwCensus.ZElim2 a b h)

variable {K : Type} [Field K]

theorem zA_eq_rename (a b h : K) : zA K a b h = MvPolynomial.rename zEmb (zpA K a b h) := by
  simp [zA, zpA, MvPolynomial.rename_X]

theorem zC_eq_rename (a b h : K) : zC K a b h = MvPolynomial.rename zEmb (zpC K a b h) := by
  simp [zC, zpC, MvPolynomial.rename_X]

theorem zg_eq_ZElim (a b h : K) : zg K a b h = Work.MotK.TwCensus.ZElim a b h := by
  rw [zg, Work.MotK.TwCensus.ZElim, Work.MotK.TwCensus.ZElim2]
  simp only [MvPolynomial.rename_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    map_add, map_sub, map_mul, map_pow, MvPolynomial.rename_C]

theorem zB_eq (a b h : K) :
    zB K a b h = MvPolynomial.rename zEmb (zpA K a b h) * X 0
      - MvPolynomial.rename zEmb (zpC K a b h) := by
  rw [zB, zA_eq_rename, zC_eq_rename]

theorem zcub_three_eq (a b h : K) :
    Work.MotK.TwCensus.Zcub a b h 3 = -(C b) * zB K a b h := by
  rw [Work.MotK.TwCensus.Zcub_three, zB, zA, zC]

theorem cert0 (a b h : K) :
    (zA K a b h)^(2:ℕ) * Work.MotK.TwCensus.Zcub a b h 0
      = (C (a*b*h^(2:ℕ)) * (-(C (a^(5:ℕ)*h)) * X 0 * (X 2)^(3:ℕ) + C (a^(4:ℕ)*b) * X 2
            + C (a^(2:ℕ)*b^(3:ℕ)*h) * X 0 * X 1 * X 2 - C (b^(5:ℕ)*h) * (X 1)^(3:ℕ))) * zB K a b h
        + (C (a*b*h^(2:ℕ)) * X 2) * zg K a b h := by
  rw [zB, zA, zC, zg_eq_ZElim, Work.MotK.TwCensus.ZElim,
    show Work.MotK.TwCensus.Zcub a b h 0
      = Work.MotK.kleinTwR0 (C a) (C b) (C h) (Work.MotK.chart3 K) from rfl,
    Work.MotK.kleinTwR0]
  simp only [Work.MotK.TwCensus.chart3_zero, Work.MotK.TwCensus.chart3_one,
    Work.MotK.TwCensus.chart3_two, Work.MotK.TwCensus.chart3_three,
    Work.MotK.TwCensus.chart3_four, C_mul, C_pow, C_add, map_ofNat,
    MvPolynomial.rename_X, Matrix.cons_val_zero, Matrix.cons_val_one, map_sub]
  first | refl_ring1 | ring

theorem cert1 (a b h : K) :
    (zA K a b h)^(2:ℕ) * Work.MotK.TwCensus.Zcub a b h 1
      = (-(C (a*b*h^(2:ℕ))) * (C (a^(5:ℕ)) * (X 2)^(2:ℕ) - C (a^(3:ℕ)*b^(2:ℕ)*h) * X 0 * X 1 * (X 2)^(2:ℕ)
            - C (a*b^(4:ℕ)*h) * (X 1)^(3:ℕ) * X 2 + C (b^(5:ℕ)*h) * X 0 * (X 1)^(2:ℕ))) * zB K a b h
        + (-(C (a^(2:ℕ)*h^(2:ℕ)) * (X 2)^(2:ℕ))) * zg K a b h := by
  rw [zB, zA, zC, zg_eq_ZElim, Work.MotK.TwCensus.ZElim,
    show Work.MotK.TwCensus.Zcub a b h 1
      = Work.MotK.kleinTwR1 (C a) (C b) (C h) (Work.MotK.chart3 K) from rfl,
    Work.MotK.kleinTwR1]
  simp only [Work.MotK.TwCensus.chart3_zero, Work.MotK.TwCensus.chart3_one,
    Work.MotK.TwCensus.chart3_two, Work.MotK.TwCensus.chart3_three,
    Work.MotK.TwCensus.chart3_four, C_mul, C_pow, C_add, map_ofNat,
    MvPolynomial.rename_X, Matrix.cons_val_zero, Matrix.cons_val_one, map_sub]
  first | refl_ring1 | ring

theorem cert2 (a b h : K) :
    (zA K a b h)^(3:ℕ) * Work.MotK.TwCensus.Zcub a b h 2
      = (C (b^(2:ℕ)*h^(2:ℕ)) * (C (a^(8:ℕ)*h^(2:ℕ)) * (X 0)^(2:ℕ) * (X 2)^(4:ℕ) - C (a^(7:ℕ)*b*h) * X 0 * (X 2)^(2:ℕ)
            + C (a^(6:ℕ)*b^(2:ℕ)*h^(2:ℕ)) * X 0 * X 1^(2:ℕ) * (X 2)^(3:ℕ) - C (a^(6:ℕ)*b^(2:ℕ)*h) * (X 2)^(5:ℕ) + C (a^(6:ℕ)*b^(2:ℕ))
            - C (2*a^(5:ℕ)*b^(3:ℕ)*h^(2:ℕ)) * (X 0)^(2:ℕ) * X 1 * (X 2)^(2:ℕ) - C (2*a^(5:ℕ)*b^(3:ℕ)*h) * (X 1)^(2:ℕ) * X 2
            + C (a^(4:ℕ)*b^(4:ℕ)*h^(2:ℕ)) * (X 1)^(4:ℕ) * (X 2)^(2:ℕ) + C (a^(4:ℕ)*b^(4:ℕ)*h) * X 0 * X 1
            - C (a^(3:ℕ)*b^(5:ℕ)*h^(2:ℕ)) * X 0 * (X 1)^(3:ℕ) * X 2 + C (2*a^(3:ℕ)*b^(5:ℕ)*h) * X 1 * (X 2)^(3:ℕ)
            + C (a^(2:ℕ)*b^(6:ℕ)*h^(2:ℕ)) * (X 0)^(2:ℕ) * (X 1)^(2:ℕ) - C (b^(8:ℕ)*h) * (X 1)^(2:ℕ) * X 2)) * zB K a b h
        + (-(C (a^(2:ℕ)*b*h^(2:ℕ))) * (C (a^(2:ℕ)*h) * X 1 * (X 2)^(3:ℕ) - C (b^(2:ℕ)))) * zg K a b h := by
  rw [zB, zA, zC, zg_eq_ZElim, Work.MotK.TwCensus.ZElim,
    show Work.MotK.TwCensus.Zcub a b h 2
      = Work.MotK.kleinTwR2 (C a) (C b) (C h) (Work.MotK.chart3 K) from rfl,
    Work.MotK.kleinTwR2]
  simp only [Work.MotK.TwCensus.chart3_zero, Work.MotK.TwCensus.chart3_one,
    Work.MotK.TwCensus.chart3_two, Work.MotK.TwCensus.chart3_three,
    Work.MotK.TwCensus.chart3_four, C_mul, C_pow, C_add, map_ofNat,
    MvPolynomial.rename_X, Matrix.cons_val_zero, Matrix.cons_val_one, map_sub]
  first | refl_ring1 | ring

theorem cert4 (a b h : K) :
    (zA K a b h)^(2:ℕ) * Work.MotK.TwCensus.Zcub a b h 4
      = (C (a^(3:ℕ)*h) * (C (a^(4:ℕ)*h) * X 1 * (X 2)^(3:ℕ) - C (a^(3:ℕ)*b*h) * X 0 * (X 2)^(2:ℕ) + C (a^(2:ℕ)*b^(2:ℕ))
            - C (2*a*b^(3:ℕ)*h) * (X 1)^(2:ℕ) * X 2 + C (b^(4:ℕ)*h) * X 0 * X 1)) * zB K a b h
        + (C (a*b*h)) * zg K a b h := by
  rw [zB, zA, zC, zg_eq_ZElim, Work.MotK.TwCensus.ZElim,
    show Work.MotK.TwCensus.Zcub a b h 4
      = Work.MotK.kleinTwR4 (C a) (C b) (C h) (Work.MotK.chart3 K) from rfl,
    Work.MotK.kleinTwR4]
  simp only [Work.MotK.TwCensus.chart3_zero, Work.MotK.TwCensus.chart3_one,
    Work.MotK.TwCensus.chart3_two, Work.MotK.TwCensus.chart3_three,
    Work.MotK.TwCensus.chart3_four, C_mul, C_pow, C_add, map_ofNat,
    MvPolynomial.rename_X, Matrix.cons_val_zero, Matrix.cons_val_one, map_sub]
  first | refl_ring1 | ring

abbrev ZD (K : Type) [Field K] (a b h : K) : Type :=
  MvPolynomial (Fin 2) K ⧸ Ideal.span {Work.MotK.TwCensus.ZElim2 a b h}

abbrev ZF (K : Type) [Field K] (a b h : K) : Type := FractionRing (ZD K a b h)

/-- `degreeOf 0 (zpA) = 1`: only the `b³h·X₀` term contributes in the variable `X₀`. -/
private lemma degreeOf_zpA (K : Type) [Field K] (a b h : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    MvPolynomial.degreeOf (0 : Fin 2) (Work.MotK.TGen.zpA K a b h) = 1 := by
  have hP : MvPolynomial.degreeOf (0 : Fin 2)
      (MvPolynomial.C (b ^(3:ℕ) * h) * MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K) = 1 := by
    rw [MvPolynomial.degreeOf_mul_eq
      (MvPolynomial.C_ne_zero.mpr (mul_ne_zero (pow_ne_zero 3 hb) hh))
      (MvPolynomial.X_ne_zero 0)]
    rw [MvPolynomial.degreeOf_C, MvPolynomial.degreeOf_X_self]
  have hQ : MvPolynomial.degreeOf (0 : Fin 2)
      (MvPolynomial.C (a ^(3:ℕ) * h) * MvPolynomial.X (1 : Fin 2) ^(2:ℕ) : MvPolynomial (Fin 2) K) = 0 := by
    rw [MvPolynomial.degreeOf_mul_eq
      (MvPolynomial.C_ne_zero.mpr (mul_ne_zero (pow_ne_zero 3 ha) hh))
      (pow_ne_zero 2 (MvPolynomial.X_ne_zero 1))]
    rw [MvPolynomial.degreeOf_C, MvPolynomial.degreeOf_X_pow_of_ne 2 (by decide), add_zero]
  have hQneg : MvPolynomial.degreeOf (0 : Fin 2)
      (-(MvPolynomial.C (a ^(3:ℕ) * h) * MvPolynomial.X (1 : Fin 2) ^(2:ℕ)) :
        MvPolynomial (Fin 2) K) = 0 := by
    rw [show MvPolynomial.degreeOf (0 : Fin 2)
          (-(MvPolynomial.C (a ^(3:ℕ) * h) * MvPolynomial.X (1 : Fin 2) ^(2:ℕ)) : MvPolynomial (Fin 2) K)
        = MvPolynomial.degreeOf (0 : Fin 2)
          (MvPolynomial.C (a ^(3:ℕ) * h) * MvPolynomial.X (1 : Fin 2) ^(2:ℕ) : MvPolynomial (Fin 2) K)
        from by simp [MvPolynomial.degreeOf_def]]
    exact hQ
  calc MvPolynomial.degreeOf (0 : Fin 2) (Work.MotK.TGen.zpA K a b h)
      = MvPolynomial.degreeOf (0 : Fin 2)
        ((MvPolynomial.C (b ^(3:ℕ) * h) * MvPolynomial.X (0 : Fin 2))
          + (-(MvPolynomial.C (a ^(3:ℕ) * h) * MvPolynomial.X (1 : Fin 2) ^(2:ℕ))) :
            MvPolynomial (Fin 2) K) := by
          rw [Work.MotK.TGen.zpA, sub_eq_add_neg]
    _ = MvPolynomial.degreeOf (0 : Fin 2)
        (MvPolynomial.C (b ^(3:ℕ) * h) * MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K) :=
        MvPolynomial.degreeOf_add_eq_of_degreeOf_lt (by rw [hQneg, hP]; norm_num)
    _ = 1 := hP

/-- `degreeOf 0 (ZElim2) = 5`: the `a·b⁷h²·X₀⁵` term is dominant in the variable `X₀`. -/
private lemma degreeOf_ZElim2 (K : Type) [Field K] (a b h : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    MvPolynomial.degreeOf (0 : Fin 2) (Work.MotK.TwCensus.ZElim2 a b h) = 5 := by
  rw [Work.MotK.TwCensus.ZElim2]
  set A1 : MvPolynomial (Fin 2) K :=
    MvPolynomial.C (a * b ^(7:ℕ) * h ^(2:ℕ)) * MvPolynomial.X (0 : Fin 2) ^(5:ℕ) with hA1
  set A2 : MvPolynomial (Fin 2) K :=
    MvPolynomial.C (b ^(3:ℕ) * h * (3 * a ^(5:ℕ) + b ^(5:ℕ))) * MvPolynomial.X (0 : Fin 2) ^(2:ℕ)
      * MvPolynomial.X (1 : Fin 2) with hA2
  set A3 : MvPolynomial (Fin 2) K :=
    MvPolynomial.C (a ^(3:ℕ) * h * (a ^(5:ℕ) + 2 * b ^(5:ℕ))) * MvPolynomial.X (0 : Fin 2)
      * MvPolynomial.X (1 : Fin 2) ^(3:ℕ) with hA3
  set A4 : MvPolynomial (Fin 2) K :=
    MvPolynomial.C (a ^(6:ℕ) * b ^(2:ℕ) * h) * MvPolynomial.X (1 : Fin 2) ^(5:ℕ) with hA4
  set A5 : MvPolynomial (Fin 2) K := MvPolynomial.C (a ^(6:ℕ) * b ^(2:ℕ)) with hA5
  have hneg : ∀ p : MvPolynomial (Fin 2) K,
      MvPolynomial.degreeOf (0 : Fin 2) (-p) = MvPolynomial.degreeOf (0 : Fin 2) p := by
    intro p; simp [MvPolynomial.degreeOf_def]
  have h1 : MvPolynomial.degreeOf (0 : Fin 2) A1 = 5 := by
    rw [hA1, MvPolynomial.degreeOf_mul_eq
      (MvPolynomial.C_ne_zero.mpr
        (mul_ne_zero (mul_ne_zero ha (pow_ne_zero 7 hb)) (pow_ne_zero 2 hh)))
      (pow_ne_zero 5 (MvPolynomial.X_ne_zero 0))]
    rw [MvPolynomial.degreeOf_C, MvPolynomial.degreeOf_X_self_pow]
  have b2 : MvPolynomial.degreeOf (0 : Fin 2) A2 ≤ 2 := by
    have e1 := MvPolynomial.degreeOf_mul_le (0 : Fin 2)
      (MvPolynomial.C (b ^(3:ℕ) * h * (3 * a ^(5:ℕ) + b ^(5:ℕ))) * MvPolynomial.X (0 : Fin 2) ^(2:ℕ) :
        MvPolynomial (Fin 2) K)
      (MvPolynomial.X (1 : Fin 2))
    have e2 := MvPolynomial.degreeOf_C_mul_le (MvPolynomial.X (0 : Fin 2) ^(2:ℕ) :
      MvPolynomial (Fin 2) K) (0 : Fin 2) (b ^(3:ℕ) * h * (3 * a ^(5:ℕ) + b ^(5:ℕ)))
    have e3 : MvPolynomial.degreeOf (0 : Fin 2)
        (MvPolynomial.X (0 : Fin 2) ^(2:ℕ) : MvPolynomial (Fin 2) K) = 2 :=
      MvPolynomial.degreeOf_X_self_pow _ _
    have e4 : MvPolynomial.degreeOf (0 : Fin 2)
        (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) = 0 :=
      MvPolynomial.degreeOf_X_of_ne (by decide)
    rw [hA2]
    omega
  have b3 : MvPolynomial.degreeOf (0 : Fin 2) A3 ≤ 1 := by
    have e1 := MvPolynomial.degreeOf_mul_le (0 : Fin 2)
      (MvPolynomial.C (a ^(3:ℕ) * h * (a ^(5:ℕ) + 2 * b ^(5:ℕ))) * MvPolynomial.X (0 : Fin 2) :
        MvPolynomial (Fin 2) K)
      (MvPolynomial.X (1 : Fin 2) ^(3:ℕ))
    have e2 := MvPolynomial.degreeOf_C_mul_le (MvPolynomial.X (0 : Fin 2) :
      MvPolynomial (Fin 2) K) (0 : Fin 2) (a ^(3:ℕ) * h * (a ^(5:ℕ) + 2 * b ^(5:ℕ)))
    have e3 : MvPolynomial.degreeOf (0 : Fin 2)
        (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K) = 1 :=
      MvPolynomial.degreeOf_X_self _
    have e4 : MvPolynomial.degreeOf (0 : Fin 2)
        (MvPolynomial.X (1 : Fin 2) ^(3:ℕ) : MvPolynomial (Fin 2) K) = 0 :=
      MvPolynomial.degreeOf_X_pow_of_ne 3 (by decide)
    rw [hA3]
    omega
  have b4 : MvPolynomial.degreeOf (0 : Fin 2) A4 ≤ 0 := by
    have e1 := MvPolynomial.degreeOf_mul_le (0 : Fin 2)
      (MvPolynomial.C (a ^(6:ℕ) * b ^(2:ℕ) * h) : MvPolynomial (Fin 2) K)
      (MvPolynomial.X (1 : Fin 2) ^(5:ℕ))
    have e2 : MvPolynomial.degreeOf (0 : Fin 2)
        (MvPolynomial.C (a ^(6:ℕ) * b ^(2:ℕ) * h) : MvPolynomial (Fin 2) K) = 0 :=
      MvPolynomial.degreeOf_C _ _
    have e3 : MvPolynomial.degreeOf (0 : Fin 2)
        (MvPolynomial.X (1 : Fin 2) ^(5:ℕ) : MvPolynomial (Fin 2) K) = 0 :=
      MvPolynomial.degreeOf_X_pow_of_ne 5 (by decide)
    rw [hA4]
    omega
  have b5 : MvPolynomial.degreeOf (0 : Fin 2) A5 ≤ 0 := by
    rw [hA5]
    exact le_of_eq (MvPolynomial.degreeOf_C _ _)
  have h12 : MvPolynomial.degreeOf (0 : Fin 2) (A1 - A2) = 5 := by
    rw [sub_eq_add_neg]
    exact (MvPolynomial.degreeOf_add_eq_of_degreeOf_lt (p := A1) (q := -A2)
      (by rw [hneg]; omega)).trans h1
  have h123 : MvPolynomial.degreeOf (0 : Fin 2) (A1 - A2 + A3) = 5 := by
    rw [show A1 - A2 + A3 = (A1 - A2) + A3 from rfl]
    exact (MvPolynomial.degreeOf_add_eq_of_degreeOf_lt (p := A1 - A2) (q := A3)
      (by omega)).trans h12
  have h1234 : MvPolynomial.degreeOf (0 : Fin 2) (A1 - A2 + A3 - A4) = 5 := by
    rw [sub_eq_add_neg, show A1 - A2 + A3 = (A1 - A2) + A3 from rfl]
    exact (MvPolynomial.degreeOf_add_eq_of_degreeOf_lt (p := (A1 - A2) + A3) (q := -A4)
      (by rw [hneg]; omega)).trans h123
  exact (MvPolynomial.degreeOf_add_eq_of_degreeOf_lt (p := A1 - A2 + A3 - A4) (q := A5)
    (by omega)).trans h1234

section Model

variable (K : Type) [Field K] (a b h : K) [IsDomain (ZD K a b h)]

noncomputable def zx0 : ZF K a b h :=
  algebraMap (ZD K a b h) (ZF K a b h) (Ideal.Quotient.mk _ (X 0 : MvPolynomial (Fin 2) K))

noncomputable def zx1 : ZF K a b h :=
  algebraMap (ZD K a b h) (ZF K a b h) (Ideal.Quotient.mk _ (X 1 : MvPolynomial (Fin 2) K))

noncomputable def za1 : ZF K a b h := algebraMap (ZD K a b h) (ZF K a b h) (Ideal.Quotient.mk _ (zpA K a b h))

noncomputable def zc1 : ZF K a b h := algebraMap (ZD K a b h) (ZF K a b h) (Ideal.Quotient.mk _ (zpC K a b h))

noncomputable def zPsi : MvPolynomial (Fin 3) K →ₐ[K] ZF K a b h :=
  MvPolynomial.aeval ![zc1 K a b h * (za1 K a b h)⁻¹, zx0 K a b h, zx1 K a b h]

theorem zPsi_X0 : zPsi K a b h (X 0) = zc1 K a b h * (za1 K a b h)⁻¹ := by
  simp [zPsi]

theorem zPsi_X1 : zPsi K a b h (X 1) = zx0 K a b h := by
  simp [zPsi]

theorem zPsi_X2 : zPsi K a b h (X 2) = zx1 K a b h := by
  simp [zPsi]

/-- The `K`-algebra hom `MvPolynomial (Fin 2) K → ZF` given by the two coordinate classes. -/
theorem zPsi2_eq (p : MvPolynomial (Fin 2) K) :
    MvPolynomial.aeval ![zx0 K a b h, zx1 K a b h] p
      = algebraMap (ZD K a b h) (ZF K a b h) (Ideal.Quotient.mk _ p) := by
  have hhom : (MvPolynomial.aeval ![zx0 K a b h, zx1 K a b h] : MvPolynomial (Fin 2) K →ₐ[K] ZF K a b h)
      = (IsScalarTower.toAlgHom K (ZD K a b h) (ZF K a b h)).comp
          (Ideal.Quotient.mkₐ K (Ideal.span {Work.MotK.TwCensus.ZElim2 a b h})) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [zx0, zx1]
  exact congrArg (fun f => f p) hhom

theorem zPsi_rename (p : MvPolynomial (Fin 2) K) :
    zPsi K a b h (MvPolynomial.rename zEmb p)
      = algebraMap (ZD K a b h) (ZF K a b h) (Ideal.Quotient.mk _ p) := by
  have hhom : (zPsi K a b h).comp (MvPolynomial.rename zEmb)
      = (IsScalarTower.toAlgHom K (ZD K a b h) (ZF K a b h)).comp
          (Ideal.Quotient.mkₐ K (Ideal.span {Work.MotK.TwCensus.ZElim2 a b h})) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [zPsi, zx0, zx1]
  simpa using congrArg (fun f => f p) hhom

theorem zPsi_zA : zPsi K a b h (zA K a b h) = za1 K a b h := by
  rw [zA_eq_rename, zPsi_rename]
  rfl

theorem zPsi_zC : zPsi K a b h (zC K a b h) = zc1 K a b h := by
  rw [zC_eq_rename, zPsi_rename]
  rfl

theorem zPsi_zg : zPsi K a b h (zg K a b h) = 0 := by
  rw [zg, zPsi_rename]
  suffices hz : (Ideal.Quotient.mk (Ideal.span {Work.MotK.TwCensus.ZElim2 a b h}))
      (Work.MotK.TwCensus.ZElim2 a b h) = 0 by
    rw [hz, map_zero]
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

/-- `za1 ≠ 0` : the elimination coefficient is not in the principal ideal `(ZElim2)`. -/
theorem za1_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) : za1 K a b h ≠ 0 := by
  have hdegA : MvPolynomial.degreeOf (0 : Fin 2) (Work.MotK.TGen.zpA K a b h) = 1 :=
    degreeOf_zpA K a b h ha hb hh
  have hdegZ : MvPolynomial.degreeOf (0 : Fin 2) (Work.MotK.TwCensus.ZElim2 a b h) = 5 :=
    degreeOf_ZElim2 K a b h ha hb hh
  intro hz
  have hmk : (Ideal.Quotient.mk (Ideal.span {Work.MotK.TwCensus.ZElim2 a b h}))
      (Work.MotK.TGen.zpA K a b h) = 0 := by
    apply IsFractionRing.injective (Work.MotK.TGen.ZD K a b h) (Work.MotK.TGen.ZF K a b h)
    rw [map_zero]
    exact hz
  rw [Ideal.Quotient.eq_zero_iff_mem] at hmk
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hmk
  have hpA_ne : Work.MotK.TGen.zpA K a b h ≠ 0 :=
    MvPolynomial.ne_zero_of_degreeOf_ne_zero (by rw [hdegA]; norm_num)
  have hZ_ne : Work.MotK.TwCensus.ZElim2 a b h ≠ 0 :=
    MvPolynomial.ne_zero_of_degreeOf_ne_zero (by rw [hdegZ]; norm_num)
  have hq_ne : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hq
    exact hpA_ne hq
  have hmul := MvPolynomial.degreeOf_mul_eq (n := (0 : Fin 2))
    (p := Work.MotK.TwCensus.ZElim2 a b h) (q := q) hZ_ne hq_ne
  rw [← hq, hdegA, hdegZ] at hmul
  omega



theorem zPsi_zB (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    zPsi K a b h (zB K a b h) = 0 := by
  rw [zB_eq, map_sub, map_mul, zPsi_rename, zPsi_rename, zPsi_X0]
  rw [show zc1 K a b h = algebraMap (ZD K a b h) (ZF K a b h)
        (Ideal.Quotient.mk _ (zpC K a b h)) from rfl,
      show za1 K a b h = algebraMap (ZD K a b h) (ZF K a b h)
        (Ideal.Quotient.mk _ (zpA K a b h)) from rfl]
  rw [← mul_assoc,
    mul_comm (algebraMap (ZD K a b h) (ZF K a b h) (Ideal.Quotient.mk _ (zpA K a b h)))
      (algebraMap (ZD K a b h) (ZF K a b h) (Ideal.Quotient.mk _ (zpC K a b h))),
    mul_assoc,
    mul_inv_cancel₀ (show algebraMap (ZD K a b h) (ZF K a b h)
        (Ideal.Quotient.mk _ (zpA K a b h)) ≠ 0 from za1_ne_zero K a b h ha hb hh),
    mul_one, sub_self]

theorem ZI_le_ker_zPsi (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    Work.MotK.TwCensus.ZI a b h ≤ RingHom.ker (zPsi K a b h) := by
  rw [Work.MotK.TwCensus.ZI, Ideal.span_le]
  rintro _ ⟨k, rfl⟩
  have hA : zPsi K a b h (zA K a b h) ≠ 0 := by
    rw [zPsi_zA]; exact za1_ne_zero K a b h ha hb hh
  fin_cases k
  · have hc := congrArg (zPsi K a b h) (cert0 (K := K) a b h)
    simp only [map_add, map_mul, map_pow, zPsi_zB K a b h ha hb hh, zPsi_zg K a b h,
      mul_zero, add_zero, RingHom.mem_ker] at hc
    rcases mul_eq_zero.mp hc with hc' | hc'
    · exact absurd hc' (pow_ne_zero _ hA)
    · exact hc'
  · have hc := congrArg (zPsi K a b h) (cert1 (K := K) a b h)
    simp only [map_add, map_mul, map_pow, zPsi_zB K a b h ha hb hh, zPsi_zg K a b h,
      mul_zero, add_zero, RingHom.mem_ker] at hc
    rcases mul_eq_zero.mp hc with hc' | hc'
    · exact absurd hc' (pow_ne_zero _ hA)
    · exact hc'
  · have hc := congrArg (zPsi K a b h) (cert2 (K := K) a b h)
    simp only [map_add, map_mul, map_pow, zPsi_zB K a b h ha hb hh, zPsi_zg K a b h,
      mul_zero, add_zero, RingHom.mem_ker] at hc
    rcases mul_eq_zero.mp hc with hc' | hc'
    · exact absurd hc' (pow_ne_zero _ hA)
    · exact hc'
  · have hc := congrArg (zPsi K a b h) (zcub_three_eq (K := K) a b h)
    simp only [map_mul, map_neg, zPsi_zB K a b h ha hb hh, mul_zero, neg_zero,
      RingHom.mem_ker] at hc
    exact hc
  · have hc := congrArg (zPsi K a b h) (cert4 (K := K) a b h)
    simp only [map_add, map_mul, map_pow, zPsi_zB K a b h ha hb hh, zPsi_zg K a b h,
      mul_zero, add_zero, RingHom.mem_ker] at hc
    rcases mul_eq_zero.mp hc with hc' | hc'
    · exact absurd hc' (pow_ne_zero _ hA)
    · exact hc'


end Model

end Work.MotK.TGen
