import Mathlib
import Submission.Work.MotK.TGen.ZpgI4W4NonZeroDiv
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.ZpgWMatMulMain`

`zpgWMat` is the multiplication matrix of `zpgW4 = b⁴·y₁ - a⁴h²·y₃²` on the five standard
monomials `1, X₀, X₁, X₂, X₀X₂` over `K[X₃]`; this file proves the reduction identity *modulo*
the chart ideal `zpgI4` (spanned by the five chart quadrics `zpgQ`), which is the `hMul` input of
`Work.MotK.TGen.ZpgI4W4NonZeroDiv_of`.

The entries of `zpgWMat` contain denominators (`b⁵h²/a`, `(a⁵-b⁵)/b`, …).  Multiplying the whole
relation by the unit `C u`, `u = a³b³h²`, clears all of them: the lemmas `scale_1 … scale_15`
merge every product `C u * C c` into a single `C (u*c)` with `u*c` a *polynomial* in `a,b,h`
(`zpgWMatS` is the resulting matrix and `zpgWMatS_spec` the comparison with `C u • zpgWMat`).
After that every scalar is a polynomial, so `simp only [map_mul, map_pow, …]` pushes `C` down to
the atoms `C a, C b, C h` and `ring` finishes.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

namespace Work.MotK.TGen

open MvPolynomial

/-! ## Unfolding `zpgEmb` on the entries of `zpgWMat` -/

section CommSemiring
variable {K : Type} [CommSemiring K]

theorem zpgEmb_mul (p q : MvPolynomial (Fin 1) K) :
    zpgEmb K (p * q) = zpgEmb K p * zpgEmb K q := map_mul _ _ _

theorem zpgEmb_C (c : K) : zpgEmb K (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [zpgEmb]

theorem zpgEmb_X0 : zpgEmb K (MvPolynomial.X 0) = MvPolynomial.X 3 := by
  simp [zpgEmb]

theorem zpgEmb_pow (p : MvPolynomial (Fin 1) K) (d : ℕ) :
    zpgEmb K (p ^ d) = zpgEmb K p ^ d := map_pow _ _ _

theorem zpgEmb_zero : zpgEmb K (0 : MvPolynomial (Fin 1) K) = 0 := map_zero _

end CommSemiring

/-! ## Clearing the denominators of `zpgWMat` by the unit `C (a³b³h²)` -/

section Scale
variable {K : Type} [Field K]

theorem scale_1 (a b h : K) :
    (MvPolynomial.C (a^(3:ℕ)*b^(3:ℕ)*h^(2:ℕ)) : MvPolynomial (Fin 4) K) * MvPolynomial.C (b^(4:ℕ))
      = MvPolynomial.C (a^(3:ℕ)*b^(7:ℕ)*h^(2:ℕ)) := by
  rw [← MvPolynomial.C_mul]; congr 1; ring

theorem scale_2 (a b h : K) :
    (MvPolynomial.C (a^(3:ℕ)*b^(3:ℕ)*h^(2:ℕ)) : MvPolynomial (Fin 4) K) * MvPolynomial.C (a^(4:ℕ)*h^(2:ℕ))
      = MvPolynomial.C (a^(7:ℕ)*b^(3:ℕ)*h^(4:ℕ)) := by
  rw [← MvPolynomial.C_mul]; congr 1; ring

theorem scale_3 (a b h : K) :
    (MvPolynomial.C (a^(3:ℕ)*b^(3:ℕ)*h^(2:ℕ)) : MvPolynomial (Fin 4) K) * MvPolynomial.C (a^(2:ℕ)*b^(2:ℕ)*h^(4:ℕ))
      = MvPolynomial.C (a^(5:ℕ)*b^(5:ℕ)*h^(6:ℕ)) := by
  rw [← MvPolynomial.C_mul]; congr 1; ring

theorem scale_4 (a b h : K) (ha : a ≠ 0) :
    (MvPolynomial.C (a^(3:ℕ)*b^(3:ℕ)*h^(2:ℕ)) : MvPolynomial (Fin 4) K) * MvPolynomial.C (b^(5:ℕ)*h^(2:ℕ)/a)
      = MvPolynomial.C (a^(2:ℕ)*b^(8:ℕ)*h^(4:ℕ)) := by
  rw [← MvPolynomial.C_mul]; congr 1; field_simp

theorem scale_5 (a b h : K) :
    (MvPolynomial.C (a^(3:ℕ)*b^(3:ℕ)*h^(2:ℕ)) : MvPolynomial (Fin 4) K) * MvPolynomial.C (a^(2:ℕ)*b^(2:ℕ))
      = MvPolynomial.C (a^(5:ℕ)*b^(5:ℕ)*h^(2:ℕ)) := by
  rw [← MvPolynomial.C_mul]; congr 1; ring

theorem scale_6 (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0) :
    (MvPolynomial.C (a^(3:ℕ)*b^(3:ℕ)*h^(2:ℕ)) : MvPolynomial (Fin 4) K)
        * MvPolynomial.C (b*(a^(5:ℕ)-b^(5:ℕ))/(a^(2:ℕ)*h^(2:ℕ)))
      = MvPolynomial.C (a*b^(4:ℕ)*(a^(5:ℕ)-b^(5:ℕ))) := by
  rw [← MvPolynomial.C_mul]; congr 1; field_simp

theorem scale_7 (a b h : K) (hb : b ≠ 0) :
    (MvPolynomial.C (a^(3:ℕ)*b^(3:ℕ)*h^(2:ℕ)) : MvPolynomial (Fin 4) K) * MvPolynomial.C (-((a^(5:ℕ)-b^(5:ℕ))/b))
      = MvPolynomial.C (-(a^(3:ℕ)*b^(2:ℕ)*h^(2:ℕ)*(a^(5:ℕ)-b^(5:ℕ)))) := by
  rw [← MvPolynomial.C_mul]; congr 1; field_simp

theorem scale_8 (a b h : K) :
    (MvPolynomial.C (a^(3:ℕ)*b^(3:ℕ)*h^(2:ℕ)) : MvPolynomial (Fin 4) K) * MvPolynomial.C (a*b^(3:ℕ)*h^(2:ℕ))
      = MvPolynomial.C (a^(4:ℕ)*b^(6:ℕ)*h^(4:ℕ)) := by
  rw [← MvPolynomial.C_mul]; congr 1; ring

theorem scale_9 (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    (MvPolynomial.C (a^(3:ℕ)*b^(3:ℕ)*h^(2:ℕ)) : MvPolynomial (Fin 4) K)
        * MvPolynomial.C (-((a^(10:ℕ)-3*a^(5:ℕ)*b^(5:ℕ)+b^(10:ℕ))/(a^(3:ℕ)*b^(3:ℕ))))
      = MvPolynomial.C (-(h^(2:ℕ)*(a^(10:ℕ)-3*a^(5:ℕ)*b^(5:ℕ)+b^(10:ℕ)))) := by
  rw [← MvPolynomial.C_mul]; congr 1; field_simp

theorem scale_10 (a b h : K) :
    (MvPolynomial.C (a^(3:ℕ)*b^(3:ℕ)*h^(2:ℕ)) : MvPolynomial (Fin 4) K) * MvPolynomial.C (a^(3:ℕ)*b*h^(2:ℕ))
      = MvPolynomial.C (a^(6:ℕ)*b^(4:ℕ)*h^(4:ℕ)) := by
  rw [← MvPolynomial.C_mul]; congr 1; ring

theorem scale_11 (a b h : K) (ha : a ≠ 0) :
    (MvPolynomial.C (a^(3:ℕ)*b^(3:ℕ)*h^(2:ℕ)) : MvPolynomial (Fin 4) K) * MvPolynomial.C ((a^(5:ℕ)-b^(5:ℕ))/a)
      = MvPolynomial.C (a^(2:ℕ)*b^(3:ℕ)*h^(2:ℕ)*(a^(5:ℕ)-b^(5:ℕ))) := by
  rw [← MvPolynomial.C_mul]; congr 1; field_simp

theorem scale_12 (a b h : K) (hb : b ≠ 0) :
    (MvPolynomial.C (a^(3:ℕ)*b^(3:ℕ)*h^(2:ℕ)) : MvPolynomial (Fin 4) K) * MvPolynomial.C (h^(2:ℕ)*(a^(5:ℕ)-2*b^(5:ℕ))/b)
      = MvPolynomial.C (a^(3:ℕ)*b^(2:ℕ)*h^(4:ℕ)*(a^(5:ℕ)-2*b^(5:ℕ))) := by
  rw [← MvPolynomial.C_mul]; congr 1; field_simp

theorem scale_13 (a b h : K) (hb : b ≠ 0) :
    (MvPolynomial.C (a^(3:ℕ)*b^(3:ℕ)*h^(2:ℕ)) : MvPolynomial (Fin 4) K)
        * MvPolynomial.C (-(a*h^(2:ℕ)*(a^(5:ℕ)-2*b^(5:ℕ))/b^(2:ℕ)))
      = MvPolynomial.C (-(a^(4:ℕ)*b*h^(4:ℕ)*(a^(5:ℕ)-2*b^(5:ℕ)))) := by
  rw [← MvPolynomial.C_mul]; congr 1; field_simp

theorem scale_14 (a b h : K) (ha : a ≠ 0) :
    (MvPolynomial.C (a^(3:ℕ)*b^(3:ℕ)*h^(2:ℕ)) : MvPolynomial (Fin 4) K) * MvPolynomial.C (-(b*(a^(5:ℕ)-b^(5:ℕ))/a^(2:ℕ)))
      = MvPolynomial.C (-(a*b^(4:ℕ)*h^(2:ℕ)*(a^(5:ℕ)-b^(5:ℕ)))) := by
  rw [← MvPolynomial.C_mul]; congr 1; field_simp

theorem scale_15 (a b h : K) :
    (MvPolynomial.C (a^(3:ℕ)*b^(3:ℕ)*h^(2:ℕ)) : MvPolynomial (Fin 4) K) * MvPolynomial.C (-(a^(2:ℕ)*b^(2:ℕ)*h^(2:ℕ)))
      = MvPolynomial.C (-(a^(5:ℕ)*b^(5:ℕ)*h^(4:ℕ))) := by
  rw [← MvPolynomial.C_mul]; congr 1; ring

end Scale

/-! ## The correspondingly scaled matrices and `zpgW4` -/

section MatS
variable {K : Type} [Field K]

/-- `zpgWMat` scaled by the unit `C (a³b³h²)`: every entry has polynomial coefficients. -/
noncomputable def zpgWMatS (a b h : K) : Matrix (Fin 5) (Fin 5) (MvPolynomial (Fin 1) K) :=
  !![0, MvPolynomial.C (a^(5:ℕ)*b^(5:ℕ)*h^(6:ℕ)) * (X 0)^(3:ℕ), MvPolynomial.C (a^(2:ℕ)*b^(8:ℕ)*h^(4:ℕ)) * (X 0)^(2:ℕ),
      MvPolynomial.C (a^(5:ℕ)*b^(5:ℕ)*h^(2:ℕ)) * X 0, MvPolynomial.C (a*b^(4:ℕ)*(a^(5:ℕ)-b^(5:ℕ)));
    MvPolynomial.C (-(a^(3:ℕ)*b^(2:ℕ)*h^(2:ℕ)*(a^(5:ℕ)-b^(5:ℕ)))), 0, 0, MvPolynomial.C (a^(4:ℕ)*b^(6:ℕ)*h^(4:ℕ)) * (X 0)^(2:ℕ),
      MvPolynomial.C (-(h^(2:ℕ)*(a^(10:ℕ)-3*a^(5:ℕ)*b^(5:ℕ)+b^(10:ℕ)))) * X 0;
    MvPolynomial.C (a^(6:ℕ)*b^(4:ℕ)*h^(4:ℕ)) * X 0, MvPolynomial.C (a^(2:ℕ)*b^(3:ℕ)*h^(2:ℕ)*(a^(5:ℕ)-b^(5:ℕ))), 0, 0,
      MvPolynomial.C (a^(3:ℕ)*b^(2:ℕ)*h^(4:ℕ)*(a^(5:ℕ)-2*b^(5:ℕ))) * (X 0)^(2:ℕ);
    0, MvPolynomial.C (-(a^(4:ℕ)*b*h^(4:ℕ)*(a^(5:ℕ)-2*b^(5:ℕ)))) * X 0, MvPolynomial.C (-(a*b^(4:ℕ)*h^(2:ℕ)*(a^(5:ℕ)-b^(5:ℕ)))), 0,
      MvPolynomial.C (a^(5:ℕ)*b^(5:ℕ)*h^(6:ℕ)) * (X 0)^(3:ℕ);
    0, 0, MvPolynomial.C (-(a^(5:ℕ)*b^(5:ℕ)*h^(4:ℕ))) * X 0, MvPolynomial.C (-(a^(3:ℕ)*b^(2:ℕ)*h^(2:ℕ)*(a^(5:ℕ)-b^(5:ℕ)))), 0]

theorem zpgWMatS_spec (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) (j i : Fin 5) :
    (MvPolynomial.C (a^(3:ℕ)*b^(3:ℕ)*h^(2:ℕ)) : MvPolynomial (Fin 4) K) * zpgEmb K (zpgWMat (K := K) a b h j i)
      = zpgEmb K (zpgWMatS (K := K) a b h j i) := by
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by fin_cases j <;> simp
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by fin_cases i <;> simp
  rcases hj with h | h | h | h | h <;> subst h <;>
    rcases hi with h | h | h | h | h <;> subst h <;>
    simp only [zpgWMat, zpgWMatS, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      Matrix.of_apply, zpgEmb_mul, zpgEmb_C, zpgEmb_X0, zpgEmb_pow, zpgEmb_zero,
      mul_one, one_mul, mul_zero, zero_mul, ← mul_assoc,
      scale_1 a b h, scale_2 a b h, scale_3 a b h, scale_4 a b h ha, scale_5 a b h,
      scale_6 a b h ha hh, scale_7 a b h hb, scale_8 a b h, scale_9 a b h ha hb,
      scale_10 a b h, scale_11 a b h ha, scale_12 a b h hb, scale_13 a b h hb,
      scale_14 a b h ha, scale_15 a b h]

theorem zpgW4S_spec (a b h : K) :
    (MvPolynomial.C (a^(3:ℕ)*b^(3:ℕ)*h^(2:ℕ)) : MvPolynomial (Fin 4) K) * zpgW4 a b h
      = MvPolynomial.C (a^(3:ℕ)*b^(7:ℕ)*h^(2:ℕ)) * (MvPolynomial.X 0)
        - MvPolynomial.C (a^(7:ℕ)*b^(3:ℕ)*h^(4:ℕ)) * (MvPolynomial.X 2)^(2:ℕ) := by
  simp only [zpgW4, mul_sub, ← mul_assoc, scale_1 a b h, scale_2 a b h]

end MatS

/-! ## The main theorem -/

theorem ZpgWMatMulMain (K : Type) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0)
    (i : Fin 5) :
    Work.MotK.TGen.zpgW4 a b h * (Work.MotK.TGen.zpgStdM (K := K) i)
      - (∑ j : Fin 5, Work.MotK.TGen.zpgEmb K (Work.MotK.TGen.zpgWMat (K := K) a b h j i)
          * Work.MotK.TGen.zpgStdM (K := K) j) ∈ Work.MotK.TGen.zpgI4 a b h := by
  classical
  have hu : (a : K)^(3:ℕ) * b^(3:ℕ) * h^(2:ℕ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 3 ha) (pow_ne_zero 3 hb)) (pow_ne_zero 2 hh)
  refine (Ideal.unit_mul_mem_iff_mem (zpgI4 a b h)
    (IsUnit.map (MvPolynomial.C : K →+* MvPolynomial (Fin 4) K)
      (isUnit_iff_ne_zero.mpr hu))).mp ?_
  -- distribute the scalar `C (a³b³h²)` over the relation
  have hdist : (MvPolynomial.C (a^(3:ℕ)*b^(3:ℕ)*h^(2:ℕ)) : MvPolynomial (Fin 4) K) *
      (zpgW4 a b h * zpgStdM (K := K) i
        - (∑ j : Fin 5, zpgEmb K (zpgWMat (K := K) a b h j i) * zpgStdM (K := K) j))
      = (MvPolynomial.C (a^(3:ℕ)*b^(3:ℕ)*h^(2:ℕ)) * zpgW4 a b h) * zpgStdM (K := K) i
        - (∑ j : Fin 5,
            (MvPolynomial.C (a^(3:ℕ)*b^(3:ℕ)*h^(2:ℕ)) * zpgEmb K (zpgWMat (K := K) a b h j i))
              * zpgStdM (K := K) j) := by
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · refl_ring1
    · exact Finset.sum_congr rfl fun j _ => by ring
  have hsum : (∑ j : Fin 5,
        (MvPolynomial.C (a^(3:ℕ)*b^(3:ℕ)*h^(2:ℕ)) * zpgEmb K (zpgWMat (K := K) a b h j i))
          * zpgStdM (K := K) j)
      = (∑ j : Fin 5,
          zpgEmb K (zpgWMatS (K := K) a b h j i) * zpgStdM (K := K) j) :=
    Finset.sum_congr rfl fun j _ => by rw [zpgWMatS_spec a b h ha hb hh j i]
  rw [hdist, zpgW4S_spec a b h, hsum]
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by fin_cases i <;> simp
  rcases hi with h | h | h | h | h
  · subst h
    have key : (MvPolynomial.C (a^(3:ℕ)*b^(7:ℕ)*h^(2:ℕ)) * (MvPolynomial.X 0)
          - MvPolynomial.C (a^(7:ℕ)*b^(3:ℕ)*h^(4:ℕ)) * (MvPolynomial.X 2)^(2:ℕ)) * zpgStdM (K := K) 0
        - (∑ j : Fin 5, zpgEmb K (zpgWMatS (K := K) a b h j 0) * zpgStdM (K := K) j)
        = MvPolynomial.C (a^(6:ℕ)*b^(2:ℕ)*h^(2:ℕ)) * zpgQ a b h 4 := by
      simp only [zpgStdM, zpgWMatS, Fin.sum_univ_five, zpgQ_zero, zpgQ_one, zpgQ_two, zpgQ_three,
        zpgQ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
        Matrix.of_apply, zpgEmb_mul, zpgEmb_C, zpgEmb_X0, zpgEmb_pow, zpgEmb_zero,
        mul_one, one_mul, mul_zero, zero_mul, zero_add, add_zero, neg_zero,
        mul_sub, mul_add, sub_mul, add_mul, mul_neg, neg_mul, neg_neg]
      simp only [map_mul, map_pow, map_add, map_sub, map_neg, map_ofNat]
      refl_ring1
    rw [key]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨4, rfl⟩)
  · subst h
    have key : (MvPolynomial.C (a^(3:ℕ)*b^(7:ℕ)*h^(2:ℕ)) * (MvPolynomial.X 0)
          - MvPolynomial.C (a^(7:ℕ)*b^(3:ℕ)*h^(4:ℕ)) * (MvPolynomial.X 2)^(2:ℕ)) * zpgStdM (K := K) 1
        - (∑ j : Fin 5, zpgEmb K (zpgWMatS (K := K) a b h j 1) * zpgStdM (K := K) j)
        = MvPolynomial.C (a^(4:ℕ)*b^(4:ℕ)*h^(4:ℕ)) * (MvPolynomial.X 3) * zpgQ a b h 2
          + MvPolynomial.C (a^(2:ℕ)*b*h^(2:ℕ)*(a^(5:ℕ)-b^(5:ℕ))) * zpgQ a b h 3
          + MvPolynomial.C (a^(6:ℕ)*b^(2:ℕ)*h^(2:ℕ)) * (MvPolynomial.X 0) * zpgQ a b h 4 := by
      simp only [zpgStdM, zpgWMatS, Fin.sum_univ_five, zpgQ_zero, zpgQ_one, zpgQ_two, zpgQ_three,
        zpgQ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
        Matrix.of_apply, zpgEmb_mul, zpgEmb_C, zpgEmb_X0, zpgEmb_pow, zpgEmb_zero,
        mul_one, one_mul, mul_zero, zero_mul, zero_add, add_zero, neg_zero,
        mul_sub, mul_add, sub_mul, add_mul, mul_neg, neg_mul, neg_neg]
      simp only [map_mul, map_pow, map_add, map_sub, map_neg, map_ofNat]
      refl_ring1
    rw [key]
    exact Ideal.add_mem _ (Ideal.add_mem _
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨2, rfl⟩))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨3, rfl⟩)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨4, rfl⟩))
  · subst h
    have key : (MvPolynomial.C (a^(3:ℕ)*b^(7:ℕ)*h^(2:ℕ)) * (MvPolynomial.X 0)
          - MvPolynomial.C (a^(7:ℕ)*b^(3:ℕ)*h^(4:ℕ)) * (MvPolynomial.X 2)^(2:ℕ)) * zpgStdM (K := K) 2
        - (∑ j : Fin 5, zpgEmb K (zpgWMatS (K := K) a b h j 2) * zpgStdM (K := K) j)
        = MvPolynomial.C (-(a^(5:ℕ)*b^(3:ℕ)*h^(2:ℕ))) * (MvPolynomial.X 2) * zpgQ a b h 0
          + MvPolynomial.C (a*b^(7:ℕ)*h^(2:ℕ)) * zpgQ a b h 2 := by
      simp only [zpgStdM, zpgWMatS, Fin.sum_univ_five, zpgQ_zero, zpgQ_one, zpgQ_two, zpgQ_three,
        zpgQ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
        Matrix.of_apply, zpgEmb_mul, zpgEmb_C, zpgEmb_X0, zpgEmb_pow, zpgEmb_zero,
        mul_one, one_mul, mul_zero, zero_mul, zero_add, add_zero, neg_zero,
        mul_sub, mul_add, sub_mul, add_mul, mul_neg, neg_mul, neg_neg]
      simp only [map_mul, map_pow, map_add, map_sub, map_neg, map_ofNat]
      refl_ring1
    rw [key]
    exact Ideal.add_mem _
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨0, rfl⟩))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨2, rfl⟩))
  · subst h
    have key : (MvPolynomial.C (a^(3:ℕ)*b^(7:ℕ)*h^(2:ℕ)) * (MvPolynomial.X 0)
          - MvPolynomial.C (a^(7:ℕ)*b^(3:ℕ)*h^(4:ℕ)) * (MvPolynomial.X 2)^(2:ℕ)) * zpgStdM (K := K) 3
        - (∑ j : Fin 5, zpgEmb K (zpgWMatS (K := K) a b h j 3) * zpgStdM (K := K) j)
        = MvPolynomial.C (a^(4:ℕ)*b^(4:ℕ)*h^(2:ℕ)) * (MvPolynomial.X 3) * zpgQ a b h 0
          + MvPolynomial.C (a^(6:ℕ)*b^(2:ℕ)*h^(2:ℕ)) * (MvPolynomial.X 2) * zpgQ a b h 4 := by
      simp only [zpgStdM, zpgWMatS, Fin.sum_univ_five, zpgQ_zero, zpgQ_one, zpgQ_two, zpgQ_three,
        zpgQ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
        Matrix.of_apply, zpgEmb_mul, zpgEmb_C, zpgEmb_X0, zpgEmb_pow, zpgEmb_zero,
        mul_one, one_mul, mul_zero, zero_mul, zero_add, add_zero, neg_zero,
        mul_sub, mul_add, sub_mul, add_mul, mul_neg, neg_mul, neg_neg]
      simp only [map_mul, map_pow, map_add, map_sub, map_neg, map_ofNat]
      refl_ring1
    rw [key]
    exact Ideal.add_mem _
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨0, rfl⟩))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨4, rfl⟩))
  · subst h
    have key : (MvPolynomial.C (a^(3:ℕ)*b^(7:ℕ)*h^(2:ℕ)) * (MvPolynomial.X 0)
          - MvPolynomial.C (a^(7:ℕ)*b^(3:ℕ)*h^(4:ℕ)) * (MvPolynomial.X 2)^(2:ℕ)) * zpgStdM (K := K) 4
        - (∑ j : Fin 5, zpgEmb K (zpgWMatS (K := K) a b h j 4) * zpgStdM (K := K) j)
        = (MvPolynomial.C (b^(3:ℕ)*(a^(5:ℕ)-b^(5:ℕ)))
              + MvPolynomial.C (a^(4:ℕ)*b^(4:ℕ)*h^(2:ℕ)) * (MvPolynomial.X 0 * MvPolynomial.X 3))
            * zpgQ a b h 0
          + (MvPolynomial.C (-(a^(3:ℕ)*b^(5:ℕ)*h^(4:ℕ))) * (MvPolynomial.X 3)^(2:ℕ)
              + MvPolynomial.C (a^(2:ℕ)*b*h^(2:ℕ)*(a^(5:ℕ)-b^(5:ℕ))) * (MvPolynomial.X 2)) * zpgQ a b h 3
          + (MvPolynomial.C (a^(3:ℕ)*h^(2:ℕ)*(a^(5:ℕ)-b^(5:ℕ))) * (MvPolynomial.X 3)
              + MvPolynomial.C (a^(6:ℕ)*b^(2:ℕ)*h^(2:ℕ)) * (MvPolynomial.X 0 * MvPolynomial.X 2))
              * zpgQ a b h 4 := by
      simp only [zpgStdM, zpgWMatS, Fin.sum_univ_five, zpgQ_zero, zpgQ_one, zpgQ_two, zpgQ_three,
        zpgQ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
        Matrix.of_apply, zpgEmb_mul, zpgEmb_C, zpgEmb_X0, zpgEmb_pow, zpgEmb_zero,
        mul_one, one_mul, mul_zero, zero_mul, zero_add, add_zero, neg_zero,
        mul_sub, mul_add, sub_mul, add_mul, mul_neg, neg_mul, neg_neg]
      simp only [map_mul, map_pow, map_add, map_sub, map_neg, map_ofNat]
      refl_ring1
    rw [key]
    exact Ideal.add_mem _ (Ideal.add_mem _
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨0, rfl⟩))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨3, rfl⟩)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨4, rfl⟩))

end Work.MotK.TGen
