import Mathlib
import Submission.Work.KronP.kdefs

/-!
# `Work.KronP.negaIntCoeff`

The integer coefficient identity behind the complex (fixed point) form of the Kronecker
substitution (paper Lemma 2.5), used by `Work.KronP.kronFinal`.

Let `u`, `v` be length-`r` lists of integer pairs, i.e. fixed-point complex vectors, and let
`fxVec p r u : Fin r → ℂ` be the complex vector `i ↦ 2^{-p}(xᵢ + yᵢ i)` (`HvdH.fxVec`).
Then for every `k < r` the `k`-th coefficient of the negacyclic product in `ℂ[y]/(y^r+1)`,
rescaled by `4^p` (which cancels the two factors `2^{-p}`), is the complex number whose real and
imaginary coefficients are the paper's `D0c` and `D1c`:

`4^p * (u·v)_k = D0c k + D1c k · i`.

The content is a finite computation.  With `z = uᵢ`, `w = vⱼ`, `Zp z = z₁ + z₂ i`:

* `4^p * (fxC p z * fxC p w) = Zp z * Zp w` (`nega_fxC_four_mul`), so the left-hand side
  becomes the double sum over `Fin r × Fin r` of
  `if i+j = k then Zp uᵢ · Zp vⱼ else if i+j = k+r then -(Zp uᵢ · Zp vⱼ) else 0`
  (`nega_negaMul_fxVec`, using the definition of `HvdH.negaMul`);
* the right-hand side rewrites to *the same* double sum: the integer double sums `dsumL` become
  complex double sums over `Fin r × Fin r` (`nega_dsumL_cast`), the two halves of `negaCoefL`
  combine into the nested-`if` form (`nega_negaCoefL_cast`, using `k < r` for disjointness), the
  four directional products are reassembled (`nega_combine_sums`) and matched pointwise with
  `Zp uᵢ · Zp vⱼ = uᵢ₁vⱼ₁ - uᵢ₂vⱼ₂ + (uᵢ₁vⱼ₂ + uᵢ₂vⱼ₁) i` (`nega_D0c_D1c_eq`).
-/

set_option autoImplicit false

namespace Work.KronP

open HvdH

/-! ## Normal form of the coefficient -/

/-- The complex number `x + iy` attached to an integer pair `(x, y)`. -/
noncomputable def Zp (z : ℤ × ℤ) : ℂ := (z.1 : ℂ) + (z.2 : ℂ) * Complex.I

/-- The common normal form of both sides: the `k`-th coefficient of the negacyclic product of the
fixed-point vectors `u`, `v`, rescaled by `4^p`, written as a double sum over `Fin r × Fin r`. -/
noncomputable def negaCoefC (u v : List (ℤ × ℤ)) (r k : ℕ) : ℂ :=
  ∑ i : Fin r, ∑ j : Fin r,
    (if (i : ℕ) + (j : ℕ) = k then Zp (u.getD (i : ℕ) (0, 0)) * Zp (v.getD (j : ℕ) (0, 0))
     else if (i : ℕ) + (j : ℕ) = k + r then
       -(Zp (u.getD (i : ℕ) (0, 0)) * Zp (v.getD (j : ℕ) (0, 0)))
     else 0)

/-! ## The left-hand side: `4^p` times the fixed-point negacyclic product -/

/-- `4^p` undoes the two denominators `2^p` of `fxC`, leaving the product of the unnormalised
Gaussian integers `Zp`. -/
theorem nega_fxC_four_mul (p : ℕ) (z w : ℤ × ℤ) :
    (4 : ℂ) ^ p * (HvdH.fxC p z * HvdH.fxC p w) = Zp z * Zp w := by
  simp only [Zp, HvdH.fxC]
  rw [div_mul_div_comm, ← mul_div_assoc]
  rw [show (2 : ℂ) ^ p * (2 : ℂ) ^ p = (4 : ℂ) ^ p from by rw [← mul_pow]; norm_num]
  field_simp

/-- The left-hand side of `negaIntCoeff`, reduced to the normal form `negaCoefC`. -/
theorem nega_negaMul_fxVec {p r : ℕ} (u v : List (ℤ × ℤ)) (k : ℕ) (hk : k < r) :
    (4 : ℂ) ^ p * HvdH.negaMul r (HvdH.fxVec p r u) (HvdH.fxVec p r v) ⟨k, hk⟩ =
      negaCoefC u v r k := by
  rw [negaCoefC]
  simp only [HvdH.negaMul, HvdH.fxVec, Finset.mul_sum, mul_ite, mul_neg, mul_zero]
  simp only [nega_fxC_four_mul]

/-! ## Reading a coefficient vector as a pair of integer lists -/

/-- `Prod.fst` of the `i`-th entry (with default `(0,0)`), stated at the level of `ℤ`: a real
coordinate list and the list of real parts carry the same data. -/
theorem nega_getD_map_fst (u : List (ℤ × ℤ)) (i : ℕ) :
    (u.map Prod.fst).getD i 0 = (u.getD i (0, 0)).1 := by
  induction u generalizing i with
  | nil => simp
  | cons a t ih => cases i with
    | zero => simp
    | succ i => simpa using ih i

/-- `Prod.snd` of the `i`-th entry (with default `(0,0)`), at the level of `ℤ`. -/
theorem nega_getD_map_snd (u : List (ℤ × ℤ)) (i : ℕ) :
    (u.map Prod.snd).getD i 0 = (u.getD i (0, 0)).2 := by
  induction u generalizing i with
  | nil => simp
  | cons a t ih => cases i with
    | zero => simp
    | succ i => simpa using ih i

/-! ## The two halves of `negaCoefL` as complex double sums -/

/-- The two branches `if c` and `if d` of the negacyclic fold are mutually exclusive: then
`x·[c] - x·[d]` is the nested conditional `if c then x else if d then -x else 0`. -/
theorem nega_int_coef_it' (c d : Prop) [Decidable c] [Decidable d] (h : ¬ (c ∧ d)) (x : ℂ) :
    (if c then x else 0) - (if d then x else 0) = if c then x else if d then -x else 0 := by
  by_cases hc : c <;> by_cases hd : d <;> simp_all

/-- The integer double sum `dsumL`, cast to `ℂ`, is the double sum over `Fin r × Fin r` of the
cast products.  (The `if i + j = m` of `dsumL` is kept as an `if` in `ℂ`.) -/
theorem nega_dsumL_cast (l1 l2 : List ℤ) (r m : ℕ) :
    ((Work.KronP.dsumL l1 l2 r m : ℤ) : ℂ) =
      ∑ i : Fin r, ∑ j : Fin r,
        (if (i : ℕ) + (j : ℕ) = m then
          ((l1.getD (i : ℕ) 0 : ℤ) : ℂ) * ((l2.getD (j : ℕ) 0 : ℤ) : ℂ) else 0) := by
  rw [Work.KronP.dsumL]
  push_cast
  rw [← Fin.sum_univ_eq_sum_range (f := fun i => ∑ j ∈ Finset.range r,
        (if i + j = m then ((l1.getD i 0 : ℤ) : ℂ) * ((l2.getD j 0 : ℤ) : ℂ) else 0)) r]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Fin.sum_univ_eq_sum_range (f := fun j =>
        (if (i : ℕ) + j = m then
          ((l1.getD (i : ℕ) 0 : ℤ) : ℂ) * ((l2.getD j 0 : ℤ) : ℂ) else 0)) r]

/-- `negaCoefL` (the negacyclic coefficient `A_k - A_{k+r}`), cast to `ℂ`, as a double sum
over `Fin r × Fin r`: the `k`-branch with sign `+` and the `(k+r)`-branch with sign `-`. -/
theorem nega_negaCoefL_cast {r k : ℕ} (hk : k < r) (l1 l2 : List ℤ) :
    ((Work.KronP.negaCoefL l1 l2 r k : ℤ) : ℂ) =
      ∑ i : Fin r, ∑ j : Fin r,
        (if (i : ℕ) + (j : ℕ) = k then
          ((l1.getD (i : ℕ) 0 : ℤ) : ℂ) * ((l2.getD (j : ℕ) 0 : ℤ) : ℂ)
         else if (i : ℕ) + (j : ℕ) = k + r then
           -(((l1.getD (i : ℕ) 0 : ℤ) : ℂ) * ((l2.getD (j : ℕ) 0 : ℤ) : ℂ)) else 0) := by
  rw [Work.KronP.negaCoefL, Int.cast_sub, nega_dsumL_cast l1 l2 r k,
    nega_dsumL_cast l1 l2 r (k + r)]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have h : ¬ (((i : ℕ) + (j : ℕ) = k) ∧ ((i : ℕ) + (j : ℕ) = k + r)) := by omega
  exact nega_int_coef_it' _ _ h _

/-- Four double sums over `Fin r × Fin r` combine into a single one: the coefficientwise
accounting of `D0c + D1c·i` (an elementary `Finset.sum` identity). -/
theorem nega_combine_sums {r : ℕ} (A B C D : Fin r → Fin r → ℂ) :
    (∑ i, ∑ j, A i j) - (∑ i, ∑ j, B i j) +
        ((∑ i, ∑ j, C i j) + (∑ i, ∑ j, D i j)) * Complex.I
      = ∑ i, ∑ j, (A i j - B i j + (C i j + D i j) * Complex.I) := by
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.sum_mul]

/-! ## The right-hand side -/

/-- The right-hand side of `negaIntCoeff`, reduced to the same normal form `negaCoefC`. -/
theorem nega_D0c_D1c_eq (u v : List (ℤ × ℤ)) (r k : ℕ) (hk : k < r) :
    ((Work.KronP.D0c u v r k : ℤ) : ℂ) + ((Work.KronP.D1c u v r k : ℤ) : ℂ) * Complex.I =
      negaCoefC u v r k := by
  have h00 := nega_negaCoefL_cast hk (u.map Prod.fst) (v.map Prod.fst)
  have h11 := nega_negaCoefL_cast hk (u.map Prod.snd) (v.map Prod.snd)
  have h01 := nega_negaCoefL_cast hk (u.map Prod.fst) (v.map Prod.snd)
  have h10 := nega_negaCoefL_cast hk (u.map Prod.snd) (v.map Prod.fst)
  simp only [Work.KronP.D0c, Work.KronP.D1c, Int.cast_sub, Int.cast_add]
  rw [h00, h11, h01, h10]
  simp only [nega_getD_map_fst, nega_getD_map_snd]
  rw [nega_combine_sums]
  rw [negaCoefC]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hc : (i : ℕ) + (j : ℕ) = k
  · have hne : ¬ (k = k + r) := by omega
    simp only [hc, hne, ite_true, ite_false, Zp]
    ring_nf
    rw [pow_two, Complex.I_mul_I]
    ring
  · by_cases hd : (i : ℕ) + (j : ℕ) = k + r
    · have hne : ¬ (k + r = k) := by omega
      simp only [hd, hne, ite_true, ite_false, Zp]
      ring_nf
      rw [pow_two, Complex.I_mul_I]
      ring
    · simp only [hc, hd, ite_false]
      ring

/-! ## The lemma -/

theorem negaIntCoeff {p r : ℕ} {u v : List (ℤ × ℤ)} (hu : u.length = r) (hv : v.length = r)
    (k : ℕ) (hk : k < r) :
    (4 : ℂ) ^ p * HvdH.negaMul r (HvdH.fxVec p r u) (HvdH.fxVec p r v) ⟨k, hk⟩ =
      ((Work.KronP.D0c u v r k : ℤ) : ℂ) +
        ((Work.KronP.D1c u v r k : ℤ) : ℂ) * Complex.I := by
  calc (4 : ℂ) ^ p * HvdH.negaMul r (HvdH.fxVec p r u) (HvdH.fxVec p r v) ⟨k, hk⟩
      = Work.KronP.negaCoefC u v r k := nega_negaMul_fxVec u v k hk
    _ = ((Work.KronP.D0c u v r k : ℤ) : ℂ) +
          ((Work.KronP.D1c u v r k : ℤ) : ℂ) * Complex.I := (nega_D0c_D1c_eq u v r k hk).symm

end Work.KronP
