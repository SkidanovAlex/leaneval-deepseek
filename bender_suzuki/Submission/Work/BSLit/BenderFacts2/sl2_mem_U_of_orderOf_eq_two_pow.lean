import Mathlib
import Submission.Work.Models.PSL2.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSLit.BenderFacts2

/-- **Powers of an upper triangular `2 × 2` matrix keep their `(0,0)`-entry**: if `A 1 0 = 0` then
`(A ^ n) 0 0 = (A 0 0) ^ n`, because in the product `A ^ n * A` the second summand
`(A ^ n) 0 1 * A 1 0` vanishes. -/
lemma pow_apply_zero_zero_of_upperTriangular {R : Type*} [CommSemiring R]
    {A : Matrix (Fin 2) (Fin 2) R} (h : A 1 0 = 0) (n : ℕ) :
    (A ^ n) 0 0 = (A 0 0) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, ih, h, mul_zero, add_zero, pow_succ]

/-- **A 2-element of the standard Borel `B` of `SL(2,F)` lies in the unipotent radical `U`**
(`F` a finite field of characteristic `2`, `B` = upper triangular matrices of
`Work.Models.SL2 F = Matrix.SpecialLinearGroup (Fin 2) F`, `U = {unip c | c : F}`,
`Work.Models.PSL2.B` / `Work.Models.PSL2.U` in `Submission/Work/Models/PSL2/Defs.lean`).

`B = U ⋊ D` with `D` the diagonal torus of order `|F| - 1` (odd) and `U` elementary abelian of
order `|F|` (`Work.Models.PSL2.B_facts`, `card_D`, `card_U`, `U_sq_one`); the natural map
`B → B ⧸ U` has odd-order image, so an element of `2`-power order maps to `1`.

Route (either of two): (a) the quotient argument as in
`Submission.Work.Models.Abstract.involutions_subset_U`: `U ⊴ B` (from
`Work.Models.PSL2.B_le_normalizer_U` via `Subgroup.normal_subgroupOf_iff_le_normalizer`),
`Nat.card (↥B ⧸ U.subgroupOf B) = |D|` is odd, and `orderOf` of the image divides both `2 ^ k`
and that odd number, hence is `1`; or (b) the entry computation: for `x = !![a,b;0,d] ∈ B` the
diagonal entries satisfy `a * d = 1`, and `x ^ (2 ^ k) = 1` gives `a ^ (2 ^ k) = 1` (via the
`(0,0)` entry of `x ^ n` for upper triangular `x`); then `(a + 1) ^ (2 ^ k) = a ^ (2 ^ k) + 1 = 0`
forces `a = 1`, so `d = 1` and `x = unip b ∈ U`. -/

/- The proof below follows route (b): with `A` the matrix of `x`, the `(0,0)`-entry of
`x ^ (2 ^ k) = 1` is `(A 0 0) ^ (2 ^ k) = 1` (`pow_apply_zero_zero_of_upperTriangular`),
Freshman's dream in characteristic `2` turns this into `(A 0 0 + 1) ^ (2 ^ k) = 0`, and a field
has no nonzero nilpotents, so `A 0 0 = 1`; the determinant condition `A 0 0 * A 1 1 = 1` then
gives `A 1 1 = 1`, and `A = !![1, A 0 1; 0, 1] = unip (A 0 1)`. -/
theorem sl2_mem_U_of_orderOf_eq_two_pow {F : Type*} [Field F] [CharP F 2] [Finite F]
    {x : Work.Models.SL2 F} (hxB : x ∈ Work.Models.PSL2.B (F := F))
    (h : ∃ k : ℕ, orderOf x = 2 ^ k) : x ∈ Work.Models.PSL2.U (F := F) := by
  obtain ⟨k, hk⟩ := h
  -- the only nonzero off-diagonal entry of an upper triangular matrix is the `(0,1)` one
  have h10 : (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hxB
  -- `x ^ (2 ^ k) = 1`, since `2 ^ k` is the order of `x`
  have hx1 : x ^ (2 ^ k) = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
  have hpow : (x : Matrix (Fin 2) (Fin 2) F) ^ (2 ^ k) = 1 := by
    have h' := congrArg (fun y : Work.Models.SL2 F => (y : Matrix (Fin 2) (Fin 2) F)) hx1
    simpa using h'
  -- the `(0,0)`-entry `a` of `x` satisfies `a ^ (2 ^ k) = 1`
  have ha : ((x : Matrix (Fin 2) (Fin 2) F) 0 0) ^ (2 ^ k) = 1 := by
    have h' := congrArg (fun N : Matrix (Fin 2) (Fin 2) F => N 0 0) hpow
    simpa [pow_apply_zero_zero_of_upperTriangular h10] using h'
  -- the determinant condition for an upper triangular matrix: `a * d = 1`
  have hdet : (x : Matrix (Fin 2) (Fin 2) F) 0 0 * (x : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    have hd := Matrix.SpecialLinearGroup.det_coe x
    rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hd
    exact hd
  -- in characteristic `2`, `(a + 1) ^ (2 ^ k) = a ^ (2 ^ k) + 1 = 0`, so `a + 1 = 0`
  have hsum : ((x : Matrix (Fin 2) (Fin 2) F) 0 0 + 1) ^ (2 ^ k) = 0 := by
    rw [add_pow_char_pow, one_pow, ha, CharTwo.add_self_eq_zero]
  have ha1 : (x : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    have hk_ne : 2 ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    have h0 : (x : Matrix (Fin 2) (Fin 2) F) 0 0 + 1 = 0 := (pow_eq_zero_iff hk_ne).mp hsum
    have h1 := eq_neg_of_add_eq_zero_right h0
    rw [CharTwo.neg_eq] at h1
    exact h1.symm
  have hd1 : (x : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    rw [ha1, one_mul] at hdet
    exact hdet
  -- hence `x = unip (x₀₁) ∈ U`
  have hAeq : (x : Matrix (Fin 2) (Fin 2) F)
      = !![1, (x : Matrix (Fin 2) (Fin 2) F) 0 1; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha1, hd1, h10]
  refine ⟨(x : Matrix (Fin 2) (Fin 2) F) 0 1, ?_⟩
  apply Subtype.ext
  rw [Work.Models.PSL2.unip_coe]
  exact hAeq

end Work.BSLit.BenderFacts2
