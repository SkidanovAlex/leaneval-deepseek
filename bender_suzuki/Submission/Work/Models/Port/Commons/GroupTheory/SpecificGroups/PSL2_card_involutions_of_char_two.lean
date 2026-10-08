import Mathlib
import Submission.Work.Models.Port.Commons.LinearAlgebra.Matrix.card_PSL2_charTwo
import Submission.Work.Models.Port.Commons.LinearAlgebra.Matrix.center_SL2_eq_bot_of_charTwo

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The number of involutions of `PSL(2,F)` in characteristic two

Let `F` be a finite field of characteristic `2` and let `q = |F|`.  Then `PSL(2,F) ≃ SL(2,F)`
(the centre of `SL(2,F)` is trivial in characteristic two) and the elements of order `2` are
the non-identity solutions of `M * M = 1` in `SL(2,F)`.  Since `det M * det M = det (M * M) = 1`
and `-1 = 1` in characteristic two, such a matrix automatically lies in `SL(2,F)`, and
`M * M = 1` is equivalent (via `M = N + 1`) to `N * N = 0`.  A `2 × 2` matrix `N` satisfies
`N * N = 0` exactly when `N = !![a, b; c, a]` with `a ^ 2 = b * c`; writing `s ^ 2 = b`,
`t ^ 2 = c` shows that the solutions of `a ^ 2 = b * c` are in bijection with `F × F`
(squaring is a bijection of a finite field of characteristic two).  Hence there are `q ^ 2`
matrices `N` with `N * N = 0`, of which `q ^ 2 - 1` are non-zero, and this is the number of
involutions of `PSL(2,F)`.

Classically, in characteristic two all involutions of `PSL(2,q)` are unipotent and there are
`q ^ 2 - 1` of them.
-/

open Matrix

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

namespace Commons.GroupTheory.SpecificGroups

/-- In characteristic two, `orderOf x = 2` means `x * x = 1` and `x ≠ 1`. -/
private lemma orderOf_eq_two_iff' {G : Type*} [Group G] (x : G) :
    orderOf x = 2 ↔ x * x = 1 ∧ x ≠ 1 := by
  rw [orderOf_eq_prime_iff, pow_two]

section MatrixCount

variable {F : Type*} [Field F] [CharP F 2]

/-- In a commutative ring of characteristic two, `a * b + b * a = 0`. -/
private lemma mul_add_mul_self_charTwo (a b : F) : a * b + b * a = 0 := by
  rw [mul_comm b a, CharTwo.add_self_eq_zero]

/-- A `2 × 2` matrix `N` over a field of characteristic two satisfies `N * N = 0` exactly
when it is of the form `!![a, b; c, a]` with `a ^ 2 = b * c`. -/
lemma mat_mul_self_eq_zero_iff (N : Matrix (Fin 2) (Fin 2) F) :
    N * N = 0 ↔ N 1 1 = N 0 0 ∧ (N 0 0) ^ 2 = N 0 1 * N 1 0 := by
  constructor
  · intro h
    have h00 : N 0 0 * N 0 0 + N 0 1 * N 1 0 = 0 := by
      have := congrFun (congrFun h 0) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have h11 : N 1 0 * N 0 1 + N 1 1 * N 1 1 = 0 := by
      have := congrFun (congrFun h 1) 1
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have h00' : N 0 0 * N 0 0 = N 0 1 * N 1 0 := CharTwo.add_eq_zero.mp h00
    have h11' : N 1 1 * N 1 1 = N 0 1 * N 1 0 := by
      rw [(CharTwo.add_eq_zero.mp h11).symm, mul_comm (N 1 0) (N 0 1)]
    have hsq : (N 0 0) ^ 2 = (N 1 1) ^ 2 := by rw [pow_two, pow_two, h00', h11']
    have hd : N 0 0 = N 1 1 := CharTwo.sq_inj.mp hsq
    exact ⟨hd.symm, by rw [pow_two]; exact h00'⟩
  · rintro ⟨hd, hsq⟩
    have hN : N = !![N 0 0, N 0 1; N 1 0, N 0 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hd]
    have hsq' : N 0 0 * N 0 0 = N 0 1 * N 1 0 := by rw [pow_two] at hsq; exact hsq
    rw [hN]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hsq', mul_add_mul_self_charTwo,
        CharTwo.add_self_eq_zero]

/-- The element of `SL(2,F)` with underlying matrix `M`. -/
private noncomputable def mkSL2 (M : Matrix (Fin 2) (Fin 2) F) (h : M.det = 1) :
    Matrix.SpecialLinearGroup (Fin 2) F := ⟨M, h⟩

private lemma mat_add_one_mul_self (A : Matrix (Fin 2) (Fin 2) F) :
    (A + 1) * (A + 1) = A * A + 1 := by
  have h : (A + 1) * (A + 1) = A * A + (A + A) + 1 := by noncomm_ring
  rw [h, CharTwo.add_self_eq_zero A, add_zero]

private lemma mat_add_one_mul_self_eq_one (A : Matrix (Fin 2) (Fin 2) F) (h : A * A = 0) :
    (A + 1) * (A + 1) = 1 := by
  rw [mat_add_one_mul_self, h, zero_add]

private lemma mat_det_eq_one_of_mul_self_eq_one (A : Matrix (Fin 2) (Fin 2) F)
    (h : A * A = 1) : A.det = 1 := by
  have h1 : A.det * A.det = 1 := by
    rw [← Matrix.det_mul, h, Matrix.det_one]
  refine CharTwo.sq_inj.mp ?_
  rw [pow_two, h1, one_pow]

private lemma mat_add_one_add_one (A : Matrix (Fin 2) (Fin 2) F) : (A + 1) + 1 = A := by
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

end MatrixCount

section Main

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- Squaring is a bijection of a finite field of characteristic two. -/
private noncomputable def sqEquiv : F ≃ F :=
  Equiv.ofBijective (fun x : F => x ^ 2)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨CharTwo.sq_injective, rfl⟩)

/-- The (unique) square root provided by `sqEquiv`. -/
private lemma sq_sqrt (x : F) : (sqEquiv.symm x) ^ 2 = x :=
  sqEquiv.apply_symm_apply x

/-- Matrices with `N * N = 0` correspond to triples `(a, b, c)` with `a ^ 2 = b * c`. -/
private noncomputable def matEquiv :
    {N : Matrix (Fin 2) (Fin 2) F // N * N = 0} ≃
      {p : F × F × F // p.1 ^ 2 = p.2.1 * p.2.2} where
  toFun N := ⟨(N.1 0 0, (N.1 0 1, N.1 1 0)), (mat_mul_self_eq_zero_iff N.1).mp N.2 |>.2⟩
  invFun p := ⟨!![p.1.1, p.1.2.1; p.1.2.2, p.1.1],
    (mat_mul_self_eq_zero_iff _).mpr ⟨rfl, p.2⟩⟩
  left_inv N := by
    have hd : N.1 1 1 = N.1 0 0 := ((mat_mul_self_eq_zero_iff N.1).mp N.2).1
    apply Subtype.ext
    show !![N.1 0 0, N.1 0 1; N.1 1 0, N.1 0 0] = N.1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hd]
  right_inv p := by
    obtain ⟨⟨a, b, c⟩, hp⟩ := p
    apply Subtype.ext
    rfl

/-- The triples `(a, b, c)` with `a ^ 2 = b * c` are in bijection with `F × F`, by
`(s, t) ↦ (s * t, s ^ 2, t ^ 2)`; the inverse takes square roots. -/
private noncomputable def tripleEquiv :
    {p : F × F × F // p.1 ^ 2 = p.2.1 * p.2.2} ≃ F × F where
  toFun p := (sqEquiv.symm p.1.2.1, sqEquiv.symm p.1.2.2)
  invFun q := ⟨(q.1 * q.2, (q.1 ^ 2, q.2 ^ 2)), by rw [mul_pow]⟩
  left_inv p := by
    obtain ⟨⟨a, b, c⟩, hp⟩ := p
    simp only at hp ⊢
    apply Subtype.ext
    have hb : (sqEquiv.symm b) ^ 2 = b := sq_sqrt b
    have hc : (sqEquiv.symm c) ^ 2 = c := sq_sqrt c
    have hmul : sqEquiv.symm b * sqEquiv.symm c = a := by
      apply CharTwo.sq_inj.mp
      rw [mul_pow, hb, hc]
      exact hp.symm
    simp only [Prod.mk.injEq]
    exact ⟨hmul, hb, hc⟩
  right_inv q := by
    obtain ⟨s, t⟩ := q
    simp only
    have hs : sqEquiv.symm (sqEquiv s) = s := sqEquiv.symm_apply_apply s
    have ht : sqEquiv.symm (sqEquiv t) = t := sqEquiv.symm_apply_apply t
    simp [sqEquiv]

/-- **A finite field of characteristic two has `q ^ 2` matrices `N` with `N * N = 0`.** -/
theorem card_matrices_mul_self_eq_zero_charTwo :
    Nat.card {N : Matrix (Fin 2) (Fin 2) F // N * N = 0} = Nat.card F ^ 2 := by
  rw [Nat.card_congr matEquiv, Nat.card_congr tripleEquiv, Nat.card_prod]
  ring

/-- The non-zero matrices `N` with `N * N = 0`: the complement of the unique zero matrix. -/
private noncomputable def neZeroEquivOption :
    {N : Matrix (Fin 2) (Fin 2) F // N * N = 0} ≃
      Option {N : Matrix (Fin 2) (Fin 2) F // N * N = 0 ∧ N ≠ 0} where
  toFun N :=
    if h : (N.1 : Matrix (Fin 2) (Fin 2) F) = 0 then none else some ⟨N.1, N.2, h⟩
  invFun o := o.elim ⟨0, by simp⟩ fun N => ⟨N.1, N.2.1⟩
  left_inv N := by
    by_cases h : (N.1 : Matrix (Fin 2) (Fin 2) F) = 0
    · dsimp only
      simp only [h, dif_pos, Option.elim_none]
      exact Subtype.ext h.symm
    · dsimp only
      simp only [dif_neg h, Option.elim_some]
  right_inv o := by
    cases o with
    | none => simp
    | some N => simp [N.2.2]

/-- **A finite field of characteristic two has `q ^ 2 - 1` non-zero matrices `N` with
`N * N = 0`.** -/
theorem card_matrices_mul_self_eq_zero_ne_zero_charTwo :
    Nat.card {N : Matrix (Fin 2) (Fin 2) F // N * N = 0 ∧ N ≠ 0} = Nat.card F ^ 2 - 1 := by
  have h : Nat.card {N : Matrix (Fin 2) (Fin 2) F // N * N = 0} =
      Nat.card {N : Matrix (Fin 2) (Fin 2) F // N * N = 0 ∧ N ≠ 0} + 1 := by
    rw [Nat.card_congr neZeroEquivOption, Finite.card_option]
  rw [card_matrices_mul_self_eq_zero_charTwo] at h
  omega

/-- Elements of order two in `SL(2,F)` correspond to the non-zero `2 × 2` matrices with
`N * N = 0`, via `x ↦ x + 1`. -/
private noncomputable def sl2Equiv :
    {x : Matrix.SpecialLinearGroup (Fin 2) F // orderOf x = 2} ≃
      {N : Matrix (Fin 2) (Fin 2) F // N * N = 0 ∧ N ≠ 0} where
  toFun x := ⟨(x.1 : Matrix (Fin 2) (Fin 2) F) + 1, by
    have hx := (orderOf_eq_two_iff' x.1).mp x.2
    have hx2 : ((x.1 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        * ((x.1 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 :=
      congrArg Subtype.val hx.1
    refine ⟨?_, ?_⟩
    · rw [mat_add_one_mul_self, hx2]
      exact CharTwo.add_self_eq_zero (1 : Matrix (Fin 2) (Fin 2) F)
    · intro h
      exact hx.2 (Subtype.ext (CharTwo.add_eq_zero.mp h))⟩
  invFun N := ⟨mkSL2 (N.1 + 1) (mat_det_eq_one_of_mul_self_eq_one (N.1 + 1)
      (mat_add_one_mul_self_eq_one N.1 N.2.1)), by
    rw [orderOf_eq_two_iff']
    constructor
    · apply Subtype.ext
      show (N.1 + 1) * (N.1 + 1) = 1
      exact mat_add_one_mul_self_eq_one N.1 N.2.1
    · intro h
      apply N.2.2
      have h2 : (N.1 + 1 : Matrix (Fin 2) (Fin 2) F) = 1 := congrArg Subtype.val h
      rw [CharTwo.add_eq_iff_eq_add] at h2
      rwa [CharTwo.add_self_eq_zero] at h2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact mat_add_one_add_one _
  right_inv N := by
    apply Subtype.ext
    exact mat_add_one_add_one _

/-- In characteristic two the centre of `SL(2,F)` is trivial, so `PSL(2,F) ≃ SL(2,F)`. -/
private noncomputable def psl2MulEquivSl2 :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
  (QuotientGroup.quotientMulEquivOfEq
      (Commons.LinearAlgebra.Matrix.center_SL2_eq_bot_of_charTwo (F := F))).trans
    QuotientGroup.quotientBot

/-- A multiplicative equivalence preserves the number of elements of order two. -/
private lemma card_orderOf_two_eq_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Nat.card {x : G // orderOf x = 2} = Nat.card {x : H // orderOf x = 2} :=
  Nat.card_congr
    { toFun := fun x => ⟨e x.1, by rw [MulEquiv.orderOf_eq]; exact x.2⟩
      invFun := fun y => ⟨e.symm y.1, by rw [MulEquiv.orderOf_eq]; exact y.2⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y.1) }

end Main

/-- **The number of involutions of `PSL(2,F)` in characteristic two is `|F| ^ 2 - 1`.** -/
theorem PSL2_card_involutions_of_char_two {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2] :
    Nat.card {x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F // orderOf x = 2}
      = Nat.card F ^ 2 - 1 := by
  have h1 : Nat.card {x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F // orderOf x = 2}
      = Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F // orderOf x = 2} :=
    card_orderOf_two_eq_of_mulEquiv
      (psl2MulEquivSl2 (F := F))
  have h2 : Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F // orderOf x = 2}
      = Nat.card {N : Matrix (Fin 2) (Fin 2) F // N * N = 0 ∧ N ≠ 0} :=
    Nat.card_congr (sl2Equiv (F := F))
  rw [h1, h2, card_matrices_mul_self_eq_zero_ne_zero_charTwo]

end Commons.GroupTheory.SpecificGroups
