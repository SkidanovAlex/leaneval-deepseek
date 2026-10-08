import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Mat2.centralizer_sq_neg_one
import Submission.Work.L2F.Mat2.trace_eq_zero_of_sq_eq_neg_one
import Submission.Work.L2F.Conic.mem_circle

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Mat2

/-! ## Two helper lemmas

The proof of `centralizer_sq_neg_one_card` runs through the conic
`{(a,b) ∈ F × F | a ^ 2 + b ^ 2 = 1}`:

* `centralizer_sq_neg_one` says `C_{SL(2,F)}(x) = {a • 1 + b • x | a ^ 2 + b ^ 2 = 1}`;
* `mem_circle` says `circle F = C_{SL(2,F)}(z) = {!![a,b;-b,a] | a ^ 2 + b ^ 2 = 1}`.

Both descriptions are the image of the *same* conic under an *injective* map, so both sets have
`#conic` elements and the two cardinalities agree.  The injectivity on the centralizer side is
the linear independence of `1` and `x` (a non-scalar traceless matrix with `det = 1`), which is
`smul_one_add_smul_injective_aux`; the injectivity on the circle side is obvious from the
entries `(0,0)` and `(0,1)`. -/

/-- A traceless nonzero `2 × 2` matrix `X` over a field with `(2 : F) ≠ 0` is not a scalar, hence
linearly independent from `1`: `(a, b) ↦ a • 1 + b • X` is injective.

Proof: if `u • 1 + v • X = 0`, taking traces (`tr X = 0`, `tr 1 = 2`) gives `2 * u = 0`, so
`u = 0`; then `v • X = 0` and `X ≠ 0` force `v = 0`. -/
private lemma smul_one_add_smul_injective_aux (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (X : Matrix (Fin 2) (Fin 2) F) (htr : X.trace = 0) (hX : X ≠ 0) :
    Function.Injective (fun p : F × F => p.1 • 1 + p.2 • X) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  change a • 1 + b • X = a' • 1 + b' • X at h
  have hzero : (a - a') • 1 + (b - b') • X = 0 := by
    have hsub : a • 1 + b • X - (a' • 1 + b' • X) = 0 := by rw [h, sub_self]
    have : (a - a') • 1 + (b - b') • X = a • 1 + b • X - (a' • 1 + b' • X) := by
      rw [sub_smul, sub_smul]; abel
    rw [this, hsub]
  have htrace : ((a - a') • 1 + (b - b') • X).trace = (a - a') * 2 := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one, htr,
      smul_zero, add_zero, Fintype.card_fin]
    norm_num
  have ha : a = a' := by
    have h0 : (a - a') * 2 = 0 := by rw [← htrace, hzero, Matrix.trace_zero]
    rcases mul_eq_zero.mp h0 with hh | hh
    · exact sub_eq_zero.mp hh
    · exact absurd hh h2
  have hbX : (b - b') • X = 0 := by
    have := hzero
    rw [ha, sub_self, zero_smul, zero_add] at this
    exact this
  have hb : b = b' := by
    by_contra hne
    have hne' : b - b' ≠ 0 := sub_ne_zero.mpr hne
    have hX0 : X = 0 := by
      have h1 : (b - b')⁻¹ • ((b - b') • X) = 0 := by rw [hbX, smul_zero]
      rwa [smul_smul, inv_mul_cancel₀ hne', one_smul] at h1
    exact (hX hX0).elim
  exact Prod.ext ha hb

/-- `Nat.card (circle F)` is the number of points of the conic `a ^ 2 + b ^ 2 = 1`.  This is
`mem_circle` read as a bijection: `x ∈ circle F ↔ ∃ a b, a ^ 2 + b ^ 2 = 1 ∧ x = !![a,b;-b,a]`,
and the matrix `!![a,b;-b,a]` determines `(a,b)` through its entries `(0,0)` and `(0,1)`. -/
private theorem card_circle_eq_ncard_conic_aux (F : Type*) [Field F] :
    Nat.card (Work.L2F.circle F) = {p : F × F | p.1 ^ 2 + p.2 ^ 2 = 1}.ncard := by
  rw [← SetLike.coe_sort_coe]
  rw [Nat.card_coe_set_eq]
  refine (Set.ncard_congr (s := {p : F × F | p.1 ^ 2 + p.2 ^ 2 = 1})
    (t := (Work.L2F.circle F : Set (Matrix.SpecialLinearGroup (Fin 2) F)))
    (fun p hp => ⟨!![p.1, p.2; -p.2, p.1], by
      rw [Matrix.det_fin_two_of]
      have hp' : p.1 ^ 2 + p.2 ^ 2 = 1 := hp
      linear_combination hp'⟩) ?_ ?_ ?_).symm
  · -- the image lies in `circle F`
    intro p hp
    exact (Work.L2F.Conic.mem_circle F _).mpr ⟨p.1, p.2, hp, rfl⟩
  · -- injectivity: the matrix determines `(a,b)`
    intro p q hp hq heq
    have hmat := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) F =>
      (x : Matrix (Fin 2) (Fin 2) F)) heq
    have h0 := congrFun (congrFun hmat 0) 0
    have h1 := congrFun (congrFun hmat 0) 1
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.cons_val_one] at h0 h1
    exact Prod.ext h0 h1
  · -- surjectivity: `mem_circle` produces the preimage
    intro x hx
    obtain ⟨a, b, hab, hxeq⟩ := (Work.L2F.Conic.mem_circle F x).mp hx
    refine ⟨(a, b), hab, ?_⟩
    apply Subtype.ext
    rw [hxeq]

/-- For `x ∈ SL(2,F)` with `x² = -1` (odd characteristic), `|C_{SL(2,F)}(x)| = |circle F|`:
`centralizer_sq_neg_one` identifies `C(x)` with the conic `a² + b² = 1` via the injective map
`(a,b) ↦ a • 1 + b • x`, and `mem_circle` identifies `circle F` with the same conic via
`(a,b) ↦ !![a,b;-b,a]`. -/
theorem centralizer_sq_neg_one_card (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : (x : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) = -1) :
    Nat.card (Subgroup.centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) =
      Nat.card (Work.L2F.circle F) := by
  -- `x` is traceless with determinant `1` (Cayley–Hamilton), and not a scalar matrix.
  have htr : (x : Matrix (Fin 2) (Fin 2) F).trace = 0 :=
    trace_eq_zero_of_sq_eq_neg_one F _ (Matrix.SpecialLinearGroup.det_coe x) hx
  have hx0 : (x : Matrix (Fin 2) (Fin 2) F) ≠ 0 := by
    intro h
    have h1 : (x : Matrix (Fin 2) (Fin 2) F).det = 1 := Matrix.SpecialLinearGroup.det_coe x
    rw [h, Matrix.det_zero] at h1
    exact one_ne_zero h1.symm
  -- the centralizer is the image of the conic under the injective map `a • 1 + b • x`
  have key : Nat.card (Subgroup.centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) =
      {p : F × F | p.1 ^ 2 + p.2 ^ 2 = 1}.ncard := by
    rw [← SetLike.coe_sort_coe]
    rw [Nat.card_coe_set_eq]
    refine (Set.ncard_congr (s := {p : F × F | p.1 ^ 2 + p.2 ^ 2 = 1})
      (t := (Subgroup.centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) :
        Set (Matrix.SpecialLinearGroup (Fin 2) F)))
      (fun p hp => ⟨p.1 • 1 + p.2 • (x : Matrix (Fin 2) (Fin 2) F), by
        rw [det_smul_one_add_smul, htr, Matrix.SpecialLinearGroup.det_coe]
        simp only [mul_zero, mul_one, add_zero]
        exact hp⟩) ?_ ?_ ?_).symm
    · -- membership in the centralizer, by `centralizer_sq_neg_one`
      intro p hp
      exact (centralizer_sq_neg_one F h2 x hx _).mpr ⟨p.1, p.2, hp, rfl⟩
    · -- injectivity: the linear independence of `1` and `x`
      intro p q hp hq heq
      have hmat : p.1 • 1 + p.2 • (x : Matrix (Fin 2) (Fin 2) F)
          = q.1 • 1 + q.2 • (x : Matrix (Fin 2) (Fin 2) F) := by
        simpa using congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) F =>
          (z : Matrix (Fin 2) (Fin 2) F)) heq
      exact smul_one_add_smul_injective_aux F h2 _ htr hx0 hmat
    · -- surjectivity: `centralizer_sq_neg_one` produces the coefficients
      intro y hy
      obtain ⟨a, b, hab, hyeq⟩ := (centralizer_sq_neg_one F h2 x hx y).mp hy
      refine ⟨(a, b), hab, ?_⟩
      apply Subtype.ext
      rw [hyeq]
  rw [key, card_circle_eq_ncard_conic_aux]

end Work.L2F.Mat2
