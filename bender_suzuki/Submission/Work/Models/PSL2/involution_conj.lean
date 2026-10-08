import Mathlib
import Submission.Work.Models.PSL2.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Models.PSL2.involution_conj` — all involutions of `SL(2,F)` are conjugate

For `F` a finite field of characteristic `2`, `SL(2,F)` has a single conjugacy class of
involutions (`t ≠ 1`, `t * t = 1`): every such `t` is conjugate to the standard unipotent
element `unip 1 = 1 + E₀₁`.

In characteristic `2` an involution `t` of `SL(2,F)` is unipotent: writing `A` for the matrix
of `t` we have `A * A = 1`, so `N := A + 1` satisfies `N * N = A*A + A + A + 1 = 0`, and
`N ≠ 0` because `t ≠ 1`.  A nonzero `2 × 2` matrix with `N² = 0` is a transvection: it is
conjugate (over the finite field, after rescaling a conjugating matrix so that its determinant
becomes `1`) to the Jordan block `E₀₁ = !![0,1;0,0]`.  Hence `A` is conjugate to
`1 + E₀₁ = unip 1`.

The two case computations (`conj_nilpotent_of_q_ne` for `N 0 1 ≠ 0` and `conj_nilpotent_of_q_zero`
for `N 0 1 = 0`, where necessarily `N 1 0 ≠ 0`) are proved first; they use only that squaring is
surjective on the finite field `F` (`isSquare_of_charTwo'`).
-/

namespace Work.Models.PSL2

open Matrix

/-- If the `(0,1)`-entry `q` of a matrix `!![p,q;r,s]` is nonzero and the matrix is square-zero
(here encoded by `q * r = p * p` and `s = p`) then it is conjugate to `!![0,1;0,0]` by an element
of `SL(2,F)`. -/
theorem conj_nilpotent_of_q_ne {F : Type*} [Field F] [CharP F 2] [Finite F]
    (p q r s : F) (hq : q ≠ 0) (hqr : q * r = p * p) (hs : s = p) :
    ∃ g : Work.Models.SL2 F,
      (g : Matrix (Fin 2) (Fin 2) F) * !![p, q; r, s]
        = !![0, 1; 0, 0] * (g : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨c, hc⟩ := isSquare_of_charTwo' q
  have hcne : c ≠ 0 := by rintro rfl; rw [mul_zero] at hc; exact hq hc
  refine ⟨⟨!![c⁻¹, 0; p * c⁻¹, c], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]; simp [inv_mul_cancel₀ hcne]
  · apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · rw [mul_comm]
    · rw [hc]; field_simp
    · field_simp
      have h1 : c ^ 2 * r = p ^ 2 := by rw [pow_two, ← hc, hqr, pow_two]
      rw [mul_zero, h1, CharTwo.add_self_eq_zero]
    · rw [hc, hs]; field_simp; rw [CharTwo.add_self_eq_zero, mul_zero]

/-- The matrix `!![0,0;r,0]` with `r ≠ 0` is conjugate to `!![0,1;0,0]` by an element of
`SL(2,F)`. -/
theorem conj_nilpotent_of_q_zero {F : Type*} [Field F] [CharP F 2] [Finite F] (r : F)
    (hr : r ≠ 0) :
    ∃ g : Work.Models.SL2 F,
      (g : Matrix (Fin 2) (Fin 2) F) * !![0, 0; r, 0]
        = !![0, 1; 0, 0] * (g : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨c, hc⟩ := isSquare_of_charTwo' r
  have hcne : c ≠ 0 := by rintro rfl; rw [mul_zero] at hc; exact hr hc
  refine ⟨⟨!![0, c⁻¹; c, 0], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]; simp [inv_mul_cancel₀ hcne, CharTwo.neg_eq]
  · apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc, hcne]

theorem involution_conj {F : Type*} [Field F] [CharP F 2] [Finite F] (t : Work.Models.SL2 F)
    (ht : t * t = 1) (hne : t ≠ 1) :
    ∃ g : Work.Models.SL2 F, g * t * g⁻¹ = Work.Models.PSL2.unip (F := F) 1 := by
  have hA : (t : Matrix (Fin 2) (Fin 2) F) * (t : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have h := congrArg (fun x : Work.Models.SL2 F => (x : Matrix (Fin 2) (Fin 2) F)) ht
    simpa using h
  set N : Matrix (Fin 2) (Fin 2) F := (t : Matrix (Fin 2) (Fin 2) F) + 1 with hNdef
  have hN2 : N * N = 0 := by
    rw [hNdef]
    have hsq : ((t : Matrix (Fin 2) (Fin 2) F) + 1) * ((t : Matrix (Fin 2) (Fin 2) F) + 1)
        = ((t : Matrix (Fin 2) (Fin 2) F) * (t : Matrix (Fin 2) (Fin 2) F))
          + ((t : Matrix (Fin 2) (Fin 2) F) + (t : Matrix (Fin 2) (Fin 2) F)) + 1 := by
      noncomm_ring
    rw [hsq, hA, CharTwo.add_self_eq_zero, add_zero, CharTwo.add_self_eq_zero]
  have hNne : N ≠ 0 := by
    intro h0
    apply hne
    apply Subtype.ext
    have hA1 : (t : Matrix (Fin 2) (Fin 2) F) + 1 = 0 := by rw [← hNdef]; exact h0
    have hsum : (t : Matrix (Fin 2) (Fin 2) F) = ((t : Matrix (Fin 2) (Fin 2) F) + 1) + 1 := by
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    rw [hsum, hA1, zero_add]
    exact Matrix.SpecialLinearGroup.coe_one.symm
  have hAN : (t : Matrix (Fin 2) (Fin 2) F) = N + 1 := by
    rw [hNdef, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hkey : ∀ i j : Fin 2, N i 0 * N 0 j + N i 1 * N 1 j = 0 := by
    intro i j
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M i j) hN2
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply] using h
  suffices hgoal : ∃ g : Work.Models.SL2 F,
      (g : Matrix (Fin 2) (Fin 2) F) * N
        = !![0, 1; 0, 0] * (g : Matrix (Fin 2) (Fin 2) F) by
    obtain ⟨g, hg⟩ := hgoal
    refine ⟨g, ?_⟩
    have hmat : (g : Matrix (Fin 2) (Fin 2) F) * (t : Matrix (Fin 2) (Fin 2) F)
        = (Work.Models.PSL2.unip (F := F) 1 : Matrix (Fin 2) (Fin 2) F)
          * (g : Matrix (Fin 2) (Fin 2) F) := by
      have hone : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) F) + 1 = !![1, 1; 0, 1] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp
      rw [hAN, unip_coe]
      calc (g : Matrix (Fin 2) (Fin 2) F) * (N + 1)
          = (g : Matrix (Fin 2) (Fin 2) F) * N + (g : Matrix (Fin 2) (Fin 2) F) * 1 := by
            rw [mul_add]
        _ = (g : Matrix (Fin 2) (Fin 2) F) * N + (g : Matrix (Fin 2) (Fin 2) F) := by rw [mul_one]
        _ = !![0, 1; 0, 0] * (g : Matrix (Fin 2) (Fin 2) F) + (g : Matrix (Fin 2) (Fin 2) F) := by
            rw [hg]
        _ = !![0, 1; 0, 0] * (g : Matrix (Fin 2) (Fin 2) F)
              + 1 * (g : Matrix (Fin 2) (Fin 2) F) := by rw [one_mul]
        _ = (!![0, 1; 0, 0] + 1) * (g : Matrix (Fin 2) (Fin 2) F) := by rw [add_mul]
        _ = !![1, 1; 0, 1] * (g : Matrix (Fin 2) (Fin 2) F) := by rw [hone]
    have hgt : g * t = Work.Models.PSL2.unip (F := F) 1 * g := by
      apply Subtype.ext
      simpa only [Matrix.SpecialLinearGroup.coe_mul] using hmat
    rw [hgt]
    group
  by_cases hq : N 0 1 = 0
  · have hp : N 0 0 = 0 := by
      have h := hkey 0 0
      rw [hq, zero_mul, add_zero] at h
      exact mul_self_eq_zero.mp h
    have hs : N 1 1 = 0 := by
      have h := hkey 1 1
      rw [hq, mul_zero, zero_add] at h
      exact mul_self_eq_zero.mp h
    have hr : N 1 0 ≠ 0 := by
      intro h0
      apply hNne
      apply Matrix.ext; intro i j
      fin_cases i <;> fin_cases j <;> simp [hp, hq, hs, h0]
    obtain ⟨g, hg⟩ := conj_nilpotent_of_q_zero (N 1 0) hr
    refine ⟨g, ?_⟩
    have hNeta : (!![0, 0; N 1 0, 0] : Matrix (Fin 2) (Fin 2) F) = N := by
      apply Matrix.ext; intro i j
      fin_cases i <;> fin_cases j <;> simp [hp, hq, hs]
    rw [← hNeta]; exact hg
  · have hfac : N 0 1 * (N 0 0 + N 1 1) = 0 := by
      rw [mul_add, mul_comm (N 0 1) (N 0 0)]
      exact hkey 0 1
    have hz : N 0 0 + N 1 1 = 0 := (mul_eq_zero.mp hfac).resolve_left hq
    have hs : N 1 1 = N 0 0 := by
      calc N 1 1 = N 1 1 + (N 0 0 + N 1 1) := by rw [hz, add_zero]
        _ = N 0 0 := by
              rw [← add_assoc, add_comm (N 1 1) (N 0 0), add_assoc,
                CharTwo.add_self_eq_zero, add_zero]
    have hqr : N 0 1 * N 1 0 = N 0 0 * N 0 0 := by
      calc N 0 1 * N 1 0 = N 0 1 * N 1 0 + (N 0 0 * N 0 0 + N 0 1 * N 1 0) := by
            rw [hkey 0 0, add_zero]
        _ = N 0 0 * N 0 0 := by
              rw [← add_assoc, add_comm (N 0 1 * N 1 0) (N 0 0 * N 0 0), add_assoc,
                CharTwo.add_self_eq_zero, add_zero]
    obtain ⟨g, hg⟩ := conj_nilpotent_of_q_ne (N 0 0) (N 0 1) (N 1 0) (N 1 1) hq hqr hs
    refine ⟨g, ?_⟩
    have hNeta : (!![N 0 0, N 0 1; N 1 0, N 1 1] : Matrix (Fin 2) (Fin 2) F) = N := by
      apply Matrix.ext; intro i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [← hNeta]; exact hg

end Work.Models.PSL2
