/-
# The odd-weight defect ideal `𝓘_odd`: the two-dimensional standard representation

For **odd** weight `k` the element `z = -I` acts on functions by `(-1)^k = -1`, so the
generator acting trivially is `1 + z`, and the relevant ideal is

  `𝓘_odd = (T-I)²R + S(T-I)²R + (1+z)R = IdealI + augIdealOdd`   (`Work.Asymptotics.idealIOdd`).

This file studies `𝓘_odd` through the **two-dimensional standard representation** `ρ₂`, the
linear extension of the inclusion `SL(2,ℤ) ↪ M₂(ℤ) ↪ M₂(ℂ)` (`rho2`).  It is the "smallest"
representation of `R` that sees the difference between the even ideal
`𝓘_even = IdealI + (z-1)R` and the odd ideal `𝓘_odd`:

* `rho2_mem_idealIOdd : x ∈ 𝓘_odd → ρ₂ x = 0`  (`ρ₂((T-1)²) = N² = 0`, `ρ₂(S(T-1)²) = 0`,
  `ρ₂(1+z) = 0` because `ρ₂(z) = -1`, `rho2_Rneg`);
* `R_T ∉ 𝓘_odd` (`R_T_not_mem_idealIOdd`) and `z - 1 ∉ 𝓘_odd`
  (`Rneg_sub_one_not_mem_idealIOdd`), because `ρ₂(R_T) = !![1,1;0,1] ≠ 0` and
  `ρ₂(z-1) = -2·1 ≠ 0`.

Since `z - 1 ∈ 𝓘_even`, the second statement shows `𝓘_even ⊄ 𝓘_odd`.  The same computation
applies to `R_T(z-1) = ρ₂(R_T)·(ρ₂(z) - 1) = -2·ρ₂(R_T) ≠ 0`, and

  `R_T·(z-1) = M6_2·S - M6_1 = Work.Residues.rowDiff R_S 2`

is the `S`-row error of the paper's representation `σ_R` in the `M6` basis.  Hence that error
vector does **not** lie in `𝓘_odd`, and the reduction of `R` modulo `𝓘_odd` in the `M6` (or, by
the change of basis `Work.Asymptotics.Pmat`, the `Mp`) basis cannot be obtained from `σ_R`.
The representation governing `R/𝓘_odd` has to be constructed directly; for right
multiplication on `R/𝓘_odd` the error vector vanishes identically, so the six-dimensional
input needed by the propagation argument is *not* of the `rowDiff`-type shape used in the even
case.
-/
import Mathlib
import Submission.Work.Asymptotics.OddIdeal
import Submission.Work.Residues.IdealImRowDiffAll

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups MonoidAlgebra ModularForm

namespace Work.Asymptotics

open Work.Kernels

/-! ## The two-dimensional standard representation `ρ₂` -/

/-- The inclusion `SL(2,ℤ) ↪ M₂(ℤ) ↪ M₂(ℂ)` as a monoid homomorphism: the two-dimensional
standard representation `ρ₂` of `SL(2,ℤ)`. -/
def stdMono : SL(2, ℤ) →* Matrix (Fin 2) (Fin 2) ℂ where
  toFun γ := (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ)
  map_one' := by
    show ((1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.map_one]
    · simp
    · simp
  map_mul' := by
    intro γ δ
    show ((γ * δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ)
      = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ)
        * (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.map_mul]

/-- The two-dimensional standard representation of `R = ℂ[SL(2,ℤ)]`. -/
def rho2 : R →ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  MonoidAlgebra.lift ℂ (Matrix (Fin 2) (Fin 2) ℂ) (SL(2, ℤ)) stdMono

lemma rho2_ofSL (γ : SL(2, ℤ)) : rho2 (ofSL γ) = stdMono γ :=
  MonoidAlgebra.lift_of _ γ

theorem rho2_R_T : rho2 R_T = !![1, 1; 0, 1] := by
  have h : R_T = ofSL ModularGroup.T := rfl
  rw [h, rho2_ofSL]
  show ((ModularGroup.T : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ)
    = !![1, 1; 0, 1]
  rw [ModularGroup.coe_T]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

theorem rho2_R_S : rho2 R_S = !![0, -1; 1, 0] := by
  have h : R_S = ofSL ModularGroup.S := rfl
  rw [h, rho2_ofSL]
  show ((ModularGroup.S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ)
    = !![0, -1; 1, 0]
  rw [ModularGroup.coe_S]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

/-- `ρ₂(z) = -1`. -/
theorem rho2_Rneg : rho2 Rneg = -1 := by
  have h : Rneg = ofSL (-1 : SL(2, ℤ)) := rfl
  rw [h, rho2_ofSL]
  show ((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ) = -1
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply]

/-! ## `ρ₂` kills the odd-weight defect ideal -/

theorem rho2_R_T_sub_one_sq : rho2 ((R_T - 1) ^ 2) = 0 := by
  rw [map_pow, map_sub, map_one, rho2_R_T]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, Fin.sum_univ_two] <;>
    norm_num

theorem rho2_R_S_mul_R_T_sub_one_sq : rho2 (R_S * (R_T - 1) ^ 2) = 0 := by
  rw [map_mul, rho2_R_S, rho2_R_T_sub_one_sq, mul_zero]

theorem rho2_mem_IdealI {x : R} (hx : x ∈ IdealI) : rho2 x = 0 := by
  obtain ⟨a, b, rfl⟩ := mem_span2.mp hx
  simp only [map_add, map_mul, rho2_R_T_sub_one_sq, zero_mul, mul_zero, add_zero]

theorem rho2_Rneg_add_one : rho2 (Rneg + 1) = 0 := by
  rw [map_add, rho2_Rneg, map_one, neg_add_cancel]

theorem rho2_mem_augIdealOdd {x : R} (hx : x ∈ augIdealOdd) : rho2 x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r, s, rfl⟩ := hy
    rw [map_mul rho2 (r * (Rneg + 1)) s, map_mul rho2 r (Rneg + 1), rho2_Rneg_add_one]
    simp
  | zero => rw [map_zero]
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | smul c y _ hy => rw [map_smul, hy, smul_zero]

/-- **`ρ₂` kills the odd-weight defect ideal `𝓘_odd`.** -/
theorem rho2_mem_idealIOdd {x : R} (hx : x ∈ idealIOdd) : rho2 x = 0 := by
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp hx
  rw [← hac, map_add, rho2_mem_IdealI ha, rho2_mem_augIdealOdd hc, add_zero]

/-! ## The no-go lemmas -/

/-- **`R_T ∉ 𝓘_odd`**: `ρ₂` kills `𝓘_odd` but `ρ₂(R_T) = !![1,1;0,1]` is nonzero. -/
theorem R_T_not_mem_idealIOdd : (R_T : R) ∉ idealIOdd := by
  intro h
  have h2 := rho2_mem_idealIOdd h
  rw [rho2_R_T] at h2
  have h4 : ((!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)) 0 0
      = (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by rw [h2]
  rw [show ((!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)) 0 0 = 1 from by
        norm_num [Matrix.of_apply],
      show ((0 : Matrix (Fin 2) (Fin 2) ℂ)) 0 0 = 0 from rfl] at h4
  exact one_ne_zero h4

/-- **`z - 1 ∉ 𝓘_odd`**: `ρ₂(z-1) = -2·1 ≠ 0`.  Since `z - 1 ∈ 𝓘_even`, this shows that the
*even* ideal is not contained in the odd one. -/
theorem Rneg_sub_one_not_mem_idealIOdd : (Rneg - 1 : R) ∉ idealIOdd := by
  intro h
  have h2 := rho2_mem_idealIOdd h
  rw [map_sub, rho2_Rneg, map_one] at h2
  have h4 : ((-1 - 1 : Matrix (Fin 2) (Fin 2) ℂ)) 0 0
      = (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by rw [h2]
  rw [show ((-1 - 1 : Matrix (Fin 2) (Fin 2) ℂ)) 0 0 = -2 from by
        norm_num [Matrix.sub_apply, Matrix.neg_apply, Matrix.one_apply],
      show ((0 : Matrix (Fin 2) (Fin 2) ℂ)) 0 0 = 0 from rfl] at h4
  norm_num at h4

end Work.Asymptotics
