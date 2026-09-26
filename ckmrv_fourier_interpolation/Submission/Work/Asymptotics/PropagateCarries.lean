/-
# The carries `N₁, N₂, N₃` of the ideal `𝓘` and the "master relation"

This file sets up the algebraic input for the analytic-continuation half of CKMRV
Proposition 3.2(1), in the form needed by `Work.Asymptotics.exists_extension_of_propagates_even`.

The six elements `M6 = (1, T, TS, S, ST, STS)` of `R = ℂ[SL(2,ℤ)]` reduce any `x ∈ R` modulo
the right ideal `𝓘 = (T-I)²R + S(T-I)²R + (z-1)R` (`z = -I`):

  `M6 i * x = ∑ j, σ_R x i j • M6 j + rowDiff x i`,   `rowDiff x i ∈ 𝓘`

(`Work.Residues.rowDiff_mem_of_idealI`).  Since `𝓘 = Work.Kernels.IdealI ⊔ augIdeal` with
`Work.Kernels.IdealI = (T-I)²R + S(T-I)²R` and `augIdeal = (z-1)R`, every element of `𝓘` can be
written as `ξ = (T-I)² * A + S(T-I)² * B + (z-1) * C`, and choosing such a decomposition of
`rowDiff x i` gives the *carries* `N₁, N₂, N₃` (`carr`).

The point of the carries is the **master relation** `slash_carry`: because the slash action is a
left action (`slash k (r * s) F = slash k s (slash k r F)`,
`Work.Kernels.AlgebraFacts.slash_mul`), applying `ξ ∈ 𝓘` to a function `f` satisfying
`T2op f = h₁` and `S2op k f = h₂` at even weight `k` (so `z - 1` acts as `0`,
`Work.Residues.slash_mem_augIdeal`) gives `slash k ξ f = slash k A h₁ + slash k B h₂`.
-/
import Mathlib
import Submission.Work.Kernels.All
import Submission.Work.Residues.Basic
import Submission.Work.Residues.IdealImDefs
import Submission.Work.Residues.IdealImRowDiffAll
import Submission.Work.Residues.ResidueTheorem
import Submission.Work.Asymptotics.PropagateDefs

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels

lemma mul_Rneg_sub_one_comm (x : R) :
    x * (Work.Residues.Rneg - 1) = (Work.Residues.Rneg - 1) * x := by
  rw [mul_sub, sub_mul, Work.Residues.Rneg_comm x, mul_one, one_mul]

/-- The augmentation ideal `(z-1)R` consists exactly of the multiples of `z - 1`. -/
lemma mem_augIdeal_iff (ξ : R) :
    ξ ∈ Work.Residues.augIdeal ↔ ∃ C : R, ξ = (Work.Residues.Rneg - 1) * C := by
  constructor
  · intro hξ
    refine Submodule.span_induction
      (p := fun y _ => ∃ C : R, y = (Work.Residues.Rneg - 1) * C) ?_ ?_ ?_ ?_ hξ
    · rintro y ⟨r, s, rfl⟩
      exact ⟨r * s, by rw [← mul_assoc, mul_Rneg_sub_one_comm r, mul_assoc]⟩
    · exact ⟨0, by rw [mul_zero]⟩
    · rintro y z _ _ ⟨C, hC⟩ ⟨D, hD⟩
      exact ⟨C + D, by rw [hC, hD, mul_add]⟩
    · rintro c y _ ⟨C, hC⟩
      exact ⟨c • C, by rw [hC, mul_smul_comm]⟩
  · rintro ⟨C, rfl⟩
    exact Work.Residues.Rneg_sub_one_mul_mem C

/-- Every element of `𝓘 = (T-I)²R + S(T-I)²R + (z-1)R` is a sum of a multiple of `(T-I)²`, a
multiple of `S(T-I)²` and a multiple of `z - 1`. -/
lemma mem_idealI_exists {ξ : R} (hξ : ξ ∈ Work.Residues.idealI) :
    ∃ A B C : R, ξ = (R_T - 1) ^ 2 * A + R_S * (R_T - 1) ^ 2 * B
      + (Work.Residues.Rneg - 1) * C := by
  rw [Work.Residues.idealI, Submodule.mem_sup] at hξ
  obtain ⟨x, hx, y, hy, hxy⟩ := hξ
  obtain ⟨A, B, hAB⟩ := Work.Kernels.mem_span2.mp hx
  obtain ⟨C, hC⟩ := mem_augIdeal_iff y |>.mp hy
  exact ⟨A, B, C, by rw [← hxy, hAB, hC]⟩

/-- The decomposition of the `i`-th row of the reduction of `x` modulo `𝓘` along the three
generators of `𝓘`.  This packages the CKMRV carry `N_i(x)` of `sigmaandN`. -/
noncomputable def carr (x : R) (i : Fin 6) : R × R × R :=
  Classical.choose (show ∃ p : R × R × R,
      Work.Residues.rowDiff x i = (R_T - 1) ^ 2 * p.1
        + R_S * (R_T - 1) ^ 2 * p.2.1 + (Work.Residues.Rneg - 1) * p.2.2 from by
    obtain ⟨A, B, C, h⟩ := mem_idealI_exists (Work.Residues.rowDiff_mem_of_idealI x i)
    exact ⟨(A, B, C), h⟩)

lemma carr_spec (x : R) (i : Fin 6) :
    Work.Residues.rowDiff x i
      = (R_T - 1) ^ 2 * (carr x i).1
        + R_S * (R_T - 1) ^ 2 * (carr x i).2.1
        + (Work.Residues.Rneg - 1) * (carr x i).2.2 :=
  Classical.choose_spec (show ∃ p : R × R × R,
      Work.Residues.rowDiff x i = (R_T - 1) ^ 2 * p.1
        + R_S * (R_T - 1) ^ 2 * p.2.1 + (Work.Residues.Rneg - 1) * p.2.2 from by
    obtain ⟨A, B, C, h⟩ := mem_idealI_exists (Work.Residues.rowDiff_mem_of_idealI x i)
    exact ⟨(A, B, C), h⟩)

/-- The first carry `N₁` of `rowDiff x i`. -/
noncomputable def carry₁ (x : R) (i : Fin 6) : R := (carr x i).1

/-- The second carry `N₂` of `rowDiff x i`. -/
noncomputable def carry₂ (x : R) (i : Fin 6) : R := (carr x i).2.1

/-- The third carry `N₃` of `rowDiff x i`; it is invisible at even weight. -/
noncomputable def carry₃ (x : R) (i : Fin 6) : R := (carr x i).2.2

lemma carry_spec (x : R) (i : Fin 6) :
    Work.Residues.rowDiff x i
      = (R_T - 1) ^ 2 * carry₁ x i
        + R_S * (R_T - 1) ^ 2 * carry₂ x i
        + (Work.Residues.Rneg - 1) * carry₃ x i :=
  carr_spec x i

/-- **The master relation.**  If `f` satisfies the two functional equations `T2op f = h₁` and
`S2op k f = h₂` (everywhere) at even weight `k`, then the slash of `f` by any element `ξ` of the
ideal `𝓘` is the corresponding combination of the defect functions with the carries of `ξ`. -/
theorem slash_carry (k : ℤ) (hk : Even k) {ξ : R} (hξ : ξ ∈ Work.Residues.idealI)
    {f h₁ h₂ : ℍ → ℂ} (hT : T2op f = h₁) (hS : S2op k f = h₂) :
    ∃ A B : R, slash k ξ f = slash k A h₁ + slash k B h₂ := by
  obtain ⟨A, B, C, rfl⟩ := mem_idealI_exists hξ
  refine ⟨A, B, ?_⟩
  simp only [Work.Kernels.slash_add]
  rw [Work.Kernels.AlgebraFacts.slash_mul, Work.Kernels.slash_T2, hT]
  rw [show Work.Kernels.slash k (R_S * (R_T - 1) ^ 2 * B) f
      = slash k B (S2op k f) from by
    rw [Work.Kernels.AlgebraFacts.slash_mul]; rfl]
  rw [hS]
  rw [Work.Residues.slash_mem_augIdeal hk
    (Work.Residues.Rneg_sub_one_mul_mem C) f]
  ring


/-- The master relation specialised to the error vector `rowDiff`: the slash of `rowDiff x i`
by `f` is the two carries applied to the defect functions. -/
theorem slash_rowDiff (k : ℤ) (hk : Even k) (x : R) (i : Fin 6) {f h₁ h₂ : ℍ → ℂ}
    (hT : T2op f = h₁) (hS : S2op k f = h₂) :
    slash k (Work.Residues.rowDiff x i) f
      = slash k (carry₁ x i) h₁ + slash k (carry₂ x i) h₂ := by
  rw [carry_spec x i]
  simp only [Work.Kernels.slash_add]
  rw [Work.Kernels.AlgebraFacts.slash_mul, Work.Kernels.slash_T2, hT]
  rw [show Work.Kernels.slash k (R_S * (R_T - 1) ^ 2 * carry₂ x i) f
      = slash k (carry₂ x i) (S2op k f) from by
    rw [Work.Kernels.AlgebraFacts.slash_mul]; rfl]
  rw [hS]
  rw [Work.Residues.slash_mem_augIdeal hk
    (Work.Residues.Rneg_sub_one_mul_mem (carry₃ x i)) f]
  ring

/-- **The propagation formula.**  For any `γ ∈ SL(2,ℤ)`, the slash by `γ` of a function `f`
satisfying the two functional equations is the corresponding combination of the six basis
slashes `f |_k M6 j` and of the two defect functions, with the carries of `rowDiff γ 0` as
coefficients.  This is CKMRV (3.7)/`sigmaandN` read at the first row. -/
theorem slash_of_eq (k : ℤ) (hk : Even k) (γ : SL(2, ℤ)) {f h₁ h₂ : ℍ → ℂ}
    (hT : T2op f = h₁) (hS : S2op k f = h₂) :
    slash k (MonoidAlgebra.of ℂ SL(2,ℤ) γ) f
      = slash k (∑ j : Fin 6,
            (Work.Residues.sigmaR (MonoidAlgebra.of ℂ SL(2,ℤ) γ) 0 j) •
              Work.Residues.M6 j) f
        + slash k (carry₁ (MonoidAlgebra.of ℂ SL(2,ℤ) γ) 0) h₁
        + slash k (carry₂ (MonoidAlgebra.of ℂ SL(2,ℤ) γ) 0) h₂ := by
  have hrow := slash_rowDiff k hk (MonoidAlgebra.of ℂ SL(2,ℤ) γ) 0 hT hS
  have hsplit : MonoidAlgebra.of ℂ SL(2,ℤ) γ
      = (∑ j : Fin 6,
            (Work.Residues.sigmaR (MonoidAlgebra.of ℂ SL(2,ℤ) γ) 0 j) •
              Work.Residues.M6 j)
        + Work.Residues.rowDiff (MonoidAlgebra.of ℂ SL(2,ℤ) γ) 0 := by
    rw [Work.Residues.rowDiff, Work.Residues.M6_zero, one_mul]
    rw [add_comm]
    exact (sub_add_cancel _ _).symm
  conv_lhs => rw [hsplit]
  rw [Work.Kernels.slash_add, hrow, add_assoc]

end Work.Asymptotics
