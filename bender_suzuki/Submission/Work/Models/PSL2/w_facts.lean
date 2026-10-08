import Mathlib
import Submission.Work.Models.PSL2.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Models.PSL2

theorem w_facts {F : Type*} [Field F] [CharP F 2] :
    Work.Models.PSL2.w (F := F) ∉ Work.Models.PSL2.B (F := F) ∧
      (∀ d : Work.Models.SL2 F, d ∈ Work.Models.PSL2.D (F := F) →
        Work.Models.PSL2.w (F := F) * d * (Work.Models.PSL2.w (F := F))⁻¹ = d⁻¹) ∧
      Work.Models.PSL2.w (F := F) ∈ Subgroup.normalizer
        ((Work.Models.PSL2.D (F := F) : Subgroup (Work.Models.SL2 F)) : Set (Work.Models.SL2 F)) := by
  -- The Weyl element is an involution, so it is its own inverse.
  have hwinv : (w (F := F))⁻¹ = w (F := F) :=
    inv_eq_of_mul_eq_one_right (w_invol (F := F))
  -- Conjugation by `w` swaps the two diagonal entries of any `2 × 2` matrix.
  have hcoe : ∀ A : SL2 F,
      ((w (F := F) * A * (w (F := F))⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
        !![(A : Matrix (Fin 2) (Fin 2) F) 1 1, (A : Matrix (Fin 2) (Fin 2) F) 1 0;
           (A : Matrix (Fin 2) (Fin 2) F) 0 1, (A : Matrix (Fin 2) (Fin 2) F) 0 0] := by
    intro A
    rw [hwinv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, w_coe]
    ext i j
    fin_cases i <;> fin_cases j <;>
      · simp only [Matrix.mul_apply, Fin.sum_univ_two]
        simp only [Fin.isValue, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_mul, one_mul,
          mul_zero, mul_one, zero_add, add_zero]
  -- Conjugation by `w` inverts every element of the standard torus `D`.
  have hconj : ∀ d : SL2 F, d ∈ D (F := F) → w (F := F) * d * (w (F := F))⁻¹ = d⁻¹ := by
    intro d hd
    obtain ⟨h01, h10⟩ := hd
    refine Subtype.ext ?_
    rw [hcoe, Matrix.SpecialLinearGroup.SL2_inv_expl]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Fin.isValue, CharTwo.neg_eq, h01, h10]
  refine ⟨?_, hconj, ?_⟩
  · -- `w` is not upper triangular: its `(1,0)` entry is `1 ≠ 0`.
    intro hw
    rw [mem_B_iff, inB, w_coe] at hw
    simp at hw
  · -- `w` permutes `D`: it conjugates each element of `D` to its inverse.
    rw [Subgroup.mem_set_normalizer_iff]
    intro n
    constructor
    · intro hn
      rw [hconj n hn]
      exact D.inv_mem hn
    · intro hn
      have hx : w (F := F) * (w (F := F) * n * (w (F := F))⁻¹) * (w (F := F))⁻¹ ∈ D (F := F) := by
        rw [hconj _ hn]
        exact D.inv_mem hn
      have heq : w (F := F) * (w (F := F) * n * (w (F := F))⁻¹) * (w (F := F))⁻¹ = n := by
        rw [hwinv]
        have h2 : w (F := F) * (w (F := F) * n * w (F := F)) * w (F := F) =
            (w (F := F) * w (F := F)) * n * (w (F := F) * w (F := F)) := by group
        rw [h2, w_invol, one_mul, mul_one]
      rwa [heq] at hx

end Work.Models.PSL2
