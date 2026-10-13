import Mathlib
import Submission.Work.Wilkies.Defs

open Set

namespace Work.WilG4a

/-- The half-line `{y : ℝ | a < (y : EReal)}`, for arbitrary `a : EReal`, is open in `ℝ`. -/
private theorem isOpen_lt_coe_ereal (a : EReal) : IsOpen {y : ℝ | a < (y : EReal)} := by
  have h : {y : ℝ | a < (y : EReal)} = Real.toEReal ⁻¹' (Ioi a) := rfl
  rw [h]
  exact isOpen_Ioi.preimage continuous_coe_real_ereal

/-- The half-line `{y : ℝ | (y : EReal) < b}`, for arbitrary `b : EReal`, is open in `ℝ`. -/
private theorem isOpen_coe_lt_ereal (b : EReal) : IsOpen {y : ℝ | (y : EReal) < b} := by
  have h : {y : ℝ | (y : EReal) < b} = Real.toEReal ⁻¹' (Iio b) := rfl
  rw [h]
  exact isOpen_Iio.preimage continuous_coe_real_ereal

/-- Cells in `ℝ⁰` are trivial: the only cell is all of `ℝ⁰`. -/
private theorem isCell_zero_eq_univ {C : Set (Fin 0 → ℝ)} (h : WilkiesDesign.IsCell 0 C) :
    C = Set.univ := by
  cases h
  rfl

/-- In dimension one the cells are exactly the singletons and the open sets: `IsCell 1 c`
splits into the graph case (over the trivial base cell, hence a singleton) and the band case
(over the trivial base cell, hence a bounded open interval, in particular open). -/
theorem isCell_one_dichotomy {c : Set (Fin 1 → ℝ)} (h : WilkiesDesign.IsCell 1 c) :
    (∃ p : Fin 1 → ℝ, c = {p}) ∨ IsOpen c := by
  cases h with
  | graph hC f hf =>
    rw [isCell_zero_eq_univ hC]
    left
    refine ⟨Fin.snoc (Fin.elim0 : Fin 0 → ℝ) (f Fin.elim0), ?_⟩
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_univ, true_and]
    constructor
    · rintro hz
      have hinit : Fin.init z = Fin.elim0 := Subsingleton.elim _ _
      rw [← Fin.snoc_init_self z, hz, hinit]
    · rintro rfl
      rw [Fin.init_snoc, Fin.snoc_last]
  | band hC a b ha hb hab =>
    rw [isCell_zero_eq_univ hC]
    right
    have hcoe : IsOpen {y : ℝ | a (Fin.elim0) < (y : EReal) ∧ (y : EReal) < b (Fin.elim0)} :=
      (isOpen_lt_coe_ereal _).inter (isOpen_coe_lt_ereal _)
    have hc : {z : Fin 1 → ℝ | Fin.init z ∈ Set.univ ∧
          a (Fin.init z) < ((z (Fin.last 0) : ℝ) : EReal) ∧
          ((z (Fin.last 0) : ℝ) : EReal) < b (Fin.init z)}
        = (fun z : Fin 1 → ℝ => z 0) ⁻¹'
            {y : ℝ | a (Fin.elim0) < (y : EReal) ∧ (y : EReal) < b (Fin.elim0)} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_univ, true_and]
      rw [Fin.fin_one_eq_zero (Fin.last 0)]
      have hinit : Fin.init z = Fin.elim0 := Subsingleton.elim _ _
      rw [hinit]
    rw [hc]
    exact hcoe.preimage (continuous_apply (0 : Fin 1))

end Work.WilG4a
