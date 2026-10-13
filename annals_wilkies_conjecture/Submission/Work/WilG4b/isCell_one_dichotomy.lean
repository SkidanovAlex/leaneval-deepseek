import Mathlib
import Submission.Work.Wilkies.Defs

open Set

namespace Work.WilG4b

/-! ### Helper lemmas: the EReal half-lines are open in `ℝ` -/

/-- For any `a : EReal`, the set of reals `y` with `a < y` (in `EReal`) is open. -/
private theorem isOpen_lt_coe_ereal (a : EReal) : IsOpen {y : ℝ | a < (y : EReal)} := by
  have h : {y : ℝ | a < (y : EReal)} = ((↑) : ℝ → EReal) ⁻¹' (Ioi a) := rfl
  rw [h]
  have h2 : ((↑) : ℝ → EReal) ⁻¹' (Ioi a ∩ range ((↑) : ℝ → EReal))
      = ((↑) : ℝ → EReal) ⁻¹' (Ioi a) := by
    rw [preimage_inter, preimage_range, inter_univ]
  rw [← h2]
  exact (isOpen_Ioi.inter EReal.isOpenEmbedding_coe.isOpen_range).preimage
    continuous_coe_real_ereal

/-- For any `b : EReal`, the set of reals `y` with `y < b` (in `EReal`) is open. -/
private theorem isOpen_coe_lt_ereal (b : EReal) : IsOpen {y : ℝ | (y : EReal) < b} := by
  have h : {y : ℝ | (y : EReal) < b} = ((↑) : ℝ → EReal) ⁻¹' (Iio b) := rfl
  rw [h]
  have h2 : ((↑) : ℝ → EReal) ⁻¹' (Iio b ∩ range ((↑) : ℝ → EReal))
      = ((↑) : ℝ → EReal) ⁻¹' (Iio b) := by
    rw [preimage_inter, preimage_range, inter_univ]
  rw [← h2]
  exact (isOpen_Iio.inter EReal.isOpenEmbedding_coe.isOpen_range).preimage
    continuous_coe_real_ereal

/-- The only cell in `ℝ⁰` is `Set.univ`. -/
private theorem isCell_zero_eq_univ {C : Set (Fin 0 → ℝ)} (h : WilkiesDesign.IsCell 0 C) :
    C = Set.univ := by
  cases h
  rfl

/-- A cell in `ℝ¹` is either a single point or an open set: a `graph` cell over the
one-point base `ℝ⁰` is a singleton, and a `band` cell over `ℝ⁰` is the preimage of an
open interval of `EReal` under the continuous map `z ↦ z 0`. -/
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

end Work.WilG4b
