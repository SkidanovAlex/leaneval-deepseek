import Mathlib
import Submission.Work.WilE7.DimOneCells

namespace Work.WilE7.CylAux

open Work.WilE7

/-- A singleton `{t} ⊆ ℝ¹` is a cylindrical cell: it is the graph of the constant
function `t` over the base cell `univ ⊆ ℝ⁰`. -/
theorem cellPt_isCell (t : ℝ) : WilkiesDesign.IsCell 1 (Work.WilE7.cellPt t) := by
  have h : Work.WilE7.cellPt t =
      {z : Fin 1 → ℝ | Fin.init z ∈ Set.univ ∧ z (Fin.last 0) = t} := by
    ext z
    constructor
    · intro hz
      rw [Work.WilE7.mem_cellPt] at hz
      subst hz
      exact ⟨trivial, rfl⟩
    · rintro ⟨-, hz⟩
      rw [Work.WilE7.mem_cellPt, Work.WilE7.pt1_eq_iff]
      exact hz
  rw [h]
  exact WilkiesDesign.IsCell.graph WilkiesDesign.IsCell.zero (fun _ => t) continuousOn_const

/-- An open interval `(a,b) ⊆ ℝ¹` with `a < b` is a cylindrical cell: it is the band
over the base cell `univ ⊆ ℝ⁰` between the constant boundary functions `a` and `b`. -/
theorem cellIoo_isCell {a b : ℝ} (hab : a < b) :
    WilkiesDesign.IsCell 1 (Work.WilE7.cellIoo a b) := by
  have h : Work.WilE7.cellIoo a b =
      {z : Fin 1 → ℝ | Fin.init z ∈ Set.univ ∧
        (fun _ : (Fin 0 → ℝ) => (a : EReal)) (Fin.init z) < ((z (Fin.last 0) : ℝ) : EReal) ∧
        ((z (Fin.last 0) : ℝ) : EReal) <
          (fun _ : (Fin 0 → ℝ) => (b : EReal)) (Fin.init z)} := by
    ext z
    simp only [Work.WilE7.mem_cellIoo, Set.mem_ofPred_eq, Set.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨EReal.coe_lt_coe_iff.mpr h1, EReal.coe_lt_coe_iff.mpr h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  rw [h]
  exact WilkiesDesign.IsCell.band WilkiesDesign.IsCell.zero _ _ continuousOn_const
    continuousOn_const (fun x _ => EReal.coe_lt_coe_iff.mpr hab)

theorem cuts_cell_shapes (U : Finset ℝ) :
    ∀ κ ∈ Work.WilE7.cuts U, WilkiesDesign.IsCell 1 κ ∧ κ.Nonempty := by
  intro κ hκ
  rcases Work.WilE7.mem_cuts.mp hκ with ⟨t, ht, rfl⟩ | ⟨a, ha, b, hb, hab, -, rfl⟩
  · exact ⟨cellPt_isCell t, Work.WilE7.cellPt_nonempty t⟩
  · exact ⟨cellIoo_isCell hab, Work.WilE7.cellIoo_nonempty hab⟩

end Work.WilE7.CylAux
