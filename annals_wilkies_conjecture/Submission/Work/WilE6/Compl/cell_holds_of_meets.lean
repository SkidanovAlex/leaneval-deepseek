import Mathlib
import Submission.Work.WilE5.Cells.cellBasic

namespace Work.WilE6.Compl

open WilkiesDesign WilkiesDesign.E

/-- If the sign cell of `σ` holds at `v`, then `σ` is exactly the sign assignment of the atoms of
`X` at `v`: the sign condition imposed by `σ` on the `i`-th atom is the true sign of that atom. -/
theorem signOf_get_eq_of_cell_holds {k : ℕ} (X : SemiPf k)
    (σ : Fin (Work.WilE5.atomsOf X).length → Work.WilE5.Sign) {v : Fin k → ℝ}
    (hv : (Work.WilE5.cell X σ).holds X.c v) (i : Fin (Work.WilE5.atomsOf X).length) :
    Work.WilE5.signOf (eaEval X.c ((Work.WilE5.atomsOf X).get i) v) = σ i := by
  by_contra hne
  exact Work.WilE5.holds_not_both hne
    ⟨Work.WilE5.signOf_holds (eaEval X.c ((Work.WilE5.atomsOf X).get i) v),
      (Work.WilE5.cell_holds_iff X σ v).mp hv i⟩

theorem cell_holds_of_meets {k : ℕ} (X : WilkiesDesign.E.SemiPf k)
    (σ : Fin (Work.WilE5.atomsOf X).length → Work.WilE5.Sign)
    {B : WilkiesDesign.E.Basic k X.r} (hB : B ∈ X.basics) {w : Fin k → ℝ}
    (hw : (Work.WilE5.cell X σ).holds X.c w) (hBw : B.holds X.c w) :
    ∀ x : Fin k → ℝ, (Work.WilE5.cell X σ).holds X.c x → B.holds X.c x := by
  intro x hx
  have hsig_w : ∀ i, Work.WilE5.signOf (eaEval X.c ((Work.WilE5.atomsOf X).get i) w) = σ i :=
    fun i => signOf_get_eq_of_cell_holds X σ hw i
  have hsig_x : ∀ i, Work.WilE5.signOf (eaEval X.c ((Work.WilE5.atomsOf X).get i) x) = σ i :=
    fun i => signOf_get_eq_of_cell_holds X σ hx i
  refine ⟨fun f hf => ?_, fun g hg => ?_⟩
  · obtain ⟨i, hif⟩ :=
      List.mem_iff_get.mp (Work.WilE5.mem_atomsOf_of_mem_basics hB (Or.inl hf))
    have hz : eaEval X.c ((Work.WilE5.atomsOf X).get i) w = 0 := by rw [hif]; exact hBw.1 f hf
    have hσ : σ i = Work.WilE5.Sign.zero := by
      rw [← hsig_w i]
      exact Work.WilE5.signOf_eq_zero_iff.mpr hz
    have hi := hsig_x i
    rw [hσ] at hi
    have hx0 : eaEval X.c ((Work.WilE5.atomsOf X).get i) x = 0 :=
      Work.WilE5.signOf_eq_zero_iff.mp hi
    rw [← hif]
    exact hx0
  · obtain ⟨i, hif⟩ :=
      List.mem_iff_get.mp (Work.WilE5.mem_atomsOf_of_mem_basics hB (Or.inr hg))
    have hp : 0 < eaEval X.c ((Work.WilE5.atomsOf X).get i) w := by rw [hif]; exact hBw.2 g hg
    have hσ : σ i = Work.WilE5.Sign.pos := by
      rw [← hsig_w i]
      exact Work.WilE5.signOf_eq_pos_iff.mpr hp
    have hi := hsig_x i
    rw [hσ] at hi
    have hxp : 0 < eaEval X.c ((Work.WilE5.atomsOf X).get i) x :=
      Work.WilE5.signOf_eq_pos_iff.mp hi
    rw [← hif]
    exact hxp

end Work.WilE6.Compl
