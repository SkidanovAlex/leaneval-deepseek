import Mathlib
import Submission.Work.WilG4a.f1affine1_defs
import Submission.Work.WilG4a.Cells
import Submission.Work.WilG4a.fibre_endpoints_bounds

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4a

/-- A subsingleton subset of `ℝ` -- possibly empty -- has equal infimum and supremum.
This is the degenerate half of the fibre dichotomy: a cell fibre over a parameter is either a
point (or empty), in which case `sInf = sSup`, or a genuine open interval. -/
theorem subsingleton_sInf_eq_sSup {s : Set ℝ} (h : s.Subsingleton) : sInf s = sSup s := by
  refine Set.Subsingleton.induction_on (p := fun t : Set ℝ => sInf t = sSup t) h ?_ ?_
  · simp [Real.sInf_empty, Real.sSup_empty]
  · intro x
    simp

/-- **Fibre dichotomy for a good cell.**  The fibre of a good cell over a parameter `l` is
either a subsingleton (with `sInf = sSup`), or the open interval spanned by its own infimum and
supremum, of positive length and contained in `I = (0,1)`.

The point is that `GoodCell_w` already exposes the fibre as `Subsingleton ∨ Ioo a b`; in the
interval case nonemptiness gives `a < b`, so `sInf`/`sSup` compute to the two endpoints `a`,
`b`, and the strip condition `κ ⊆ {z | z(last) ∈ I}` confines the fibre to `I`, bounding those
endpoints in `[0,1]`. -/
theorem goodCell_fibre_dichotomy {p k r : ℕ} {F : Fin k → (Fin p → ℝ) → ℝ → ℝ}
    {κ : Set (Fin (p + 1) → ℝ)} (hcell : Work.WilG4a.GoodCell_w k r F κ) (l : Fin p → ℝ) :
    (Work.WilG4a.fibre κ l).Subsingleton ∧ sInf (Work.WilG4a.fibre κ l) = sSup (Work.WilG4a.fibre κ l) ∨
      (Work.WilG4a.fibre κ l = Set.Ioo (sInf (Work.WilG4a.fibre κ l)) (sSup (Work.WilG4a.fibre κ l)) ∧
        sInf (Work.WilG4a.fibre κ l) < sSup (Work.WilG4a.fibre κ l) ∧
        0 ≤ sInf (Work.WilG4a.fibre κ l) ∧ sSup (Work.WilG4a.fibre κ l) ≤ 1) := by
  obtain ⟨hstrip, hdich, -⟩ := hcell
  rcases hdich l with hsub | ⟨a, b, hfib⟩
  · exact Or.inl ⟨hsub, subsingleton_sInf_eq_sSup hsub⟩
  · by_cases hne : (fibre κ l).Nonempty
    · -- The fibre is a genuine open interval: compute its infimum/supremum and bound it.
      have hne' : (Set.Ioo a b).Nonempty := by rw [← hfib]; exact hne
      have hlt : a < b := Set.nonempty_Ioo.mp hne'
      have hsInf : sInf (fibre κ l) = a := by rw [hfib]; exact csInf_Ioo hlt
      have hsSup : sSup (fibre κ l) = b := by rw [hfib]; exact csSup_Ioo hlt
      have hsubI : Set.Ioo a b ⊆ Set.Ioo 0 1 := by
        intro y hy
        have hyfib : y ∈ fibre κ l := by rw [hfib]; exact hy
        have hmem : Fin.snoc l y ∈ strip p := hstrip hyfib
        have hI : y ∈ I := (strip_mem_iff_snoc l y).mp hmem
        simpa [I] using hI
      obtain ⟨h0a, hb1⟩ := bounds_of_Ioo_subset_Ioo hsubI hlt
      exact Or.inr
        ⟨by rw [hsInf, hsSup]; exact hfib,
         by rw [hsInf, hsSup]; exact hlt,
         by rw [hsInf]; exact h0a,
         by rw [hsSup]; exact hb1⟩
    · -- The fibre is empty, hence a subsingleton: fall back on the degenerate branch.
      rw [Set.not_nonempty_iff_eq_empty] at hne
      have hsub' : (fibre κ l).Subsingleton := by rw [hne]; exact Set.subsingleton_empty
      exact Or.inl ⟨hsub', subsingleton_sInf_eq_sSup hsub'⟩

end Work.WilG4a
