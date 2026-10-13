import Mathlib
import Submission.Work.WilkG4c.ExactCellDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG0 Work.WilG1

/-- **The chart maps the cube into the fibre.** -/
theorem exactCell_mem {p : ℕ} {κ : Set (Fin (p + 1) → ℝ)} {f : (Fin (p + 1) → ℝ) → ℝ}
    {g : (Fin (p + 1) → ℝ) → ℝ} {α β : (Fin p → ℝ) → ℝ} {l : Fin p → ℝ}
    (hF : CellFacts κ f g α β l) (hcube : κ ⊆ Work.WilG4c.inCubeSet p 1) :
    ∀ t ∈ openCube 1, chartVal g α β l t ∈ Set.Ioo (0 : ℝ) 1 ∧
      Fin.snoc l (chartVal g α β l t) ∈ κ := by
  intro t ht
  have ht0 : t 0 ∈ Set.Ioo (0 : ℝ) 1 := ht 0
  obtain ⟨s, hs1, hs2⟩ := hF.img (t 0) ht0
  have hgv : g (Fin.snoc l (α l + t 0 * (β l - α l))) = s :=
    hF.inv_eq (α l + t 0 * (β l - α l)) s (by rw [mem_invSet]; exact ⟨hs1, hs2⟩)
  have hφt : chartVal g α β l t = s := hgv
  exact ⟨by rw [hφt]; simpa using inCubeSet_one_last (hcube hs1), by rw [hφt]; exact hs1⟩

/-- **The chart hits every point of the fibre with `(0,1)`-coordinate.** -/
theorem exactCell_surj {p : ℕ} {κ : Set (Fin (p + 1) → ℝ)} {f : (Fin (p + 1) → ℝ) → ℝ}
    {g : (Fin (p + 1) → ℝ) → ℝ} {α β : (Fin p → ℝ) → ℝ} {l : Fin p → ℝ}
    (hF : CellFacts κ f g α β l) :
    ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) 1 → Fin.snoc l s ∈ κ →
      ∃ t ∈ openCube 1, chartVal g α β l t = s := by
  intro s _ hsκ
  by_cases hlt : α l < β l
  · have hstr := hF.strict hlt s hsκ
    have hpos : 0 < β l - α l := sub_pos.mpr hlt
    refine ⟨fun _ : Fin 1 => (f (Fin.snoc l s) - α l) / (β l - α l), ?_, ?_⟩
    · intro i
      exact ⟨div_pos (sub_pos.mpr hstr.1) hpos, by rw [div_lt_one hpos]; linarith [hstr.2]⟩
    · have hA : α l + ((f (Fin.snoc l s) - α l) / (β l - α l)) * (β l - α l)
          = f (Fin.snoc l s) := by
        field_simp
        ring
      have hgv : g (Fin.snoc l (α l + ((f (Fin.snoc l s) - α l) / (β l - α l))
          * (β l - α l))) = s :=
        hF.inv_eq _ s (by rw [mem_invSet]; exact ⟨hsκ, hA.symm⟩)
      rw [chartVal]
      exact hgv
  · have heq : α l = β l := le_antisymm hF.le (le_of_not_gt hlt)
    have hfs : f (Fin.snoc l s) = α l := by
      have h1 := (hF.bound s hsκ).1
      have h2 := (hF.bound s hsκ).2
      exact le_antisymm (by rw [heq]; exact h2) h1
    refine ⟨fun _ : Fin 1 => (1 : ℝ) / 2, ?_, ?_⟩
    · intro i
      exact ⟨by norm_num, by norm_num⟩
    · have hA : α l + ((1 : ℝ) / 2) * (β l - α l) = f (Fin.snoc l s) := by
        rw [hfs, heq]
        ring
      have hgv : g (Fin.snoc l (α l + ((1 : ℝ) / 2) * (β l - α l))) = s :=
        hF.inv_eq _ s (by rw [mem_invSet]; exact ⟨hsκ, hA.symm⟩)
      rw [chartVal]
      exact hgv

end Work.WilkG4c
