import Mathlib
import Submission.Work.Peluse.VanDerCorput.Defs

namespace Work.Peluse.VanDerCorput

open scoped BigOperators

/-- The shift-sum identity behind the van der Corput argument: summing the shifted correlation
`star (zext I g (u + h₁)) * zext I g (u + h₂)` over the window `u ∈ [1 - H, M - 1]` is the same as
summing `star (g (y + (h₁ - h₂))) * g y` over those `y ∈ [1, M]` with `y + (h₁ - h₂) ∈ [1, M]`.

The hypothesis `h₂ ∈ [1, H]` is exactly what makes the two index sets correspond: it gives
`1 - H ≤ y - h₂ ≤ M - 1` for `y ∈ [1, M]`. -/
theorem shift_sum_zext_eq {M H : ℕ} (g : ℤ → ℂ) {h₁ h₂ : ℤ}
    (h₂H : h₂ ∈ Finset.Icc (1 : ℤ) (H : ℤ)) :
    ∑ u ∈ Finset.Icc (1 - (H : ℤ)) ((M : ℤ) - 1),
        star (Work.Peluse.VanDerCorput.zext (Finset.Icc (1 : ℤ) (M : ℤ)) g (u + h₁)) *
          Work.Peluse.VanDerCorput.zext (Finset.Icc (1 : ℤ) (M : ℤ)) g (u + h₂) =
      ∑ y ∈ (Finset.Icc (1 : ℤ) (M : ℤ)).filter
              (fun y => y + (h₁ - h₂) ∈ Finset.Icc (1 : ℤ) (M : ℤ)),
        star (g (y + (h₁ - h₂))) * g y := by
  have h2lo : (1 : ℤ) ≤ h₂ := (Finset.mem_Icc.mp h₂H).1
  have h2hi : h₂ ≤ (H : ℤ) := (Finset.mem_Icc.mp h₂H).2
  -- the summands of the left-hand side, written with an explicit indicator
  have key : ∀ u : ℤ,
      star (zext (Finset.Icc (1 : ℤ) (M : ℤ)) g (u + h₁)) *
        zext (Finset.Icc (1 : ℤ) (M : ℤ)) g (u + h₂) =
      if u + h₁ ∈ Finset.Icc (1 : ℤ) (M : ℤ) ∧ u + h₂ ∈ Finset.Icc (1 : ℤ) (M : ℤ)
        then star (g (u + h₁)) * g (u + h₂) else 0 := by
    intro u
    by_cases ha : u + h₁ ∈ Finset.Icc (1 : ℤ) (M : ℤ) <;>
      by_cases hb : u + h₂ ∈ Finset.Icc (1 : ℤ) (M : ℤ) <;>
      simp [zext, ha, hb]
  have stepA :
      (∑ u ∈ Finset.Icc (1 - (H : ℤ)) ((M : ℤ) - 1),
          star (zext (Finset.Icc (1 : ℤ) (M : ℤ)) g (u + h₁)) *
            zext (Finset.Icc (1 : ℤ) (M : ℤ)) g (u + h₂))
        = ∑ u ∈ (Finset.Icc (1 - (H : ℤ)) ((M : ℤ) - 1)).filter
              (fun u => u + h₁ ∈ Finset.Icc (1 : ℤ) (M : ℤ) ∧
                u + h₂ ∈ Finset.Icc (1 : ℤ) (M : ℤ)),
            star (g (u + h₁)) * g (u + h₂) := by
    rw [Finset.sum_congr rfl (fun u _ => key u)]
    exact (Finset.sum_filter (s := Finset.Icc (1 - (H : ℤ)) ((M : ℤ) - 1))
      (fun u => u + h₁ ∈ Finset.Icc (1 : ℤ) (M : ℤ) ∧
        u + h₂ ∈ Finset.Icc (1 : ℤ) (M : ℤ))
      (fun u => star (g (u + h₁)) * g (u + h₂))).symm
  rw [stepA]
  -- reindex `u ↦ u + h₂`
  refine Finset.sum_bij (fun u _ => u + h₂) ?_ ?_ ?_ ?_
  · intro u hu
    obtain ⟨-, h₁', h₂'⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_filter.mpr ⟨h₂', by
      rw [show (u + h₂) + (h₁ - h₂) = u + h₁ by ring]
      exact h₁'⟩
  · intro a _ b _ hab
    omega
  · intro y hy
    obtain ⟨hyI, hyh⟩ := Finset.mem_filter.mp hy
    have hy1 : (1 : ℤ) ≤ y := (Finset.mem_Icc.mp hyI).1
    have hyM : y ≤ (M : ℤ) := (Finset.mem_Icc.mp hyI).2
    refine ⟨y - h₂, ?_, by ring⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_, ?_⟩
    · rw [show (y - h₂) + h₁ = y + (h₁ - h₂) by ring]; exact hyh
    · rw [show (y - h₂) + h₂ = y by ring]; exact hyI
  · intro u _
    rw [show (u + h₂) + (h₁ - h₂) = u + h₁ by ring]

end Work.Peluse.VanDerCorput
