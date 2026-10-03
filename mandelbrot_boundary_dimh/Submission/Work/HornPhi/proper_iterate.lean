import Mathlib
import Submission.Work.Interfaces.HornParts

/-!
# Properness of the iterates of `f₀` on the immediate basin `B`

If `f₀ : B → B` is proper (one of the clauses of `IsImmediateBasin`) and forwards-invariant on
`B`, then so is every iterate `f₀^[N] : B → B`: for every compact `L ⊆ B`,
`B ∩ (f₀^[N]) ⁻¹' L` is compact.

Route: induction on `N`.  For `N = 0` the set is `B ∩ L = L`.  For `N = k+1`, use
`f₀^[k+1] = f₀^[k] ∘ f₀` and the fact that `MapsTo f₀ B B` makes
`B ∩ f₀ ⁻¹' (B ∩ (f₀^[k]) ⁻¹' L) = B ∩ (f₀^[k+1]) ⁻¹' L`; the inner set
`B ∩ (f₀^[k]) ⁻¹' L` is compact by the induction hypothesis and lies in `B`, and properness of `f₀`
applies to it.
-/

namespace Work.HornPhi

open MandelDim

theorem proper_iterate {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ} {d : MandelDim.ParabData f₀ D₀}
    (h : MandelDim.IsF0Setup f₀ D₀ B c) (N : ℕ) :
    ∀ L : Set ℂ, L ⊆ B → IsCompact L → IsCompact (B ∩ (f₀^[N]) ⁻¹' L) := by
  -- Unwind the two clauses of `IsImmediateBasin` that the induction uses.
  obtain ⟨_, _, _, _, hBMaps, _, hBproper⟩ := h.2.1
  intro L hLB hL
  induction N with
  | zero =>
      -- `f₀^[0] = id`, so the set is `B ∩ L = L` because `L ⊆ B`.
      have h0 : (f₀^[0]) ⁻¹' L = L := by
        ext z
        simp [Function.iterate_zero]
      rw [h0, Set.inter_eq_right.mpr hLB]
      exact hL
  | succ k ih =>
      -- Compactness of the inner set, by the induction hypothesis.
      have hK : IsCompact (B ∩ (f₀^[k]) ⁻¹' L) := ih
      -- `B ∩ (f₀^[k+1]) ⁻¹' L = B ∩ f₀ ⁻¹' (B ∩ (f₀^[k]) ⁻¹' L)`.
      have hset : B ∩ (f₀^[k + 1]) ⁻¹' L = B ∩ f₀ ⁻¹' (B ∩ (f₀^[k]) ⁻¹' L) := by
        ext z
        simp only [Set.mem_inter_iff, Set.mem_preimage, Function.iterate_succ,
          Function.comp_apply]
        constructor
        · rintro ⟨hzB, hz⟩
          exact ⟨hzB, hBMaps hzB, hz⟩
        · rintro ⟨hzB, _, hz⟩
          exact ⟨hzB, hz⟩
      rw [hset]
      exact hBproper _ Set.inter_subset_left hK

end Work.HornPhi
