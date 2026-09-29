import Mathlib
import Submission.Work.TMC16Core.Defs

namespace Work.TMC16Core.Core

theorem Uniform_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {ε : ℝ} {z : ι → ℝ} {w : κ → ℝ} (e : ι ≃ κ) (h : ∀ i, w (e i) = z i)
    (hz : Work.TMC16Core.Uniform ε z) : Work.TMC16Core.Uniform ε w := by
  rw [Work.TMC16Core.Uniform] at hz ⊢
  refine ⟨?_, ?_⟩
  · intro k l hkl
    have hk : w k = z (e.symm k) := by simpa using h (e.symm k)
    have hl : w l = z (e.symm l) := by simpa using h (e.symm l)
    rw [hk, hl]
    exact hz.1 (e.symm k) (e.symm l) (fun hh => hkl (e.symm.injective hh))
  · intro j x hx
    have key : (∏ i ∈ Finset.univ.erase (e.symm j),
          (x - Real.cos (2 * Real.pi * z i)) /
            (Real.cos (2 * Real.pi * z (e.symm j)) - Real.cos (2 * Real.pi * z i)))
        = (∏ i ∈ Finset.univ.erase j,
          (x - Real.cos (2 * Real.pi * w i)) /
            (Real.cos (2 * Real.pi * w j) - Real.cos (2 * Real.pi * w i))) := by
      refine Finset.prod_equiv e ?_ ?_
      · intro i
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        constructor
        · intro hi hh
          exact hi (e.injective (by rw [hh, Equiv.apply_symm_apply e j]))
        · intro hi hh
          exact hi (by rw [hh, Equiv.apply_symm_apply e j])
      · intro i hi
        rw [h i, show w j = z (e.symm j) from by simpa using h (e.symm j)]
    rw [← key]
    rw [← Fintype.card_congr e]
    exact hz.2 (e.symm j) x hx

end Work.TMC16Core.Core
