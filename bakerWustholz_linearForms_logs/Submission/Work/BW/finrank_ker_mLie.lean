import Mathlib
import Submission.Work.BW.finrank_lieSubDefs
import Submission.Work.BW.finrank_ker_mulVecLin_fin

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Base change of linear independence along `ℚ → ℂ`: if the rows of an integer matrix `M` are
`ℚ`-linearly independent, then the rows `fun i => (M j i : ℂ)` of the entrywise cast matrix are
`ℂ`-linearly independent. -/
theorem linearIndependent_int_cast_row {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ)
    (hM : LinearIndependent ℚ (fun j i => (M j i : ℚ))) :
    LinearIndependent ℂ (fun j i => (M j i : ℂ)) := by
  have h := (linearIndependent_algebraMap_comp_iff (R := ℚ) (S := ℂ)
      (v := fun (j : Fin ρ) (i : Fin N) => (M j i : ℚ))).mpr hM
  have hfun : (fun j i => (M j i : ℂ))
      = (fun j => ⇑(algebraMap ℚ ℂ) ∘ (fun i => (M j i : ℚ))) := by
    funext j i
    simp
  rw [hfun]
  exact h

/-- The kernel of `mLie M : ℂ^N → ℂ^ρ`, the matrix-vector map of the entrywise cast of the integer
matrix `M`, has dimension `N - ρ` whenever `ρ ≤ N` and the rows of `M` are `ℚ`-linearly
independent. The rows being independent over `ℚ` means (by base change along `ℚ → ℂ`) that they
stay independent over `ℂ`, so the map has rank `ρ` and rank–nullity gives `N - ρ`. -/
theorem finrank_ker_mLie {N ρ : ℕ} (hρN : ρ ≤ N) (M : Fin ρ → Fin N → ℤ)
    (hM : LinearIndependent ℚ (fun j i => (M j i : ℚ))) :
    Module.finrank ℂ (LinearMap.ker (mLie M)) = N - ρ := by
  have hMℂ : LinearIndependent ℂ (fun j i => (M j i : ℂ)) := linearIndependent_int_cast_row M hM
  have key := finrank_ker_mulVecLin_fin (F := ℂ) (M := ρ) (N := N)
    (a := fun j i => (M j i : ℂ)) hMℂ
  rw [show mLie M = (Matrix.of (fun j i => (M j i : ℂ))).mulVecLin from rfl]
  exact key

end Work.BW
