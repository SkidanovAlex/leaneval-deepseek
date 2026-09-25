import Mathlib
import Submission.Work.LT.gb_ext_defs

namespace Work.LT

/-- `matExt A B (opVec T₁) (opVec T₂)` agrees with `x` on the rectangle `A × B`: on that
rectangle the extension operators act as the identity, so the double sum collapses onto the
single entry `x (i, j)`. -/
theorem gb_matExt_agree {D : ℕ} {CA CB : Submodule (ZMod 2) (Fin D → ZMod 2)}
    (A B : Finset (Fin D)) (T₁ : GB.ExtOp CA A) (T₂ : GB.ExtOp CB B)
    (x : Fin D × Fin D → ZMod 2) {i j : Fin D} (hi : i ∈ A) (hj : j ∈ B) :
    GB.matExt A B (GB.opVec T₁) (GB.opVec T₂) x (i, j) = x (i, j) := by
  rw [GB.matExt_apply]
  -- On the rectangle the extension operators act as the identity:
  -- `opVec T₁ i' i = if i = i' then 1 else 0` for `i ∈ A`, and similarly for `T₂`.
  have h1 : ∀ i' : Fin D, GB.opVec T₁ i' i = (if i = i' then (1 : ZMod 2) else 0) :=
    fun i' => T₁.opVec_agree hi
  have h2 : ∀ j' : Fin D, GB.opVec T₂ j' j = (if j = j' then (1 : ZMod 2) else 0) :=
    fun j' => T₂.opVec_agree hj
  simp only [h1, h2]
  -- The double sum then collapses onto `(i, j) ∈ A × B`.
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hne
      simp [Ne.symm hne]
    · intro h
      exact absurd hj h
  · intro i' _ hne
    simp [Ne.symm hne]
  · intro h
    exact absurd hi h

end Work.LT
