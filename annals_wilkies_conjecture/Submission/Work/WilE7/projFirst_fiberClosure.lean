import Mathlib
import Submission.Work.Wilkies.E.Spec

namespace Work.WilE7

/-- `Fin.append` reassembles a function on `Fin (n+m)` from its first `n` and last `m`
coordinates. -/
theorem append_projFirst_projSnd {n m : ℕ} (z : Fin (n + m) → ℝ) :
    Fin.append (WilkiesDesign.E.projFirst n m z) (WilkiesDesign.E.projSnd n m z) = z := by
  funext i
  unfold WilkiesDesign.E.projFirst WilkiesDesign.E.projSnd Fin.append
  exact Fin.addCases_castAdd_natAdd z i

/-- The first `n` coordinates of `Fin.append x y` are `x`. -/
theorem projFirst_append {n m : ℕ} (x : Fin n → ℝ) (y : Fin m → ℝ) :
    WilkiesDesign.E.projFirst n m (Fin.append x y) = x := by
  unfold WilkiesDesign.E.projFirst
  ext i
  exact Fin.append_left x y i

/-- The last `m` coordinates of `Fin.append x y` are `y`. -/
theorem projSnd_append {n m : ℕ} (x : Fin n → ℝ) (y : Fin m → ℝ) :
    WilkiesDesign.E.projSnd n m (Fin.append x y) = y := by
  unfold WilkiesDesign.E.projSnd
  ext i
  exact Fin.append_right x y i

/-- Membership in the fibre, rewritten through `Fin.append`. -/
theorem mem_fiber_iff {n m : ℕ} (Y : Set (Fin (n + m) → ℝ)) (x : Fin n → ℝ)
    (y : Fin m → ℝ) :
    y ∈ WilkiesDesign.E.fiber Y x ↔ Fin.append x y ∈ Y := Iff.rfl

/-- The projection of the fibrewise closure of `Y` agrees with that of `Y` itself.

Forward: `Y ⊆ fiberClosure Y`, since every point of `Y` lies in the closure of its own fibre.
Backward: a point of `fiberClosure Y` projects to `x` only if the fibre `Y_x` has nonempty
closure, hence is nonempty, so `x` is already a projection of `Y`. -/
theorem projFirst_fiberClosure {n m : ℕ} (Y : Set (Fin (n + m) → ℝ)) :
    WilkiesDesign.E.projFirst n m '' WilkiesDesign.E.fiberClosure Y =
      WilkiesDesign.E.projFirst n m '' Y := by
  apply Set.Subset.antisymm
  · -- `projFirst '' fiberClosure Y ⊆ projFirst '' Y`
    rintro x ⟨z, hz, rfl⟩
    -- `hz : projSnd n m z ∈ closure (fiber Y (projFirst n m z))`
    have hne : (WilkiesDesign.E.fiber Y (WilkiesDesign.E.projFirst n m z)).Nonempty :=
      Set.Nonempty.of_closure ⟨WilkiesDesign.E.projSnd n m z, hz⟩
    obtain ⟨y, hy⟩ := hne
    refine ⟨Fin.append (WilkiesDesign.E.projFirst n m z) y, hy, ?_⟩
    exact projFirst_append _ _
  · -- `projFirst '' Y ⊆ projFirst '' fiberClosure Y`
    rintro x ⟨z, hz, rfl⟩
    refine ⟨z, ?_, rfl⟩
    show WilkiesDesign.E.projSnd n m z ∈
      closure (WilkiesDesign.E.fiber Y (WilkiesDesign.E.projFirst n m z))
    have hmem : WilkiesDesign.E.projSnd n m z ∈
        WilkiesDesign.E.fiber Y (WilkiesDesign.E.projFirst n m z) := by
      show Fin.append (WilkiesDesign.E.projFirst n m z) (WilkiesDesign.E.projSnd n m z) ∈ Y
      rw [append_projFirst_projSnd z]
      exact hz
    exact subset_closure hmem

end Work.WilE7
