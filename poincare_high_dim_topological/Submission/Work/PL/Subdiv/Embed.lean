import Submission.Work.PL.Subdiv.Defs

/-!
# Embedding `E N` into `E (N+1)`, pushforward complexes, cones (blueprint A2 items 5–6)

`embedELin N : E N →ₗ[ℝ] E (N+1)` is the canonical map onto the first `N` coordinates
(last coordinate `0`).  It is isometric, and a point of `E (N+1)` whose last coordinate is
nonzero is never in the affine span of the embedded copy of any complex, so it can serve as a
cone apex.
-/

open Set Metric
open scoped BigOperators
open PL

namespace Work.PL.Subdiv

noncomputable section

/-- The canonical inclusion `E N ↪ E (N+1)` as the first `N` coordinates (last coordinate `0`). -/
def embedELin (N : ℕ) : E N →ₗ[ℝ] E (N+1) where
  toFun x := WithLp.toLp 2 (fun i : Fin (N+1) => if h : (i : ℕ) < N then x ⟨i, h⟩ else 0)
  map_add' x y := by
    ext i
    by_cases h : (i : ℕ) < N <;> simp [WithLp.toLp, h]
  map_smul' c x := by
    ext i
    by_cases h : (i : ℕ) < N <;> simp [WithLp.toLp, h]

/-- The canonical embedding as an affine map (for pushing forward complexes). -/
def embedEAffine (N : ℕ) : E N →ᵃ[ℝ] E (N+1) := (embedELin N).toAffineMap

lemma embedELin_apply_last (N : ℕ) (x : E N) : (embedELin N) x (Fin.last N) = 0 := by
  simp [embedELin, WithLp.toLp]

end

end Work.PL.Subdiv
