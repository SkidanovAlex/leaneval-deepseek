import Mathlib
import Submission.Work.RatHurewicz.Bridge.Defs
import Submission.Work.RatHurewicz.Bridge.SigmaChain

/-!
# SUBPROJECT SERRE — E0 in range form: the simplicial boundary of `Δⁿ`

Vocabulary for the cone construction of `Work.Serre.SerreE0Range`
(`Submission/Work/Drive/SERRE_BLUEPRINT.md`, ADDENDUM 1 (C)).

* `Work.Serre.simplexBdry n` — the simplicial boundary `∂Δⁿ = {z | ∃ j, z j = 0}` of the standard
  `n`-simplex `Work.RatHurewicz.Bridge.H`'s target `stdSimplex ℝ (Fin (n+1))`;
* `Work.Serre.faceIncl n i` — the `i`-th face `Δⁿ → ∂Δⁿ⁺¹` (the coface
  `Work.RatHurewicz.Bridge.coface`, corestricted to the boundary).
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial
open scoped Simplicial

namespace Work.Serre

noncomputable section

/-- The **simplicial boundary** of the standard `n`-simplex: the set of points with a vanishing
barycentric coordinate. -/
def simplexBdry (n : ℕ) : Set (↥(stdSimplex ℝ (Fin (n + 1)))) :=
  {z | ∃ j : Fin (n + 1), z.1 j = 0}

@[simp]
theorem mem_simplexBdry {n : ℕ} (z : ↥(stdSimplex ℝ (Fin (n + 1)))) :
    z ∈ simplexBdry n ↔ ∃ j : Fin (n + 1), z.1 j = 0 := Iff.rfl

/-- The **`i`-th face inclusion** of the standard `(n+1)`-simplex, as a map into the boundary of
`Δ^{n+1}`; it is the coface `Work.RatHurewicz.Bridge.coface n i`. -/
def faceIncl (n : ℕ) (i : Fin (n + 2)) :
    C(↥(stdSimplex ℝ (Fin (n + 1))), ↥(simplexBdry (n + 1))) where
  toFun z := ⟨Work.RatHurewicz.Bridge.coface n i z,
    ⟨i, Work.RatHurewicz.Bridge.coface_apply_self n i z⟩⟩
  continuous_toFun := Continuous.subtype_mk (Work.RatHurewicz.Bridge.coface n i).continuous _

@[simp]
theorem faceIncl_coe (n : ℕ) (i : Fin (n + 2)) (z : ↥(stdSimplex ℝ (Fin (n + 1)))) :
    ((faceIncl n i z : ↥(simplexBdry (n + 1))) : ↥(stdSimplex ℝ (Fin (n + 2)))) =
      Work.RatHurewicz.Bridge.coface n i z := rfl

end

end Work.Serre
