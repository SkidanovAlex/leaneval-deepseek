import Mathlib
import Submission.Work.RatHurewicz.Excision
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.RatHurewicz.relPiVanishingOfPiInjSurj
import Submission.Work.Serre.piMap_fibreIncl_surjective_of_subsingleton
import Submission.Work.StemsB.fibrationLES_of_serre

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.RatHurewicz

/-- For a Hurewicz fibration `p : E → B` with fibre `F = p ⁻¹' {p e₀}`: if `π_j(B) = 0` (and `π_i(F) = 0` for all `i < j`, `j ≥ 2`), then the relative homotopy group `π_{j-1}(E,F)` — realised as `π_{j-1}` of the homotopy fibre of the inclusion `F ↪ E` — is trivial.  (The "the pair `(E,F)` has the homotopy of the base" computation, in the exact form needed as a hypothesis of Blakers–Massey.) -/
theorem relPiVanishing_of_isHurewiczFibration {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsHurewiczFibration p) (e₀ : E) (j : ℕ) (hj : 2 ≤ j)
    (hbase : Subsingleton (HomotopyGroup (Fin j) B (p e₀)))
    (hfib : ∀ i : ℕ, i < j → Subsingleton (HomotopyGroup (Fin i) (↥(p ⁻¹' {p e₀})) ⟨e₀, rfl⟩)) :
    Subsingleton (Work.RatHurewicz.RelHomotopyGroup
      (Work.RatHurewicz.setIncl (p ⁻¹' {p e₀})) ⟨e₀, rfl⟩ (j - 1)) := by
  -- `π_j(B)` is trivial, stated with the index `(j - 1) + 1` in which the long exact sequence
  -- of the fibration reads off its surjectivity statement.
  have hB' : Subsingleton (HomotopyGroup (Fin ((j - 1) + 1)) B (p e₀)) := by
    rw [show j - 1 + 1 = j from by omega]
    exact hbase
  -- The long exact sequence of the pair `(E, F)` (`F = p ⁻¹' {p e₀}`): it suffices to know that
  -- the inclusion `F ↪ E` is injective on `π_{j-1}` (it is, since `π_{j-1}(F) = 0` as `j - 1 < j`)
  -- and surjective on `π_j` (exactness at `π_j(E)` of the fibration `p`, plus `π_j(B) = 0`).
  refine Work.RatHurewicz.relPiVanishingOfPiInjSurj (A := p ⁻¹' {p e₀}) (j - 1) ⟨e₀, rfl⟩ ?_ ?_
  · intro x y _
    exact (hfib (j - 1) (by omega)).allEq x y
  · exact Work.Serre.piMap_fibreIncl_surjective_of_subsingleton p hp.isSerreFibration e₀ (j - 1)
      (by omega) hB'

end Work.RatHurewicz
