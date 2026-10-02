import Mathlib
import Submission.Work.Serre.StableExact
import Submission.Work.Serre.serreK2
import Submission.Work.Serre.serreE2d
import Submission.Work.Serre.serrePostnikovTower
import Submission.Work.Serre.cubeDiskHomeo
import Submission.Work.Serre.attachIncl_piMap_bijective_of_compress
import Submission.Work.Serre.attachIncl_pi0_bijective
import Submission.Work.Serre.exists_joined_attachIncl
import Submission.Work.Serre.serreAttachKillPi
import Submission.Work.Serre.cubeRelIso
import Submission.Work.Serre.serreK2Int
import Submission.Work.Serre.bijective_piMapN_of_joined
import Submission.Work.Serre.serrePairComparison
import Submission.Work.Serre.ZeroCase.Bridge
import Submission.Work.RatHurewicz.attachCells_extension
import Submission.Work.RatHurewicz.killFamily_subsingleton

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Serre exact sequence in the stable range

**Target.**  `Work.Serre.SerreStableExact` (`Submission/Work/Serre/StableExact.lean`): for a Serre
fibration `p : E → B` with `B` `(b-1)`-connected (`1 ≤ b`) and the fibre `p⁻¹(b₀)`
`(f-1)`-connected, the map of pairs `(E, F) → (B, {b₀})` induced by `p`
(`Work.StemsB.relPairMap p b₀`) is an isomorphism on integral homology in degrees `< b + f`.

**The two ends of the stable range.**

* `f = 0`: no hypothesis on the fibre, and the comparison is a statement about the *base*: the pair
  `(B, {b₀})` is compressible in all dimensions `≤ b-1` (a map `(Iᵈ, ∂Iᵈ) → (B, b₀)` is a
  generalized loop, trivial in `π_d(B, b₀) = π_d(B)`), and the compression property lifts along the
  fibration (`Work.Serre.compressRel_preimage_of_isSerreFibration`); hence both relative homologies
  vanish in degrees `≤ b - 1` and the map between them is an isomorphism.  This is
  `Work.Serre.serreComparison_zero` (`Submission/Work/Serre/ZeroCase/Basic.lean`).
* `f ≥ 1`: the statement is the cell-attachment argument over a CW model of the base, assembled as
  `Work.Serre.serrePairComparison`; the fibre hypothesis is transported from the `π`-form of the
  statement to the homological form by
  `Work.Serre.isZero_singularChains_homology_of_pi_subsingleton`
  (`Submission/Work/Serre/ZeroCase/Bridge.lean`).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre

theorem serreStableExact : Work.Serre.SerreStableExact := by
  intro E _ B _ p hp e₀ b₀ he₀ b f hb hconn hfibπ i hi
  rcases Nat.eq_zero_or_pos f with hf0 | hfpos
  · -- `f = 0`: the fibre hypothesis is vacuous, and both sides vanish in degrees `< b`
    subst hf0
    exact serreComparison_zero p hp b₀ b hb hconn i (by simpa using hi)
  · -- `f ≥ 1`: the cell-attachment comparison, with the fibre hypothesis in homological form
    have hfib0 : Subsingleton (HomotopyGroup (Fin 0) (Work.StemsB.fibre p b₀) ⟨e₀, he₀⟩) :=
      hfibπ 0 (by omega)
    have hfibH : ∀ j : ℕ, 0 < j → j < f → IsZero ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.StemsB.fibre p b₀))).homology j) :=
      fun j hj hjl => isZero_singularChains_homology_of_pi_subsingleton
        (X := Work.StemsB.fibre p b₀) ⟨e₀, he₀⟩ f
        (fun i hi' => hfibπ i hi') j hj hjl
    exact (serrePairComparison p hp b₀ e₀ he₀ b f hb (by omega) hconn hfib0 hfibH).1 i hi

end Work.Serre
