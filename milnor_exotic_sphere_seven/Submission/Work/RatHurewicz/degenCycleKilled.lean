import Mathlib
import Submission.Work.RatHurewicz.degenCycleReduction
import Submission.Work.RatHurewicz.ConnectivityBridge
import Submission.Work.RatHurewicz.constCubeKilled
import Submission.Work.RatHurewicz.degenCycleBoundaryAddConst

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The crux `DegenCycleKilled`, from the chain-level normalization statement

The target `Work.RatHurewicz.DegenCycleKilled` says that the linearised based-ification
`psiLinGen N m K hN` kills every degenerate `(m+2)`-cycle, for a space `X` whose homotopy groups
vanish below degree `m+2`.

The proof is a two-step reduction; both steps are tower-free.

* **Tower level.**  `psiLinGen` kills cubical boundaries (Hutchings' `(2.5)`, in additive form
  `psiLinGen_cubD_eq_zero`) and the constant cube (`psiLinGen_single_cconst`), hence everything in
  `range (cubD (m+2) X) ⊔ ConstChain (m+2) X x₀`.
* **Chain level.**  A degenerate `(m+2)`-chain `d` which is a cycle lies in that submodule: it is a
  cubical boundary modulo the constant cube at the base point.  This is the normalization statement
  `Deg n ∩ Z n ⊆ B n + Const n` (`Work.RatHurewicz.degenCycleBoundaryAddConst`), proved by
  degeneracy-compatible filling towers: the filling of a degenerate cube is the degenerate extension
  of the filling of the underlying cube, so only `π_m` (not `π_{m+1}`) is needed.

The connectivity hypothesis of `DegenCycleKilled` is *cube-based*; the `i = 0` case
(`Subsingleton (π₀)`) yields `PathConnectedSpace X` via
`Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero`, which is what the chain-level
statement wants.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- `psiLinGen` kills `range (cubD (m+2) X) ⊔ ConstChain (m+2) X x₀`: boundaries by the linearity of
the tower contraction `(Y)`, the constant cube by `psiLinGen_single_cconst`. -/
theorem psiLinGen_eq_zero_of_mem_sup (N m : ℕ) [Nontrivial (Fin (m + 2))] {x₀ : X}
    (K : Work.RatHurewicz.Tower x₀ N) (hN : m + 1 ≤ N) (d : Cub (m + 2) X)
    (hmem : d ∈ LinearMap.range (cubD (m + 2) X) ⊔ ConstChain (m + 2) X x₀) :
    Work.Stems.Hur2c.psiLinGen N m K hN d = 0 := by
  obtain ⟨E, hE, c, hc, hsum⟩ := Submodule.mem_sup.mp hmem
  have hE' : Work.Stems.Hur2c.psiLinGen N m K hN E = 0 := by
    obtain ⟨E', rfl⟩ := hE
    exact Work.Stems.Hur2c.psiLinGen_cubD_eq_zero N m K hN E'
  have hc' : Work.Stems.Hur2c.psiLinGen N m K hN c = 0 := by
    rw [ConstChain] at hc
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hc
    rw [← ht, map_smul, psiLinGen_single_cconst N m K hN x₀, smul_zero]
  rw [← hsum, map_add, hE', hc', add_zero]

/-- **The crux.**  `psiLinGen` kills degenerate `(m+2)`-cycles. -/
theorem degenCycleKilled : Work.RatHurewicz.DegenCycleKilled := by
  intro N m _ X _ x₀ hconn K hN d hd hcyc
  have hpc : PathConnectedSpace X :=
    pathConnectedSpace_of_subsingleton_pi_zero x₀ (hconn 0 (by omega))
  have hmem : d ∈ LinearMap.range (cubD (m + 2) X) ⊔ ConstChain (m + 2) X x₀ :=
    degenCycleBoundaryAddConst (m + 1) X x₀ (by omega) hpc
      (fun i _ hi => hconn i (by omega)) d hd hcyc
  exact psiLinGen_eq_zero_of_mem_sup N m K hN d hmem

end

end Work.RatHurewicz
