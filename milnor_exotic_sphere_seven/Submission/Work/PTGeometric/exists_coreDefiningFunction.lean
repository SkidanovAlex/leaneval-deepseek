import Mathlib
import Submission.Work.PTGeometric.SourceZero
import Submission.Work.PTGeometric.exists_sourceDefiningFunction

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: a smooth defining function of the core tail of the `0`-end

For a genuine tube geometry `G` and a multiplicity `m`, the "core tail"

  `Z = {u : ℝ^{k+8} | alphaFamily G m (cubeCoord (k+8) u) ∈ G.core}`

is the preimage of the (closed) core under the continuous map
`u ↦ alphaFamily G m (cubeCoord (k+8) u)`, hence closed.  This file produces a `C^∞` function
`a : ℝ^{k+8} → ℝ` with `0 ≤ a ≤ 1` whose zero set is **exactly** `Z` — Mathlib's smooth Urysohn
lemma `exists_contMDiff_zero_iff_one_iff_of_isClosed` applied with the second closed set empty.

This is the (unconditional) existence half of the defining function of the core tail used by the
last mile of the source construction; compactness of `Z` (which needs
`(∏ i, tubeAlpha (G.rep i)) ^ m = 1`, see `Work.PTGeometric.isCompact_sourceCoreTail`) is not
required for the existence statement.

## Main results

* `Work.PTGeometric.exists_coreDefiningFunction`
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.ThomBordism.PontryaginThom

/-- **The core tail of the `0`-end is closed.**  It is the preimage of the closed core under the
continuous composition of the generalised loop `alphaFamily G m` with the cube chart `cubeCoord`. -/
theorem isClosed_coreTail {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Man8} (G : GenuineTubeGeometry k D ι Fam) (m : ℕ) :
    IsClosed {u : EuclideanSpace ℝ (Fin (k + 8)) |
      alphaFamily (D := D) (Fam := Fam) G m (cubeCoord (k + 8) u) ∈ G.core} :=
  G.isClosed_core.preimage ((alphaFamily G m).1.continuous.comp (continuous_cubeCoord _))

/-- **A smooth defining function of the core tail.**  For every genuine tube geometry `G` and every
`m` there is a `C^∞` function `a : ℝ^{k+8} → ℝ` with `0 ≤ a ≤ 1` and
`a u = 0 ↔ alphaFamily G m (cubeCoord (k+8) u) ∈ G.core`. -/
theorem exists_coreDefiningFunction {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8}
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ) :
    ∃ a : EuclideanSpace ℝ (Fin (k + 8)) → ℝ,
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 8))))
        (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) a ∧
      (∀ u, 0 ≤ a u) ∧ (∀ u, a u ≤ 1) ∧
      (∀ u, a u = 0 ↔ Work.PTGeometric.alphaFamily (D := D) (Fam := Fam) G m
        (Work.PTGeometric.cubeCoord (k + 8) u) ∈ G.core) := by
  have hZcl : IsClosed {u : EuclideanSpace ℝ (Fin (k + 8)) |
      alphaFamily (D := D) (Fam := Fam) G m (cubeCoord (k + 8) u) ∈ G.core} :=
    isClosed_coreTail G m
  -- Smooth Urysohn for the pair (`core tail`, `∅`).
  obtain ⟨f, hf, hrange, h0, _⟩ :=
    exists_contMDiff_zero_iff_one_iff_of_isClosed
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 8)))) hZcl isClosed_empty
      (by simp)
  exact ⟨f, hf, fun u => (hrange (Set.mem_range_self u)).1,
    fun u => (hrange (Set.mem_range_self u)).2, fun u => (h0 u).symm⟩

end

end Work.PTGeometric
