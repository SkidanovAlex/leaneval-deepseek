import Submission.Work.RatHurewicz.Bridge.Defs
import Submission.Work.Stems.CubicalNorm

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The degeneracy operators on cubical chains

Vocabulary for the chain-level study of the degenerate subcomplex `Work.RatHurewicz.Deg`:

* `dropProj n j` — the projection `I^{n+1} → I^n` dropping the coordinate `j`;
* `degenMap n j` — its pullback on cubical chains, `c ↦ c ∘ dropProj n j`, extended linearly.
  Its image is exactly the span of the cubes independent of the coordinate `j`; in particular
  `Deg (n+1) X = ⨆ j, range (degenMap n j)`.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.Stems.Hur2c

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The projection `I^{n+1} → I^n` dropping the coordinate `j`. -/
abbrev dropProj (n : ℕ) (j : Fin (n+1)) : C(IC (n+1), IC n) :=
  Work.RatHurewicz.Bridge.proj n j

@[simp] theorem dropProj_apply (n : ℕ) (j : Fin (n+1)) (t : IC (n+1)) (k : Fin n) :
    dropProj n j t k = t (Fin.succAbove j k) := rfl

/-- The "degeneracy" operator: append a dummy coordinate in position `j` to an `n`-cube. -/
def degenMap (n : ℕ) (j : Fin (n+1)) : Cub n X →ₗ[ℤ] Cub (n+1) X :=
  Finsupp.lmapDomain _ _ (fun c : C(IC n, X) => c.comp (dropProj n j))

theorem degenMap_apply_single (n : ℕ) (j : Fin (n+1)) (c : C(IC n, X)) :
    degenMap (X := X) n j (Finsupp.single c 1)
      = Finsupp.single (c.comp (dropProj n j)) 1 := by
  simp [degenMap]

/-- A cube of `degenMap n j` is independent of the coordinate `j`. -/
theorem degenMap_single_mem_Deg (n : ℕ) (j : Fin (n+1)) (c : C(IC n, X)) :
    Finsupp.single (c.comp (dropProj n j)) 1 ∈ Work.RatHurewicz.Deg (n+1) X := by
  rw [Work.RatHurewicz.Deg]
  refine Submodule.mem_iSup_of_mem j (Submodule.subset_span ?_)
  exact ⟨c.comp (dropProj n j), fun t t' h => by
    show c (dropProj n j t) = c (dropProj n j t')
    congr 1
    funext k
    rw [dropProj_apply, dropProj_apply]
    exact h _ (Fin.succAbove_ne j k), rfl⟩

/-- The image of `degenMap` is contained in the degenerate subcomplex. -/
theorem degenMap_le_Deg (n : ℕ) (j : Fin (n+1)) :
    LinearMap.range (degenMap (X := X) n j) ≤ Work.RatHurewicz.Deg (n+1) X := by
  intro x hx
  obtain ⟨c, rfl⟩ := hx
  exact Finsupp.induction c (Submodule.zero_mem _) fun a b f _ hb ih => by
    have hsingle : (Finsupp.single a b : Cub n X) = b • Finsupp.single a 1 := by
      rw [Finsupp.smul_single]
      simp
    rw [hsingle, map_add, map_smul, degenMap_apply_single]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (degenMap_single_mem_Deg n j a)) ih

end

end Work.Stems.Hur2c
