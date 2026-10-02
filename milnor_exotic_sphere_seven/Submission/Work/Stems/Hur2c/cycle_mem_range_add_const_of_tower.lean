import Mathlib
import Submission.Work.Stems.Hur2c.TowerCubD
import Submission.Work.RatHurewicz.fillingFamilyConst
import Submission.Work.RatHurewicz.towerContraction

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Cycles are boundaries modulo the constant cube

`Work.RatHurewicz.towerChainContraction` says that the `ℤ`-linear extension `Klin K (n+1)` of the
tower filling `p ↦ K.Kf (n+1) p` satisfies

`∂ (Klin K (n+1) c) = (-1)^{n+1} • (aug c • const - c) + Klin K n (∂ c)`.

For a cycle `c = W` (so `∂ W = 0`) this reads `∂ (Klin K (n+1) W) = (-1)^{n+1} • (aug W • const - W)`;
multiplying by the sign `s = (-1)^{n+1}` (whose square is `1`) and rearranging gives

`W = aug W • const - s • ∂ (Klin K (n+1) W)`,

i.e. `W` is a boundary plus a multiple of the constant cube at the base point.
-/

open Work.Stems.Cubical

namespace Work.Stems.Hur2c

theorem cycle_mem_range_add_const_of_tower {X : Type} [TopologicalSpace X] {x₀ : X} {N : ℕ}
    (K : Work.RatHurewicz.Tower x₀ N) (m : ℕ) (hm : m + 1 ≤ N) (W : Work.Stems.Cubical.Cub (m + 1) X)
    (hcyc : Work.Stems.Cubical.cubD m X W = 0) :
    W ∈ LinearMap.range (Work.Stems.Cubical.cubD (m + 1) X) ⊔
      Work.RatHurewicz.ConstChain (m + 1) X x₀ := by
  have h := Work.RatHurewicz.towerChainContraction K m hm W
  rw [hcyc, map_zero, add_zero] at h
  have hss : ((-1 : ℤ) ^ (m + 1)) * ((-1 : ℤ) ^ (m + 1)) = 1 := by
    rw [← pow_add, show (m + 1) + (m + 1) = 2 * (m + 1) from by ring, pow_mul]
    simp
  have hssmul : ∀ y : Cub (m + 1) X,
      ((-1 : ℤ) ^ (m + 1)) • (((-1 : ℤ) ^ (m + 1)) • y) = y := by
    intro y
    rw [smul_smul, hss, one_smul]
  have h2 : ((-1 : ℤ) ^ (m + 1)) •
      Work.Stems.Cubical.cubD (m + 1) X (Work.RatHurewicz.Klin K (m + 1) W)
      = Work.RatHurewicz.aug (X := X) (m + 1) W •
          Finsupp.single (Work.RatHurewicz.cconst (m + 1) x₀) (1 : ℤ) - W := by
    rw [h]
    exact hssmul _
  have hconst : Work.RatHurewicz.aug (X := X) (m + 1) W •
      Finsupp.single (Work.RatHurewicz.cconst (m + 1) x₀) (1 : ℤ)
      ∈ Work.RatHurewicz.ConstChain (m + 1) X x₀ := by
    rw [Work.RatHurewicz.ConstChain]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  have hbdy : -(((-1 : ℤ) ^ (m + 1)) •
      Work.Stems.Cubical.cubD (m + 1) X (Work.RatHurewicz.Klin K (m + 1) W))
      ∈ LinearMap.range (Work.Stems.Cubical.cubD (m + 1) X) :=
    Submodule.neg_mem _ (Submodule.smul_mem _ _
      (⟨Work.RatHurewicz.Klin K (m + 1) W, rfl⟩ : Work.Stems.Cubical.cubD (m + 1) X
        (Work.RatHurewicz.Klin K (m + 1) W) ∈ LinearMap.range (Work.Stems.Cubical.cubD (m + 1) X)))
  have hW : W = Work.RatHurewicz.aug (X := X) (m + 1) W •
        Finsupp.single (Work.RatHurewicz.cconst (m + 1) x₀) (1 : ℤ)
      + -(((-1 : ℤ) ^ (m + 1)) •
        Work.Stems.Cubical.cubD (m + 1) X (Work.RatHurewicz.Klin K (m + 1) W)) := by
    rw [h2]
    abel
  rw [hW]
  exact Submodule.add_mem _ (Submodule.mem_sup_right hconst) (Submodule.mem_sup_left hbdy)

end Work.Stems.Hur2c
