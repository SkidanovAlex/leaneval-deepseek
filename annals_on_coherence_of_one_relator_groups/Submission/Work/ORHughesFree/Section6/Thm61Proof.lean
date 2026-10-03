/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# [JZLA20, Theorem 6.1] from the induction step

This file assembles the final statements of [JZLA20, Theorem 6.1] from the induction on the
`G`-complexity proved in `Section6.Thm61InductionMain`, together with the last step
`isDivisionRing_of_isDivisionRing_divisionClosure` of `Section6.isDivisionRing_of_step`.

The only remaining input is the **construction of the induction step** `Thm61Step K G U φ H` for
every finitely generated non-trivial `H ≤ G` (the "Step A + Step B" of the route design), which
enters as the explicit hypothesis `hstep`.

We also record `nontrivial_of_rank_compat`: the compatibility of `rk` and `rkU` forces `U` to be
non-trivial (the `1 × 1` identity matrix has rank `1 ≤ 0 = rank of the zero matrix`), which is the
`Nontrivial U` hypothesis that the `H = ⊥` branch of the induction needs.
-/
import Mathlib
import Submission.Work.ORHughesFree.Main
import Submission.Work.ORHughesFree.Section6.Thm61InductionMain
import Submission.Work.ORHughesFree.Section6.isDivisionRing_of_step

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace Work.ORHughesFree.Section6

open Work.ORHughesFree

variable {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]

/-- **Compatibility of the rank functions forces `U` to be non-trivial.**  The `1 × 1` identity
matrix is `oneByOne 1`, and its rank is `1` by `SylvesterRank.rk_one`; passing to `U` along `φ` it
is the rank of `1 ∈ U`, which vanishes if `1 = 0`. -/
theorem nontrivial_of_rank_compat (φ : MonoidAlgebra K G →+* U)
    (rk : SylvesterRank (MonoidAlgebra K G)) (rkU : SylvesterRank U)
    (hcompat : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)),
      rk.rk n m A = rkU.rk n m (A.map φ)) : Nontrivial U := by
  have hone : oneByOne (1 : U) = (1 : Matrix (Fin 1) (Fin 1) U) := by
    ext i j
    rw [Matrix.one_apply]
    exact (if_pos (Subsingleton.elim i j)).symm
  have hmap1 : (1 : Matrix (Fin 1) (Fin 1) (MonoidAlgebra K G)).map φ
      = (1 : Matrix (Fin 1) (Fin 1) U) := by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.map_apply]
  have hrk : rkU.rk 1 1 (oneByOne (1 : U)) = 1 := by
    rw [hone]
    have h := hcompat 1 1 (1 : Matrix (Fin 1) (Fin 1) (MonoidAlgebra K G))
    rw [hmap1, rk.rk_one] at h
    exact h.symm
  refine ⟨1, 0, fun h10 => ?_⟩
  have h0 : oneByOne (1 : U) = (0 : Matrix (Fin 1) (Fin 1) U) := by
    ext i j
    exact h10
  rw [h0, rkU.rk_zero] at hrk
  exact one_ne_zero hrk.symm

/-- **[JZLA20, Theorem 6.1], the induction.**  Given the environment of the induction step for
every finitely generated non-trivial subgroup `H ≤ G`, every non-zero element of
`D_{K[G],U}` is a unit. -/
theorem isUnit_of_mem_divisionClosure (φ : MonoidAlgebra K G →+* U) [Nontrivial U]
    (hstep : ∀ H : Subgroup G, H.FG → H ≠ ⊥ → Nonempty (Thm61Step K G U φ H)) :
    ∀ a : ↥(divisionClosure (Set.range φ)), a ≠ 0 → IsUnit a :=
  isUnit_of_mem_divisionClosure_of_reduction φ
    (sourceReduction_of_exists_source_reduction φ) hstep

/-- **[JZLA20, Theorem 6.1].**  Let `G` be a group, `K` a field, `U` a ring, `φ : K[G] →+* U` an
epic ring homomorphism and `rk`, `rkU` Sylvester rank functions on `K[G]` and `U` with
`rk = rkU ∘ φ`.  If the environment `Thm61Step K G U φ H` of the induction step exists for every
finitely generated non-trivial `H ≤ G`, then `U` is a division ring. -/
theorem isDivisionRing_of_thm61Step (φ : MonoidAlgebra K G →+* U)
    (rk : SylvesterRank (MonoidAlgebra K G)) (rkU : SylvesterRank U) (hφ : IsEpic φ)
    (hcompat : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)),
      rk.rk n m A = rkU.rk n m (A.map φ))
    (hstep : ∀ H : Subgroup G, H.FG → H ≠ ⊥ → Nonempty (Thm61Step K G U φ H)) :
    IsDivisionRing U := by
  haveI : Nontrivial U := nontrivial_of_rank_compat φ rk rkU hcompat
  have hD : IsDivisionRing ↥(divisionClosure (Set.range φ)) :=
    ⟨⟨1, 0, fun h => one_ne_zero (Subtype.ext_iff.mp h)⟩,
      isUnit_of_mem_divisionClosure φ hstep⟩
  exact isDivisionRing_of_isDivisionRing_divisionClosure φ hφ hD

end Work.ORHughesFree.Section6

namespace Work.ORHughesFree

/-- **[JZLA20, Theorem 6.1]**, in the form of the `Prop`-valued statement `JZLA20Thm61` of
`Main.lean`, with the induction step as an explicit hypothesis. -/
theorem JZLA20Thm61_of_step {K : Type} [Field K] {G : Type} [Group G] [LocallyIndicable G]
    (rk : SylvesterRank (MonoidAlgebra K G))
    (hstep : ∀ (U : Type) [Ring U] (φ : MonoidAlgebra K G →+* U) (rkU : SylvesterRank U),
      IsEpic φ → rkU.IsFaithful →
      (∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) (MonoidAlgebra K G)),
        rk.rk n m A = rkU.rk n m (A.map φ)) →
      ∀ H : Subgroup G, H.FG → H ≠ ⊥ → Nonempty (Thm61Step K G U φ H)) :
    JZLA20Thm61 rk := by
  intro _hHF _hSR U _ _ _ _ φ rkU hφ hfaith hcompat
  exact Section6.isDivisionRing_of_thm61Step φ rk rkU hφ hcompat
    (hstep U φ rkU hφ hfaith hcompat)

end Work.ORHughesFree
