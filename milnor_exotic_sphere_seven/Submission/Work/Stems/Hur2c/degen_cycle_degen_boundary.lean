import Mathlib
import Submission.Work.RatHurewicz.CubicalDefs
import Submission.Work.RatHurewicz.degeneracyChains
import Submission.Work.RatHurewicz.degenFaces
import Submission.Work.RatHurewicz.towerContraction
import Submission.Work.RatHurewicz.fillingFamilyConst
import Submission.Work.RatHurewicz.DCTowerDefs
import Submission.Work.RatHurewicz.DCTowerAux
import Submission.Work.RatHurewicz.DCBuild.dcTowerExists
import Submission.Work.RatHurewicz.degenCycleBoundaryAddConst

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Reduced degenerate cycles bound degenerate chains

Target: `Work.Stems.Hur2c.degen_cycle_degen_boundary` — for `X` path connected with
`π_i(X) = 0` for `1 ≤ i ≤ m`, every degenerate `(m+1)`-cycle of augmentation `0` is the boundary
of a *degenerate* `(m+2)`-chain.

## The proof

The engine is the **degeneracy-compatible filling tower** `Work.RatHurewicz.DCTower`
(`DCTowerDefs.lean`, existence `DCBuild.dcTowerExists`): a filling tower whose filling of the
degenerate cube `degenOp j φ` is the degenerate extension `degenOp (Fin.castSucc j) (Kf m φ)` of
the filling of the underlying cube.  A degenerate `(k+1)`-chain
`d = ∑ j, Dlin k j (e j)` is filled by the *degenerate* `(k+2)`-chain
`∑ j, Glin K k j (e j)`, whose boundary is computed by

* `Work.RatHurewicz.cubD_Glin` (the chain-level form of the cube identity `cubD_single_degenExt`),
  which says that the boundary of the degenerate extension of `Kf k φ` is
  `(-1)^{k+1}(const - degenOp j φ)` plus the filling of the boundary of `degenOp j φ`;

and the cycle hypothesis `∂d = 0` then cancels the "filling of the boundary" terms.  The result is

`∃ D ∈ Deg (k+2) X, ∂D = aug d • const - d`

(`degen_cycle_mem_range_degen`).  For `aug d = 0` this is exactly the target.

Everything here needs only the connectivity `π_i(X,x₀) = 0` for `i ≤ k`: the missing
`π_{k+1}(X,x₀) = 0` of the plain chain-contraction argument is replaced by the *degeneracy* of `d`
(the degenerate extension of the level-`k` fillings is a genuine `(k+2)`-cube filling the
`(k+1)`-cube `degenOp j φ`).
-/

open scoped unitInterval Topology
open Work.Stems.Cubical
open Work.RatHurewicz

namespace Work.Stems.Hur2c

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The degenerate extensions of a filling tower are degenerate chains: `Glin K k j a` is a sum of
degeneracies `degenOp (Fin.castSucc j) (Kf k φ)`, each of which is independent of the coordinate
`castSucc j`. -/
theorem Glin_mem_Deg {x₀ : X} {N : ℕ} (K : DCTower x₀ N) (k : ℕ) (j : Fin (k + 1))
    (a : Cub k X) : Glin K k j a ∈ Deg (k + 2) X := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | single φ m =>
      rw [show (Finsupp.single φ m : Cub k X) = m • Finsupp.single φ (1 : ℤ) by
            rw [Finsupp.smul_single]; simp,
        map_smul, Glin_single]
      refine Submodule.smul_mem _ _ ?_
      rw [← Dlin_single (n := k + 1) (k := Fin.castSucc j) (s := K.Kf k φ)]
      exact Dlin_mem_Deg (k + 1) (Fin.castSucc j) _

/-- **The décalage.**  A degenerate `(k+1)`-cycle `d` is a boundary, *in the degenerate
subcomplex*, of the constant correction: there is a *degenerate* `(k+2)`-chain whose boundary is
`aug d • const - d`.  (With `aug d = 0` this is the target statement.) -/
theorem degen_cycle_mem_range_degen (k : ℕ) (x₀ : X)
    (hconn : ∀ i : ℕ, i ≤ k → Subsingleton (HomotopyGroup (Fin i) X x₀))
    (d : Cub (k + 1) X) (hd : d ∈ Deg (k + 1) X) (hcyc : cubD k X d = 0) :
    ∃ D : Cub (k + 2) X, D ∈ Deg (k + 2) X ∧
      cubD (k + 1) X D
        = aug (X := X) (k + 1) d • Finsupp.single (cconst (k + 1) x₀) (1 : ℤ) - d := by
  classical
  obtain ⟨K⟩ := Work.RatHurewicz.DCBuild.dcTowerExists k x₀ hconn
  obtain ⟨e, he⟩ := Work.RatHurewicz.exists_decomposition_of_mem_Deg (X := X) (n := k) hd
  have haug : aug (X := X) (k + 1) d = ∑ j : Fin (k + 1), aug (X := X) k (e j) := by
    rw [he, map_sum]
    exact Finset.sum_congr rfl fun j _ => aug_Dlin (X := X) j (e j)
  have hterm : ∀ j : Fin (k + 1),
      cubD (k + 1) X (Glin K k j (e j)) =
        (-1 : ℤ) ^ (k + 1) •
            (aug (X := X) k (e j) • Finsupp.single (cconst (k + 1) x₀) (1 : ℤ)
              - Dlin (X := X) k j (e j))
          + Klin K.toTower k (cubD k X (Dlin (X := X) k j (e j))) := by
    intro j
    rw [← LinearMap.comp_apply, Work.RatHurewicz.cubD_Glin K k le_rfl j]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      LinearMap.smulRight_apply, LinearMap.comp_apply]
  have hB0 : (∑ x : Fin (k + 1),
        Klin K.toTower k (cubD k X (Dlin (X := X) k x (e x)))) = 0 := by
    rw [← map_sum, ← map_sum (cubD k X), he.symm, hcyc, map_zero]
  have hA : (∑ x : Fin (k + 1), (-1 : ℤ) ^ (k + 1) •
        (aug (X := X) k (e x) • Finsupp.single (cconst (k + 1) x₀) (1 : ℤ)
          - Dlin (X := X) k x (e x))) =
      (-1 : ℤ) ^ (k + 1) •
        (aug (X := X) (k + 1) d • Finsupp.single (cconst (k + 1) x₀) (1 : ℤ) - d) := by
    rw [← Finset.smul_sum]
    congr 1
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, haug.symm, he.symm]
  have hG : cubD (k + 1) X (∑ j : Fin (k + 1), Glin K k j (e j)) =
      (-1 : ℤ) ^ (k + 1) •
        (aug (X := X) (k + 1) d • Finsupp.single (cconst (k + 1) x₀) (1 : ℤ) - d) := by
    rw [map_sum, Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, hA, hB0,
      add_zero]
  have hss : ((-1 : ℤ) ^ (k + 1)) * ((-1 : ℤ) ^ (k + 1)) = 1 := by
    rw [← pow_add, show (k + 1) + (k + 1) = 2 * (k + 1) from by ring, pow_mul]
    simp
  refine ⟨((-1 : ℤ) ^ (k + 1)) • (∑ j : Fin (k + 1), Glin K k j (e j)), ?_, ?_⟩
  · exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => Glin_mem_Deg K k j (e j))
  · rw [map_smul, hG, smul_smul, hss, one_smul]

/-- **The target.**  For `X` path connected with `π_i(X) = 0` for `1 ≤ i ≤ m`, every degenerate
`(m+1)`-cycle of augmentation zero is the boundary of a degenerate `(m+2)`-chain. -/
theorem degen_cycle_degen_boundary (m : ℕ) {X : Type} [TopologicalSpace X] (x₀ : X)
    (hpc : PathConnectedSpace X)
    (hconn : ∀ i : ℕ, 1 ≤ i → i ≤ m → Subsingleton (HomotopyGroup (Fin i) X x₀))
    (c : Work.Stems.Cubical.Cub (m + 1) X)
    (hc : c ∈ Work.RatHurewicz.Deg (m + 1) X)
    (hcyc : Work.Stems.Cubical.cubD m X c = 0)
    (haug : Work.RatHurewicz.aug (X := X) (m + 1) c = 0) :
    ∃ D : Work.Stems.Cubical.Cub (m + 2) X,
      D ∈ Work.RatHurewicz.Deg (m + 2) X ∧ Work.Stems.Cubical.cubD (m + 1) X D = c := by
  have hconn' : ∀ i : ℕ, i ≤ m → Subsingleton (HomotopyGroup (Fin i) X x₀) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      have hsub : Subsingleton (ZerothHomotopy X) :=
        (pathConnectedSpace_iff_zerothHomotopy.mp hpc).2
      haveI := hsub
      exact (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x₀)).injective.subsingleton
    · exact hconn i hpos hi
  obtain ⟨D, hDmem, hDbd⟩ := degen_cycle_mem_range_degen m x₀ hconn' c hc hcyc
  refine ⟨-D, Submodule.neg_mem _ hDmem, ?_⟩
  rw [map_neg, hDbd, haug, zero_smul, zero_sub, neg_neg]

end

end Work.Stems.Hur2c
