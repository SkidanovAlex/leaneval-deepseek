import Mathlib
import Submission.Work.RatHurewicz.CubicalDefs
import Submission.Work.Stems.Hur2c.cycle_mem_range_add_const_of_tower
import Submission.Work.RatHurewicz.degeneracyChains
import Submission.Work.RatHurewicz.fillingFamilyConst
import Submission.Work.RatHurewicz.DCTowerDefs
import Submission.Work.RatHurewicz.DCTowerAux
import Submission.Work.RatHurewicz.DCBuild.dcTowerExists

/-!
# Degenerate `(k+1)`-cycles are boundaries plus the constant cube

`Work.RatHurewicz.degenCycleBoundaryAddConst`:  for `X` with `π_i(X,x₀) = 0` for `1 ≤ i ≤ k` (and
`X` path connected), every **degenerate** `(k+1)`-cycle `d ∈ Deg (k+1) X` is a boundary plus a
multiple of the constant `(k+1)`-cube at `x₀`:

`d ∈ range (∂ : Cub (k+2) X → Cub (k+1) X) ⊔ ConstChain (k+1) X x₀`.

The point of the statement is that the *degeneracy* hypothesis replaces the missing connectivity
`π_{k+1}(X,x₀) = 0` which the plain chain-contraction argument
(`Work.Stems.Hur2c.cycle_mem_range_add_const_of_tower`) would need: a degenerate `(k+1)`-cube
`degenOp j φ` can be filled by the *degenerate extension* `degenOp (castSucc j) (Kf k φ)` of the
filling of the underlying `k`-cube, which only needs `π_k = 0`.  This is exactly the
`hDC`-compatibility of a `Work.RatHurewicz.DCTower` (`Submission/Work/RatHurewicz/DCTowerDefs.lean`),
whose existence is `Work.RatHurewicz.dcTowerExists`.

The proof has two layers:

* `cubD_single_degenExt` — the cube-level identity `∂ (D_{castSucc j} (Kf k φ))
  = ±(const - D_j φ) + Kf k (∂ D_j φ)`, from the face lemmas `dcTower_last_face`,
  `dcTower_side_matched_zero`/`_one` of the filling tower;
* the linearisation `cubD_Glin` and the cancellation of the boundary terms against the cycle
  hypothesis `∂ d = 0` (`degenCycleBoundaryAddConst_of_dcTower`).
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-! ## The degenerate extension of the tower filings -/

/-- The `ℤ`-linear extension of the degeneracy extension `φ ↦ D_{castSucc j} (Kf k φ)`:
the "filling" of the degenerate `(k+1)`-cube `degenOp j φ`, on chains. -/
def Glin {x₀ : X} {N : ℕ} (K : DCTower x₀ N) (k : ℕ) (j : Fin (k + 1)) :
    Cub k X →ₗ[ℤ] Cub (k + 2) X :=
  Finsupp.linearCombination ℤ fun φ : C(IC k, X) =>
    Finsupp.single (degenOp (Fin.castSucc j) (K.Kf k φ)) (1 : ℤ)

@[simp] theorem Glin_single {x₀ : X} {N : ℕ} (K : DCTower x₀ N) (k : ℕ) (j : Fin (k + 1))
    (φ : C(IC k, X)) :
    Glin K k j (Finsupp.single φ 1) =
      Finsupp.single (degenOp (Fin.castSucc j) (K.Kf k φ)) (1 : ℤ) := by
  rw [Glin, Finsupp.linearCombination_single, one_smul]

/-- **The cube-level identity.**  The boundary of the filling of the degenerate `(k+1)`-cube
`degenOp j φ` is (the constant cube minus that cube) plus the filling of its boundary. -/
theorem cubD_single_degenExt {x₀ : X} {N : ℕ} (K : DCTower x₀ N) (k : ℕ) (hk : k ≤ N)
    (j : Fin (k + 1)) (φ : C(IC k, X)) :
    cubD (k + 1) X (Finsupp.single (degenOp (Fin.castSucc j) (K.Kf k φ)) (1 : ℤ)) =
      (-1 : ℤ) ^ (k + 1) •
          (Finsupp.single (cconst (k + 1) x₀) (1 : ℤ)
            - Finsupp.single (degenOp j φ) (1 : ℤ))
        + Klin K.toTower k (cubD k X (Finsupp.single (degenOp j φ) (1 : ℤ))) := by
  rw [cubD_single (n := k + 1), Fin.sum_univ_castSucc]
  simp only [Work.Stems.Cubical.faceCube]
  have hlast : (-1 : ℤ) ^ ((Fin.last (k + 1) : Fin (k + 1 + 1)) : ℕ) •
        (Finsupp.single ((degenOp (Fin.castSucc j) (K.Kf k φ)).comp
            (faceCM (Fin.last (k + 1)) 0)) (1 : ℤ)
          - Finsupp.single ((degenOp (Fin.castSucc j) (K.Kf k φ)).comp
            (faceCM (Fin.last (k + 1)) 1)) (1 : ℤ)) =
      (-1 : ℤ) ^ (k + 1) •
        (Finsupp.single (cconst (k + 1) x₀) (1 : ℤ)
          - Finsupp.single (degenOp j φ) (1 : ℤ)) := by
    rw [Fin.val_last,
      dcTower_last_face k j (K.Kf k φ) 0, dcTower_last_face k j (K.Kf k φ) 1,
      (K.hα k hk φ).2, (K.hα k hk φ).1, degenOp_cconst]
  have hside : ∀ l : Fin (k + 1),
      (-1 : ℤ) ^ ((Fin.castSucc l : Fin (k + 1 + 1)) : ℕ) •
        (Finsupp.single ((degenOp (Fin.castSucc j) (K.Kf k φ)).comp
            (faceCM (Fin.castSucc l) 0)) (1 : ℤ)
          - Finsupp.single ((degenOp (Fin.castSucc j) (K.Kf k φ)).comp
            (faceCM (Fin.castSucc l) 1)) (1 : ℤ)) =
      (-1 : ℤ) ^ (l : ℕ) • (Klin K.toTower k
        (Finsupp.single ((degenOp j φ).comp (faceCM l 0)) (1 : ℤ)
          - Finsupp.single ((degenOp j φ).comp (faceCM l 1)) (1 : ℤ))) := by
    intro l
    rw [Fin.val_castSucc, map_sub, Klin_single, Klin_single]
    by_cases hlj : l = j
    · subst hlj
      simp only [degenOp_comp_faceCM_self, sub_self, smul_zero]
    · have hjl : j ≠ l := fun h => hlj h.symm
      rw [dcTower_side_matched_zero K k hk j l hlj hjl φ,
        dcTower_side_matched_one K k hk j l hlj hjl φ]
  rw [Finset.sum_congr rfl fun l _ => hside l, hlast]
  have hc : cubD k X (Finsupp.single (degenOp j φ) (1 : ℤ)) =
      ∑ l : Fin (k + 1), (-1 : ℤ) ^ (l : ℕ) •
        (Finsupp.single ((degenOp j φ).comp (faceCM l 0)) (1 : ℤ)
          - Finsupp.single ((degenOp j φ).comp (faceCM l 1)) (1 : ℤ)) := by
    rw [cubD_single (degenOp j φ)]
    simp only [Work.Stems.Cubical.faceCube]
  rw [hc, map_sum]
  simp only [map_smul]
  abel

/-- **The chain-level form of `cubD_single_degenExt`**, as an identity of linear maps on `Cub k X`. -/
theorem cubD_Glin {x₀ : X} {N : ℕ} (K : DCTower x₀ N) (k : ℕ) (hk : k ≤ N) (j : Fin (k + 1)) :
    (cubD (k + 1) X).comp (Glin K k j) =
      ((-1 : ℤ) ^ (k + 1)) •
          ((aug (X := X) k).smulRight (Finsupp.single (cconst (k + 1) x₀) (1 : ℤ))
            - Dlin (X := X) k j)
        + (Klin K.toTower k).comp ((cubD k X).comp (Dlin (X := X) k j)) := by
  have h2 : (Finsupp.lift (Cub (k + 1) X) ℤ (C(IC k, X))).symm
        ((cubD (k + 1) X).comp (Glin K k j)) =
      (Finsupp.lift (Cub (k + 1) X) ℤ (C(IC k, X))).symm
        (((-1 : ℤ) ^ (k + 1)) •
            ((aug (X := X) k).smulRight (Finsupp.single (cconst (k + 1) x₀) (1 : ℤ))
              - Dlin (X := X) k j)
          + (Klin K.toTower k).comp ((cubD k X).comp (Dlin (X := X) k j))) := by
    funext φ
    rw [Finsupp.lift_symm_apply, Finsupp.lift_symm_apply]
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.smulRight_apply, Glin_single, Dlin_single, aug_single,
      one_smul]
    exact cubD_single_degenExt K k hk j φ
  simpa using congrArg (Finsupp.lift (Cub (k + 1) X) ℤ (C(IC k, X))) h2

/-- The augmentation of a degenerate extension: `D_i` is a bijection on generators, so it does not
change the augmentation. -/
theorem aug_Dlin {n : ℕ} (i : Fin (n + 1)) (c : Cub n X) :
    aug (X := X) (n + 1) (Dlin (X := X) n i c) = aug (X := X) n c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single φ a =>
      rw [Dlin_single_smul, map_smul, aug_single, aug_smul_single, smul_eq_mul, mul_one]

/-! ## The assembly -/

/-- **A degenerate `(k+1)`-cycle is a boundary plus the constant cube**, given a
degeneracy-compatible filling tower at level `k`. -/
theorem degenCycleBoundaryAddConst_of_dcTower (k : ℕ) (x₀ : X) (hk : 1 ≤ k)
    (K : DCTower x₀ k) (d : Cub (k + 1) X) (hd : d ∈ Deg (k + 1) X)
    (hcyc : cubD k X d = 0) :
    d ∈ LinearMap.range (cubD (k + 1) X) ⊔ ConstChain (k + 1) X x₀ := by
  classical
  obtain ⟨e, he⟩ := exists_decomposition_of_mem_Deg (n := k) hd
  have haug : aug (X := X) (k + 1) d = ∑ j : Fin (k + 1), aug (X := X) k (e j) := by
    rw [he, map_sum]
    exact Finset.sum_congr rfl fun j _ => aug_Dlin j (e j)
  have hterm : ∀ j : Fin (k + 1), cubD (k + 1) X (Glin K k j (e j)) =
      (-1 : ℤ) ^ (k + 1) •
          (aug (X := X) k (e j) • Finsupp.single (cconst (k + 1) x₀) (1 : ℤ)
            - Dlin (X := X) k j (e j))
        + Klin K.toTower k (cubD k X (Dlin (X := X) k j (e j))) := by
    intro j
    rw [← LinearMap.comp_apply, cubD_Glin K k le_rfl j]
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
  have hd_eq : d = aug (X := X) (k + 1) d • Finsupp.single (cconst (k + 1) x₀) (1 : ℤ)
      - ((-1 : ℤ) ^ (k + 1)) •
          cubD (k + 1) X (∑ j : Fin (k + 1), Glin K k j (e j)) := by
    rw [hG, smul_smul, hss, one_smul]
    abel
  rw [hd_eq, sub_eq_add_neg]
  refine Submodule.add_mem _ ?_ ?_
  · exact Submodule.mem_sup_right (Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_singleton _)))
  · refine Submodule.mem_sup_left ?_
    refine ⟨-(((-1 : ℤ) ^ (k + 1)) • (∑ j : Fin (k + 1), Glin K k j (e j))), ?_⟩
    rw [map_neg, map_smul]

theorem degenCycleBoundaryAddConst (k : ℕ) (X : Type) [TopologicalSpace X] (x₀ : X)
    (hk : 1 ≤ k)
    (hpc : PathConnectedSpace X)
    (hconn : ∀ i : ℕ, 1 ≤ i → i ≤ k → Subsingleton (HomotopyGroup (Fin i) X x₀))
    (d : Work.Stems.Cubical.Cub (k + 1) X)
    (hd : d ∈ Work.RatHurewicz.Deg (k + 1) X)
    (hcyc : Work.Stems.Cubical.cubD k X d = 0) :
    d ∈ LinearMap.range (Work.Stems.Cubical.cubD (k + 1) X) ⊔
      Work.RatHurewicz.ConstChain (k + 1) X x₀ := by
  have hconn' : ∀ i : ℕ, i ≤ k → Subsingleton (HomotopyGroup (Fin i) X x₀) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      have hsub : Subsingleton (ZerothHomotopy X) :=
        (pathConnectedSpace_iff_zerothHomotopy.mp hpc).2
      haveI := hsub
      exact (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x₀)).injective.subsingleton
    · exact hconn i hpos hi
  obtain ⟨K⟩ := DCBuild.dcTowerExists k x₀ hconn'
  exact degenCycleBoundaryAddConst_of_dcTower k x₀ hk K d hd hcyc

end

end Work.RatHurewicz
