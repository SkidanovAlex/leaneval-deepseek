import Mathlib
import Submission.Work.EKLContract.Interfaces

/-!
# Density of the rational `aDiag · u_ij` shell in the real one

For the endgame of the EKL argument one needs that the real "diagonal times root group"
shell `{(aDiag t) * u_ij(s) : t ∈ ℝ³, s ∈ ℝ}` lies in the closure of its rational
counterpart.  Both ingredients are elementary:

* `t ↦ aDiag t` and `s ↦ u_ij(s)` are continuous (entrywise continuity of the matrices
  `diag(e^{t_i - |t|/3})` and `1 + s E_{ij}`), hence so is the product map;
* the rational points `(ℚ³ × ℚ)` are dense in `ℝ³ × ℝ` (product of the coordinatewise
  embeddings of `ℚ`).

The closure statement is then the standard `f '' closure s ⊆ closure (f '' s)` for a
continuous `f` evaluated at a point of the dense rational set.
-/

set_option autoImplicit false
open Set Topology Filter
open Work.EKLContract

namespace Work.EKLComp

/-- `t ↦ aDiag t` is continuous: entrywise continuity of `diag (fun i => exp (t i - (∑ j, t j)/3))`
through the subspace topology on `SL₃(ℝ)`. -/
theorem continuous_aDiag : Continuous (fun t : Fin 3 → ℝ => aDiag t) := by
  refine Continuous.subtype_mk (p := fun M : Matrix (Fin 3) (Fin 3) ℝ => M.det = 1)
    (f := fun t : Fin 3 → ℝ => Matrix.diagonal (fun i => Real.exp (t i - (∑ j, t j) / 3))) ?_ ?_
  · apply continuous_matrix
    intro k l
    simp only [Matrix.diagonal_apply]
    by_cases hkl : k = l
    · simp only [hkl, if_true]
      fun_prop
    · simp only [hkl, if_false]
      exact continuous_const

/-- `s ↦ u_ij(s)` is continuous (entrywise continuity of `1 + s·E_ij`). -/
theorem continuous_uij {i j : Fin 3} (hij : i ≠ j) : Continuous (fun s : ℝ => uij hij s) := by
  refine Continuous.subtype_mk (p := fun M : Matrix (Fin 3) (Fin 3) ℝ => M.det = 1)
    (f := fun s : ℝ => (1 : Matrix (Fin 3) (Fin 3) ℝ) + Matrix.single i j s) ?_ ?_
  · refine Continuous.add continuous_const ?_
    apply continuous_matrix
    intro k l
    by_cases hkl : i = k ∧ j = l
    · simp only [Matrix.single_apply, if_pos hkl]; exact continuous_id
    · simp only [Matrix.single_apply, if_neg hkl]; exact continuous_const

/-- The rational points of `ℝ³ × ℝ` are dense: coordinatewise density of `ℚ` in `ℝ`, in the
product of the product topologies. -/
theorem denseRange_rat_lift :
    DenseRange (fun p : (Fin 3 → ℚ) × ℚ => ((fun k => (p.1 k : ℝ)), (p.2 : ℝ))) := by
  have hf : DenseRange (fun q : Fin 3 → ℚ => fun k => (q k : ℝ)) := by
    have h := DenseRange.piMap (fun _ : Fin 3 => (Rat.denseRange_cast (𝕜 := ℝ)))
    have h2 : (Pi.map (fun _ : Fin 3 => (Rat.cast : ℚ → ℝ))) =
        (fun q : Fin 3 → ℚ => fun k => (q k : ℝ)) := by
      funext q k; rw [Pi.map_apply]
    rwa [h2] at h
  have hg : DenseRange (fun q : ℚ => (q : ℝ)) := Rat.denseRange_cast
  change DenseRange (Prod.map (fun q : Fin 3 → ℚ => fun k => (q k : ℝ)) (fun q : ℚ => (q : ℝ)))
  rw [DenseRange, Dense, Set.range_prodMap, closure_prod_eq, hf.closure_eq, hg.closure_eq,
    Set.univ_prod_univ]
  intro x
  exact Set.mem_univ x

/-- The real shell `{(aDiag t) * u_ij(s)}` is contained in the closure of its rational
counterpart. -/
theorem Endgame_dense_rat {i j : Fin 3} (hij : i ≠ j) :
    Set.range (fun p : (Fin 3 → ℝ) × ℝ =>
        Work.EKLContract.aDiag p.1 * Work.EKLContract.uij hij p.2) ⊆
      closure (Set.range (fun p : (Fin 3 → ℚ) × ℚ =>
        Work.EKLContract.aDiag (fun k => (p.1 k : ℝ)) * Work.EKLContract.uij hij (p.2 : ℝ))) := by
  intro x hx
  obtain ⟨q, rfl⟩ := hx
  have hcont : Continuous (fun p : (Fin 3 → ℝ) × ℝ => aDiag p.1 * uij hij p.2) :=
    (continuous_aDiag.comp continuous_fst).mul ((continuous_uij hij).comp continuous_snd)
  have hdense : DenseRange (fun p : (Fin 3 → ℚ) × ℚ =>
      ((fun k => (p.1 k : ℝ)), (p.2 : ℝ))) := denseRange_rat_lift
  have hmem : ((fun k => (q.1 k : ℝ)), (q.2 : ℝ)) ∈
      closure (Set.range (fun p : (Fin 3 → ℚ) × ℚ =>
        ((fun k => (p.1 k : ℝ)), (p.2 : ℝ)))) := by
    rw [hdense.closure_eq]; exact Set.mem_univ _
  have hmem2 : (fun p : (Fin 3 → ℝ) × ℝ => aDiag p.1 * uij hij p.2)
      ((fun k => (q.1 k : ℝ)), (q.2 : ℝ)) ∈
      (fun p : (Fin 3 → ℝ) × ℝ => aDiag p.1 * uij hij p.2) ''
        closure (Set.range (fun p : (Fin 3 → ℚ) × ℚ => ((fun k => (p.1 k : ℝ)), (p.2 : ℝ)))) :=
    Set.mem_image_of_mem _ hmem
  have himg := image_closure_subset_closure_image hcont hmem2
  have hset : (fun p : (Fin 3 → ℝ) × ℝ => aDiag p.1 * uij hij p.2) ''
      Set.range (fun p : (Fin 3 → ℚ) × ℚ => ((fun k => (p.1 k : ℝ)), (p.2 : ℝ)))
      = Set.range (fun p : (Fin 3 → ℚ) × ℚ =>
        aDiag (fun k => (p.1 k : ℝ)) * uij hij (p.2 : ℝ)) := by
    rw [← Set.range_comp]
    rfl
  rwa [hset] at himg

end Work.EKLComp
