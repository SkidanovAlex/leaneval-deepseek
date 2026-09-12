import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.polytope_parallelBody_cellDecomposition
import Submission.Commons.Geometry.Convex.Hadwiger.cell_volume_monomial_and_measurable

open scoped Pointwise BigOperators
open Set

namespace Commons.Geometry.Convex.Hadwiger

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The parallel-body cell over the (intrinsic) interior of `F` in the direction of the
normal cone `normalCone P F`, truncated at radius `s`. -/
private def cellV (P F : Set V) (s : ℝ) : Set V :=
  intrinsicInterior ℝ F + (normalCone P F ∩ Metric.closedBall (0 : V) s)

/-- The commons cell-decomposition lemma, rephrased with the local notation. -/
private lemma cellDecomp_local
    (u : Finset V) (P : Set V)
    (hP : P = convexHull ℝ (u : Set V)) (hint : (interior P).Nonempty) :
    ∃ faces : Finset (Set V),
      (∀ F ∈ faces, F.Nonempty ∧ IsExposed ℝ P F) ∧
      (∀ F ∈ faces, ∃ S : Finset V, ↑S ⊆ u ∧ F = convexHull ℝ (↑S : Set V)) ∧
      (∀ p ∈ P, ∃! F : Set V, F ∈ faces ∧ p ∈ intrinsicInterior ℝ F) ∧
      (∀ t : ℝ, 0 ≤ t →
        (∀ F ∈ faces, cellV P F t ⊆ P + Metric.closedBall (0 : V) t) ∧
        (P + Metric.closedBall (0 : V) t ⊆ ⋃ F ∈ faces, cellV P F t) ∧
        (∀ F ∈ faces, ∀ G ∈ faces, F ≠ G → Disjoint (cellV P F t) (cellV P G t))) := by
  classical
  rcases polytope_parallelBody_cellDecomposition (V := V) u P hP hint with
    ⟨faces, hFprop, hFconv, hFpart, hcell⟩
  refine ⟨faces, hFprop, hFconv, hFpart, ?_⟩
  intro t ht
  specialize hcell t ht
  exact hcell

/-- The commons monomial-cell lemma, rephrased with the local notation. -/
private lemma cellMono_local
    (P F : Set V) (hFP : F ⊆ P) (hFne : F.Nonempty) (hFcl : IsClosed F)
    (hFcvx : Convex ℝ F) (hFbd : Bornology.IsBounded F)
    (t : ℝ) (ht : 0 ≤ t) :
    MeasurableSet (cellV P F t) ∧
    MeasureTheory.volume (cellV P F t) =
      ENNReal.ofReal (t ^ Module.finrank ℝ (Submodule.orthogonal (affineSpan ℝ F).direction)) *
        MeasureTheory.volume (cellV P F 1) := by
  classical
  have h := cell_volume_monomial_and_measurable (V := V) P F hFP hFne hFcl hFcvx hFbd t ht
  simpa [cellV, normalCone] using h

-- ---------------------------------------------------------------
-- elementary helpers
-- ---------------------------------------------------------------

private lemma smul_closedBall_unit {t : ℝ} (ht : 0 ≤ t) :
    t • (Metric.closedBall (0 : V) 1) = Metric.closedBall (0 : V) t := by
  rw [smul_closedBall t (0 : V) (le_of_lt zero_lt_one)]
  simp [Real.norm_eq_abs, abs_of_nonneg ht]

private lemma measure_ne_top_of_subset_compact {A K : Set V} (hK : IsCompact K)
    (hsub : A ⊆ K) : MeasureTheory.volume A ≠ ⊤ := by
  have hmono : MeasureTheory.volume A ≤ MeasureTheory.volume K :=
    MeasureTheory.measure_mono hsub
  have hlt : MeasureTheory.volume K < ⊤ := hK.measure_lt_top
  exact ne_of_lt (lt_of_le_of_lt hmono hlt)

private lemma volume_cell_finite_of_subset {P F : Set V} {t : ℝ}
    (hPcpt : IsCompact P) (hsub : cellV P F t ⊆ P + Metric.closedBall (0 : V) t) :
    MeasureTheory.volume (cellV P F t) ≠ ⊤ := by
  exact measure_ne_top_of_subset_compact
    ((hPcpt).add (ProperSpace.isCompact_closedBall (0 : V) t)) hsub

/-- `p.natDegree ≤ N` when every coefficient at index above `N` vanishes. -/
private lemma natDegree_le_of_coeff_eq_zero {p : Polynomial ℝ} {N : ℕ}
    (h : ∀ m : ℕ, N < m → p.coeff m = 0) : p.natDegree ≤ N := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  exact h

-- ---------------------------------------------------------------
-- polynomial coefficient helper
-- ---------------------------------------------------------------

private lemma coeff_sum_C_mul_X_pow_eq_zero
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℝ) (e : ι → ℕ) (m : ℕ)
    (h : ∀ i ∈ s, e i < m) :
    (∑ i ∈ s, Polynomial.C (c i) * Polynomial.X ^ (e i)).coeff m = 0 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Polynomial.coeff_add]
      have hterm : (Polynomial.C (c a) * Polynomial.X ^ (e a)).coeff m = 0 := by
        have hlt : e a < m := h a (by simp)
        have hne : m ≠ e a := ne_of_gt hlt
        rw [Polynomial.coeff_C_mul_X_pow, if_neg hne]
      rw [hterm]
      simpa using ih (fun i hi => h i (by exact Finset.mem_insert_of_mem hi))

-- ---------------------------------------------------------------
-- main assembly
-- ---------------------------------------------------------------

theorem polytope_parallel_body_polynomial_fullDim_generic_v4
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (u : Finset V) (P : Set V)
    (hP : P = convexHull ℝ (u : Set V)) (hPint : (interior P).Nonempty) :
    ∃ p : Polynomial ℝ, p.natDegree ≤ Module.finrank ℝ V ∧
      ∀ t : ℝ, 0 ≤ t →
        (MeasureTheory.volume (P + t • Metric.closedBall (0 : V) 1)).toReal = p.eval t := by
  classical
  rcases cellDecomp_local u P hP hPint with
    ⟨faces, hFprop, hFconv, hFpart, hcell⟩
  have hPcpt : IsCompact P := by
    rw [hP]
    exact u.finite_toSet.isCompact_convexHull ℝ
  have hFcl : ∀ F ∈ faces, IsClosed F := by
    intro F hF
    rcases hFconv F hF with ⟨S, hS, hFS⟩
    rw [hFS]
    exact (S.finite_toSet.isCompact_convexHull ℝ).isClosed
  have hFcvx : ∀ F ∈ faces, Convex ℝ F := by
    intro F hF
    rcases hFconv F hF with ⟨S, hS, hFS⟩
    rw [hFS]
    exact convex_convexHull ℝ (S : Set V)
  have hFbd : ∀ F ∈ faces, Bornology.IsBounded F := by
    intro F hF
    rcases hFconv F hF with ⟨S, hS, hFS⟩
    rw [hFS]
    exact (S.finite_toSet.isCompact_convexHull ℝ).isBounded
  have hFsub : ∀ F ∈ faces, F ⊆ P := by
    intro F hF
    exact (IsExposed.subset (hFprop F hF).2)
  let eF : Set V → ℕ := fun F => Module.finrank ℝ (Submodule.orthogonal (affineSpan ℝ F).direction)
  let coeff : Set V → ℝ := fun F => (MeasureTheory.volume (cellV P F 1)).toReal
  let p : Polynomial ℝ := ∑ F ∈ faces, Polynomial.C (coeff F) * Polynomial.X ^ (eF F)
  have hcellFin_sub : ∀ (t : ℝ), 0 ≤ t → ∀ F ∈ faces,
      cellV P F t ⊆ P + Metric.closedBall (0 : V) t := by
    intro t ht F hF
    exact (hcell t ht).1 F hF
  have hvol_fin : ∀ (t : ℝ), 0 ≤ t → ∀ F ∈ faces,
      MeasureTheory.volume (cellV P F t) ≠ ⊤ := by
    intro t ht F hF
    exact volume_cell_finite_of_subset hPcpt (hcellFin_sub t ht F hF)
  have hmeasm : ∀ (t : ℝ), 0 ≤ t → ∀ F ∈ faces, MeasurableSet (cellV P F t) := by
    intro t ht F hF
    exact (cellMono_local P F (hFsub F hF) (hFprop F hF).1
      (hFcl F hF) (hFcvx F hF) (hFbd F hF) t ht).1
  have hvol_sum : ∀ t : ℝ, 0 ≤ t →
      MeasureTheory.volume (P + Metric.closedBall (0 : V) t) =
        ∑ F ∈ faces, MeasureTheory.volume (cellV P F t) := by
    intro t ht
    have hdisj : (faces : Set (Set V)).PairwiseDisjoint (fun F => cellV P F t) := by
      intro F hF G hG hFG
      exact (hcell t ht).2.2 F hF G hG hFG
    have hsum : MeasureTheory.volume (⋃ F ∈ faces, cellV P F t) =
        ∑ F ∈ faces, MeasureTheory.volume (cellV P F t) :=
      MeasureTheory.measure_biUnion_finset (μ := MeasureTheory.volume) (s := faces)
        (f := fun F : Set V => cellV P F t) hdisj (hmeasm t ht)
    rw [← hsum]
    congr 1
    apply Subset.antisymm
    · exact (hcell t ht).2.1
    · intro x hx
      rcases (Set.mem_iUnion₂.mp hx) with ⟨F, hF, hxF⟩
      rcases (Set.mem_image2.mp hxF) with ⟨y, hy, z, hz, hxz⟩
      refine ⟨y, (IsExposed.subset (hFprop F hF).2)
        (intrinsicInterior_subset (𝕜 := ℝ) (s := F) hy), z, hz.2, hxz⟩
  have he_le : ∀ F ∈ faces, eF F ≤ Module.finrank ℝ V := by
    intro F hF
    dsimp [eF]
    exact Submodule.finrank_le (Submodule.orthogonal (affineSpan ℝ F).direction)
  refine ⟨p, ?deg, ?val⟩
  · -- degree
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hmgt
    dsimp [p]
    exact coeff_sum_C_mul_X_pow_eq_zero faces coeff eF m (by
      intro F hF
      exact lt_of_le_of_lt (he_le F hF) hmgt)
  · -- values
    intro t ht
    calc
      (MeasureTheory.volume (P + t • Metric.closedBall (0 : V) 1)).toReal
          = (MeasureTheory.volume (P + Metric.closedBall (0 : V) t)).toReal := by
              rw [smul_closedBall_unit ht]
      _ = (∑ F ∈ faces, MeasureTheory.volume (cellV P F t)).toReal := by
              rw [hvol_sum t ht]
      _ = ∑ F ∈ faces, (MeasureTheory.volume (cellV P F t)).toReal := by
              rw [ENNReal.toReal_sum]
              intro F hF
              exact hvol_fin t ht F hF
      _ = ∑ F ∈ faces, t ^ (eF F) * coeff F := by
              apply Finset.sum_congr rfl
              intro F hF
              have hmono := cellMono_local P F (hFsub F hF)
                (hFprop F hF).1 (hFcl F hF) (hFcvx F hF) (hFbd F hF) t ht
              have hre : (MeasureTheory.volume (cellV P F t)).toReal =
                  t ^ (eF F) * coeff F := by
                dsimp [coeff, eF]
                rw [hmono.2, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg ht _)]
              exact hre
      _ = p.eval t := by
              dsimp [p]
              rw [Polynomial.eval_finsetSum]
              apply Finset.sum_congr rfl
              intro F hF
              rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
              ring
end
