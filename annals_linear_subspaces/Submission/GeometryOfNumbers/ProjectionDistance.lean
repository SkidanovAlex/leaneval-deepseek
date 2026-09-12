import Mathlib
import Submission.Commons.Analysis.InnerProductSpace.cauchySchwarz_sum_smul_normSq
import Submission.Commons.Analysis.InnerProductSpace.orthonormal_normSq_sum_smul
import Submission.Commons.Analysis.InnerProductSpace.orthonormal_sum_inner_eq_self_of_mem_span

/-!
# Projection distance to a subspace, via any orthonormal basis (Lemma 1(a), seed)

For a subspace `x ≤ E` and an orthonormal family `u : Fin k → E`, any vector
`v = Σ i, a i • u i` satisfies
`‖v − π_x v‖² ≤ (Σ i ‖u i − π_x u i‖²) · ‖v‖²`.
This is the Cauchy–Schwarz half of the paper's Lemma 1(a): the distance from `v` to `x`
(measured by the size of the orthogonal residual) is controlled by the sum of the residuals
of the basis vectors, which for a subspace `V = span (range u)` bounds the operator-norm
distance `δ(V,x)`.

All results here are Mathlib-only.
-/

noncomputable section

open InnerProductSpace
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Submission.ProjectionDistance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Cauchy–Schwarz-type inequality: square norm of a linear combination of vectors is at most
the product of the sums of the squared coefficients and squared norms (routines). -/
lemma cs_comb_normSq {ι : Type*} [Fintype ι] (a : ι → ℝ) (b : ι → E) :
    ‖(Finset.univ.sum fun i => a i • b i)‖ ^ 2 ≤
      (Finset.univ.sum fun i => (a i) ^ 2) * (Finset.univ.sum fun i => ‖b i‖ ^ 2) :=
  Commons.Analysis.InnerProductSpace.cauchySchwarz_sum_smul_normSq a b

/-- Pythagoras for orthonormal families: square norm of a combination is the sum of the
squared coefficients (routines). -/
lemma orthonormal_comb_normSq {ι : Type*} [Fintype ι] (u : ι → E) (hu : Orthonormal ℝ u)
    (a : ι → ℝ) :
    ‖(Finset.univ.sum fun i => a i • u i)‖ ^ 2 =
      Finset.univ.sum (fun i => (a i) ^ 2) :=
  Commons.Analysis.InnerProductSpace.orthonormal_normSq_sum_smul u hu a

/-- **Lemma 1(a), seed**: for any orthonormal family `u` and any coefficients `a`, the squared
distance of `v = Σᵢ aᵢuᵢ` from the subspace `x` is bounded by the squared distance of the
`uᵢ`'s from `x`, times the squared norm of `v`. -/
lemma proj_residual_normSq_le_sum_smul {x : Submodule ℝ E} {k : ℕ} (u : Fin k → E)
    (hu : Orthonormal ℝ u) (a : Fin k → ℝ) :
    ‖(Finset.univ.sum (fun i => a i • u i)) -
        ((x.orthogonalProjectionOnto (Finset.univ.sum (fun i => a i • u i))) : E)‖ ^ 2 ≤
      (Finset.univ.sum (fun i : Fin k =>
        ‖(u i) - ((x.orthogonalProjectionOnto (u i)) : E)‖ ^ 2)) *
      ‖(Finset.univ.sum (fun i => a i • u i))‖ ^ 2 := by
  let P : E →ₗ[ℝ] E := (x.subtype).comp (x.orthogonalProjectionOnto).toLinearMap
  let v : E := Finset.univ.sum (fun i : Fin k => a i • u i)
  -- P is the orthogonal projection onto x (viewed in E): P z = (π_x z : E)
  have hP : ∀ z : E, P z = ((x.orthogonalProjectionOnto z) : E) := by
    intro z
    rfl
  -- P is linear: P(Σ aᵢuᵢ) = Σ aᵢ • P uᵢ
  have hlin : P v = Finset.univ.sum (fun i : Fin k => a i • P (u i)) := by
    dsimp [v]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_smul]
  -- split the residual: v − Pv = Σᵢ aᵢ • (uᵢ − P uᵢ)
  have hsplit : v - P v = Finset.univ.sum (fun i : Fin k => a i • ((u i) - P (u i))) := by
    calc
      v - P v = (Finset.univ.sum (fun i : Fin k => a i • u i)) - P (Finset.univ.sum (fun i : Fin k => a i • u i)) := by
                dsimp [v]
      _ = (Finset.univ.sum (fun i : Fin k => a i • u i)) -
            (Finset.univ.sum (fun i : Fin k => a i • P (u i))) := by
                rw [hlin]
      _ = Finset.univ.sum (fun i : Fin k => (a i • u i) - (a i • P (u i))) := by
                rw [Finset.sum_sub_distrib]
      _ = Finset.univ.sum (fun i : Fin k => a i • ((u i) - P (u i))) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [← smul_sub]
  -- Cauchy–Schwarz
  have hcs : ‖Finset.univ.sum (fun i : Fin k => a i • ((u i) - P (u i)))‖ ^ 2 ≤
      (Finset.univ.sum (fun i : Fin k => (a i) ^ 2)) *
        (Finset.univ.sum (fun i : Fin k => ‖(u i) - P (u i)‖ ^ 2)) :=
    cs_comb_normSq a (fun i => (u i) - P (u i))
  -- Pythagoras: Σ aᵢ² = ‖v‖²
  have hpyth : (Finset.univ.sum (fun i : Fin k => (a i) ^ 2)) = ‖v‖ ^ 2 := by
    dsimp [v]
    exact (orthonormal_comb_normSq u hu a).symm
  calc
    ‖v - ((x.orthogonalProjectionOnto v) : E)‖ ^ 2 = ‖v - P v‖ ^ 2 := by
          rw [hP]
    _ = ‖Finset.univ.sum (fun i : Fin k => a i • ((u i) - P (u i)))‖ ^ 2 := by
          rw [hsplit]
    _ ≤ (Finset.univ.sum (fun i : Fin k => (a i) ^ 2)) *
          (Finset.univ.sum (fun i : Fin k => ‖(u i) - P (u i)‖ ^ 2)) := hcs
    _ = ‖v‖ ^ 2 * (Finset.univ.sum (fun i : Fin k => ‖(u i) - P (u i)‖ ^ 2)) := by
          rw [hpyth]
    _ = (Finset.univ.sum (fun i : Fin k => ‖(u i) - P (u i)‖ ^ 2)) * ‖v‖ ^ 2 := by
          rw [mul_comm]

/-- **Lemma 1(a), per-vector form**: for any `v` in the span of an orthonormal family `u`,
the squared distance of `v` from `x` is bounded by the sum of the squared distances of the
`uᵢ`'s from `x`, times the squared norm of `v`. (Plug-in of the representation lemma
`v = Σᵢ ⟪uᵢ, v⟫ uᵢ` into `proj_residual_normSq_le_sum_smul`.) -/
lemma proj_residual_normSq_le_of_mem {x : Submodule ℝ E} {k : ℕ} (u : Fin k → E)
    (hu : Orthonormal ℝ u) {v : E} (hv : v ∈ Submodule.span ℝ (Set.range u)) :
    ‖v - ((x.orthogonalProjectionOnto v) : E)‖ ^ 2 ≤
      (Finset.univ.sum (fun i : Fin k =>
        ‖(u i) - ((x.orthogonalProjectionOnto (u i)) : E)‖ ^ 2)) * ‖v‖ ^ 2 := by
  let a : Fin k → ℝ := fun i => inner ℝ (u i) v
  have hrep : (Finset.univ.sum (fun i : Fin k => a i • u i)) = v := by
    simpa [a] using
      (Commons.Analysis.InnerProductSpace.orthonormal_sum_inner_eq_self_of_mem_span u hu hv)
  have hseed := proj_residual_normSq_le_sum_smul (x := x) (u := u) (hu := hu) (a := a)
  rw [hrep] at hseed
  exact hseed

/-- **Lemma 1(a), unit-vector form**: every unit vector `v` in the span of the orthonormal
family `u` has its distance from `x` bounded by the square root of the sum of the squared
distances of the `uᵢ`'s from `x`. -/
lemma unit_residual_le_sqrt_sum {x : Submodule ℝ E} {k : ℕ} (u : Fin k → E)
    (hu : Orthonormal ℝ u) {v : E} (hv : v ∈ Submodule.span ℝ (Set.range u)) (hv1 : ‖v‖ = 1) :
    ‖v - ((x.orthogonalProjectionOnto v) : E)‖ ≤
      Real.sqrt (Finset.univ.sum (fun i : Fin k =>
        ‖(u i) - ((x.orthogonalProjectionOnto (u i)) : E)‖ ^ 2)) := by
  have hsq := proj_residual_normSq_le_of_mem (x := x) (u := u) (hu := hu) (v := v) hv
  have hle : ‖v - ((x.orthogonalProjectionOnto v) : E)‖ ^ 2 ≤
      Finset.univ.sum (fun i : Fin k =>
        ‖(u i) - ((x.orthogonalProjectionOnto (u i)) : E)‖ ^ 2) := by
    simpa [hv1] using hsq
  have ha : 0 ≤ ‖v - ((x.orthogonalProjectionOnto v) : E)‖ := norm_nonneg _
  have hS : 0 ≤ Finset.univ.sum (fun i : Fin k =>
      ‖(u i) - ((x.orthogonalProjectionOnto (u i)) : E)‖ ^ 2) := by
    exact Finset.sum_nonneg (fun i hi => sq_nonneg _)
  exact (Real.le_sqrt ha hS).2 hle

/-- The operator-norm distance from a subspace `V` to the subspace `x`: the largest sine of
the angle between a unit vector of `V` and `x` (equivalently the largest residual after
orthogonal projection onto `x`). This is the `δ(V,x)` of the paper's Lemma 1 for `V` of
dimension `k ≤ dim x`. -/
def planeResidual (V x : Submodule ℝ E) : ℝ :=
  sSup {r : ℝ | ∃ v : E, v ∈ V ∧ ‖v‖ = 1 ∧ ‖v - ((x.orthogonalProjectionOnto v) : E)‖ = r}

/-- **Lemma 1(a)**: if `u` is an orthonormal basis of `V`, the distance `δ(V,x)` is bounded by
the square root of the sum of the squared residuals of the `uᵢ`'s. -/
lemma planeResidual_le_sqrt_sum {x V : Submodule ℝ E} {k : ℕ} (hk : 0 < k) (u : Fin k → E)
    (hu : Orthonormal ℝ u) (hV : V = Submodule.span ℝ (Set.range u)) :
    planeResidual V x ≤
      Real.sqrt (Finset.univ.sum (fun i : Fin k =>
        ‖(u i) - ((x.orthogonalProjectionOnto (u i)) : E)‖ ^ 2)) := by
  classical
  let S : Set ℝ := {r : ℝ | ∃ v : E, v ∈ V ∧ ‖v‖ = 1 ∧
    ‖v - ((x.orthogonalProjectionOnto v) : E)‖ = r}
  let T : ℝ := Real.sqrt (Finset.univ.sum (fun i : Fin k =>
    ‖(u i) - ((x.orthogonalProjectionOnto (u i)) : E)‖ ^ 2))
  have hmem : ∀ r ∈ S, r ≤ T := by
    intro r hr
    rcases hr with ⟨v, hvV, hv1, rfl⟩
    have hvspan : v ∈ Submodule.span ℝ (Set.range u) := by
      simpa [hV] using hvV
    exact unit_residual_le_sqrt_sum u hu hvspan hv1
  have hne : S.Nonempty := by
    let i0 : Fin k := ⟨0, hk⟩
    refine ⟨‖(u i0) - ((x.orthogonalProjectionOnto (u i0)) : E)‖, ?_⟩
    refine ⟨u i0, ?_, ?_, rfl⟩
    · have hspan : (u i0) ∈ Submodule.span ℝ (Set.range u) := Submodule.subset_span ⟨i0, rfl⟩
      simpa [hV] using hspan
    · exact hu.norm_eq_one i0
  exact csSup_le hne (fun r hr => hmem r hr)

end Submission.ProjectionDistance
