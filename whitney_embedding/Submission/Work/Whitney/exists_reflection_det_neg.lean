import Mathlib
import Submission.Work.Whitney.exists_bump_model_pair_smooth

/-!
# A norm-preserving linear reflection of `ℝⁿ × ℝⁿ` of determinant `-1` fixing a prescribed point

This file proves `Work.Whitney.exists_reflection_det_neg`.  Geometrically the statement says:

* for every point `z = (a, b)` of `EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)` with
  `n ≥ 2` there is a linear isometry `S` of the product (endowed with the product norm, i.e.
  `‖(x, y)‖ = max ‖x‖ ‖y‖`) which
  1. fixes the first factor `EuclideanSpace ℝ (Fin n) × {0}` pointwise,
  2. fixes `z`, and
  3. has determinant `-1` (so it reverses orientation).

The reason this exists is that in dimension `n ≥ 2` the orthogonal complement of the line
`ℝ ∙ b` is non-trivial; choosing `0 ≠ w ⊥ b` and letting `K = (ℝ ∙ w)ᗮ ∋ b` be a hyperplane
containing `b`, the orthogonal reflection `K.reflection` fixes `K` pointwise (in particular `b`)
and negates the `1`-dimensional line `Kᗮ`, whence its determinant is `(-1) ^ finrank ℝ Kᗮ = -1`
(`Submodule.det_reflection`).  Building `S` as `id × K.reflection` on the product finishes.

The result is the linear-algebra engine behind the "flip the sign of an inserted double point"
step of Whitney's self-intersection cancellation: precomposing a local model `H` with such an `S`
product is a norm-preserving bijection fixing the axis `u ↦ (u, 0)`, keeps the double point image
and changes the determinant of the two-sheet differential by the factor `det S = -1`.
-/

namespace Work.Whitney

open scoped RealInnerProductSpace

theorem exists_reflection_det_neg (n : ℕ) (hn : 2 ≤ n)
    (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    ∃ S : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      (∀ u : EuclideanSpace ℝ (Fin n), S (u, 0) = (u, 0)) ∧ S z = z ∧
      (∀ w, ‖S w‖ = ‖w‖) ∧ LinearMap.det S.toLinearMap = -1 := by
  -- A non-zero vector orthogonal to the second component of `z`.
  obtain ⟨w, hwne, hwb⟩ : ∃ w : EuclideanSpace ℝ (Fin n), w ≠ 0 ∧ ⟪w, z.2⟫ = 0 := by
    have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n :=
      finrank_euclideanSpace_fin (𝕜 := ℝ)
    have hsum := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ)
      (E := EuclideanSpace ℝ (Fin n)) (ℝ ∙ z.2)
    rw [hdim] at hsum
    have hle : Module.finrank ℝ ↥(ℝ ∙ z.2) ≤ 1 := by
      have h := finrank_span_le_card (R := ℝ) ({z.2} : Set (EuclideanSpace ℝ (Fin n)))
      simpa using h
    have hpos : 0 < Module.finrank ℝ ↥((ℝ ∙ z.2)ᗮ) := by omega
    have hne : ((ℝ ∙ z.2)ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) ≠ ⊥ := by
      intro h
      have : Module.finrank ℝ ↥((ℝ ∙ z.2)ᗮ) = 0 := by
        rw [h]; exact finrank_bot ℝ (EuclideanSpace ℝ (Fin n))
      omega
    obtain ⟨v, hvmem, hvne⟩ := (Submodule.ne_bot_iff _).mp hne
    refine ⟨v, hvne, ?_⟩
    rw [Submodule.mem_orthogonal] at hvmem
    have := hvmem z.2 (Submodule.mem_span_singleton_self z.2)
    rwa [real_inner_comm] at this
  -- The hyperplane `K = (ℝ ∙ w)ᗮ`, which contains `z.2`.
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := (ℝ ∙ w)ᗮ
  have hbK : z.2 ∈ K := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]; exact hwb
  -- The orthogonal reflection in `K`, as a linear map.
  let Llin : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    K.reflection.toLinearEquiv.toLinearMap
  have hLfix : Llin z.2 = z.2 := by
    show K.reflection z.2 = z.2
    exact Submodule.reflection_mem_subspace_eq_self hbK
  have hLnorm : ∀ y, ‖Llin y‖ = ‖y‖ := fun y => K.reflection.norm_map y
  have hLdet : LinearMap.det Llin = -1 := by
    show LinearMap.det (K.reflection.toLinearEquiv.toLinearMap) = -1
    rw [Submodule.det_reflection]
    have h1 : Module.finrank ℝ ↥(Kᗮ) = 1 := by
      show Module.finrank ℝ ↥(((ℝ ∙ w)ᗮ)ᗮ) = 1
      rw [Submodule.orthogonal_orthogonal, finrank_span_singleton hwne]
    rw [h1]; norm_num
  -- The product map `id × K.reflection`, as a continuous linear map.
  let S : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    LinearMap.toContinuousLinearMap (LinearMap.prodMap (LinearMap.id) Llin)
  have hSapp : ∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      S p = (p.1, Llin p.2) := by
    intro p
    simp only [S, LinearMap.coe_toContinuousLinearMap', LinearMap.prodMap_apply,
      LinearMap.id_apply]
  have hSlin : S.toLinearMap = LinearMap.prodMap (LinearMap.id) Llin := by
    simp only [S, LinearMap.coe_toContinuousLinearMap]
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · intro u
    rw [hSapp]; simp
  · rw [hSapp, hLfix]
  · intro u
    rw [hSapp, Prod.norm_def, Prod.norm_def, hLnorm]
  · rw [hSlin, LinearMap.det_prodMap, LinearMap.det_id, one_mul, hLdet]

end Work.Whitney
