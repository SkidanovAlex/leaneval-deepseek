import Mathlib
import Submission.GeometryOfNumbers.ProjectionDistance

/-!
# Isometry invariance of projections and the residual distance

For a real finite-dimensional inner product space `E`, a linear isometry `g : E ≃ₗᵢ[ℝ] E`
that preserves a subspace `K` (`K.map g = K`) also preserves its orthogonal complement,
commutes with the orthogonal projection onto `K`, and leaves the residual
`‖v − π_K v‖` invariant.  Consequently the operator-norm distance
`planeResidual V x` (`Submission.ProjectionDistance`) is invariant under replacing `V` by
its image under such an isometry (with `x` fixed).

This is the transfer principle behind the rotation reduction used to prove the general
pure-tensor Lemma 1 (paper de Saxcé §1) from the graph-coordinate form: one rotates the
plane `V` (within the reference plane `x`) into graph position; distance and exterior-power
blocks are unchanged by the rotation.

All results here are Mathlib-only.
-/

noncomputable section

open Module Real InnerProductGeometry Real
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Submission.Bridge.Isometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- An isometry preserving `K` also preserves the orthogonal complement `Kᗮ`. -/
lemma orthogonal_map_eq_of_map_eq (K : Submodule ℝ E) (g : E ≃ₗᵢ[ℝ] E)
    (hg : K.map (g : E →ₗ[ℝ] E) = K) :
    (Kᗮ).map (g : E →ₗ[ℝ] E) = Kᗮ := by
  classical
  apply le_antisymm
  · intro z hz
    rcases (Submodule.mem_map.mp hz) with ⟨w, hw, hzval⟩
    subst z
    rw [Submodule.mem_orthogonal]
    intro y hy
    rcases (Submodule.mem_map.mp (by rw [hg]; exact hy)) with ⟨y', hy', hyval⟩
    calc
      inner ℝ y (g w) = inner ℝ (g y') (g w) := by
            rw [← hyval]
            rfl
      _ = inner ℝ y' w := by rw [LinearIsometryEquiv.inner_map_map]
      _ = 0 := (Submodule.mem_orthogonal K w).mp hw y' hy'
  · intro y hy
    rw [Submodule.mem_map]
    refine ⟨g.symm y, ?_, ?_⟩
    · rw [Submodule.mem_orthogonal]
      intro x hx
      have hmem {x : E} (hx : x ∈ K) : g x ∈ K := by
        rw [← hg]
        exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
      have hgx : g x ∈ K := hmem hx
      calc
        inner ℝ x (g.symm y) = inner ℝ (g x) (g (g.symm y)) := by
              exact (LinearIsometryEquiv.inner_map_map g x (g.symm y)).symm
        _ = inner ℝ (g x) y := by rw [LinearIsometryEquiv.apply_symm_apply]
        _ = 0 := (Submodule.mem_orthogonal K y).mp hy (g x) hgx
    · exact LinearIsometryEquiv.apply_symm_apply g y

/-- The orthogonal projection onto `K` commutes with an isometry preserving `K`. -/
lemma starProjection_comm (K : Submodule ℝ E) (g : E ≃ₗᵢ[ℝ] E)
    (hg : K.map (g : E →ₗ[ℝ] E) = K) (v : E) :
    K.starProjection (g v) = g (K.starProjection v) := by
  classical
  apply Submodule.eq_starProjection_of_mem_orthogonal (K := K) (u := g v) (v := g (K.starProjection v))
  · have hmem {x : E} (hx : x ∈ K) : g x ∈ K := by
      rw [← hg]
      exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    exact hmem (Submodule.starProjection_apply_mem K v)
  · have hres : v - K.starProjection v ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal v
    have hm : g (v - K.starProjection v) ∈ (Kᗮ).map (g : E →ₗ[ℝ] E) :=
      Submodule.mem_map.mpr ⟨v - K.starProjection v, hres, rfl⟩
    rw [orthogonal_map_eq_of_map_eq K g hg] at hm
    have hsub : g v - g (K.starProjection v) = g (v - K.starProjection v) :=
      (LinearIsometryEquiv.map_sub g v (K.starProjection v)).symm
    rw [hsub]
    exact hm

/-- The residual `‖v − π_K v‖` is invariant under an isometry preserving `K`. -/
lemma residual_norm_map (K : Submodule ℝ E) (g : E ≃ₗᵢ[ℝ] E)
    (hg : K.map (g : E →ₗ[ℝ] E) = K) (v : E) :
    ‖g v - K.starProjection (g v)‖ = ‖v - K.starProjection v‖ := by
  rw [starProjection_comm K g hg v]
  calc
    ‖g v - g (K.starProjection v)‖ = ‖g (v - K.starProjection v)‖ := by
          exact (congrArg norm (LinearIsometryEquiv.map_sub g v (K.starProjection v))).symm
    _ = ‖v - K.starProjection v‖ := LinearIsometryEquiv.norm_map g (v - K.starProjection v)

/-- `planeResidual (V.map g) x = planeResidual V x` whenever the isometry `g` preserves `x`. -/
lemma planeResidual_map (V x : Submodule ℝ E) (g : E ≃ₗᵢ[ℝ] E)
    (hgx : x.map (g : E →ₗ[ℝ] E) = x) :
    Submission.ProjectionDistance.planeResidual (V.map (g : E →ₗ[ℝ] E)) x =
      Submission.ProjectionDistance.planeResidual V x := by
  classical
  unfold Submission.ProjectionDistance.planeResidual
  apply congrArg sSup
  ext r
  constructor
  · rintro ⟨w, hwV, hw1, hwr⟩
    rcases (Submodule.mem_map.mp hwV) with ⟨v, hvV, hwval⟩
    subst w
    refine ⟨v, hvV, ?_, ?_⟩
    · exact (LinearIsometryEquiv.norm_map g v).symm.trans hw1
    · rw [Submodule.coe_orthogonalProjectionOnto_apply]
      rw [Submodule.coe_orthogonalProjectionOnto_apply] at hwr
      exact (residual_norm_map x g hgx v).symm.trans hwr
  · rintro ⟨v, hvV, hv1, hvr⟩
    refine ⟨g v, ?_, ?_, ?_⟩
    · exact Submodule.mem_map.mpr ⟨v, hvV, rfl⟩
    · rw [LinearIsometryEquiv.norm_map g v]
      exact hv1
    · rw [Submodule.coe_orthogonalProjectionOnto_apply]
      rw [residual_norm_map x g hgx v]
      rw [Submodule.coe_orthogonalProjectionOnto_apply] at hvr
      exact hvr



/-- Orthogonal projection onto a transported subspace commutes with the transporting
isometry: `π_{(K.map g)} (g v) = g (π_K v)`. -/
lemma starProjection_map (K : Submodule ℝ E) (g : E ≃ₗᵢ[ℝ] E) (v : E) :
    (K.map (g : E →ₗ[ℝ] E)).starProjection (g v) = g (K.starProjection v) := by
  classical
  apply Submodule.eq_starProjection_of_mem_orthogonal (K := K.map (g : E →ₗ[ℝ] E))
    (u := g v) (v := g (K.starProjection v))
  · exact Submodule.mem_map.mpr ⟨K.starProjection v, Submodule.starProjection_apply_mem K v, rfl⟩
  · have hres : v - K.starProjection v ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal v
    rw [Submodule.mem_orthogonal]
    intro y hy
    rcases (Submodule.mem_map.mp hy) with ⟨y', hy', hyval⟩
    have hsub : g v - g (K.starProjection v) = g (v - K.starProjection v) :=
      (LinearIsometryEquiv.map_sub g v (K.starProjection v)).symm
    calc
      inner ℝ y (g v - g (K.starProjection v)) = inner ℝ y (g (v - K.starProjection v)) := by rw [hsub]
      _ = inner ℝ (g y') (g (v - K.starProjection v)) := by rw [← hyval]; rfl
      _ = inner ℝ y' (v - K.starProjection v) := by rw [LinearIsometryEquiv.inner_map_map]
      _ = 0 := (Submodule.mem_orthogonal K (v - K.starProjection v)).mp hres y' hy'

/-- The residual `‖w − π_K w‖` is invariant under simultaneous transport of the vector and
the subspace: `‖g v − π_{(K.map g)} (g v)‖ = ‖v − π_K v‖`. -/
lemma residual_norm_map_map (K : Submodule ℝ E) (g : E ≃ₗᵢ[ℝ] E) (v : E) :
    ‖g v - (K.map (g : E →ₗ[ℝ] E)).starProjection (g v)‖ = ‖v - K.starProjection v‖ := by
  rw [starProjection_map K g v]
  calc
    ‖g v - g (K.starProjection v)‖ = ‖g (v - K.starProjection v)‖ := by
          exact (congrArg norm (LinearIsometryEquiv.map_sub g v (K.starProjection v))).symm
    _ = ‖v - K.starProjection v‖ := LinearIsometryEquiv.norm_map g (v - K.starProjection v)

/-- The operator-norm distance is invariant under simultaneous transport of both subspaces by
an isometry: `planeResidual (V.map g) (x.map g) = planeResidual V x`.  (This is the transfer
principle that reduces the distance from an arbitrary plane `x` to the reference plane
`x₀`: apply the isometry sending `x` to `x₀`.) -/
lemma planeResidual_map_map (V x : Submodule ℝ E) (g : E ≃ₗᵢ[ℝ] E) :
    Submission.ProjectionDistance.planeResidual (V.map (g : E →ₗ[ℝ] E))
      (x.map (g : E →ₗ[ℝ] E)) = Submission.ProjectionDistance.planeResidual V x := by
  classical
  unfold Submission.ProjectionDistance.planeResidual
  apply congrArg sSup
  ext r
  constructor
  · rintro ⟨w, hwV, hw1, hwr⟩
    rcases (Submodule.mem_map.mp hwV) with ⟨v, hvV, hwval⟩
    subst w
    refine ⟨v, hvV, ?_, ?_⟩
    · exact (LinearIsometryEquiv.norm_map g v).symm.trans hw1
    · rw [Submodule.coe_orthogonalProjectionOnto_apply]
      rw [Submodule.coe_orthogonalProjectionOnto_apply] at hwr
      exact (residual_norm_map_map x g v).symm.trans hwr
  · rintro ⟨v, hvV, hv1, hvr⟩
    refine ⟨g v, ?_, ?_, ?_⟩
    · exact Submodule.mem_map.mpr ⟨v, hvV, rfl⟩
    · rw [LinearIsometryEquiv.norm_map g v]
      exact hv1
    · rw [Submodule.coe_orthogonalProjectionOnto_apply]
      rw [residual_norm_map_map x g v]
      rw [Submodule.coe_orthogonalProjectionOnto_apply] at hvr
      exact hvr


end Submission.Bridge.Isometry
