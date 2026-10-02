import Mathlib
import Submission.Work.ThomBordism.nwtDefs
import Submission.Work.Tubular.NormalFrame

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-!
# The kernel of the coordinate projection of the normal bundle

`Work.ThomBordism.complP E ND i x` is the *reading* of the ambient coordinates in an orthonormal
frame of the normal space `ν_x` (the normal space of the embedding `E.e` at `x`), transported to the
coordinate spaces `Fin (8 + k) → ℝ` and `Fin k → ℝ`.  Its kernel is the family of ambient coordinate
vectors that are tangent to the image of the embedding — i.e. the plane spanned by the frame
`frame E.e (coverChart i) x` of the derivative of the embedding.

This is the `ker_eq_range` hypothesis of `Work.ThomBordism.PontryaginThom.SplittingData` in the
form in which the reading map (rather than the coordinate projection `planeProj`) is used; the
mathematical content is that

* the reading map vanishes exactly on the orthogonal complement of the span of the orthonormal
  normal frame (`Work.Tubular.readCLM_apply`, `Work.Tubular.span_orthFrame`), and
* the orthogonal complement of the normal space is the tangent space
  (`Work.Tubular.tangentSpace_sup_normalSpace`, `Work.Tubular.tangentSpace_inf_normalSpace`),

while the coordinates of the tangent space are the range of `coeffMap` of the frame
(`Work.Tubular.range_coeffMap_frame_eq_tangentSpace`).
-/

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom Work.TangentClasses Work.Thom
open Work.ThomBordism.Grassmann

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- `eucToFun` is zero exactly at zero. -/
theorem eucToFun_eq_zero_iff {n : ℕ} (y : Euc n) : eucToFun n y = 0 ↔ y = 0 := by
  constructor
  · intro h
    have h1 := congrArg (funToEuc n) h
    rw [funToEuc_eucToFun] at h1
    simpa using h1
  · rintro rfl
    exact map_zero _

/-- `funToEuc` is zero exactly at zero. -/
theorem funToEuc_eq_zero_iff {n : ℕ} (y : Fin n → ℝ) : funToEuc n y = 0 ↔ y = 0 := by
  constructor
  · intro h
    have h1 := congrArg (eucToFun n) h
    rw [eucToFun_funToEuc] at h1
    simpa using h1
  · rintro rfl
    exact map_zero _

/-- **The reading map of the normal bundle vanishes exactly on the tangent space**: the coordinates
of a vector in the orthonormal frame of the normal plane `ν_x` are all zero if and only if the
vector is tangent to the image of the embedding (i.e. orthogonal to `ν_x`). -/
theorem readCLM_eq_zero_iff (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) (w : Euc (8 + k)) :
    Work.Tubular.readCLM E ND i x w = 0 ↔ w ∈ Work.Tubular.tangentSpace E x := by
  constructor
  · intro h
    -- all the inner products with the orthonormal normal frame vanish
    have hinner : ∀ j : Fin k, inner ℝ (Work.Tubular.orthFrame E ND i x j) w = 0 := by
      intro j
      have h1 := congrArg (fun v : Euc k => eucToFun k v j) h
      simp only [Work.Tubular.readCLM_apply, eucToFun_funToEuc, map_zero, Pi.zero_apply] at h1
      exact h1
    -- hence `w` is orthogonal to the normal space
    have horth : w ∈ (Work.Tubular.normalSpace E x)ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro z hz
      rw [← Work.Tubular.span_orthFrame E ND i hx] at hz
      refine Submodule.span_induction (p := fun z _ => inner ℝ z w = 0) ?_ ?_ ?_ ?_ hz
      · rintro y ⟨j, rfl⟩
        exact hinner j
      · simp
      · intro a b _ _ ha hb
        rw [inner_add_left, ha, hb, add_zero]
      · intro c a _ ha
        rw [inner_smul_left, ha, mul_zero]
    -- and the orthogonal of the normal space is the tangent space
    rw [Work.Tubular.normalSpace] at horth
    rwa [Submodule.orthogonal_orthogonal] at horth
  · intro hw
    rw [Work.Tubular.readCLM_apply]
    refine (funToEuc_eq_zero_iff _).mpr ?_
    funext j
    exact Work.Tubular.inner_eq_zero_of_mem_tangentSpace hw (Work.Tubular.orthFrame_mem E ND i hx j)

theorem nwtKerComplP {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (i : Work.ThomBordism.PontryaginThom.CoverIdx V k) {x : V.pt}
    (hx : x ∈ ND.D.baseSet i) :
    LinearMap.ker ((Work.ThomBordism.complP E ND i x : (Fin (8 + k) → ℝ) →L[ℝ] (Fin k → ℝ)) :
        (Fin (8 + k) → ℝ) →ₗ[ℝ] (Fin k → ℝ))
      = LinearMap.range (Work.ThomBordism.Grassmann.coeffMap
          (Work.ThomBordism.PontryaginThom.frame E.e
            (Work.ThomBordism.PontryaginThom.coverChart i) x)) := by
  have hsrc : x ∈ (coverChart i).1.source := ND.baseSet_sub i.1 i.2 x hx
  have hmap := Work.Tubular.range_coeffMap_frame_eq_tangentSpace E (coverChart i) hsrc
  have key : ∀ u : Fin (8 + k) → ℝ,
      complP E ND i x u = 0 ↔ u ∈ LinearMap.range
        (coeffMap (frame E.e (coverChart i) x)) := by
    intro u
    rw [complP_apply_of_mem E ND i hx, hmap]
    constructor
    · intro hu
      refine ⟨funToEuc (8 + k) u, ?_, eucToFun_funToEuc (8 + k) u⟩
      exact (readCLM_eq_zero_iff E ND i hx _).mp ((eucToFun_eq_zero_iff (n := k) _).mp hu)
    · rintro ⟨w, hw, hwu⟩
      have hw' : funToEuc (8 + k) u = w := by rw [← hwu]; exact funToEuc_eucToFun (8 + k) w
      rw [hw', (readCLM_eq_zero_iff E ND i hx w).mpr hw]
      exact map_zero _
  refine le_antisymm ?_ ?_
  · intro u hu
    rw [LinearMap.mem_ker] at hu
    exact (key u).mp hu
  · intro u hu
    rw [LinearMap.mem_ker]
    exact (key u).mpr hu

end

end Work.ThomBordism
