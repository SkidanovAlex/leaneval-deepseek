import Mathlib
import Submission.Work.Tubular.Rank
import Submission.Work.ThomBordism.PontryaginThom.FramesRange

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The tangent frame of an embedding, as a smooth family of linear maps

For an embedding `E : V ↪ ℝ^{8+k}` and a chart `i` of `V`, the **tangent frame** in `i` is the
derivative of the chart representative `E.e ∘ i.symm`:
`x ↦ fderiv ℝ (chartRep E.e i) (i x) : ℝ^8 →L ℝ^{8+k}`, a family of linear maps whose range is the
tangent space `T_x` of the image.  This file records:

* `Work.Tubular.contDiffOn_tangentFrame_coord` — in the chart's *coordinates*, the family `τ ↦ A_τ`
  of linear maps is `C^∞` (the derivative of a `C^∞` map is `C^∞`);
* `Work.Tubular.tangentFrame_range` — its range is the tangent space
  (via `Work.ThomBordism.PontryaginThom.range_coeffMap_frame_eq_mfderiv`, which is stated for the
  coordinate map `coeffMap` of the frame);
* `Work.Tubular.tangentFrame_adjoint_eq_zero_iff` — a vector of `ℝ^{8+k}` is annihilated by the
  adjoint of the tangent frame exactly when it is **normal** to `V` at `x`, i.e. lies in `ν_x`.

The last statement is the reason the tubular neighbourhood theorem can be proved *without ever
constructing an orthogonal projection*: the normal bundle over the chart is the kernel of the smooth
family of surjective maps `A_τ† : ℝ^{8+k} → ℝ^8`, and the "normal foot" of a nearby point `y` is the
solution of the equation `A_τ† (y - E.e (i.symm τ)) = 0`, to which the implicit function theorem
applies.  See `README.md` §5.
-/

open scoped Manifold ContDiff Topology InnerProduct
open Work.ThomBordism Work.ThomBordism.PontryaginThom Work.ThomBordism.Grassmann

namespace Work.Tubular

noncomputable section

variable {V : Man8} {k : ℕ}

/-- The **tangent frame of an embedding in a chart**, as a continuous linear map `ℝ^8 → ℝ^{8+k}`:
the derivative of the chart representative `E.e ∘ i.symm` at the chart coordinates of `x`. -/
def tangentFrame (E : EmbeddingData V (8 + k)) (i : atlas (Euc 8) V.pt) (x : V.pt) :
    Euc 8 →L[ℝ] Euc (8 + k) :=
  fderiv ℝ (chartRep E.e i) (i.1 x)

/-- The tangent frame is the derivative of the chart representative. -/
theorem tangentFrame_eq_fderiv (E : EmbeddingData V (8 + k)) (i : atlas (Euc 8) V.pt) (x : V.pt) :
    tangentFrame E i x = fderiv ℝ (chartRep E.e i) (i.1 x) := rfl

@[simp] theorem tangentFrame_apply (E : EmbeddingData V (8 + k)) (i : atlas (Euc 8) V.pt)
    (x : V.pt) (v : Euc 8) :
    tangentFrame E i x v = fderiv ℝ (chartRep E.e i) (i.1 x) v := rfl

/-- **The tangent frame is `C^∞` in the chart coordinates**: the chart representative is `C^∞` on the
chart's (open) target, and the derivative of a `C^∞` map is `C^∞`. -/
theorem contDiffOn_tangentFrame_coord (E : EmbeddingData V (8 + k))
    (i : atlas (Euc 8) V.pt) :
    ContDiffOn ℝ ∞ (fun τ : Euc 8 => fderiv ℝ (chartRep E.e i) τ) i.1.target := by
  have hmem : i.1 ∈ IsManifold.maximalAtlas (𝓡 8) ∞ V.pt :=
    IsManifold.subset_maximalAtlas (I := 𝓡 8) (n := ∞) i.2
  have hsymm : ContMDiffOn 𝓘(ℝ, Euc 8) (𝓡 8) ∞ (fun y => i.1.symm y) i.1.target :=
    contMDiffOn_symm_of_mem_maximalAtlas hmem
  have hcomp : ContMDiffOn 𝓘(ℝ, Euc 8) (𝓡 (8 + k)) ∞ (fun y => E.e (i.1.symm y)) i.1.target :=
    (E.smooth.contMDiffOn).comp hsymm (t := Set.univ) (fun y _ => Set.mem_univ (i.1.symm y))
  exact (hcomp.contDiffOn).fderiv_of_isOpen i.1.open_target (by simp)

/-- The range of a linear map `ℝ^n → F` is the span of its values on the standard basis. -/
theorem range_eq_span_single {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : Euc n →L[ℝ] F) :
    LinearMap.range A.toLinearMap =
      Submodule.span ℝ (Set.range fun j : Fin n => A (EuclideanSpace.single j 1)) := by
  refine le_antisymm ?_ (Submodule.span_le.mpr
    (Set.range_subset_iff.mpr fun j => ⟨EuclideanSpace.single j 1, rfl⟩))
  rintro v ⟨u, rfl⟩
  have hu : u = ∑ j : Fin n, (EuclideanSpace.basisFun (Fin n) ℝ).repr u j •
      EuclideanSpace.single j 1 := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr u]
    simp [EuclideanSpace.basisFun_apply]
  rw [hu, map_sum]
  simp only [map_smul]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self (f := fun j : Fin n =>
      A (EuclideanSpace.single j 1)) j))

/-- The range of the tangent frame is the span of the columns of the frame. -/
theorem range_tangentFrame_eq_span (E : EmbeddingData V (8 + k)) (i : atlas (Euc 8) V.pt)
    (x : V.pt) :
    LinearMap.range (tangentFrame E i x).toLinearMap =
      Submodule.span ℝ (Set.range (frame E.e i x)) := by
  rw [range_eq_span_single]
  rfl

/-- The range of `coeffMap` of a frame is the image of the span of the frame under the coordinate
identification `ℝ^n ≅ (Fin n → ℝ)`. -/
theorem range_coeffMap_eq_map_span {m : ℕ} (f : Fin 8 → Euc (8 + m)) :
    LinearMap.range (coeffMap f) =
      Submodule.map (eucToFun (8 + m)).toLinearMap (Submodule.span ℝ (Set.range f)) := by
  refine le_antisymm ?_ ?_
  · rintro w ⟨v, rfl⟩
    refine ⟨∑ j, v j • f j, Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self (f := f) j)), ?_⟩
    exact (coeffMap_eq_sum f v).symm
  · rintro w ⟨z, hz, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℝ)).mp
      (show z ∈ Submodule.span ℝ (Set.range f) from hz)
    exact ⟨c, (coeffMap_eq_sum f c).trans (by rw [hc]; rfl)⟩

/-- The coordinate form of the tangent space: the range of `coeffMap` of the frame of the chart is
the coordinate image of `T_x`. -/
theorem range_coeffMap_frame_eq_tangentSpace (E : EmbeddingData V (8 + k))
    (i : atlas (Euc 8) V.pt) {x : V.pt} (hx : x ∈ i.1.source) :
    LinearMap.range (coeffMap (frame E.e i x)) =
      Submodule.map (eucToFun (8 + k)).toLinearMap (tangentSpace E x) :=
  range_coeffMap_frame_eq_mfderiv E.e (E.smooth.of_le (by simp)) i hx

/-- Applying `funToEuc` to the coordinate image of a subspace of `ℝ^n` returns the subspace. -/
theorem map_funToEuc_map_eucToFun {n : ℕ} (S : Submodule ℝ (Euc n)) :
    Submodule.map (funToEuc n).toLinearMap (Submodule.map (eucToFun n).toLinearMap S) = S := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro x hx
    exact ⟨eucToFun n x, ⟨x, hx, rfl⟩, by simp⟩

/-- **The span of the columns of the frame is the tangent space.** -/
theorem frame_span_eq_tangentSpace (E : EmbeddingData V (8 + k)) (i : atlas (Euc 8) V.pt)
    {x : V.pt} (hx : x ∈ i.1.source) :
    (Submodule.span ℝ (Set.range (frame E.e i x)) : Submodule ℝ (Euc (8 + k))) =
      tangentSpace E x := by
  have h1 : Submodule.map (eucToFun (8 + k)).toLinearMap
      (Submodule.span ℝ (Set.range (frame E.e i x)))
      = Submodule.map (eucToFun (8 + k)).toLinearMap (tangentSpace E x) :=
    (range_coeffMap_eq_map_span (frame E.e i x)).symm.trans
      (range_coeffMap_frame_eq_tangentSpace E i hx)
  have h2 := congrArg (Submodule.map (funToEuc (8 + k)).toLinearMap) h1
  rwa [map_funToEuc_map_eucToFun, map_funToEuc_map_eucToFun] at h2

/-- **The range of the tangent frame is the tangent space of the image.** -/
theorem tangentFrame_range (E : EmbeddingData V (8 + k)) (i : atlas (Euc 8) V.pt) {x : V.pt}
    (hx : x ∈ i.1.source) :
    LinearMap.range (tangentFrame E i x).toLinearMap = tangentSpace E x := by
  rw [range_tangentFrame_eq_span, frame_span_eq_tangentSpace E i hx]

/-- The adjoint of a linear map vanishes on `w` exactly when `w` is orthogonal to its range. -/
theorem adjoint_eq_zero_iff_mem_orthogonal {m n : ℕ} (A : Euc m →L[ℝ] Euc n)
    (w : Euc n) : A.adjoint w = 0 ↔ w ∈ (LinearMap.range A.toLinearMap)ᗮ := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h u hu
    obtain ⟨v, rfl⟩ := hu
    exact (ContinuousLinearMap.adjoint_inner_right A v w).symm.trans
      (by rw [h, inner_zero_right])
  · intro h
    have h2 : inner ℝ (A.adjoint w) (A.adjoint w) = 0 := by
      rw [ContinuousLinearMap.adjoint_inner_right]
      exact h _ (LinearMap.mem_range.mpr ⟨A.adjoint w, rfl⟩)
    exact inner_self_eq_zero.mp h2

/-- **A vector is annihilated by the adjoint of the tangent frame exactly when it is normal**: the
kernel of `A_x†` is the fibre `ν_x` of the normal bundle. -/
theorem tangentFrame_adjoint_eq_zero_iff (E : EmbeddingData V (8 + k))
    (i : atlas (Euc 8) V.pt) {x : V.pt} (hx : x ∈ i.1.source) (w : Euc (8 + k)) :
    (tangentFrame E i x).adjoint w = 0 ↔ w ∈ normalSpace E x := by
  rw [adjoint_eq_zero_iff_mem_orthogonal, tangentFrame_range E i hx, normalSpace]

end

end Work.Tubular
