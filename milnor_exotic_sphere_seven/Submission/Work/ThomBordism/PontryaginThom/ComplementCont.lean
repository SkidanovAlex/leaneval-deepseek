import Submission.Work.ThomBordism.PontryaginThom.Complement
import Submission.Work.ThomBordism.PontryaginThom.ClmContinuity
import Submission.Work.ThomBordism.Grassmann.Coord

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The complement of an immersed plane: continuity

`Complement.lean` proves the pointwise linear algebra of the complement of an immersed rank-`8`
plane in `ℝ^{k+8}`: the projection `planeProj f S h` onto the complement of the plane spanned by
the frame `f`, the insertion `planeInj f S h` of that complement, and
`ker (planeProj f S h) = range (coeffMap f)`.

This file adds what the *bundle* construction needs:

* `sMonoEquiv_symm_eq` — the inverse of the `S`-coordinate projection of the frame is the
  matrix inverse: `(sMonoEquiv f S h).symm = Matrix.toLin' ((frameMatrix S f)⁻¹)`;
* `graphMap_eq`, `planeProj_eq` — the corresponding explicit formulas;
* `continuous_frameMatrix_family`, `continuous_frameMatrix_inv_family` — the frame matrix, and its
  inverse where `det ≠ 0`, depend continuously on a continuous family of frames;
* **`continuous_planeProj_family`** — `planeProj` too: for a continuous family
  `F : X → Fin 8 → ℝ^{k+8}` of frames with `(frameMatrix S (F x)).det ≠ 0` for all `x`, the
  transition functions `x ↦ planeProj (F x) S (h x)` form a continuous family of continuous linear
  maps `ℝ^{k+8} → ℝ^k`.  This is the input that the gluing data of the complement bundle consume
  (`continuousOn_coordChange`).
-/

open scoped Topology

namespace Work.ThomBordism.PontryaginThom

open Work.ThomBordism.Grassmann

noncomputable section

variable {k : ℕ}

/-- `Matrix.toLin'` is matrix-vector multiplication (in a form free of the `*ᵥ` notation, so that
it can be used by `rw`). -/
theorem toLin'_apply_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    Matrix.toLin' M v = M.mulVec v :=
  Matrix.toLin'_apply M v

/-- The `j`-th column of a matrix is the value of `mulVec` on the `j`-th basis vector. -/
theorem mulVec_single_one_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (j j' : Fin n) :
    M.mulVec (Pi.single j 1) j' = M j' j := by
  rw [show M.mulVec (Pi.single j 1) = M.col j from Matrix.mulVec_single_one M j,
    Matrix.col_apply]

/-- The defining formula of `sMono`, as an equality of linear maps (so that it can be rewritten
with). -/
theorem sMono_eq (f : Fin 8 → Amb (8 + k)) (S : ChartIdx 8 k) :
    sMono f S = (coordProj S).comp (coeffMap f) := rfl

/-- **The inverse of the `S`-coordinate projection of a frame is the inverse of its matrix**:
`sMonoEquiv f S h` is the linear equivalence `u ↦ (S-coordinates of the plane vector with
coordinates u)` and its inverse is multiplication by `(frameMatrix S f)⁻¹`. -/
theorem sMonoEquiv_symm_eq (f : Fin 8 → Amb (8 + k)) (S : ChartIdx 8 k)
    (h : (frameMatrix S f).det ≠ 0) :
    ((sMonoEquiv f S h).symm : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ))
      = Matrix.toLin' ((frameMatrix S f)⁻¹) := by
  have h2 : (sMono f S).comp ((sMonoEquiv f S h).symm : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ))
      = LinearMap.id := by
    apply LinearMap.ext
    intro u
    show (sMono f S) ((sMonoEquiv f S h).symm u) = u
    exact LinearEquiv.apply_symm_apply (sMonoEquiv f S h) u
  have h3 : (Matrix.toLin' ((frameMatrix S f)⁻¹)).comp (sMono f S) = LinearMap.id := by
    rw [sMono_eq, ← toLin'_frameMatrix, ← Matrix.toLin'_mul,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h), Matrix.toLin'_one]
  have hcalc : Matrix.toLin' ((frameMatrix S f)⁻¹)
      = ((sMonoEquiv f S h).symm : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ)) :=
    calc Matrix.toLin' ((frameMatrix S f)⁻¹)
        = (Matrix.toLin' ((frameMatrix S f)⁻¹)).comp LinearMap.id := (LinearMap.comp_id _).symm
      _ = (Matrix.toLin' ((frameMatrix S f)⁻¹)).comp
            ((sMono f S).comp ((sMonoEquiv f S h).symm : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ))) := by
          rw [h2]
      _ = ((Matrix.toLin' ((frameMatrix S f)⁻¹)).comp (sMono f S)).comp
            ((sMonoEquiv f S h).symm : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ)) := by
          rw [LinearMap.comp_assoc]
      _ = LinearMap.id.comp ((sMonoEquiv f S h).symm : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ)) := by
          rw [h3]
      _ = ((sMonoEquiv f S h).symm : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ)) := LinearMap.id_comp _
  exact hcalc.symm

/-- **The graph map is multiplication by the inverse matrix**: the plane vector with `S`-coordinates
`u` has `Sᶜ`-coordinates `complProj S (coeffMap f ((frameMatrix S f)⁻¹ *ᵥ u))`. -/
theorem graphMap_eq (f : Fin 8 → Amb (8 + k)) (S : ChartIdx 8 k)
    (h : (frameMatrix S f).det ≠ 0) :
    graphMap f S h
      = (complProj S).comp ((coeffMap f).comp (Matrix.toLin' ((frameMatrix S f)⁻¹))) := by
  rw [graphMap, sMonoEquiv_symm_eq]

/-- The pointwise computation rule of `planeProj` in terms of the inverse matrix. -/
theorem planeProj_eq (f : Fin 8 → Amb (8 + k)) (S : ChartIdx 8 k)
    (h : (frameMatrix S f).det ≠ 0) (y : Fin (8 + k) → ℝ) :
    planeProj f S h y
      = complProj S y
        - complProj S (coeffMap f ((frameMatrix S f)⁻¹.mulVec (coordProj S y))) := by
  rw [planeProj_apply, graphMap_eq, LinearMap.comp_apply, LinearMap.comp_apply,
    toLin'_apply_mulVec]

/-! ## Continuity in the frame -/

variable {X : Type*} [TopologicalSpace X]

/-- The `(i,j)`-entry of `M.mulVec v`, in a form free of the `*ᵥ` notation. -/
theorem mulVec_apply_sum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (i : Fin n) :
    M.mulVec v i = ∑ j, M i j * v j := rfl

/-- The frame matrix of a continuous family of frames is continuous. -/
theorem continuous_frameMatrix_family (F : X → Fin 8 → Amb (8 + k)) (hF : Continuous F)
    (S : ChartIdx 8 k) : Continuous (fun x => frameMatrix S (F x)) := by
  refine continuous_matrix fun i j => ?_
  exact (EuclideanSpace.proj (𝕜 := ℝ)
      (((S.1.equivFinOfCardEq S.2).symm i : ↥S.1) : Fin (8 + k))).continuous.comp
    ((continuous_apply j).comp hF)

/-- The inverse of the frame matrix of a continuous family of frames is continuous where the
determinant does not vanish. -/
theorem continuous_frameMatrix_inv_family (F : X → Fin 8 → Amb (8 + k)) (hF : Continuous F)
    (S : ChartIdx 8 k) (hd : ∀ x, (frameMatrix S (F x)).det ≠ 0) :
    Continuous (fun x => (frameMatrix S (F x))⁻¹) := by
  have h := (continuousOn_matrix_inv 8).comp
    ((continuous_frameMatrix_family F hF S).continuousOn (s := Set.univ))
    (fun x _ => hd x)
  rw [continuousOn_univ] at h
  simpa only [Function.comp_def] using h

/-- **The graph map of a continuous family of frames is continuous**, for each fixed vector of
`S`-coordinates `v`.  With `graphMap_eq` this is the continuity of
`x ↦ complProj S (coeffMap (F x) ((frameMatrix S (F x))⁻¹ *ᵥ v))`, i.e. of the "graph part" of
`planeProj`; `graphMap` appears as the second summand of `planeProj` in the form
`planeProj = complProj - graphMap ∘ coordProj`. -/
theorem continuous_graphMap_family (F : X → Fin 8 → Amb (8 + k)) (hF : Continuous F)
    (S : ChartIdx 8 k) (hd : ∀ x, (frameMatrix S (F x)).det ≠ 0) (v : Fin 8 → ℝ) :
    Continuous (fun x => graphMap (F x) S (hd x) v) := by
  rw [continuous_pi_iff]
  intro i
  have hfun : (fun x => graphMap (F x) S (hd x) v i) = fun x =>
      ∑ j' : Fin 8, (∑ i' : Fin 8, ((frameMatrix S (F x))⁻¹) j' i' * v i')
        * EuclideanSpace.proj (𝕜 := ℝ)
            (((S.1ᶜ.equivFinOfCardEq (chartIdx_compl_card S)).symm i : ↥S.1ᶜ) :
              Fin (8 + k)) (F x j') := by
    funext x
    rw [graphMap_eq, LinearMap.comp_apply, LinearMap.comp_apply, complProj_apply,
      toLin'_apply_mulVec, coeffMap_apply]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [mulVec_apply_sum]
  rw [hfun]
  refine continuous_finsetSum _ fun j' _ => ?_
  refine Continuous.mul ?_ ?_
  · refine continuous_finsetSum _ fun i' _ => ?_
    exact ((continuous_apply_apply j' i').comp
      (continuous_frameMatrix_inv_family F hF S hd)).mul continuous_const
  · exact (EuclideanSpace.proj (𝕜 := ℝ)
      (((S.1ᶜ.equivFinOfCardEq (chartIdx_compl_card S)).symm i : ↥S.1ᶜ) :
        Fin (8 + k))).continuous.comp ((continuous_apply j').comp hF)

/-- **`planeProj` depends continuously on a continuous family of frames** (with the chart index `S`
fixed and `(frameMatrix S (F x)).det ≠ 0` for all `x`).  This is the pointwise form of the
continuity of the transition functions of the complement bundle. -/
theorem continuous_planeProj_family (F : X → Fin 8 → Amb (8 + k)) (hF : Continuous F)
    (S : ChartIdx 8 k) (hd : ∀ x, (frameMatrix S (F x)).det ≠ 0) :
    Continuous (fun x => LinearMap.toContinuousLinearMap (planeProj (F x) S (hd x))) := by
  rw [continuous_toContinuousLinearMap_iff]
  intro j
  have hval : (fun x => planeProj (F x) S (hd x) (Pi.single j 1))
      = fun x => complProj S (Pi.single j 1)
          - graphMap (F x) S (hd x) (coordProj S (Pi.single j 1)) := by
    funext x
    rw [planeProj_apply]
  rw [hval]
  exact continuous_const.sub (continuous_graphMap_family F hF S hd (coordProj S (Pi.single j 1)))

end

end Work.ThomBordism.PontryaginThom
