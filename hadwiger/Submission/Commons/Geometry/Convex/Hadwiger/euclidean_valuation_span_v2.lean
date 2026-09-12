import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.simple_rigid_invariant_eq_const_volume
import Submission.Commons.Geometry.Convex.Hadwiger.polytope_dense
import Submission.Commons.Geometry.Convex.Hadwiger.polytope_parallel_body_polynomial_fullDim
import Submission.Commons.Geometry.Convex.Hadwiger.exists_fullDim_polytope_close
import Submission.Commons.Geometry.Convex.Hadwiger.continuous_parallel_body_volume
import Submission.Commons.Geometry.Convex.Hadwiger.convexBody_add_smul_unitBall_eq
import Submission.Commons.Analysis.InnerProductSpace.fin_split_coord_isometry
import Submission.Commons.Geometry.Convex.Hadwiger.slice_moment
import Submission.Commons.Geometry.Convex.Hadwiger.exists_isometry_add_subset_hyperplane
import Submission.Commons.Geometry.Convex.Hadwiger.parallel_body_lift_slice

open scoped Classical Pointwise BigOperators Topology
open Metric MeasureTheory Set Filter

namespace Commons.Geometry.Convex.Hadwiger

namespace EucV2

noncomputable section

/-! ## Standard bodies and the coordinate splitting

We fix the convention that the *transverse* coordinate of `EuclideanSpace ℝ (Fin (m+1))` is
coordinate `0`: a body `K ⊆ E m` is lifted to `liftFun x = (0, x)` (coordinate `0` receives `0`,
the remaining coordinates are those of `x`). -/

/-- The unit ball of `EuclideanSpace ℝ (Fin m)` as a convex body. -/
abbrev uball (m : ℕ) : ConvexBody (EuclideanSpace ℝ (Fin m)) :=
  ⟨Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1, convex_closedBall (0 : _) 1,
    isCompact_closedBall (0 : _) 1, Metric.nonempty_closedBall.mpr zero_le_one⟩

@[simp] lemma uball_coe (m : ℕ) :
    ((uball m : ConvexBody (EuclideanSpace ℝ (Fin m))) : Set (EuclideanSpace ℝ (Fin m))) =
      Metric.closedBall (0 : _) 1 := rfl

/-- The lift `E m → E (m+1)`: coordinate `0` receives `0`, the other coordinates are shifted. -/
def liftFun (m : ℕ) (x : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin (m+1)) :=
  WithLp.toLp 2 (Fin.cases 0 (fun i : Fin m => x i))

/-- The projection `E (m+1) → E m` dropping coordinate `0`. -/
def dropFun (m : ℕ) (y : EuclideanSpace ℝ (Fin (m+1))) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i : Fin m => y i.succ)

/-- The coordinate-splitting map `E (m+1) → WithLp 2 (ℝ × E m)`. -/
def fwdW (m : ℕ) (x : EuclideanSpace ℝ (Fin (m+1))) :
    WithLp 2 (ℝ × EuclideanSpace ℝ (Fin m)) :=
  WithLp.toLp 2 (x 0, dropFun m x)

/-- The inverse coordinate-splitting map. -/
def bwdW (m : ℕ) (p : WithLp 2 (ℝ × EuclideanSpace ℝ (Fin m))) :
    EuclideanSpace ℝ (Fin (m+1)) :=
  WithLp.toLp 2 (Fin.cases p.ofLp.1 (fun i : Fin m => p.ofLp.2 i))

@[simp] lemma fwdW_ofLp (m : ℕ) (x : EuclideanSpace ℝ (Fin (m+1))) :
    (fwdW m x).ofLp = (x 0, dropFun m x) := rfl

@[simp] lemma dropFun_apply_succ (m : ℕ) (y : EuclideanSpace ℝ (Fin (m+1))) (i : Fin m) :
    dropFun m y i = y i.succ := rfl

lemma dropFun_liftFun (m : ℕ) (x : EuclideanSpace ℝ (Fin m)) :
    dropFun m (liftFun m x) = x := by
  apply WithLp.ofLp_injective 2
  funext i
  simp [dropFun, liftFun]

lemma fwdW_liftFun (m : ℕ) (x : EuclideanSpace ℝ (Fin m)) :
    fwdW m (liftFun m x) = WithLp.toLp 2 ((0 : ℝ), x) := by
  rw [fwdW, dropFun_liftFun]
  congr 1

lemma bwdW_fwdW (m : ℕ) (x : EuclideanSpace ℝ (Fin (m+1))) : bwdW m (fwdW m x) = x := by
  apply WithLp.ofLp_injective 2
  ext i
  refine Fin.cases ?_ ?_ i
  · simp [bwdW]
  · intro j
    simp [bwdW]

lemma fwdW_bwdW (m : ℕ) (p : WithLp 2 (ℝ × EuclideanSpace ℝ (Fin m))) :
    fwdW m (bwdW m p) = p := by
  apply WithLp.ofLp_injective 2
  ext i <;> simp [bwdW, fwdW, dropFun]

/-- The splitting map as a linear map. -/
def fwdLM (m : ℕ) :
    EuclideanSpace ℝ (Fin (m+1)) →ₗ[ℝ] WithLp 2 (ℝ × EuclideanSpace ℝ (Fin m)) where
  toFun := fwdW m
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    ext i <;> simp [fwdW, dropFun]
  map_smul' c x := by
    apply WithLp.ofLp_injective 2
    ext i <;> simp [fwdW, dropFun]

/-- The inverse splitting map as a linear map. -/
def bwdLM (m : ℕ) :
    WithLp 2 (ℝ × EuclideanSpace ℝ (Fin m)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m+1)) where
  toFun := bwdW m
  map_add' p q := by
    apply WithLp.ofLp_injective 2
    ext i
    refine Fin.cases ?_ ?_ i <;> simp [bwdW]
  map_smul' c p := by
    apply WithLp.ofLp_injective 2
    ext i
    refine Fin.cases ?_ ?_ i <;> simp [bwdW]

lemma fwdW_norm (m : ℕ) (x : EuclideanSpace ℝ (Fin (m+1))) : ‖fwdW m x‖ = ‖x‖ := by
  have h2 : ‖fwdW m x‖ ^ 2 = (‖x 0‖ ^ 2 + ∑ i : Fin m, ‖x i.succ‖ ^ 2) := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, fwdW]
    rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin m => ℝ) (dropFun m x)]
    simp [dropFun]
  have h3 : ‖x‖ ^ 2 = (‖x 0‖ ^ 2 + ∑ i : Fin m, ‖x i.succ‖ ^ 2) := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]
  nlinarith [norm_nonneg (fwdW m x), norm_nonneg x]

lemma liftFun_norm (m : ℕ) (x : EuclideanSpace ℝ (Fin m)) : ‖liftFun m x‖ = ‖x‖ := by
  have h2 : ‖liftFun m x‖ ^ 2 = (∑ i : Fin m, ‖x i‖ ^ 2) := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]
    simp [liftFun]
  have h3 : ‖x‖ ^ 2 = (∑ i : Fin m, ‖x i‖ ^ 2) := PiLp.norm_sq_eq_of_L2 _ x
  nlinarith [norm_nonneg (liftFun m x), norm_nonneg x]

/-- The coordinate splitting `E (m+1) ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E m)`. -/
def splitIso (m : ℕ) :
    EuclideanSpace ℝ (Fin (m+1)) ≃ₗᵢ[ℝ] WithLp 2 (ℝ × EuclideanSpace ℝ (Fin m)) where
  toLinearEquiv :=
    LinearEquiv.ofLinearMap (fwdLM m) (bwdLM m)
      (by
        apply LinearMap.ext
        intro p
        exact fwdW_bwdW m p)
      (by
        apply LinearMap.ext
        intro x
        exact bwdW_fwdW m x)
  norm_map' := fun x => fwdW_norm m x

@[simp] lemma splitIso_apply (m : ℕ) (x : EuclideanSpace ℝ (Fin (m+1))) :
    splitIso m x = fwdW m x := rfl

lemma splitIso_liftFun (m : ℕ) (x : EuclideanSpace ℝ (Fin m)) :
    splitIso m (liftFun m x) = WithLp.toLp 2 ((0 : ℝ), x) := by
  rw [splitIso_apply, fwdW_liftFun]

lemma splitIso_symm (m : ℕ) (p : WithLp 2 (ℝ × EuclideanSpace ℝ (Fin m))) :
    (splitIso m).symm p = bwdW m p := by
  calc (splitIso m).symm p = (splitIso m).symm (splitIso m (bwdW m p)) := by
        rw [splitIso_apply, fwdW_bwdW]
    _ = bwdW m p := (splitIso m).symm_apply_apply (bwdW m p)

lemma splitIso_symm_toLp (m : ℕ) (s : ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    (splitIso m).symm (WithLp.toLp 2 (s, x)) = WithLp.toLp 2 (Fin.cases s (fun i : Fin m => x i)) := by
  rw [splitIso_symm]
  rfl

/-- The lift `E m → E (m+1)` as a linear map. -/
def liftLM (m : ℕ) : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m+1)) where
  toFun := liftFun m
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    ext i
    refine Fin.cases ?_ ?_ i <;> simp [liftFun]
  map_smul' c x := by
    apply WithLp.ofLp_injective 2
    ext i
    refine Fin.cases ?_ ?_ i <;> simp [liftFun]

/-- The lift `E m → E (m+1)` as a linear isometry. -/
def liftLI (m : ℕ) : EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m+1)) where
  toLinearMap := liftLM m
  norm_map' := liftFun_norm m

/-- The projection `E (m+1) → E m` as a linear map. -/
def dropLM (m : ℕ) : EuclideanSpace ℝ (Fin (m+1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) where
  toFun := dropFun m
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    ext i
    simp [dropFun]
  map_smul' c x := by
    apply WithLp.ofLp_injective 2
    ext i
    simp [dropFun]

/-- The lift of a convex body into `E (m+1)`. -/
@[simp] lemma liftLM_apply (m : ℕ) (x : EuclideanSpace ℝ (Fin m)) :
    liftLM m x = liftFun m x := rfl

@[simp] lemma liftLI_apply (m : ℕ) (x : EuclideanSpace ℝ (Fin m)) :
    liftLI m x = liftFun m x := rfl

@[simp] lemma dropLM_apply (m : ℕ) (x : EuclideanSpace ℝ (Fin (m+1))) :
    dropLM m x = dropFun m x := rfl

def liftCB (m : ℕ) (K : ConvexBody (EuclideanSpace ℝ (Fin m))) :
    ConvexBody (EuclideanSpace ℝ (Fin (m+1))) :=
  ⟨(liftLI m) '' (K : Set _),
    K.convex.linear_image (liftLI m).toLinearMap,
    K.isCompact.image (liftLI m).continuous,
    K.nonempty.image (liftLI m)⟩

lemma liftLM_image (m : ℕ) (s : Set (EuclideanSpace ℝ (Fin m))) :
    (liftLM m) '' s = liftFun m '' s :=
  Set.image_congr (fun x _ => liftLM_apply m x)

lemma dropLM_image (m : ℕ) (s : Set (EuclideanSpace ℝ (Fin (m+1)))) :
    (dropLM m) '' s = dropFun m '' s :=
  Set.image_congr (fun x _ => dropLM_apply m x)

@[simp] lemma liftCB_coe (m : ℕ) (K : ConvexBody (EuclideanSpace ℝ (Fin m))) :
    ((liftCB m K : ConvexBody (EuclideanSpace ℝ (Fin (m+1)))) : Set _) =
      (liftLM m) '' (K : Set _) := rfl

lemma liftCB_coe' (m : ℕ) (K : ConvexBody (EuclideanSpace ℝ (Fin m))) :
    ((liftCB m K : ConvexBody (EuclideanSpace ℝ (Fin (m+1)))) : Set _) =
      liftFun m '' (K : Set _) := by
  rw [liftCB_coe, liftLM_image]

/-- The projection of a convex body lying in the hyperplane `{y | y 0 = 0}`. -/
def dropCB (m : ℕ) (L : ConvexBody (EuclideanSpace ℝ (Fin (m+1))))
    (hL : ∀ y ∈ (L : Set (EuclideanSpace ℝ (Fin (m+1)))), y 0 = 0) :
    ConvexBody (EuclideanSpace ℝ (Fin m)) :=
  ⟨(dropLM m) '' (L : Set _),
    L.convex.linear_image (dropLM m),
    L.isCompact.image (dropLM m).continuous_of_finiteDimensional,
    L.nonempty.image (dropLM m)⟩

@[simp] lemma dropCB_coe (m : ℕ) (L : ConvexBody (EuclideanSpace ℝ (Fin (m+1))))
    (hL : ∀ y ∈ (L : Set (EuclideanSpace ℝ (Fin (m+1)))), y 0 = 0) :
    ((dropCB m L hL : ConvexBody (EuclideanSpace ℝ (Fin m))) : Set _) =
      (dropLM m) '' (L : Set _) := rfl

lemma dropCB_coe' (m : ℕ) (L : ConvexBody (EuclideanSpace ℝ (Fin (m+1))))
    (hL : ∀ y ∈ (L : Set (EuclideanSpace ℝ (Fin (m+1)))), y 0 = 0) :
    ((dropCB m L hL : ConvexBody (EuclideanSpace ℝ (Fin m))) : Set _) =
      dropFun m '' (L : Set _) := by
  rw [dropCB_coe, dropLM_image]


/-! ## The lift and the hyperplane -/

lemma liftFun_dropFun_of_mem {m : ℕ} {L : ConvexBody (EuclideanSpace ℝ (Fin (m+1)))}
    (hL : ∀ y ∈ (L : Set (EuclideanSpace ℝ (Fin (m+1)))), y 0 = 0)
    {y : EuclideanSpace ℝ (Fin (m+1))} (hy : y ∈ (L : Set _)) :
    liftFun m (dropFun m y) = y := by
  apply WithLp.ofLp_injective 2
  ext i
  refine Fin.cases ?_ ?_ i
  · simp only [liftFun, WithLp.ofLp_toLp]
    exact (hL y hy).symm
  · intro j
    simp only [liftFun, dropFun, WithLp.ofLp_toLp]
    exact Fin.cases_succ j

/-- A convex body contained in the hyperplane `{y | y 0 = 0}` is the lift of its projection. -/
lemma liftCB_dropCB {m : ℕ} (L : ConvexBody (EuclideanSpace ℝ (Fin (m+1))))
    (hL : ∀ y ∈ (L : Set (EuclideanSpace ℝ (Fin (m+1)))), y 0 = 0) :
    liftCB m (dropCB m L hL) = L := by
  apply ConvexBody.ext
  ext y
  constructor
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    simp only [liftLI_apply, dropLM_apply]
    rw [liftFun_dropFun_of_mem hL hw]
    exact hw
  · intro hy
    exact ⟨dropFun m y, ⟨y, hy, rfl⟩, liftFun_dropFun_of_mem hL hy⟩

/-- In the splitting coordinates an isometry `e` of `E m` acts as `(id, e)`. -/
def blockIso (m : ℕ) (e : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin (m+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m+1)) :=
  (splitIso m).trans
    ((Commons.Analysis.InnerProductSpace.withLpProdCongr (LinearIsometryEquiv.refl ℝ ℝ) e).trans
      (splitIso m).symm)

lemma blockIso_liftFun (m : ℕ) (e : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin m)) : blockIso m e (liftFun m x) = liftFun m (e x) := by
  simp only [blockIso, LinearIsometryEquiv.trans_apply, splitIso_apply, fwdW_liftFun,
    Commons.Analysis.InnerProductSpace.withLpProdCongr_apply, splitIso_symm_toLp]
  apply WithLp.ofLp_injective 2
  ext i
  refine Fin.cases ?_ ?_ i <;> simp [liftFun]

lemma blockIso_coord (m : ℕ) (e : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m))
    (y : EuclideanSpace ℝ (Fin (m+1))) : blockIso m e y 0 = y 0 := by
  have h : blockIso m e y =
      (splitIso m).symm (Commons.Analysis.InnerProductSpace.withLpProdCongr (LinearIsometryEquiv.refl ℝ ℝ) e
        (splitIso m y)) := rfl
  rw [h]
  have h3 : Commons.Analysis.InnerProductSpace.withLpProdCongr (LinearIsometryEquiv.refl ℝ ℝ) e
      (splitIso m y) = WithLp.toLp 2
        ((splitIso m y).ofLp.1, e ((splitIso m y).ofLp.2)) := by
    rw [Commons.Analysis.InnerProductSpace.withLpProdCongr_apply]
    rfl
  rw [h3, splitIso_symm_toLp]
  simp [splitIso_apply, fwdW]

lemma dist_liftCB (m : ℕ) (A B : ConvexBody (EuclideanSpace ℝ (Fin m))) :
    dist (liftCB m A) (liftCB m B) = dist A B := by
  rw [← ConvexBody.hausdorffDist_coe, ← ConvexBody.hausdorffDist_coe, liftCB_coe, liftCB_coe]
  exact Metric.hausdorffDist_image (liftLI m).isometry

lemma continuous_liftCB (m : ℕ) : Continuous (liftCB m) := by
  rw [Metric.continuous_iff]
  intro A ε hε
  exact ⟨ε, hε, fun B hB => by rw [dist_liftCB]; exact hB⟩

lemma liftFun_add (m : ℕ) (x y : EuclideanSpace ℝ (Fin m)) :
    liftFun m (x + y) = liftFun m x + liftFun m y := by
  rw [← liftLM_apply m (x + y), ← liftLM_apply m x, ← liftLM_apply m y, map_add]

lemma liftFun_image_union (m : ℕ) (s t : Set (EuclideanSpace ℝ (Fin m))) :
    liftFun m '' (s ∪ t) = liftFun m '' s ∪ liftFun m '' t :=
  Set.image_union (liftFun m) s t

lemma liftFun_injective (m : ℕ) : Function.Injective (liftFun m) :=
  fun x y h => dropFun_liftFun m x ▸ dropFun_liftFun m y ▸ congrArg (dropFun m) h

lemma liftFun_image_inter (m : ℕ) (s t : Set (EuclideanSpace ℝ (Fin m))) :
    liftFun m '' (s ∩ t) = liftFun m '' s ∩ liftFun m '' t :=
  Set.image_inter (f := liftFun m) (liftFun_injective m)

lemma liftFun_image_translate (m : ℕ) (t : EuclideanSpace ℝ (Fin m)) (s : Set (EuclideanSpace ℝ (Fin m))) :
    liftFun m '' ((fun x => x + t) '' s) = (fun y => y + liftFun m t) '' (liftFun m '' s) := by
  rw [Set.image_image, Set.image_image]
  apply Set.image_congr
  intro x hx
  exact liftFun_add m x t

/-! ## Steiner's formula: the parallel-body volume is a polynomial

This is a re-development (avoiding the name clash with the `E` abbreviation of
`Submission.Commons.Geometry.Convex.Hadwiger.zonoidLimit_of_continuous_even_nonneg`) of
`Commons.Geometry.Convex.Hadwiger.steiner_parallel_body_polynomial`: for every convex body `K`
in `EuclideanSpace ℝ (Fin m)` the function `t ↦ vol (K + t • B)`, `t ≥ 0`, is the restriction of
a polynomial of degree at most `m`.  The assembly uses the full-dimensional polytope case
(`polytope_parallel_body_polynomial_fullDim`), the density of full-dimensional polytopes
(`exists_fullDim_polytope_close`) and joint continuity of `(K, t) ↦ vol (K + tB)`. -/

/-- The parallel-body volume `vol (K + t • B)`. -/
def volval (m : ℕ) (K : ConvexBody (EuclideanSpace ℝ (Fin m))) (t : ℝ) : ℝ :=
  (volume ((K + t • uball m : ConvexBody (EuclideanSpace ℝ (Fin m))) :
    Set (EuclideanSpace ℝ (Fin m)))).toReal

lemma continuous_volval_inK (m : ℕ) (t : ℝ) :
    Continuous (fun K : ConvexBody (EuclideanSpace ℝ (Fin m)) => volval m K t) :=
  Commons.Geometry.Convex.Hadwiger.continuous_parallel_body_volume m (t • uball m)

namespace SteinerInterp

/-- Interpolation nodes `{0, …, m}`. -/
def nodes (m : ℕ) : Finset ℕ := Finset.range (m + 1)
/-- The node values `0, …, m`. -/
def vv : ℕ → ℝ := fun i => (i : ℝ)

lemma hv_inj (m : ℕ) : Set.InjOn (vv) ((nodes m : Finset ℕ) : Set ℕ) := by
  intro i hi j hj hij
  dsimp [vv] at hij
  exact_mod_cast hij

lemma eval_interpolate {m : ℕ} (r : ℕ → ℝ) (x : ℝ) :
    (Lagrange.interpolate (nodes m) vv r).eval x
      = ∑ i ∈ nodes m, r i * (Lagrange.basis (nodes m) vv i).eval x := by
  rw [Lagrange.interpolate_apply]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]

lemma interp_eq_of_degree_le {m : ℕ} (f : Polynomial ℝ) (r : ℕ → ℝ)
    (hdeg : f.degree < ((nodes m).card : WithBot ℕ))
    (hvals : ∀ i ∈ nodes m, f.eval (vv i) = r i) :
    f = Lagrange.interpolate (nodes m) vv r :=
  Lagrange.eq_interpolate_of_eval_eq (s := nodes m) (v := vv) (r := r) (f := f) (hv_inj m) hdeg hvals

end SteinerInterp

/-- If a sequence of convex bodies `Pn → P` has each parallel-body volume function
`t ↦ vol (Pn n + tB)`, `t ≥ 0`, polynomial of degree ≤ m, then so does the one for `P`. -/
lemma limit_lift_polynomial (m : ℕ) (P : ConvexBody (EuclideanSpace ℝ (Fin m)))
    (Pn : ℕ → ConvexBody (EuclideanSpace ℝ (Fin m))) (hP : Tendsto Pn atTop (nhds P))
    (hpoly : ∀ n : ℕ, ∃ p : Polynomial ℝ, p.natDegree ≤ m ∧
       ∀ t : ℝ, 0 ≤ t → volval m (Pn n) t = p.eval t) :
    ∃ p : Polynomial ℝ, p.natDegree ≤ m ∧
       ∀ t : ℝ, 0 ≤ t → volval m P t = p.eval t := by
  classical
  choose pn hdeg_n heval_n using hpoly
  let s : Finset ℕ := SteinerInterp.nodes m
  let v : ℕ → ℝ := SteinerInterp.vv
  have hs_card : s.card = m + 1 := by simp [s, SteinerInterp.nodes]
  let p : Polynomial ℝ := Lagrange.interpolate s v (fun i => volval m P (i : ℝ))
  refine ⟨p, ?deg, ?val⟩
  · have hdegP : p.degree < (s.card : WithBot ℕ) :=
      Lagrange.degree_interpolate_lt (s := s) (v := v)
        (hvs := by simpa [s, v] using SteinerInterp.hv_inj m) (r := fun i => volval m P (i : ℝ))
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    apply Polynomial.coeff_eq_zero_of_degree_lt
    have hcard : (s.card : WithBot ℕ) = ((m + 1 : ℕ) : WithBot ℕ) := by rw [hs_card]
    have hNge : (m + 1 : WithBot ℕ) ≤ (N : WithBot ℕ) := by
      exact_mod_cast Nat.succ_le_of_lt hN
    exact lt_of_lt_of_le (by simpa [hcard] using hdegP) hNge
  · intro t ht
    have hpn_eq_interp : ∀ n : ℕ,
        pn n = Lagrange.interpolate s v (fun i => volval m (Pn n) (i : ℝ)) := by
      intro n
      refine SteinerInterp.interp_eq_of_degree_le (m := m) (f := pn n) (r := fun i => volval m (Pn n) (i : ℝ)) ?_ ?_
      · have hdegn : (pn n).natDegree ≤ m := hdeg_n n
        have hdeg' : (pn n).degree ≤ (m : WithBot ℕ) :=
          le_trans (Polynomial.degree_le_natDegree) (by exact_mod_cast hdegn)
        have hdeg_lt : (pn n).degree < ((m + 1 : ℕ) : WithBot ℕ) :=
          lt_of_le_of_lt hdeg' (by exact_mod_cast (Nat.lt_succ_self m))
        simpa [s, hs_card, v, SteinerInterp.nodes] using hdeg_lt
      · intro i hi
        have hni0 : 0 ≤ (i : ℝ) := by exact_mod_cast (Nat.zero_le i)
        exact (heval_n n (i : ℝ) hni0).symm
    have hval_sum : ∀ n : ℕ,
        volval m (Pn n) t =
          ∑ i ∈ s, volval m (Pn n) (i : ℝ) * (Lagrange.basis s v i).eval t := by
      intro n
      calc
        volval m (Pn n) t = (pn n).eval t := heval_n n t ht
        _ = (Lagrange.interpolate s v (fun i => volval m (Pn n) (i : ℝ))).eval t := by
          rw [hpn_eq_interp n]
        _ = ∑ i ∈ s, volval m (Pn n) (i : ℝ) * (Lagrange.basis s v i).eval t := by
          simpa [v, s, SteinerInterp.nodes] using
            SteinerInterp.eval_interpolate (m := m) (r := fun i => volval m (Pn n) (i : ℝ)) t
    have hleft : Tendsto (fun n : ℕ => volval m (Pn n) t) atTop (𝓝 (volval m P t)) :=
      (continuous_volval_inK m t).tendsto P |>.comp hP
    have hsum_lim : Tendsto
        (fun n : ℕ => ∑ i ∈ s, volval m (Pn n) (i : ℝ) * (Lagrange.basis s v i).eval t)
        atTop (𝓝 (∑ i ∈ s, volval m P (i : ℝ) * (Lagrange.basis s v i).eval t)) := by
      have hterm : ∀ i ∈ s, Tendsto
          (fun n : ℕ => volval m (Pn n) (i : ℝ) * (Lagrange.basis s v i).eval t)
          atTop (𝓝 (volval m P (i : ℝ) * (Lagrange.basis s v i).eval t)) := by
        intro i hi
        have hcv : Tendsto (fun n : ℕ => volval m (Pn n) (i : ℝ)) atTop (𝓝 (volval m P (i : ℝ))) :=
          (continuous_volval_inK m (i : ℝ)).tendsto P |>.comp hP
        simpa using hcv.mul_const ((Lagrange.basis s v i).eval t)
      exact tendsto_finsetSum s hterm
    have hsum_target : (∑ i ∈ s, volval m P (i : ℝ) * (Lagrange.basis s v i).eval t) = p.eval t := by
      simpa [p, s, v, SteinerInterp.nodes] using
        (SteinerInterp.eval_interpolate (m := m) (r := fun i => volval m P (i : ℝ)) t).symm
    have hleft_sum : Tendsto
        (fun n : ℕ => ∑ i ∈ s, volval m (Pn n) (i : ℝ) * (Lagrange.basis s v i).eval t)
        atTop (𝓝 (volval m P t)) :=
      hleft.congr' (Filter.Eventually.of_forall (fun n => hval_sum n))
    have heq := tendsto_nhds_unique hsum_lim hleft_sum
    rw [hsum_target] at heq
    exact heq.symm

/-- Steiner's formula for polytopes: for a polytope `P = convexHull u` in `EuclideanSpace ℝ (Fin m)`
the parallel-body volume is the restriction of a polynomial of degree at most `m`. -/
theorem steiner_polynomial_polytope (m : ℕ)
    (P : ConvexBody (EuclideanSpace ℝ (Fin m))) (u : Finset (EuclideanSpace ℝ (Fin m)))
    (hP : (P : Set (EuclideanSpace ℝ (Fin m))) = convexHull ℝ (u : Set _)) :
    ∃ p : Polynomial ℝ, p.natDegree ≤ m ∧ ∀ t : ℝ, 0 ≤ t → volval m P t = p.eval t := by
  classical
  by_cases hint : (interior (P : Set (EuclideanSpace ℝ (Fin m)))).Nonempty
  · obtain ⟨p, hpdeg, hpeval⟩ := polytope_parallel_body_polynomial_fullDim m P u hP hint
    exact ⟨p, hpdeg, fun t ht => hpeval t ht⟩
  · have hdist : ∀ n : ℕ, ∃ Q : ConvexBody (EuclideanSpace ℝ (Fin m)),
        ∃ w : Finset (EuclideanSpace ℝ (Fin m)),
        (Q : Set (EuclideanSpace ℝ (Fin m))) = convexHull ℝ (w : Set (EuclideanSpace ℝ (Fin m))) ∧
        (interior (Q : Set (EuclideanSpace ℝ (Fin m)))).Nonempty ∧ dist Q P < ((n : ℝ) + 1)⁻¹ := by
      intro n
      exact exists_fullDim_polytope_close m P (δ := ((n : ℝ) + 1)⁻¹) (by positivity)
    choose Pn un hPn hint_n hdist_n using hdist
    have hPntend : Tendsto Pn atTop (nhds P) := by
      refine Metric.tendsto_atTop.mpr ?_
      intro ε hε
      have ht : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) := by
        simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      rcases Metric.tendsto_atTop.mp ht ε hε with ⟨N, hN⟩
      refine ⟨N, ?_⟩
      intro n hn
      have hlt := hN n hn
      have hpos : 0 ≤ ((n : ℝ) + 1)⁻¹ := inv_nonneg.mpr (by positivity)
      have habs : dist (((n : ℝ) + 1)⁻¹) (0 : ℝ) = ((n : ℝ) + 1)⁻¹ := by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hpos]
      exact lt_trans (hdist_n n) (by simpa [habs] using hlt)
    have hpoly_n : ∀ n : ℕ, ∃ p : Polynomial ℝ, p.natDegree ≤ m ∧
        ∀ t : ℝ, 0 ≤ t → volval m (Pn n) t = p.eval t := by
      intro n
      obtain ⟨p, hpdeg, hpeval⟩ := polytope_parallel_body_polynomial_fullDim m (Pn n) (un n) (hPn n) (hint_n n)
      exact ⟨p, hpdeg, fun t ht => hpeval t ht⟩
    exact limit_lift_polynomial m P Pn hPntend hpoly_n

/-- **Steiner's formula**: for every convex body `K` in `EuclideanSpace ℝ (Fin m)` the
parallel-body volume function `t ↦ vol (K + t • B)`, `t ≥ 0`, is the restriction of a
polynomial of degree at most `m`. -/
theorem steiner_polynomial (m : ℕ) (K : ConvexBody (EuclideanSpace ℝ (Fin m))) :
    ∃ p : Polynomial ℝ, p.natDegree ≤ m ∧ ∀ t : ℝ, 0 ≤ t → volval m K t = p.eval t := by
  classical
  have hex : ∀ n : ℕ, ∃ P : ConvexBody (EuclideanSpace ℝ (Fin m)),
      ∃ u : Finset (EuclideanSpace ℝ (Fin m)),
      (P : Set (EuclideanSpace ℝ (Fin m))) = convexHull ℝ (u : Set (EuclideanSpace ℝ (Fin m))) ∧
      dist P K < ((n : ℝ) + 1)⁻¹ := by
    intro n
    exact polytope_dense (V := EuclideanSpace ℝ (Fin m)) K (δ := ((n : ℝ) + 1)⁻¹) (by positivity)
  choose Pn un hPn hPndist using hex
  have hPntend' : Tendsto Pn atTop (nhds K) := by
    refine Metric.tendsto_atTop.mpr ?_
    intro ε hε
    have ht : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) := by
      simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rcases Metric.tendsto_atTop.mp ht ε hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hlt := hN n hn
    have hpos : 0 ≤ ((n : ℝ) + 1)⁻¹ := inv_nonneg.mpr (by positivity)
    have habs : dist (((n : ℝ) + 1)⁻¹) (0 : ℝ) = ((n : ℝ) + 1)⁻¹ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hpos]
    exact lt_trans (hPndist n) (by simpa [habs] using hlt)
  have hpoly_n : ∀ n : ℕ, ∃ p : Polynomial ℝ, p.natDegree ≤ m ∧
      ∀ t : ℝ, 0 ≤ t → volval m (Pn n) t = p.eval t :=
    fun n => steiner_polynomial_polytope m (Pn n) (un n) (hPn n)
  exact limit_lift_polynomial m K Pn hPntend' hpoly_n

/-! ## The coefficient functionals of the Steiner polynomial -/

/-- The `k`-th coefficient functional of the Steiner polynomial of a convex body. -/
def steinerCoeff (m : ℕ) (k : ℕ) (K : ConvexBody (EuclideanSpace ℝ (Fin m))) : ℝ :=
  ∑ i ∈ SteinerInterp.nodes m, volval m K (i : ℝ) *
    (Lagrange.basis (SteinerInterp.nodes m) SteinerInterp.vv i).coeff k

/-- The `k`-th coefficient of a polynomial of degree `≤ m` from its values at `0, …, m`. -/
lemma coeff_eq_sum_lagrange (m : ℕ) (P : Polynomial ℝ) (hP : P.natDegree ≤ m) (k : ℕ) :
    P.coeff k = ∑ i ∈ SteinerInterp.nodes m, P.eval (SteinerInterp.vv i) *
      (Lagrange.basis (SteinerInterp.nodes m) SteinerInterp.vv i).coeff k := by
  have hcard : (SteinerInterp.nodes m).card = m + 1 := by simp [SteinerInterp.nodes]
  have hdeg : P.degree < ((SteinerInterp.nodes m).card : WithBot ℕ) := by
    rw [hcard]
    exact lt_of_le_of_lt
      (le_trans Polynomial.degree_le_natDegree (Nat.cast_le.mpr hP))
      (Nat.cast_lt.mpr (Nat.lt_succ_self m))
  have hinterp : P = Lagrange.interpolate (SteinerInterp.nodes m) SteinerInterp.vv
      (fun i => P.eval (SteinerInterp.vv i)) :=
    Lagrange.eq_interpolate (s := SteinerInterp.nodes m) (v := SteinerInterp.vv)
      (SteinerInterp.hv_inj m) hdeg
  have hL : P.coeff k = (Lagrange.interpolate (SteinerInterp.nodes m) SteinerInterp.vv
      (fun i => P.eval (SteinerInterp.vv i))).coeff k :=
    congrArg (fun q : Polynomial ℝ => q.coeff k) hinterp
  rw [hL, Lagrange.interpolate_apply, Polynomial.finsetSum_coeff]
  exact Finset.sum_congr rfl (fun i hi => by rw [Polynomial.coeff_C_mul, mul_comm])

lemma steinerCoeff_eq (m : ℕ) (K : ConvexBody (EuclideanSpace ℝ (Fin m))) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ m) (hpv : ∀ t : ℝ, 0 ≤ t → volval m K t = p.eval t) (k : ℕ) :
    steinerCoeff m k K = p.coeff k := by
  rw [coeff_eq_sum_lagrange m p hp k, steinerCoeff]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi0 : 0 ≤ (i : ℝ) := by exact_mod_cast (Nat.zero_le i)
  rw [hpv (i : ℝ) hi0, SteinerInterp.vv]

/-- The values of `volval` at a nonnegative argument are the Stirling polynomial combination
of the coefficient functionals. -/
lemma volval_eq_sum_steinerCoeff (m : ℕ) (K : ConvexBody (EuclideanSpace ℝ (Fin m)))
    (t : ℝ) (ht : 0 ≤ t) :
    volval m K t = ∑ k ∈ Finset.range (m+1), steinerCoeff m k K * t^k := by
  obtain ⟨p, hp, hpv⟩ := steiner_polynomial m K
  have h1 : p.eval t = ∑ k ∈ Finset.range (m+1), p.coeff k * t^k := by
    rw [Polynomial.eval_eq_sum_range]
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    · intro x hx hxnot
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
      · ring
      · simp only [Finset.mem_range, not_lt] at hxnot
        omega
  rw [hpv t ht, h1]
  exact Finset.sum_congr rfl (fun k hk => by rw [steinerCoeff_eq m K p hp hpv k])


/-! ## The slice identity and the relation between the coefficient functionals -/

/-- The moment `∫_(-t)^t (√(t²-s²))^k ds = c_k t^{k+1}` with the explicit constant
`c_k = ∫_(-1)^1 (√(1-u²))^k du`. -/
lemma slice_moment_explicit (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (-t)..t, (Real.sqrt (t^2 - s^2))^k)
      = (∫ u in (-1)..1, (Real.sqrt (1 - u^2))^k) * t^(k+1) := by
  obtain ⟨c, hc0, hc⟩ := slice_moment k
  have h1 : (∫ u in (-1)..1, (Real.sqrt (1 - u^2))^k) = c := by
    have h := hc 1 (by norm_num)
    simpa using h
  rw [h1, hc t ht]

/-- The expansion of a polynomial of degree `≤ m` as a sum of monomials `j ≤ m`. -/
lemma eval_eq_sum_range_le {m : ℕ} {p : Polynomial ℝ} (hp : p.natDegree ≤ m) (x : ℝ) :
    p.eval x = ∑ j ∈ Finset.range (m+1), p.coeff j * x^j := by
  rw [Polynomial.eval_eq_sum_range]
  refine Finset.sum_subset ?_ ?_
  · intro y hy
    simp only [Finset.mem_range] at hy ⊢
    omega
  · intro y hy hynot
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · ring
    · simp only [Finset.mem_range, not_lt] at hynot
      omega

/-- The model parallel-body volume generators on `EuclideanSpace ℝ (Fin n)`. -/
def Fgen (n : ℕ) : Fin (n+1) → ConvexBody (EuclideanSpace ℝ (Fin n)) → ℝ :=
  fun i K => volval n K (i : ℝ)

/-- The rigid-motion-invariant valuation predicate. -/
def CurvVal (n : ℕ) (f : ConvexBody (EuclideanSpace ℝ (Fin n)) → ℝ) : Prop :=
  Continuous f ∧
  (∀ A B C D : ConvexBody (EuclideanSpace ℝ (Fin n)),
      (A : Set (EuclideanSpace ℝ (Fin n))) =
          (C : Set (EuclideanSpace ℝ (Fin n))) ∪ (D : Set (EuclideanSpace ℝ (Fin n))) →
      (B : Set (EuclideanSpace ℝ (Fin n))) =
          (C : Set (EuclideanSpace ℝ (Fin n))) ∩ (D : Set (EuclideanSpace ℝ (Fin n))) →
      f A + f B = f C + f D) ∧
  (∀ A B : ConvexBody (EuclideanSpace ℝ (Fin n)),
      ∀ e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      (B : Set (EuclideanSpace ℝ (Fin n))) = e '' (A : Set (EuclideanSpace ℝ (Fin n))) → f B = f A) ∧
  (∀ A B : ConvexBody (EuclideanSpace ℝ (Fin n)), ∀ t : EuclideanSpace ℝ (Fin n),
      (B : Set (EuclideanSpace ℝ (Fin n))) =
        (fun x => x + t) '' (A : Set (EuclideanSpace ℝ (Fin n))) → f A = f B)

lemma curvVal_Fgen (n : ℕ) (i : Fin (n+1)) : CurvVal n (Fgen n i) := by
  obtain ⟨h1, h2, h3, h4⟩ := parallel_body_valuation n (i : ℝ)
  exact ⟨h1, h2, h3, h4⟩

/-- The set of continuous rigid-motion-invariant valuations is a submodule. -/
def curvSubmodule (n : ℕ) : Submodule ℝ (ConvexBody (EuclideanSpace ℝ (Fin n)) → ℝ) where
  carrier := {f | CurvVal n f}
  zero_mem' := by
    refine ⟨continuous_zero, ?_, ?_, ?_⟩
    · intro A B C D hU hI; simp
    · intro A B e h; rfl
    · intro A B t h; rfl
  add_mem' := by
    rintro f g ⟨hf1, hf2, hf3, hf4⟩ ⟨hg1, hg2, hg3, hg4⟩
    refine ⟨hf1.add hg1, ?_, ?_, ?_⟩
    · intro A B C D hU hI
      have h1 := hf2 A B C D hU hI
      have h2 := hg2 A B C D hU hI
      simp only [Pi.add_apply]
      linarith
    · intro A B e h
      have h1 := hf3 A B e h
      have h2 := hg3 A B e h
      simp only [Pi.add_apply, h1, h2]
    · intro A B t h
      have h1 := hf4 A B t h
      have h2 := hg4 A B t h
      simp only [Pi.add_apply, h1, h2]
  smul_mem' := by
    rintro c f ⟨hf1, hf2, hf3, hf4⟩
    refine ⟨hf1.const_smul c, ?_, ?_, ?_⟩
    · intro A B C D hU hI
      have h1 := hf2 A B C D hU hI
      simp only [Pi.smul_apply, smul_eq_mul]
      linear_combination c * h1
    · intro A B e h
      have h1 := hf3 A B e h
      simp only [Pi.smul_apply, smul_eq_mul, h1]
    · intro A B t h
      have h1 := hf4 A B t h
      simp only [Pi.smul_apply, smul_eq_mul, h1]

lemma curvVal_span {n : ℕ} {f : ConvexBody (EuclideanSpace ℝ (Fin n)) → ℝ}
    (hf : f ∈ Submodule.span ℝ (Set.range (Fgen n))) : CurvVal n f :=
  have h : Submodule.span ℝ (Set.range (Fgen n)) ≤ curvSubmodule n :=
    Submodule.span_le.mpr (by rintro g ⟨i, rfl⟩; exact curvVal_Fgen n i)
  h hf

/-- The classification statement for `EuclideanSpace ℝ (Fin n)`. -/
def EuclidClass (n : ℕ) : Prop :=
  ∀ f : ConvexBody (EuclideanSpace ℝ (Fin n)) → ℝ, CurvVal n f →
    f ∈ Submodule.span ℝ (Set.range (Fgen n))

lemma steinerCoeff_mem_span (n k : ℕ) :
    steinerCoeff n k ∈ Submodule.span ℝ (Set.range (Fgen n)) := by
  have h : steinerCoeff n k = ∑ i ∈ SteinerInterp.nodes n,
      (Lagrange.basis (SteinerInterp.nodes n) SteinerInterp.vv i).coeff k •
        (fun K : ConvexBody (EuclideanSpace ℝ (Fin n)) => volval n K (i : ℝ)) := by
    funext K
    simp only [steinerCoeff, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [h]
  refine Submodule.sum_mem _ (fun i hi => ?_)
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  refine ⟨⟨i, by simpa [SteinerInterp.nodes] using hi⟩, ?_⟩
  funext K
  simp [Fgen]

/-- Given the Fubini/slice identity for the lifted parallel bodies, the `(k+1)`-st coefficient
functional of the Steiner polynomial in dimension `m+1` of a lifted body is the `k`-th
coefficient functional in dimension `m`, rescaled by the moment constant `c_k`. -/
lemma steinerCoeff_lift_of_slice (m : ℕ)
    (hslice : ∀ (K : ConvexBody (EuclideanSpace ℝ (Fin m))) (t : ℝ), 0 ≤ t →
      volval (m+1) (liftCB m K) t
        = ∫ s in (-t)..t, volval m K (Real.sqrt (t^2 - s^2)))
    (k : ℕ) (hk : k ≤ m) (K : ConvexBody (EuclideanSpace ℝ (Fin m))) :
    steinerCoeff (m+1) (k+1) (liftCB m K)
      = (∫ u in (-1)..1, (Real.sqrt (1 - u^2))^k) * steinerCoeff m k K := by
  obtain ⟨p, hp, hpv⟩ := steiner_polynomial m K
  obtain ⟨q, hq, hqv⟩ := steiner_polynomial (m+1) (liftCB m K)
  have hp_eval : ∀ x : ℝ, p.eval x = ∑ j ∈ Finset.range (m+1), p.coeff j * x^j :=
    fun x => eval_eq_sum_range_le hp x
  -- key integral identity
  have hint : ∀ t : ℝ, 0 ≤ t →
      (∫ s in (-t)..t, p.eval (Real.sqrt (t^2 - s^2)))
        = ∑ j ∈ Finset.range (m+1),
            (∫ u in (-1)..1, (Real.sqrt (1 - u^2))^j) * p.coeff j * t^(j+1) := by
    intro t ht
    have h1 : (∫ s in (-t)..t, p.eval (Real.sqrt (t^2 - s^2)))
        = ∫ s in (-t)..t, ∑ j ∈ Finset.range (m+1), p.coeff j * (Real.sqrt (t^2 - s^2))^j := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact hp_eval _
    rw [h1, intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [intervalIntegral.integral_const_mul, slice_moment_explicit j ht]
      ring
    · intro j hj
      exact (by fun_prop : Continuous fun s : ℝ =>
        p.coeff j * (Real.sqrt (t^2 - s^2))^j).intervalIntegrable _ _
  -- polynomial identity
  set R : Polynomial ℝ :=
    ∑ j ∈ Finset.range (m+1),
      Polynomial.C ((∫ u in (-1)..1, (Real.sqrt (1 - u^2))^j) * p.coeff j) *
        Polynomial.X^(j+1) with hR
  have hpoly : q = R := by
    refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq q R (f := fun i : Fin (m+2) => (i : ℝ))
      (fun i j hij => Fin.ext (Nat.cast_injective hij)) ?_ ?_
    · intro i
      have hi0 : (0 : ℝ) ≤ (i : ℝ) := by exact_mod_cast (Nat.zero_le (i : ℕ))
      rw [← hqv (i : ℝ) hi0, hslice K (i : ℝ) hi0]
      have h2 : ∀ s : ℝ, volval m K (Real.sqrt ((i : ℝ)^2 - s^2))
          = p.eval (Real.sqrt ((i : ℝ)^2 - s^2)) :=
        fun s => hpv _ (Real.sqrt_nonneg _)
      rw [intervalIntegral.integral_congr (fun s hs => h2 s)]
      rw [hint (i : ℝ) hi0, hR]
      rw [Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    · have hq' : q.natDegree < m + 2 := by omega
      have hRle : R.natDegree ≤ m + 1 := by
        rw [hR]
        refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
        refine Finset.sup_le ?_
        intro j hj
        refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
        rw [Polynomial.natDegree_X_pow]
        exact Nat.succ_le_of_lt (Finset.mem_range.mp hj)
      have hR' : R.natDegree < m + 2 :=
        lt_of_le_of_lt hRle (Nat.lt_succ_self (m+1))
      simpa using max_lt hq' hR'
  -- coefficient comparison
  have hcoeff : q.coeff (k+1)
      = (∫ u in (-1)..1, (Real.sqrt (1 - u^2))^k) * p.coeff k := by
    rw [hpoly, hR, Polynomial.finsetSum_coeff]
    have hsub : ∀ j ∈ Finset.range (m+1), j ≠ k →
        (Polynomial.C ((∫ u in (-1)..1, (Real.sqrt (1 - u^2))^j) * p.coeff j) *
          Polynomial.X^(j+1)).coeff (k+1) = 0 := by
      intro j hj hjk
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_neg (fun hcon => hjk (Nat.succ.inj hcon).symm), mul_zero]
    rw [Finset.sum_eq_single k hsub
      (fun hknot => absurd (Finset.mem_range.mpr (by omega)) hknot)]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  rw [steinerCoeff_eq (m+1) (liftCB m K) q hq hqv (k+1),
      steinerCoeff_eq m K p hp hpv k]
  exact hcoeff


/-! ## The slice hypothesis and the classification theorem -/

/-- The Fubini/slice identity in the form needed below. -/
lemma slice_hyp (m : ℕ) (K : ConvexBody (EuclideanSpace ℝ (Fin m))) (t : ℝ) (ht : 0 ≤ t) :
    volval (m+1) (liftCB m K) t
      = ∫ s in (-t)..t, volval m K (Real.sqrt (t^2 - s^2)) := by
  have h1 : volval (m+1) (liftCB m K) t
      = (volume {y : EuclideanSpace ℝ (Fin (m+1)) |
          ∃ x ∈ (K : Set (EuclideanSpace ℝ (Fin m))), dist y (liftFun m x) ≤ t}).toReal := by
    have hset : {y : EuclideanSpace ℝ (Fin (m+1)) |
          ∃ k ∈ (liftCB m K : Set (EuclideanSpace ℝ (Fin (m+1)))), dist y k ≤ t}
        = {y : EuclideanSpace ℝ (Fin (m+1)) |
          ∃ x ∈ (K : Set (EuclideanSpace ℝ (Fin m))), dist y (liftFun m x) ≤ t} := by
      ext y
      constructor
      · rintro ⟨z, hz, hyz⟩
        rw [liftCB_coe'] at hz
        rcases hz with ⟨x, hx, rfl⟩
        exact ⟨x, hx, hyz⟩
      · rintro ⟨x, hx, hyx⟩
        refine ⟨liftFun m x, ?_, hyx⟩
        rw [liftCB_coe']
        exact ⟨x, hx, rfl⟩
    rw [volval, convexBody_add_smul_unitBall_eq _ ht, hset]
  have hPa := parallel_body_lift_slice m K t ht
  have hset2 : {y : EuclideanSpace ℝ (Fin (m+1)) |
        ∃ x ∈ (K : Set (EuclideanSpace ℝ (Fin m))),
          dist y ((EuclideanSpace.equiv (Fin (m+1)) ℝ).symm
            (Fin.cases 0 (fun i : Fin m => x i))) ≤ t}
      = {y : EuclideanSpace ℝ (Fin (m+1)) |
          ∃ x ∈ (K : Set (EuclideanSpace ℝ (Fin m))), dist y (liftFun m x) ≤ t} := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, hxy⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, hxy⟩
  rw [hset2] at hPa
  rw [h1, hPa]
  refine intervalIntegral.integral_congr (fun s hs => ?_)
  rw [volval, convexBody_add_smul_unitBall_eq _ (Real.sqrt_nonneg _)]

lemma slice_const_pos (k : ℕ) : 0 < ∫ u in (-1)..1, (Real.sqrt (1 - u^2))^k := by
  obtain ⟨c, hc0, hc⟩ := slice_moment k
  have h : (∫ u in (-1)..1, (Real.sqrt (1 - u^2))^k) = c := by
    have h := hc 1 (by norm_num)
    simpa using h
  rw [h]
  exact hc0

lemma volval_zero (n : ℕ) (K : ConvexBody (EuclideanSpace ℝ (Fin n))) :
    volval n K 0 = (volume (K : Set (EuclideanSpace ℝ (Fin n)))).toReal := by
  have hset : {x : EuclideanSpace ℝ (Fin n) | ∃ k ∈ (K : Set _), dist x k ≤ 0} = (K : Set _) := by
    ext x
    constructor
    · rintro ⟨k, hk, hxk⟩
      rwa [dist_eq_zero.mp (le_antisymm hxk dist_nonneg)]
    · intro hx
      exact ⟨x, hx, by simp⟩
  rw [volval, convexBody_add_smul_unitBall_eq K (le_refl (0:ℝ)), hset]

/-- The restricted valuation of a rigid-motion-invariant valuation is again one. -/
lemma curvVal_liftCB {m : ℕ} {f : ConvexBody (EuclideanSpace ℝ (Fin (m+1))) → ℝ}
    (hf : CurvVal (m+1) f) : CurvVal m (fun K => f (liftCB m K)) := by
  obtain ⟨hfcont, hfadd, hfiso, hftrans⟩ := hf
  refine ⟨hfcont.comp (continuous_liftCB m), ?_, ?_, ?_⟩
  · intro A B C D hU hI
    have hU' : (liftCB m A : Set (EuclideanSpace ℝ (Fin (m+1)))) =
        (liftCB m C : Set (EuclideanSpace ℝ (Fin (m+1)))) ∪
          (liftCB m D : Set (EuclideanSpace ℝ (Fin (m+1)))) := by
      rw [liftCB_coe', liftCB_coe', liftCB_coe', hU, Set.image_union]
    have hI' : (liftCB m B : Set (EuclideanSpace ℝ (Fin (m+1)))) =
        (liftCB m C : Set (EuclideanSpace ℝ (Fin (m+1)))) ∩
          (liftCB m D : Set (EuclideanSpace ℝ (Fin (m+1)))) := by
      rw [liftCB_coe', liftCB_coe', liftCB_coe', hI, liftFun_image_inter]
    exact hfadd _ _ _ _ hU' hI'
  · intro A B e hB
    have hset : (liftCB m B : Set (EuclideanSpace ℝ (Fin (m+1)))) =
        blockIso m e '' (liftCB m A : Set (EuclideanSpace ℝ (Fin (m+1)))) := by
      rw [liftCB_coe', liftCB_coe', hB, Set.image_image, Set.image_image]
      apply Set.image_congr
      intro x hx
      exact (blockIso_liftFun m e x).symm
    exact hfiso _ _ (blockIso m e) hset
  · intro A B t hB
    have hset : (liftCB m B : Set (EuclideanSpace ℝ (Fin (m+1)))) =
        (fun y => y + liftFun m t) '' (liftCB m A : Set (EuclideanSpace ℝ (Fin (m+1)))) := by
      rw [liftCB_coe', liftCB_coe', hB, liftFun_image_translate]
    exact hftrans _ _ (liftFun m t) hset

/-- The induction step: the classification in dimension `m` implies that in dimension `m+1`. -/
lemma euclidClass_succ (m : ℕ) (ih : EuclidClass m) : EuclidClass (m+1) := by
  intro f hfval
  have hfcont : Continuous f := hfval.1
  have hfadd := hfval.2.1
  have hfiso := hfval.2.2.1
  have hftrans := hfval.2.2.2
  set μ : ConvexBody (EuclideanSpace ℝ (Fin m)) → ℝ := fun K => f (liftCB m K) with hμ
  have hμval : CurvVal m μ := curvVal_liftCB (m := m) (f := f) hfval
  obtain ⟨b, hb⟩ :=
    (Submodule.mem_span_range_iff_exists_fun (R := ℝ) (v := Fgen m)).1 (ih μ hμval)
  -- the moment constants and the coefficients of `μ`
  set c : ℕ → ℝ := fun k => ∫ u in (-1)..1, (Real.sqrt (1 - u^2))^k with hc
  set β : ℕ → ℝ := fun k => ∑ i : Fin (m+1), b i * (i : ℝ)^k with hβ
  have hcpos : ∀ k, 0 < c k := fun k => slice_const_pos k
  set ν : ConvexBody (EuclideanSpace ℝ (Fin (m+1))) → ℝ :=
    ∑ k ∈ Finset.range (m+1), (β k / c k) • steinerCoeff (m+1) (k+1) with hν
  have hνmem : ν ∈ Submodule.span ℝ (Set.range (Fgen (m+1))) := by
    rw [hν]
    refine Submodule.sum_mem _ (fun k hk => ?_)
    exact Submodule.smul_mem _ _ (steinerCoeff_mem_span (m+1) (k+1))
  -- `ν` agrees with `f` on the hyperplane
  have hν_lift : ∀ K : ConvexBody (EuclideanSpace ℝ (Fin m)), ν (liftCB m K) = μ K := by
    intro K
    have hνK : ν (liftCB m K) =
        ∑ k ∈ Finset.range (m+1), β k * steinerCoeff m k K := by
      rw [hν]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk' : k ≤ m := by simpa [Finset.mem_range] using hk
      rw [steinerCoeff_lift_of_slice m (slice_hyp m) k hk' K]
      have hne : c k ≠ 0 := ne_of_gt (hcpos k)
      field_simp [hne]
      ring
    have hμK : μ K = ∑ k ∈ Finset.range (m+1), β k * steinerCoeff m k K := by
      have h1 : μ K = ∑ i : Fin (m+1), b i * volval m K (i : ℝ) := by
        have h := (congrFun hb K).symm
        simpa [Fgen, Pi.smul_apply, smul_eq_mul] using h
      rw [h1, hβ]
      have h2 : ∀ i : Fin (m+1),
          volval m K (i : ℝ) = ∑ k ∈ Finset.range (m+1), steinerCoeff m k K * (i : ℝ)^k :=
        fun i => volval_eq_sum_steinerCoeff m K _ (by positivity)
      simp only [h2, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i hi => by ring)
    rw [hνK, hμK]
  -- the difference is simple
  have hηC : f - ν ∈ curvSubmodule (m+1) := by
    have hfC : f ∈ curvSubmodule (m+1) := hfval
    have hνC : ν ∈ curvSubmodule (m+1) := curvVal_span hνmem
    have hneg : (-1 : ℝ) • ν ∈ curvSubmodule (m+1) := (curvSubmodule _).smul_mem (-1) hνC
    have := (curvSubmodule (m+1)).add_mem hfC hneg
    simpa [sub_eq_add_neg] using this
  obtain ⟨hηcont, hηadd, hηiso, hηtrans⟩ := hηC
  have hsimple : ∀ L : ConvexBody (EuclideanSpace ℝ (Fin (m+1))),
      interior (L : Set (EuclideanSpace ℝ (Fin (m+1)))) = ∅ → (f - ν) L = 0 := by
    intro L hL
    obtain ⟨e, t, ht⟩ :=
      exists_isometry_add_subset_hyperplane (m+1) (Nat.succ_pos m) L hL
    let L₁ : ConvexBody (EuclideanSpace ℝ (Fin (m+1))) :=
      ⟨e '' (L : Set (EuclideanSpace ℝ (Fin (m+1)))),
        L.convex.linear_image (e : EuclideanSpace ℝ (Fin (m+1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m+1))),
        L.isCompact.image e.continuous,
        L.nonempty.image e⟩
    let L₂ : ConvexBody (EuclideanSpace ℝ (Fin (m+1))) :=
      ⟨(fun x => x + t) '' (L₁ : Set (EuclideanSpace ℝ (Fin (m+1)))),
        by simpa only [add_comm] using L₁.convex.translate t,
        L₁.isCompact.image (continuous_id.add continuous_const),
        L₁.nonempty.image (fun x => x + t)⟩
    have hL₂in : ∀ y ∈ (L₂ : Set (EuclideanSpace ℝ (Fin (m+1)))), y 0 = 0 := by
      rintro y ⟨x, hx, rfl⟩
      rcases hx with ⟨z, hz, rfl⟩
      simpa using ht z hz
    have hL₂eq : L₂ = liftCB m (dropCB m L₂ hL₂in) := (liftCB_dropCB L₂ hL₂in).symm
    have h1 : (f - ν) L₂ = 0 := by
      rw [hL₂eq]
      have hlift := hν_lift (dropCB m L₂ hL₂in)
      simp only [Pi.sub_apply]
      rw [hlift]
      simp [hμ]
    have h2 : (f - ν) L = (f - ν) L₂ := by
      have hiso := hηiso L L₁ e rfl
      have htr := hηtrans L₁ L₂ t rfl
      exact hiso.symm.trans htr
    rw [h2, h1]
  obtain ⟨c₀, hc₀⟩ :=
    simple_rigid_invariant_eq_const_volume (f - ν) hηcont hηadd hηiso hηtrans hsimple
  have hfeq : f = ν + c₀ • Fgen (m+1) ⟨0, by omega⟩ := by
    funext L
    have h1 : (f - ν) L = c₀ * (volume (L : Set (EuclideanSpace ℝ (Fin (m+1))))).toReal := hc₀ L
    have h2 : Fgen (m+1) ⟨0, by omega⟩ L
        = (volume (L : Set (EuclideanSpace ℝ (Fin (m+1))))).toReal := by
      simpa [Fgen] using volval_zero (m+1) L
    simp only [Pi.sub_apply] at h1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h2]
    linarith
  rw [hfeq]
  refine Submodule.add_mem _ hνmem ?_
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨0, by omega⟩, rfl⟩)

/-- The base case: dimension `0`. -/
lemma euclidClass_zero : EuclidClass 0 := by
  intro f hf
  have hvol : (volume (Set.univ : Set (EuclideanSpace ℝ (Fin 0)))).toReal = 1 := by
    have h2 : (volume (Set.univ : Set (Fin 0 → ℝ))) = 1 := by
      rw [show (volume : Measure (Fin 0 → ℝ)) =
        Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ)) from rfl, Measure.pi_univ]
      simp
    have hmp := PiLp.volume_preserving_toLp (ι := Fin 0)
    have h1 := hmp.measure_preimage (s := (Set.univ : Set (EuclideanSpace ℝ (Fin 0))))
      MeasurableSet.univ
    rw [Set.preimage_univ] at h1
    rw [← h1, h2]
    norm_num
  have huniv : ∀ K : ConvexBody (EuclideanSpace ℝ (Fin 0)),
      (K : Set (EuclideanSpace ℝ (Fin 0))) = Set.univ := by
    intro K
    refine Set.eq_univ_iff_forall.mpr (fun x => ?_)
    have hx : x = K.nonempty.some := Subsingleton.elim x _
    rw [hx]
    exact K.nonempty.some_mem
  haveI hsub : Subsingleton (ConvexBody (EuclideanSpace ℝ (Fin 0))) :=
    ⟨fun A B => ConvexBody.ext (by rw [huniv A, huniv B])⟩
  have hF0 : Fgen 0 ⟨0, Nat.lt_succ_self 0⟩ =
      fun _ : ConvexBody (EuclideanSpace ℝ (Fin 0)) => (1 : ℝ) := by
    funext K
    have h1 : Fgen 0 ⟨0, Nat.lt_succ_self 0⟩ K = volval 0 K 0 := by simp [Fgen]
    rw [h1, volval_zero]
    rw [huniv K]
    exact hvol
  have hfeq : f = f 0 • Fgen 0 ⟨0, Nat.lt_succ_self 0⟩ := by
    funext K
    rw [hF0, Pi.smul_apply, smul_eq_mul]
    have hK : K = (0 : ConvexBody (EuclideanSpace ℝ (Fin 0))) := Subsingleton.elim K 0
    rw [hK]
    ring
  rw [hfeq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨0, Nat.lt_succ_self 0⟩, rfl⟩)

/-- The classification statement in every dimension. -/
theorem euclid_class (n : ℕ) : EuclidClass n := by
  induction n with
  | zero => exact euclidClass_zero
  | succ m ih => exact euclidClass_succ m ih

end

end EucV2

/-- Hadwiger's characterization result (classification half) for `EuclideanSpace ℝ (Fin n)`:
every continuous rigid-motion-invariant valuation lies in the span of the `n+1` parallel-body
volume functionals `K ↦ vol (K + i • B)`, `i = 0, …, n` (`B` the unit ball).

This is a second, independent attempt (the first lives at
`Commons.Geometry.Convex.Hadwiger.euclidean_valuation_span`); whichever completes first is used. -/
theorem euclidean_valuation_span_v2 (n : ℕ) :
    let V := EuclideanSpace ℝ (Fin n)
    let B : ConvexBody V := ⟨Metric.closedBall (0 : V) 1, convex_closedBall (0 : V) 1, isCompact_closedBall (0 : V) 1, Metric.nonempty_closedBall.mpr zero_le_one⟩
    let F : Fin (n + 1) → ConvexBody V → ℝ := fun i K => (MeasureTheory.volume ((K + (i : ℝ) • B : ConvexBody V) : Set V)).toReal
    ∀ f : ConvexBody V → ℝ,
      Continuous f →
      (∀ A B C D : ConvexBody V,
          (A : Set V) = (C : Set V) ∪ (D : Set V) →
          (B : Set V) = (C : Set V) ∩ (D : Set V) →
          f A + f B = f C + f D) →
      (∀ A B : ConvexBody V, ∀ e : V ≃ₗᵢ[ℝ] V,
          (B : Set V) = e '' (A : Set V) → f B = f A) →
      (∀ A B : ConvexBody V, ∀ t : V,
          (B : Set V) = (fun x : V => x + t) '' (A : Set V) → f A = f B) →
      f ∈ Submodule.span ℝ (Set.range F) := by
  dsimp only
  intro f hcont hadd hiso htrans
  exact EucV2.euclid_class n f ⟨hcont, hadd, hiso, htrans⟩

end Commons.Geometry.Convex.Hadwiger
