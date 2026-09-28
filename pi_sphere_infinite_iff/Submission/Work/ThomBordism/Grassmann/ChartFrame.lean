import Submission.Work.ThomBordism.Grassmann.Grassmannian

set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-!
# The canonical frame of a chart of the oriented Grassmannian

This module builds the missing link between the *gluing-data* model of the tautological bundle
`Work.ThomBordism.Grassmann.tautologicalBundle` (a `VectorBundleCore` whose fibre is the model
space `Amb k = ℝ^k` and whose cover is the finite set `ChartIdx k m` of coordinate charts
`baseSet S`) and the *geometric* model of that bundle (the total space of pairs
`(P, w)` with `P` an oriented `k`-plane in `Amb (k+m)` and `w ∈ P`).

The tautological bundle's fibre coordinate over a point `x` of the chart `baseSet S` is the
`S`-coordinate vector of the corresponding vector of the plane: this is exactly what the
transition functions `coordChange S T` say, they are the change from the `S`-canonical
coordinates to the `T`-canonical ones.  Concretely:

* `coordVec S f i` — the `i`-th `S`-coordinate vector of the plane of the frame `f`: the (unique)
  vector of that plane whose `S`-coordinates are the standard basis vector `e_i`.  It is computed
  as `∑ j, (frameMatrix S f)⁻¹ j i • f j`, which makes sense for every frame (with the junk value
  `0` when the `S`-matrix is singular) and is **invariant under the `SO(k)`-action**
  (`coordVec_soActFun`), hence depends only on the point of the Grassmannian.
* `coordProj_coordVec` — its `S`-coordinates are `e_i` (`coordProj S (coordVec S f i) = e_i`).

The invariance is the statement that makes the descent to the Grassmannian possible; it is the
analogue, for the coordinate vectors of the plane, of
`Work.ThomBordism.Grassmann.frameMatrix_mul_inv_invariant` for the transition matrices.
-/

open scoped Topology

namespace Work.ThomBordism.Grassmann

noncomputable section

variable {k m : ℕ}

/-! ## The `S`-coordinate vectors of the plane of a frame -/

/-- The `i`-th `S`-coordinate vector of the plane of the frame `f`: the vector of the plane of `f`
whose `S`-coordinates are the standard basis vector `e_i`.  (The junk value `0` is taken when the
`S`-matrix is singular; the interesting case is `f ∈ chartSet S`.) -/
def coordVec (S : ChartIdx k m) (f : Stiefel k m) (i : Fin k) : Amb (k+m) :=
  ∑ j, (frameMatrix S f.1)⁻¹ j i • f.1 j

theorem coordVec_mem_span (S : ChartIdx k m) (f : Stiefel k m) (i : Fin k) :
    coordVec S f i ∈ Submodule.span ℝ (Set.range f.1) :=
  Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- The `S`-coordinates of the `j`-th vector of the frame `f` are the `j`-th column of the
`S`-matrix. -/
theorem coordProj_frame (S : ChartIdx k m) (f : Stiefel k m) (j : Fin k) :
    coordProj S (WithLp.ofLp (f.1 j)) = (frameMatrix S f.1).mulVec (Pi.single j 1) := by
  ext i
  rw [coordProj_apply, Matrix.mulVec_apply, dotProduct]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  rfl

/-- The `S`-coordinates of the `i`-th `S`-coordinate vector of the plane are the standard basis
vector `e_i`. -/
theorem coordProj_coordVec (S : ChartIdx k m) (f : Stiefel k m) (i : Fin k)
    (hf : f ∈ chartSet S) :
    coordProj S (WithLp.ofLp (coordVec S f i)) = Pi.single i 1 := by
  have hunit : IsUnit (frameMatrix S f.1).det := isUnit_iff_ne_zero.mpr ((mem_chartSet S f).mp hf)
  have hsum : WithLp.ofLp (coordVec S f i)
      = ∑ j, ((frameMatrix S f.1)⁻¹ j i) • WithLp.ofLp (f.1 j) := by
    rw [coordVec, WithLp.ofLp_sum]
    exact Finset.sum_congr rfl fun j _ => WithLp.ofLp_smul _ _ _
  rw [hsum, map_sum]
  simp only [map_smul]
  rw [Finset.sum_congr rfl fun j _ => by rw [coordProj_frame]]
  rw [Finset.sum_congr rfl fun j _ => by rw [Matrix.mulVec_single_one]]
  ext l
  simp only [Finset.sum_apply, Matrix.col_apply, Pi.smul_apply, smul_eq_mul]
  rw [show (∑ c, (frameMatrix S f.1)⁻¹ c i * frameMatrix S f.1 l c)
      = ∑ c, frameMatrix S f.1 l c * (frameMatrix S f.1)⁻¹ c i from
    Finset.sum_congr rfl fun c _ => mul_comm _ _]
  rw [← Matrix.mul_apply, Matrix.mul_nonsing_inv _ hunit, Matrix.one_apply]
  simp [Pi.single_apply]

/-! ## The evaluation of a coordinate vector in the plane -/

/-- **The vector of the plane of the frame `f` with `S`-coordinates `v`**: the linear combination
`∑ i, v i • coordVec S f i`, i.e. the vector whose `S`-coordinates are `v` (this is
`coordProj_coordEval` below).  It is the tautological bundle's fibre-coordinate parametrisation of
the plane. -/
def coordEval (S : ChartIdx k m) (f : Stiefel k m) (v : Amb k) : Amb (k+m) :=
  ∑ i, WithLp.ofLp v i • coordVec S f i

/-- The vector of the plane of `f` with `S`-coordinates `v` is the linear combination of the frame
with *frame coordinates* `(frameMatrix S f)⁻¹ v`. -/
theorem coordEval_eq_sum_frame (S : ChartIdx k m) (f : Stiefel k m) (v : Amb k) :
    coordEval S f v
      = ∑ j, ((frameMatrix S f.1)⁻¹).mulVec (WithLp.ofLp v) j • f.1 j := by
  ext l
  simp only [coordEval, coordVec, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **The evaluation is the inverse of the `S`-coordinate projection** on the plane of a frame of
the chart `S`. -/
theorem coordProj_coordEval (S : ChartIdx k m) (f : Stiefel k m) (v : Amb k)
    (hf : f ∈ chartSet S) :
    coordProj S (WithLp.ofLp (coordEval S f v)) = WithLp.ofLp v := by
  simp only [coordEval, WithLp.ofLp_sum, WithLp.ofLp_smul]
  rw [map_sum]
  simp only [map_smul]
  rw [Finset.sum_congr rfl fun i _ => by rw [coordProj_coordVec S f i hf]]
  ext i
  simp [Pi.single_apply]

/-- The evaluation is trivial exactly on the zero coordinate vector. -/
theorem coordEval_eq_zero_iff (S : ChartIdx k m) (f : Stiefel k m) (v : Amb k)
    (hf : f ∈ chartSet S) : coordEval S f v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have h1 := coordProj_coordEval S f v hf
    rw [h] at h1
    simp only [WithLp.ofLp_zero, map_zero] at h1
    exact (WithLp.ext_iff (p := 2)).mpr h1.symm
  · intro h
    rw [h]
    simp [coordEval]


/-- **Invariance of the coordinate vectors under the `SO(k)`-action**: acting by a special
orthogonal matrix on the frame does not change the coordinate vectors, so `coordVec S · i` depends
only on the point of the oriented Grassmannian. -/
theorem coordVec_soActFun (S : ChartIdx k m) (f : Stiefel k m) (i : Fin k) (A : SOk k) :
    coordVec S (A.act f) i = coordVec S f i := by
  by_cases hunit : IsUnit (frameMatrix S f.1).det
  · rw [coordVec, coordVec, show (A.act f).1 = soActFun A.1 f.1 from rfl,
      frameMatrix_soActFun, Matrix.mul_inv_rev]
    simp only [soActFun, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hcoef : (∑ j, ((A.1⁻¹ * (frameMatrix S f.1)⁻¹) j i * A.1 l j))
        = (frameMatrix S f.1)⁻¹ l i := by
      rw [show (∑ j, ((A.1⁻¹ * (frameMatrix S f.1)⁻¹) j i * A.1 l j))
          = ∑ j, (A.1 l j * ((A.1⁻¹ * (frameMatrix S f.1)⁻¹) j i)) from
        Finset.sum_congr rfl fun j _ => mul_comm _ _]
      rw [← Matrix.mul_apply]
      rw [show (A.1 * (A.1⁻¹ * (frameMatrix S f.1)⁻¹)) = (frameMatrix S f.1)⁻¹ from by
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ A.2.isUnit_det, Matrix.one_mul]]
    simp only [← mul_smul]
    rw [← Finset.sum_smul, hcoef]
  · have hdet : (frameMatrix S f.1).det = 0 := by
      by_contra h
      exact hunit (isUnit_iff_ne_zero.mpr h)
    have hdet2 : (frameMatrix S (A.act f).1).det = 0 := by
      rw [show (A.act f).1 = soActFun A.1 f.1 from rfl, frameMatrix_soActFun, Matrix.det_mul,
        A.2.2, mul_one, hdet]
    rw [coordVec, coordVec, Matrix.nonsing_inv_apply_not_isUnit _ (by rw [hdet2]; simp),
      Matrix.nonsing_inv_apply_not_isUnit _ (by rw [hdet]; simp)]
    simp

/-- **Invariance of the evaluation under the `SO(k)`-action.** -/
theorem coordEval_soActFun (S : ChartIdx k m) (f : Stiefel k m) (v : Amb k) (A : SOk k) :
    coordEval S (A.act f) v = coordEval S f v := by
  rw [coordEval, coordEval]
  exact Finset.sum_congr rfl fun i _ => by rw [coordVec_soActFun S f i A]

/-- **The evaluation is compatible with the transition functions** — this is the statement that the
tautological bundle's fibre coordinate is the `S`-coordinate vector of the vector of the plane: the
`T`-coordinates of the vector with `S`-coordinates `v` are `coordChange S T x v`, so the vector does
not depend on the chart used to describe it. -/
theorem coordEval_coordChangeAux (S T : ChartIdx k m) (f : Stiefel k m)
    (hS : f ∈ chartSet S) (hT : f ∈ chartSet T) (v : Amb k) :
    coordEval S f v = coordEval T f (coordChangeAux S T f v) := by
  have hunitS : IsUnit (frameMatrix S f.1).det := isUnit_iff_ne_zero.mpr ((mem_chartSet S f).mp hS)
  have hunitT : IsUnit (frameMatrix T f.1).det := isUnit_iff_ne_zero.mpr ((mem_chartSet T f).mp hT)
  rw [coordEval_eq_sum_frame, coordEval_eq_sum_frame]
  rw [show coordChangeAux S T f v
      = ((frameMatrix T f.1 * (frameMatrix S f.1)⁻¹)).mulVec v from by
    rw [coordChangeAux, dif_pos ((mem_chartSet S f).mp hS), matLin_apply]]
  rw [show (frameMatrix T f.1)⁻¹.mulVec
        (((frameMatrix T f.1 * (frameMatrix S f.1)⁻¹)).mulVec v)
      = (frameMatrix S f.1)⁻¹.mulVec v from by
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunitT, Matrix.one_mul]]

/-! ## The orthonormal frame of a chart, and the coordinate-evaluation -/

/-- **The orthonormal frame of the plane of the frame `f` attached to the chart `S`**: the
Gram–Schmidt orthonormalization of the `S`-coordinate vectors of the plane.  On `chartSet S` it is
an orthonormal frame spanning the same plane as `f` (`chartFrame_orthonormal`,
`chartFrame_span`), and it is invariant under the `SO(k)`-action
(`chartFrame_soActFun`), so it descends to the oriented Grassmannian. -/
def chartFrame (S : ChartIdx k m) (f : Stiefel k m) : Fin k → Amb (k+m) :=
  fun i => InnerProductSpace.gramSchmidtNormed ℝ (fun i => coordVec S f i) i

theorem coordVec_linearIndependent (S : ChartIdx k m) (f : Stiefel k m)
    (hf : f ∈ chartSet S) : LinearIndependent ℝ (fun i => coordVec S f i) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h1 : coordProj S (WithLp.ofLp (∑ j, g j • coordVec S f j)) = 0 := by rw [hg]; simp
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul] at h1
  rw [map_sum] at h1
  simp only [map_smul] at h1
  rw [Finset.sum_congr rfl fun j _ => by rw [coordProj_coordVec S f j hf]] at h1
  have h2 : g = 0 := by
    ext j
    have := congrFun h1 j
    simpa [Pi.single_apply] using this
  rw [h2]
  simp

/-- **The chart frame is orthonormal** on the frames of the chart. -/
theorem chartFrame_orthonormal (S : ChartIdx k m) (f : Stiefel k m) (hf : f ∈ chartSet S) :
    Orthonormal ℝ (chartFrame S f) :=
  InnerProductSpace.gramSchmidtNormed_orthonormal (coordVec_linearIndependent S f hf)

/-- **The plane of a frame of the chart is the range of the coordinate evaluation**: every vector
of the plane of `f` is the evaluation of its `S`-coordinates.  (This is the statement that the
`S`-coordinates trivialise the tautological bundle over the chart.) -/
theorem coordEval_coordProj (S : ChartIdx k m) (f : Stiefel k m) (hf : f ∈ chartSet S)
    {w : Amb (k+m)} (hw : w ∈ Submodule.span ℝ (Set.range (f.1 : Fin k → Amb (k+m)))) :
    coordEval S f (WithLp.toLp 2 (coordProj S (WithLp.ofLp w))) = w := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hw
  have hw' : w = ∑ i, c i • f.1 i := hc.symm
  rw [hw']
  have hcoord : coordProj S (WithLp.ofLp (∑ i, c i • f.1 i))
      = (frameMatrix S f.1).mulVec c := by
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul]
    rw [map_sum]
    simp only [map_smul]
    rw [Finset.sum_congr rfl fun i _ => by rw [coordProj_frame S f i]]
    rw [show (∑ i, c i • (frameMatrix S f.1).mulVec (Pi.single i 1))
        = (frameMatrix S f.1).mulVec (∑ i, c i • Pi.single i 1) from by
      rw [Matrix.mulVec_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [Matrix.mulVec_smul]]
    congr 1
    ext x
    simp [Pi.single_apply]
  rw [show WithLp.toLp 2 (coordProj S (WithLp.ofLp (∑ i, c i • f.1 i)))
      = WithLp.toLp 2 ((frameMatrix S f.1).mulVec c) from by rw [hcoord]]
  rw [coordEval_eq_sum_frame]
  rw [show WithLp.ofLp (WithLp.toLp 2 ((frameMatrix S f.1).mulVec c))
      = (frameMatrix S f.1).mulVec c from WithLp.ofLp_toLp 2 _]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr ((mem_chartSet S f).mp hf)), Matrix.one_mulVec]

/-- **The coordinate projection is injective on the plane** of a frame of the chart. -/
theorem coordProj_injOn_span (S : ChartIdx k m) (f : Stiefel k m) (hf : f ∈ chartSet S)
    {v w : Amb (k+m)} (hv : v ∈ Submodule.span ℝ (Set.range (f.1 : Fin k → Amb (k+m))))
    (hw : w ∈ Submodule.span ℝ (Set.range (f.1 : Fin k → Amb (k+m))))
    (h : coordProj S (WithLp.ofLp v) = coordProj S (WithLp.ofLp w)) : v = w := by
  rw [← coordEval_coordProj S f hf hv, ← coordEval_coordProj S f hf hw, h]

/-- **The chart frame spans the plane** of the frame (for a frame of the chart). -/
theorem chartFrame_span (S : ChartIdx k m) (f : Stiefel k m) (hf : f ∈ chartSet S) :
    Submodule.span ℝ (Set.range (chartFrame S f))
      = Submodule.span ℝ (Set.range (f.1 : Fin k → Amb (k+m))) := by
  have hspan : Submodule.span ℝ (Set.range (chartFrame S f))
      = Submodule.span ℝ (Set.range fun i => coordVec S f i) := by
    show Submodule.span ℝ (Set.range fun i =>
      InnerProductSpace.gramSchmidtNormed ℝ (fun i => coordVec S f i) i) = _
    rw [InnerProductSpace.span_gramSchmidtNormed_range,
      InnerProductSpace.span_gramSchmidt]
  rw [hspan]
  refine le_antisymm (Submodule.span_le.mpr fun x hx => ?_) (Submodule.span_le.mpr fun x hx => ?_)
  · rcases hx with ⟨i, rfl⟩
    exact coordVec_mem_span S f i
  · rcases hx with ⟨j, rfl⟩
    rw [← coordEval_coordProj S f hf (Submodule.subset_span ⟨j, rfl⟩ :
      f.1 j ∈ Submodule.span ℝ (Set.range (f.1 : Fin k → Amb (k+m))))]
    simp only [coordEval]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, rfl⟩)

/-- **The chart frame is invariant under the `SO(k)`-action**. -/
theorem chartFrame_soActFun (S : ChartIdx k m) (f : Stiefel k m) (A : SOk k) :
    chartFrame S (A.act f) = chartFrame S f := by
  show (fun i => InnerProductSpace.gramSchmidtNormed ℝ (fun i => coordVec S (A.act f) i) i)
      = (fun i => InnerProductSpace.gramSchmidtNormed ℝ (fun i => coordVec S f i) i)
  refine congrArg (fun l : Fin k → Amb (k+m) =>
    fun i => InnerProductSpace.gramSchmidtNormed ℝ l i) ?_
  exact funext fun i => coordVec_soActFun S f i A


/-! ## Continuity of the coordinate vectors and of the evaluation -/

theorem continuousOn_coordVec (S : ChartIdx k m) (i : Fin k) :
    ContinuousOn (fun f : Stiefel k m => coordVec S f i) (chartSet S) := by
  have hinv : ContinuousOn (fun f : Stiefel k m => (frameMatrix S f.1)⁻¹) (chartSet S) :=
    (continuousOn_matrix_inv k).comp (continuous_frameMatrix S).continuousOn
      (fun f hf => hf)
  have hterm : ∀ j : Fin k, ContinuousOn (fun f : Stiefel k m =>
      ((frameMatrix S f.1)⁻¹ : Matrix (Fin k) (Fin k) ℝ) j i
        • (f.1 j : Amb (k+m))) (chartSet S) := by
    intro j
    have h1 : ContinuousOn (fun f : Stiefel k m =>
        ((frameMatrix S f.1)⁻¹ : Matrix (Fin k) (Fin k) ℝ) j i) (chartSet S) :=
      (continuous_apply i).comp_continuousOn ((continuous_apply j).comp_continuousOn hinv)
    have h2 : ContinuousOn (fun f : Stiefel k m => (f.1 j : Amb (k+m))) (chartSet S) :=
      (continuous_apply j).comp_continuousOn continuous_subtype_val.continuousOn
    exact continuous_smul.comp_continuousOn (h1.prodMk h2)
  have := continuousOn_finsetSum Finset.univ (fun j _ => hterm j)
  simpa only [coordVec] using this

theorem continuousOn_coordEval (S : ChartIdx k m) :
    ContinuousOn (fun p : Stiefel k m × Amb k => coordEval S p.1 p.2) (chartSet S ×ˢ Set.univ) := by
  rw [show (fun p : Stiefel k m × Amb k => coordEval S p.1 p.2)
      = fun p => ∑ i, EuclideanSpace.proj i p.2 • coordVec S p.1 i from by
    funext p; rw [coordEval]; rfl]
  refine continuousOn_finsetSum _ fun i _ => ?_
  have h1 : ContinuousOn (fun p : Stiefel k m × Amb k => EuclideanSpace.proj i p.2)
      (chartSet S ×ˢ Set.univ) :=
    ((EuclideanSpace.proj i).continuous.comp continuous_snd).continuousOn
  have h2 : ContinuousOn (fun p : Stiefel k m × Amb k => coordVec S p.1 i)
      (chartSet S ×ˢ Set.univ) :=
    (continuousOn_coordVec S i).comp continuous_fst.continuousOn (fun p hp => hp.1)
  exact continuous_smul.comp_continuousOn (h1.prodMk h2)


/-! ## The descended evaluation over a chart, and its gluing -/

theorem exists_continuous_evalChart (k m : ℕ) (S : ChartIdx k m) :
    ∃ g : C(↥(baseSet S) × Amb k, Amb (k+m)),
      ∀ (f : Stiefel k m) (hf : f ∈ chartSet S) (v : Amb k),
        g (⟨Quotient.mk'' f, (mem_baseSet_iff S f).mpr hf⟩, v) = coordEval S f v := by
  classical
  have hpre : (Quotient.mk'' ⁻¹' (baseSet S : Set (OG k m))) = chartSet S := by
    ext f
    rw [Set.mem_preimage, mem_baseSet_iff]
  have hchart : Continuous fun p : ↥(chartSet S) × Amb k =>
      coordEval S (p.1 : Stiefel k m) p.2 := by
    have h := continuousOn_coordEval (k := k) (m := m) S
    rw [continuousOn_iff_continuous_domRestrict] at h
    have h2 : Continuous fun p : ↥(chartSet S) × Amb k =>
        ((chartSet S ×ˢ Set.univ).domRestrict
          (fun p : Stiefel k m × Amb k => coordEval S p.1 p.2)) ⟨(p.1, p.2), ⟨p.1.2, trivial⟩⟩ :=
      h.comp (((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk _)
    simpa using h2
  have hsub : Continuous fun p : ↥(Quotient.mk'' ⁻¹' (baseSet S : Set (OG k m))) × Amb k =>
      coordEval S (p.1 : Stiefel k m) p.2 := by
    rw [hpre]
    exact hchart
  let gfun : ↥(baseSet S) × Amb k → Amb (k+m) :=
    fun p => coordEval S (Quotient.out (p.1 : OG k m)) p.2
  have hg : Continuous gfun := by
    refine (Topology.IsQuotientMap.restrictPreimage_isOpen
      (s := (baseSet S : Set (OG k m))) isQuotientMap_quotient_mk' (isOpen_baseSet S)).continuous_lift_prod_left ?_
    have hfun2 : ∀ p : ↥(Quotient.mk'' ⁻¹' (baseSet S : Set (OG k m))) × Amb k,
        gfun (((baseSet S : Set (OG k m)).restrictPreimage
          (Quotient.mk'' : Stiefel k m → OG k m)) p.1, p.2)
          = coordEval S (p.1 : Stiefel k m) p.2 := by
      intro p
      show coordEval S (Quotient.out (Quotient.mk'' (p.1 : Stiefel k m))) p.2
        = coordEval S (p.1 : Stiefel k m) p.2
      obtain ⟨A, hA⟩ := Quotient.exact
        (Quotient.out_eq (s := grassmannSetoid k m) (Quotient.mk'' (p.1 : Stiefel k m)))
      conv_rhs => rw [hA, coordEval_soActFun]
    exact hsub.congr fun p => (hfun2 p).symm
  refine ⟨⟨gfun, hg⟩, ?_⟩
  intro f hf v
  show coordEval S (Quotient.out (Quotient.mk'' f)) v = coordEval S f v
  obtain ⟨A, hA⟩ := Quotient.exact (Quotient.out_eq (s := grassmannSetoid k m) (Quotient.mk'' f))
  conv_rhs => rw [hA, coordEval_soActFun]


/-- **The evaluation of the fibre coordinate over a point of the chart `S`**, as a continuous map
on `baseSet S × Amb k`: the vector of the plane with `S`-coordinates `v`.  It is the descent of
`coordEval S` along the quotient map `Stiefel k m → OG k m`, which is why it exists as a
continuous map (`exists_continuous_evalChart`). -/
noncomputable def evalChart (S : ChartIdx k m) : C(↥(baseSet S) × Amb k, Amb (k+m)) :=
  Classical.choose (exists_continuous_evalChart k m S)

theorem evalChart_spec (S : ChartIdx k m) (x : ↥(baseSet S)) (f : Stiefel k m)
    (hf : f ∈ chartSet S) (hx : (x : OG k m) = Quotient.mk'' f) (v : Amb k) :
    evalChart S (x, v) = coordEval S f v := by
  have hxe : (⟨Quotient.mk'' f, (mem_baseSet_iff S f).mpr hf⟩ : ↥(baseSet S)) = x :=
    Subtype.ext hx.symm
  obtain rfl : x = ⟨Quotient.mk'' f, (mem_baseSet_iff S f).mpr hf⟩ := hxe.symm
  exact Classical.choose_spec (exists_continuous_evalChart k m S) f hf v

/-- **The evaluation is compatible with the transition functions**: the same vector is obtained
from the two charts `S`, `T` (this is the statement that the fibre coordinate of the tautological
bundle is well defined). -/
theorem evalChart_glue (S T : ChartIdx k m) (x : OG k m) (hx : x ∈ baseSet S ∩ baseSet T)
    (v : Amb k) :
    evalChart S (⟨x, hx.1⟩, v) = evalChart T (⟨x, hx.2⟩, coordChange S T x v) := by
  obtain ⟨f₁, hf₁, hx₁⟩ := hx.1
  obtain ⟨f₂, hf₂, hx₂⟩ := hx.2
  have hT : f₁ ∈ chartSet T :=
    chartSet_saturated T hf₂ (Quotient.exact (hx₂.trans hx₁.symm))
  have hxT : ((⟨x, hx.2⟩ : ↥(baseSet T)) : OG k m) = Quotient.mk'' f₁ := hx₁.symm
  have hc : coordChange S T x v = coordChangeAux S T f₁ v := by
    have h := coordChange_mk S T f₁
    rw [hx₁] at h
    exact DFunLike.congr_fun h v
  rw [evalChart_spec S ⟨x, hx.1⟩ f₁ hf₁ hx₁.symm v, evalChart_spec T ⟨x, hx.2⟩ f₁ hT hxT
    (coordChange S T x v), hc, coordEval_coordChangeAux S T f₁ hf₁ hT v]

end

end Work.ThomBordism.Grassmann
