import Mathlib
import Submission.Work.Tubular.Defs
import Submission.Work.Tubular.NormalFrame
import Submission.Work.Tubular.Rank
import Submission.Work.ThomBordism.PontryaginThom.NormalData
import Submission.Work.ThomBordism.PontryaginThom.exists_normalData_of_immersion

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

/-!
# The normal total space is the total space of the normal bundle of an immersion

`Work.Tubular.NormalTotal E` is the concrete model of the normal bundle of an embedding
`E : EmbeddingData V (8 + k)`: the pairs `(x, w)` with `x ∈ V` and `w` in the orthogonal complement
`ν_x ⊆ ℝ^{8+k}` of the tangent space.  The Pontryagin–Thom chapter models the *same* bundle as
gluing data (`Work.ThomBordism.PontryaginThom.NormalData V k E.e`, a
`Work.TangentClasses.RealBundle`): a cover of `V` by charts, a projection `P i x` onto a complement
of the tangent plane with kernel exactly `im (d E.e_x)`, an insertion `I i x` with `P i x ∘ I i x =
id`, and the coherence `ker P i x` is independent of the chart.

This file proves `Work.Tubular.normalTotalIso`: the two models are homeomorphic, by the map

  `Φ ⟨x, v⟩ = (x, orthInj (frame E.e i x) (I i x v))`   (`i = indexAt x`),

where `orthInj A = 1 - orthProj A` is the matrix orthogonal projection onto the complement of the
plane spanned by the frame `A` (`Work.ThomBordism.PontryaginThom.Orthogonal`).  The facts that make
this work are:

* `range_orthInj_frame`: in the coordinates `Fin (8+k) → ℝ`, the range of `orthInj A` is the
  coordinate image of the normal space `ν_x` — the bridge between the matrix algebra of
  `orthInj`/`coeffMap` and the inner product space `Euc (8+k)`;
* `orthInj_eucToFun_eq_self_iff` and `P_orthInj`: `orthInj A` is the orthogonal projection onto
  `ν_x`, and the abstract projection `P i x` of the gluing data agrees with any representative
  modulo the (chart independent) tangent plane;
* `normalChartVec_agree`: the parametrisation is compatible with the transition functions of the
  gluing data, so that `Φ` is continuous in the glued topology and is inverted by
  `q ↦ (q.1, P (indexAt q.1) q.1 q.2)`.
-/

open scoped Manifold ContDiff Topology
open Function Topology

namespace Work.Tubular

open Work.ThomBordism.PontryaginThom Work.ThomBordism.Grassmann

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-! ## The linear algebra of the orthogonal complement of the plane of a frame -/

/-- The injectivity of the coordinate identification `(Fin n → ℝ) → Euc n`. -/
theorem funToEuc_injective (n : ℕ) : Function.Injective (funToEuc n) := by
  intro a b h
  have := congrArg (eucToFun n) h
  simpa using this

/-- The coordinate inner product of the Euclidean space: on the coordinates `Fin n → ℝ` of `Euc n`,
`⟪x, y⟫ = ∑ r, y r * (eucToFun n x) r`. -/
theorem inner_funToEuc_eq_sum (n : ℕ) (x : Euc n) (w : Fin n → ℝ) :
    inner ℝ x (funToEuc n w) = ∑ r, w r * eucToFun n x r := by
  rw [PiLp.inner_apply]
  simp [funToEuc_apply]

/-- **The matrix identity `Aᵀ (1 - P) = 0` in coordinates**: `orthInj A u` is orthogonal to every
vector of the frame (in the coordinate form of the standard inner product). -/
theorem sum_frameMat_mul_orthInj {k : ℕ} (A : Fin 8 → Euc (8 + k))
    (hA : LinearIndependent ℝ A) (u : Fin (8 + k) → ℝ) (l : Fin 8) :
    ∑ r, frameMat A r l * (orthInj A u) r = 0 := by
  have hmat : (frameMat A).transpose * (1 - orthMat A) = 0 :=
    transpose_frameMat_mul_orthInj A hA
  have h2 : ((frameMat A).transpose).mulVec ((1 - orthMat A).mulVec u) = 0 := by
    have h := congrArg (fun M => M.mulVec u) hmat
    rwa [mulVec_mulVec_eq, Matrix.zero_mulVec] at h
  have h4 : (1 - orthMat A).mulVec u = orthInj A u := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    simp [orthInj, orthProj]
  have h3 : ((frameMat A).transpose).mulVec (orthInj A u) = 0 := by
    rwa [h4] at h2
  have h5 := congrFun h3 l
  rw [mulVec_apply_sum'] at h5
  simpa [Matrix.transpose_apply] using h5

/-- **The orthogonal complement of the plane of a frame, in coordinates.**  For a linearly
independent frame `A : Fin 8 → ℝ^{8+k}`, the range of the matrix orthogonal insertion `orthInj A`
is, after the identification `funToEuc : (Fin (8+k) → ℝ) ≅ ℝ^{8+k}`, the orthogonal complement of
the span of `A`. -/
theorem map_funToEuc_orthInj_range {k : ℕ} (A : Fin 8 → Euc (8 + k))
    (hA : LinearIndependent ℝ A) :
    Submodule.map (funToEuc (8 + k)).toLinearMap (LinearMap.range (orthInj A))
      = (Submodule.span ℝ (Set.range A))ᗮ := by
  have hinj : Function.Injective (funToEuc (8 + k)) := funToEuc_injective (8 + k)
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro v ⟨w, hw, rfl⟩
    obtain ⟨u, rfl⟩ := hw
    rw [Submodule.mem_orthogonal]
    intro z hz
    refine Submodule.span_induction
      (p := fun z _ => inner ℝ z (funToEuc (8 + k) (orthInj A u)) = 0) ?_ ?_ ?_ ?_ hz
    · rintro y ⟨l, rfl⟩
      rw [inner_funToEuc_eq_sum]
      simpa [frameMat, mul_comm] using sum_frameMat_mul_orthInj A hA u l
    · simp
    · intro x y hx hy ihx ihy
      rw [inner_add_left, ihx, ihy, add_zero]
    · intro a x hx ih
      rw [inner_smul_left, ih, mul_zero]
  · have h1 : Module.finrank ℝ ↥(LinearMap.range (orthInj A)) = k := by
      have hker : (orthInj A).ker = (coeffMap A).range := ker_orthInj A hA
      have hfin : Module.finrank ℝ ↥((coeffMap A).range) = 8 := by
        rw [LinearMap.finrank_range_of_inj (coeffMap_injective_of_linearIndependent A hA),
          Module.finrank_fin_fun ℝ]
      have hfr := LinearMap.finrank_range_add_finrank_ker (orthInj A)
      rw [hker, hfin, Module.finrank_fin_fun ℝ] at hfr
      omega
    have h2 : Module.finrank ℝ ↥((Submodule.span ℝ (Set.range A))ᗮ) = k := by
      have hfr := Submodule.finrank_add_finrank_orthogonal (Submodule.span ℝ (Set.range A))
      rw [finrank_span_eq_card hA, Fintype.card_fin, finrank_euclideanSpace_fin] at hfr
      omega
    rw [← (Submodule.equivMapOfInjective (funToEuc (8 + k)).toLinearMap hinj
      (LinearMap.range (orthInj A))).finrank_eq, h1, h2]

/-- The linear map `orthInj A` is idempotent: it is the orthogonal projection onto the complement
of the plane. -/
theorem orthInj_idem {k : ℕ} (A : Fin 8 → Euc (8 + k)) (hA : LinearIndependent ℝ A)
    (u : Fin (8 + k) → ℝ) : orthInj A (orthInj A u) = orthInj A u := by
  have hp : orthProj A (orthProj A u) = orthProj A u := by
    rw [orthProj, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, ← mulVec_mulVec_eq,
      orthMat_idem A hA]
  have hstep : ∀ z : Fin (8 + k) → ℝ, orthInj A z = z - orthProj A z := by
    intro z
    simp [orthInj, LinearMap.sub_apply]
  rw [hstep (orthInj A u), hstep (u), map_sub, hp, sub_self, sub_zero]


/-- The injectivity of the coordinate identification `Euc n → (Fin n → ℝ)`. -/
theorem eucToFun_injective (n : ℕ) : Function.Injective (eucToFun n) := by
  intro a b h
  have := congrArg (funToEuc n) h
  simpa using this

/-- Mapping coordinates to the Euclidean space and back is the identity on submodules. -/
theorem map_eucToFun_map_funToEuc {n : ℕ} (S : Submodule ℝ (Fin n → ℝ)) :
    Submodule.map (eucToFun n).toLinearMap (Submodule.map (funToEuc n).toLinearMap S) = S := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hx
    simpa using hz
  · intro y hy
    exact ⟨funToEuc n y, Submodule.mem_map_of_mem hy, by simp⟩

/-! ## The normal space is the range of the matrix orthogonal insertion -/

/-- The frame of an embedding is linearly independent at every point of a chart (the derivative of
an embedding is injective). -/
theorem frame_linearIndependent_at (E : EmbeddingData V (8 + k))
    (i : atlas (Euc 8) V.pt) {x : V.pt} (hx : x ∈ i.1.source) :
    LinearIndependent ℝ (frame E.e i x) :=
  frame_linearIndependent E.e (E.smooth.of_le (by simp)) E.injective_mfderiv i hx

/-- **The coordinate image of the normal space is the range of the matrix orthogonal insertion.**
This is the bridge between the concrete normal bundle (`normalSpace E x`, defined by the inner
product of `Euc (8+k)`) and the matrix algebra of `Work.ThomBordism.PontryaginThom.orthInj`. -/
theorem range_orthInj_frame (E : EmbeddingData V (8 + k)) (i : atlas (Euc 8) V.pt)
    {x : V.pt} (hx : x ∈ i.1.source) :
    LinearMap.range (orthInj (frame E.e i x))
      = Submodule.map (eucToFun (8 + k)).toLinearMap (normalSpace E x) := by
  have hspan := frame_span_eq_tangentSpace E i hx
  have hA := frame_linearIndependent_at E i hx
  have h1 := map_funToEuc_orthInj_range (frame E.e i x) hA
  have h2 := congrArg (Submodule.map (eucToFun (8 + k)).toLinearMap) h1
  rw [map_eucToFun_map_funToEuc, hspan] at h2
  simpa [normalSpace] using h2

/-- **A normal vector is fixed by the orthogonal projection of the frame**, in coordinates. -/
theorem orthInj_eucToFun_eq_self_iff (E : EmbeddingData V (8 + k)) (i : atlas (Euc 8) V.pt)
    {x : V.pt} (hx : x ∈ i.1.source) (w : Euc (8 + k)) :
    orthInj (frame E.e i x) (eucToFun (8 + k) w) = eucToFun (8 + k) w
      ↔ w ∈ normalSpace E x := by
  have h1 := range_orthInj_frame E i hx
  have hA := frame_linearIndependent_at E i hx
  constructor
  · intro h
    have hmem : eucToFun (8 + k) w
        ∈ Submodule.map (eucToFun (8 + k)).toLinearMap (normalSpace E x) := by
      rw [← h1]
      exact ⟨eucToFun (8 + k) w, h⟩
    obtain ⟨u, hu, hu'⟩ := hmem
    have : u = w := eucToFun_injective (8 + k) hu'
    rwa [this] at hu
  · intro hw
    have hmem : eucToFun (8 + k) w ∈ LinearMap.range (orthInj (frame E.e i x)) := by
      rw [h1]
      exact Submodule.mem_map_of_mem hw
    obtain ⟨u, hu⟩ := hmem
    rw [← hu]
    exact orthInj_idem (frame E.e i x) hA u

/-! ## The gluing data of the normal bundle and the concrete normal space -/

/-- The insertion `I i x` of the gluing data is a right inverse of the projection `P i x`. -/
theorem P_I_apply (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (x : V.pt) (w : Fin k → ℝ) :
    (ND.D.P i x) ((ND.D.I i x) w) = w := by
  have h2 := congrArg (fun (f : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ)) => f w) (ND.D.P_comp_I i x)
  simpa using h2

/-- **The projection of the gluing data agrees with any representative modulo the plane**: `orthInj`
and the identity differ by `orthProj A z`, which lies in the plane `im (d E.e_x) = ker (P i x)`. -/
theorem P_orthInj (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    {i : CoverIdx V k} {x : V.pt} (hx : x ∈ ND.D.baseSet i) (z : Fin (8 + k) → ℝ) :
    (ND.D.P i x) (orthInj (frame E.e (coverChart i) x) z) = (ND.D.P i x) z := by
  have hmem : orthInj (frame E.e (coverChart i) x) z - z
      ∈ LinearMap.ker ((ND.D.P i x : (Fin (8 + k) → ℝ) →ₗ[ℝ] (Fin k → ℝ))) := by
    rw [ND.ker_eq_range i.1 i.2 x hx]
    have hsub : orthInj (frame E.e (coverChart i) x) z - z
        = -orthProj (frame E.e (coverChart i) x) z := by
      simp [orthInj, LinearMap.sub_apply]
    rw [hsub]
    exact neg_mem (range_orthProj_le (frame E.e (coverChart i) x) ⟨z, rfl⟩)
  have h0 : ((ND.D.P i x : (Fin (8 + k) → ℝ) →ₗ[ℝ] (Fin k → ℝ))
      (orthInj (frame E.e (coverChart i) x) z)
        - (ND.D.P i x : (Fin (8 + k) → ℝ) →ₗ[ℝ] (Fin k → ℝ)) z) = 0 := by
    rw [← map_sub]
    exact LinearMap.mem_ker.mp hmem
  exact sub_eq_zero.mp h0

/-- **The orthogonal projection kills the plane**, so the insertion `I i x` of the gluing data may
be replaced by any vector congruent to it modulo the plane. -/
theorem orthInj_I_P (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    {i : CoverIdx V k} {x : V.pt} (hx : x ∈ ND.D.baseSet i) (z : Fin (8 + k) → ℝ) :
    orthInj (frame E.e (coverChart i) x) ((ND.D.I i x) ((ND.D.P i x) z))
      = orthInj (frame E.e (coverChart i) x) z := by
  have hsrc := ND.baseSet_sub i.1 i.2 x hx
  have hA := frame_linearIndependent_at E (coverChart i) hsrc
  have hmem : (ND.D.I i x) ((ND.D.P i x) z) - z
      ∈ LinearMap.ker (orthInj (frame E.e (coverChart i) x)) := by
    rw [ker_orthInj _ hA, ← ND.ker_eq_range i.1 i.2 x hx]
    rw [LinearMap.mem_ker]
    change (ND.D.P i x) ((ND.D.I i x) ((ND.D.P i x) z) - z) = 0
    rw [map_sub, P_I_apply E ND i x ((ND.D.P i x) z), sub_self]
  have h0 : orthInj (frame E.e (coverChart i) x) ((ND.D.I i x) ((ND.D.P i x) z))
      - orthInj (frame E.e (coverChart i) x) z = 0 := by
    rw [← map_sub]
    exact LinearMap.mem_ker.mp hmem
  exact sub_eq_zero.mp h0

/-- **The projection `P i x` is injective on normal vectors**: the only normal vector projecting to
`0` is `0`, because `ker (P i x)` is the tangent plane and `T_x ∩ ν_x = 0`. -/
theorem eq_of_P_eq_of_mem_normalSpace (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    {i : CoverIdx V k} {x : V.pt} (hx : x ∈ ND.D.baseSet i) {z z' : Fin (8 + k) → ℝ}
    (hz : funToEuc (8 + k) z ∈ normalSpace E x)
    (hz' : funToEuc (8 + k) z' ∈ normalSpace E x)
    (h : (ND.D.P i x) z = (ND.D.P i x) z') : z = z' := by
  have hsrc := ND.baseSet_sub i.1 i.2 x hx
  have hmem : z - z' ∈ LinearMap.range (coeffMap (frame E.e (coverChart i) x)) := by
    rw [← ND.ker_eq_range i.1 i.2 x hx]
    rw [LinearMap.mem_ker]
    change (ND.D.P i x) (z - z') = 0
    rw [map_sub, h, sub_self]
  rw [range_coeffMap_frame_eq_tangentSpace E (coverChart i) hsrc] at hmem
  obtain ⟨u, hu, hu'⟩ := hmem
  have hu'' : eucToFun (8 + k) u = z - z' := by simpa using hu'
  have huν : u ∈ normalSpace E x := by
    have h1 : funToEuc (8 + k) (z - z') = u := by
      rw [← hu'']
      exact funToEuc_eucToFun (8 + k) u
    rw [← h1]
    simpa using sub_mem hz hz'
  have h0 : u = 0 := by
    have hinf : u ∈ tangentSpace E x ⊓ normalSpace E x := ⟨hu, huν⟩
    rw [tangentSpace_inf_normalSpace E x] at hinf
    simpa using hinf
  have : z - z' = 0 := by
    have h3 : eucToFun (8 + k) u = 0 := by rw [h0, map_zero]
    rw [← hu'', h3]
  exact sub_eq_zero.mp this

/-! ## The parametrisation of the normal fibre in a chart -/

/-- **The concrete normal vector attached to a vector of the gluing data in the chart `i`**: its
fibre coordinates are read in the chart `i` and the resulting ambient vector is projected
orthogonally onto `ν_x`. -/
noncomputable def normalChartVec (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (x : V.pt) (v : Fin k → ℝ) : Euc (8 + k) :=
  funToEuc (8 + k) (orthInj (frame E.e (coverChart i) x) ((ND.D.I i x) v))

/-- The coordinate form of `normalChartVec`. -/
theorem eucToFun_normalChartVec (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (x : V.pt) (v : Fin k → ℝ) :
    eucToFun (8 + k) (normalChartVec E ND i x v)
      = orthInj (frame E.e (coverChart i) x) ((ND.D.I i x) v) := by
  rw [normalChartVec]
  exact eucToFun_funToEuc (8 + k) _

theorem normalChartVec_mem (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) (v : Fin k → ℝ) :
    normalChartVec E ND i x v ∈ normalSpace E x := by
  have hsrc := ND.baseSet_sub i.1 i.2 x hx
  have h1 := range_orthInj_frame E (coverChart i) hsrc
  have hmem : orthInj (frame E.e (coverChart i) x) ((ND.D.I i x) v)
      ∈ Submodule.map (eucToFun (8 + k)).toLinearMap (normalSpace E x) := by
    rw [← h1]
    exact ⟨_, rfl⟩
  obtain ⟨u, hu, hu'⟩ := hmem
  have hu'' : eucToFun (8 + k) u = orthInj (frame E.e (coverChart i) x) ((ND.D.I i x) v) := by
    simpa using hu'
  have h2 : normalChartVec E ND i x v = u := by
    have h3 : funToEuc (8 + k) (eucToFun (8 + k) u) = u := funToEuc_eucToFun (8 + k) u
    rw [hu''] at h3
    exact h3
  rw [h2]
  exact hu

/-- **The parametrisation is compatible with the transition functions of the gluing data**: reading
the same fibre point in two charts gives the same normal vector. -/
theorem normalChartVec_agree (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    {i j : CoverIdx V k} {x : V.pt} (hi : x ∈ ND.D.baseSet i) (hj : x ∈ ND.D.baseSet j)
    (v : Fin k → ℝ) :
    normalChartVec E ND j x v
      = normalChartVec E ND i x ((ND.D.P i x) ((ND.D.I j x) v)) := by
  have hmem1 : funToEuc (8 + k) (eucToFun (8 + k) (normalChartVec E ND j x v))
      ∈ normalSpace E x := by
    rw [funToEuc_eucToFun]
    exact normalChartVec_mem E ND j hj v
  have hmem2 : funToEuc (8 + k)
      (eucToFun (8 + k) (normalChartVec E ND i x ((ND.D.P i x) ((ND.D.I j x) v))))
      ∈ normalSpace E x := by
    rw [funToEuc_eucToFun]
    exact normalChartVec_mem E ND i hi _
  have key : (ND.D.P i x) (eucToFun (8 + k) (normalChartVec E ND j x v))
      = (ND.D.P i x) (eucToFun (8 + k)
          (normalChartVec E ND i x ((ND.D.P i x) ((ND.D.I j x) v)))) := by
    rw [eucToFun_normalChartVec, eucToFun_normalChartVec]
    -- the two normal representatives have the same `P i x`-image
    have hleft : (ND.D.P i x) (orthInj (frame E.e (coverChart j) x) ((ND.D.I j x) v))
        = (ND.D.P i x) ((ND.D.I j x) v) := by
      have hker := ND.D.ker_agree i j x hi hj
      have hmem : orthInj (frame E.e (coverChart j) x) ((ND.D.I j x) v) - (ND.D.I j x) v
          ∈ LinearMap.ker ((ND.D.P i x : (Fin (8 + k) → ℝ) →ₗ[ℝ] (Fin k → ℝ))) := by
        rw [hker, ND.ker_eq_range j.1 j.2 x hj]
        have hsub : orthInj (frame E.e (coverChart j) x) ((ND.D.I j x) v) - (ND.D.I j x) v
            = -orthProj (frame E.e (coverChart j) x) ((ND.D.I j x) v) := by
          simp [orthInj, LinearMap.sub_apply]
        rw [hsub]
        exact neg_mem (range_orthProj_le (frame E.e (coverChart j) x) ⟨_, rfl⟩)
      have h0 : ((ND.D.P i x : (Fin (8 + k) → ℝ) →ₗ[ℝ] (Fin k → ℝ))
          (orthInj (frame E.e (coverChart j) x) ((ND.D.I j x) v))
            - (ND.D.P i x : (Fin (8 + k) → ℝ) →ₗ[ℝ] (Fin k → ℝ))
              ((ND.D.I j x) v)) = 0 := by
        rw [← map_sub]
        exact LinearMap.mem_ker.mp hmem
      exact sub_eq_zero.mp h0
    rw [hleft, P_orthInj E ND hi]
    have hPI := P_I_apply E ND i x ((ND.D.P i x) ((ND.D.I j x) v))
    exact hPI.symm
  exact eucToFun_injective (8 + k)
    (eq_of_P_eq_of_mem_normalSpace E ND hi hmem1 hmem2 key)

/-! ## The two maps -/

/-- **The parametrisation of the normal total space by the total space of the gluing data**: read
the fibre point in the chart `indexAt x` and project it orthogonally onto `ν_x`. -/
noncomputable def toNormalTotal (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) :
    ND.D.toRealBundle.TotalSpace → NormalTotal E :=
  fun p => ⟨(p.1, normalChartVec E ND (ND.D.indexAt p.1) p.1 p.2),
    normalChartVec_mem E ND (ND.D.indexAt p.1) (ND.D.mem_baseSet_at p.1) p.2⟩

/-- **The inverse parametrisation**: read the normal vector in the chart `indexAt x` with the
projection `P` of the gluing data. -/
noncomputable def ofNormalTotal (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) :
    NormalTotal E → ND.D.toRealBundle.TotalSpace :=
  fun q => ⟨q.1.1, (ND.D.P (ND.D.indexAt q.1.1) q.1.1) (eucToFun (8 + k) q.1.2)⟩

theorem ofNormalTotal_toNormalTotal (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (p : ND.D.toRealBundle.TotalSpace) :
    ofNormalTotal E ND (toNormalTotal E ND p) = p := by
  have hmem := ND.D.mem_baseSet_at p.1
  have h1 : (ND.D.P (ND.D.indexAt p.1) p.1)
      (orthInj (frame E.e (coverChart (ND.D.indexAt p.1)) p.1)
        ((ND.D.I (ND.D.indexAt p.1) p.1) p.2)) = p.2 := by
    rw [P_orthInj E ND hmem]
    exact P_I_apply E ND (ND.D.indexAt p.1) p.1 p.2
  show (⟨p.1, (ND.D.P (ND.D.indexAt p.1) p.1)
      (eucToFun (8 + k) (normalChartVec E ND (ND.D.indexAt p.1) p.1 p.2))⟩ :
        ND.D.toRealBundle.TotalSpace) = p
  rw [eucToFun_normalChartVec, h1]

theorem toNormalTotal_ofNormalTotal (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (q : NormalTotal E) :
    toNormalTotal E ND (ofNormalTotal E ND q) = q := by
  have hmem := ND.D.mem_baseSet_at q.1.1
  have hsrc : q.1.1 ∈ (coverChart (ND.D.indexAt q.1.1)).1.source :=
    ND.baseSet_sub _ _ _ hmem
  have hz : orthInj (frame E.e (coverChart (ND.D.indexAt q.1.1)) q.1.1)
      (eucToFun (8 + k) q.1.2) = eucToFun (8 + k) q.1.2 :=
    (orthInj_eucToFun_eq_self_iff E (coverChart (ND.D.indexAt q.1.1)) hsrc q.1.2).mpr q.2
  have h2 := orthInj_I_P E ND hmem (eucToFun (8 + k) q.1.2)
  have h3 : eucToFun (8 + k) (normalChartVec E ND (ND.D.indexAt q.1.1) q.1.1
      ((ND.D.P (ND.D.indexAt q.1.1) q.1.1) (eucToFun (8 + k) q.1.2))) = eucToFun (8 + k) q.1.2 := by
    rw [eucToFun_normalChartVec, h2, hz]
  apply Subtype.ext
  show ((q.1.1, normalChartVec E ND (ND.D.indexAt q.1.1) q.1.1
      ((ND.D.P (ND.D.indexAt q.1.1) q.1.1) (eucToFun (8 + k) q.1.2))) : V.pt × Euc (8 + k)) = q.1
  rw [Prod.mk.injEq]
  exact ⟨rfl, eucToFun_injective (8 + k) h3⟩

/-! ## Continuity of the two parametrisations -/

/-- The orthogonal insertion of the frame of an embedding is continuous on the chart. -/
theorem continuousOn_orthInj_frame (E : EmbeddingData V (8 + k)) (i : atlas (Euc 8) V.pt) :
    ContinuousOn (fun x => LinearMap.toContinuousLinearMap (orthInj (frame E.e i x)))
      i.1.source := by
  have hproj := continuousOn_orthProjCLM (fun x => frame E.e i x) i.1.source
    (continuousOn_frame E.e (E.smooth.of_le (by simp)) i)
    (fun x hx => frame_linearIndependent_at E i hx)
  have hone : ContinuousOn (fun _ : V.pt => ContinuousLinearMap.id ℝ (Fin (8 + k) → ℝ))
      i.1.source := continuousOn_const
  refine (hone.sub hproj).congr ?_
  intro x hx
  ext v
  simp [orthInj, sub_apply]

theorem continuous_toNormalTotal_ambient (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) :
    Continuous (fun p : ND.D.toRealBundle.TotalSpace =>
      ((p.1, normalChartVec E ND (ND.D.indexAt p.1) p.1 p.2) : V.pt × Euc (8 + k))) := by
  have hpsi : ∀ i : CoverIdx V k, ContinuousOn (fun q : V.pt × (Fin k → ℝ) =>
      ((q.1, normalChartVec E ND i q.1 q.2) : V.pt × Euc (8 + k)))
      ((ND.D.baseSet i) ×ˢ Set.univ) := by
    intro i
    refine ContinuousOn.prodMk continuousOn_fst ?_
    have hCLM : ContinuousOn (fun q : V.pt × (Fin k → ℝ) =>
        LinearMap.toContinuousLinearMap (orthInj (frame E.e (coverChart i) q.1)))
        ((ND.D.baseSet i) ×ˢ Set.univ) :=
      (continuousOn_orthInj_frame E (coverChart i)).comp continuousOn_fst
        (fun q hq => ND.baseSet_sub i.1 i.2 q.1 hq.1)
    have hI : ContinuousOn (fun q : V.pt × (Fin k → ℝ) => (ND.D.I i q.1) q.2)
        ((ND.D.baseSet i) ×ˢ Set.univ) :=
      ((ND.D.continuousOn_I i).comp continuousOn_fst (fun q hq => hq.1)).clm_apply
        continuousOn_snd
    have hmain := (funToEuc (8 + k)).continuous.comp_continuousOn (hCLM.clm_apply hI)
    refine hmain.congr (fun q hq => ?_)
    rw [normalChartVec]
    rfl
  have hOn : ∀ i : CoverIdx V k, ContinuousOn (fun p : ND.D.toRealBundle.TotalSpace =>
      ((p.1, normalChartVec E ND (ND.D.indexAt p.1) p.1 p.2) : V.pt × Euc (8 + k)))
      (ND.D.toRealBundle.localTriv i).source := by
    intro i
    have hmap : Set.MapsTo (fun p : ND.D.toRealBundle.TotalSpace => (ND.D.toRealBundle.localTriv i p))
        (ND.D.toRealBundle.localTriv i).source ((ND.D.baseSet i) ×ˢ Set.univ) := by
      intro p hp
      refine ⟨?_, Set.mem_univ _⟩
      rw [Bundle.Trivialization.coe_fst _ hp]
      show p.1 ∈ ND.D.baseSet i
      exact (VectorBundleCore.mem_localTriv_source _ i p).mp hp
    have hcomp := (hpsi i).comp (ND.D.toRealBundle.localTriv i).continuousOn hmap
    refine hcomp.congr (fun p hp => ?_)
    simp only [Function.comp_apply]
    have hfst : ((ND.D.toRealBundle.localTriv i) p).1 = p.1 :=
      Bundle.Trivialization.coe_fst _ hp
    have hx : p.1 ∈ ND.D.baseSet i := (VectorBundleCore.mem_localTriv_source _ i p).mp hp
    have hcc : (ND.D.toRealBundle.localTriv i p).2
        = (ND.D.P i p.1) ((ND.D.I (ND.D.indexAt p.1) p.1) p.2) := by
      have hpair := VectorBundleCore.localTriv_apply (Z := ND.D.toRealBundle) (i := i) p
      have hcc0 : ((ND.D.toRealBundle.localTriv i) p).2
          = (ND.D.coordChange (ND.D.indexAt p.1) i p.1) p.2 := by
        simpa using congrArg Prod.snd hpair
      rw [hcc0, ND.D.coordChange_of_mem (ND.D.indexAt p.1) i p.1
        ⟨ND.D.mem_baseSet_at p.1, hx⟩, ContinuousLinearMap.comp_apply]
    rw [hfst, hcc]
    exact congrArg (fun w => ((p.1, w) : V.pt × Euc (8 + k)))
      (normalChartVec_agree E ND (i := i) (j := ND.D.indexAt p.1) (x := p.1) hx
        (ND.D.mem_baseSet_at p.1) p.2)
  rw [continuous_iff_continuousAt]
  intro p
  exact (hOn (ND.D.indexAt p.1)).continuousAt
    ((ND.D.toRealBundle.localTriv (ND.D.indexAt p.1)).open_source.mem_nhds
      ((VectorBundleCore.mem_localTriv_source _ (ND.D.indexAt p.1) p).mpr
        (ND.D.mem_baseSet_at p.1)))

theorem continuous_ofNormalTotal (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) :
    Continuous (ofNormalTotal E ND) := by
  have hg : ∀ i : CoverIdx V k, ContinuousOn (fun q : NormalTotal E =>
      ((q.1.1, (ND.D.P i q.1.1) (eucToFun (8 + k) q.1.2)) : V.pt × (Fin k → ℝ)))
      {q : NormalTotal E | q.1.1 ∈ ND.D.baseSet i} := by
    intro i
    refine ContinuousOn.prodMk (continuous_subtype_val.fst.continuousOn) ?_
    refine ContinuousOn.clm_apply ?_ ?_
    · exact (ND.D.continuousOn_P i).comp continuous_subtype_val.fst.continuousOn
        (fun q hq => hq)
    · exact (eucToFun (8 + k)).continuous.comp_continuousOn
        (continuous_subtype_val.snd.continuousOn)
  have hOn : ∀ i : CoverIdx V k, ContinuousOn (ofNormalTotal E ND)
      {q : NormalTotal E | q.1.1 ∈ ND.D.baseSet i} := by
    intro i
    have hcomp : ContinuousOn (fun q : NormalTotal E =>
        (⟨q.1.1, (ND.D.toRealBundle.localTriv i).symm q.1.1
          ((ND.D.P i q.1.1) (eucToFun (8 + k) q.1.2))⟩ :
            ND.D.toRealBundle.TotalSpace))
        {q : NormalTotal E | q.1.1 ∈ ND.D.baseSet i} :=
      (Bundle.Trivialization.continuousOn_symm (ND.D.toRealBundle.localTriv i)).comp
        (hg i) (fun q hq => ⟨hq, Set.mem_univ _⟩)
    refine hcomp.congr (fun q hq => ?_)
    show ofNormalTotal E ND q
      = (⟨q.1.1, (ND.D.toRealBundle.localTriv i).symm q.1.1
          ((ND.D.P i q.1.1) (eucToFun (8 + k) q.1.2))⟩ : ND.D.toRealBundle.TotalSpace)
    have hj : q.1.1 ∈ ND.D.baseSet (ND.D.indexAt q.1.1) := ND.D.mem_baseSet_at q.1.1
    have hkey : (ND.D.P (ND.D.indexAt q.1.1) q.1.1)
        ((ND.D.I i q.1.1) ((ND.D.P i q.1.1) (eucToFun (8 + k) q.1.2)))
          = (ND.D.P (ND.D.indexAt q.1.1) q.1.1) (eucToFun (8 + k) q.1.2) := by
      have hker := ND.D.ker_agree i (ND.D.indexAt q.1.1) q.1.1 hq hj
      have hmem : (ND.D.I i q.1.1) ((ND.D.P i q.1.1) (eucToFun (8 + k) q.1.2))
          - eucToFun (8 + k) q.1.2
          ∈ LinearMap.ker ((ND.D.P (ND.D.indexAt q.1.1) q.1.1 :
              (Fin (8 + k) → ℝ) →ₗ[ℝ] (Fin k → ℝ))) := by
        rw [← hker]
        rw [LinearMap.mem_ker]
        change (ND.D.P i q.1.1) ((ND.D.I i q.1.1)
          ((ND.D.P i q.1.1) (eucToFun (8 + k) q.1.2)) - eucToFun (8 + k) q.1.2) = 0
        rw [map_sub, P_I_apply E ND i q.1.1 ((ND.D.P i q.1.1) (eucToFun (8 + k) q.1.2)),
          sub_self]
      have h0 : ((ND.D.P (ND.D.indexAt q.1.1) q.1.1 :
            (Fin (8 + k) → ℝ) →ₗ[ℝ] (Fin k → ℝ))
          ((ND.D.I i q.1.1) ((ND.D.P i q.1.1) (eucToFun (8 + k) q.1.2)))
            - (ND.D.P (ND.D.indexAt q.1.1) q.1.1) (eucToFun (8 + k) q.1.2)) = 0 := by
        have h2 := LinearMap.mem_ker.mp hmem
        rw [map_sub] at h2
        exact h2
      exact sub_eq_zero.mp h0
    have hsym := VectorBundleCore.localTriv_symm_apply ND.D.toRealBundle i hq
      ((ND.D.P i q.1.1) (eucToFun (8 + k) q.1.2))
    rw [hsym]
    simp only [ComplementData.toRealBundle_coordChange, ComplementData.toRealBundle_indexAt]
    rw [ND.D.coordChange_of_mem i (ND.D.indexAt q.1.1) q.1.1 ⟨hq, hj⟩,
      ContinuousLinearMap.comp_apply]
    exact congrArg (fun w => (⟨q.1.1, w⟩ : ND.D.toRealBundle.TotalSpace)) hkey.symm
  rw [continuous_iff_continuousAt]
  intro q
  refine (hOn (ND.D.indexAt q.1.1)).continuousAt ?_
  exact ((ND.D.isOpen_baseSet (ND.D.indexAt q.1.1)).preimage
    (continuous_subtype_val.fst)).mem_nhds (ND.D.mem_baseSet_at q.1.1)

/-! ## The homeomorphism -/

theorem normalTotalIso {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) :
    Nonempty (ND.D.toRealBundle.TotalSpace ≃ₜ Work.Tubular.NormalTotal E) := by
  have hcontΦ : Continuous (toNormalTotal E ND) :=
    (continuous_toNormalTotal_ambient E ND).subtype_mk _
  exact ⟨{ toFun := toNormalTotal E ND, invFun := ofNormalTotal E ND,
           left_inv := ofNormalTotal_toNormalTotal E ND,
           right_inv := toNormalTotal_ofNormalTotal E ND,
           continuous_toFun := hcontΦ,
           continuous_invFun := continuous_ofNormalTotal E ND }⟩

end

end Work.Tubular
