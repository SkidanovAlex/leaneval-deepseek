import Mathlib
import Submission.Work.Serre.E0SimplexDefs

set_option synthInstance.maxHeartbeats 400000

/-!
# The boundary of the standard simplex as the frontier of the corner body

This file sets up the elementary geometry which identifies the simplicial boundary
`Work.Serre.simplexBdry n ⊆ Δⁿ = stdSimplex ℝ (Fin (n+1))` with the frontier of the *corner body*

`cornerSimplex n = {y : ℝⁿ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1}`,

the convex hull of the origin and the standard basis of `ℝⁿ`.  The identification is the affine
coordinate map

* `simplexProj n : ℝⁿ⁺¹ →ₗ[ℝ] ℝⁿ`,  `x ↦ (x 0, …, x (n-1))` (drop the last barycentric
  coordinate), restricted to `Δⁿ`;
* `simplexLift n : ℝⁿ → ℝⁿ⁺¹`,  `y ↦ (y 0, …, y (n-1), 1 - ∑ y)`, the inverse on the hyperplane
  `∑ x = 1`.

Since `simplexBdry n` is precisely the set of points of `Δⁿ` with a vanishing coordinate, and since
`simplexProj n '' (simplexBdry n) = frontier (cornerSimplex n)`, the projection is a homeomorphism
of `simplexBdry n` onto `frontier (cornerSimplex n)`
(`Work.Serre.simplexBdry_homeo_frontier`, conditional on the description of `interior
(cornerSimplex n)` proved in `Submission/Work/Serre/cornerSimplex_interior.lean`).

Mathlib's gauge rescaling (`exists_homeomorph_image_interior_closure_frontier_eq_unitBall`) then
carries the frontier of the corner body onto the unit sphere, so that `simplexBdry n` is homotopy
equivalent to `Sⁿ⁻¹`; this is the route to the vanishing of the reduced homology of `∂Δⁿ` used in
the E3(a) computation (`Submission/Work/Serre/E3A_PLAN.md` §7–§9).
-/

set_option linter.style.haveILetI false

open Set Finset

namespace Work.Serre

noncomputable section

/-! ## The affine coordinates of the simplex and of the corner body -/

/-- The linear projection `ℝⁿ⁺¹ → ℝⁿ` dropping the last barycentric coordinate. -/
def simplexProj (n : ℕ) : (Fin (n + 1) → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun x := WithLp.toLp 2 (fun i => x (Fin.castSucc i))
  map_add' x y := by ext i; rfl
  map_smul' c x := by ext i; rfl

@[simp] theorem simplexProj_ofLp (n : ℕ) (x : Fin (n + 1) → ℝ) :
    (simplexProj n x).ofLp = fun i => x (Fin.castSucc i) := rfl

@[simp] theorem simplexProj_apply (n : ℕ) (x : Fin (n + 1) → ℝ) (i : Fin n) :
    simplexProj n x i = x (Fin.castSucc i) := rfl

theorem continuous_simplexProj (n : ℕ) : Continuous (simplexProj n) :=
  LinearMap.continuous_of_finiteDimensional _

/-- The section of `simplexProj` which lands in the affine hyperplane `∑ x = 1`. -/
def simplexLift (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) : Fin (n + 1) → ℝ :=
  Fin.snoc (α := fun _ => ℝ) y.ofLp (1 - ∑ i, y i)

@[simp] theorem simplexLift_castSucc (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    simplexLift n y (Fin.castSucc i) = y i := by
  show Fin.snoc (α := fun _ => ℝ) y.ofLp (1 - ∑ i, y i) (Fin.castSucc i) = y.ofLp i
  exact Fin.snoc_castSucc (α := fun _ => ℝ) (1 - ∑ i, y i) y.ofLp i

@[simp] theorem simplexLift_last (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    simplexLift n y (Fin.last n) = 1 - ∑ i, y i := by
  show Fin.snoc (α := fun _ => ℝ) y.ofLp (1 - ∑ i, y i) (Fin.last n) = 1 - ∑ i, y i
  exact Fin.snoc_last (α := fun _ => ℝ) (1 - ∑ i, y i) y.ofLp

theorem simplexProj_lift (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    simplexProj n (simplexLift n y) = y := by
  ext i; simp

theorem simplexLift_sum (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    ∑ i, simplexLift n y i = 1 := by
  rw [Fin.sum_univ_castSucc]; simp

theorem simplexLift_mem_stdSimplex (n : ℕ) {y : EuclideanSpace ℝ (Fin n)}
    (h : ∀ i, 0 ≤ y i) (h1 : ∑ i, y i ≤ 1) :
    simplexLift n y ∈ stdSimplex ℝ (Fin (n + 1)) := by
  refine ⟨fun j => ?_, simplexLift_sum n y⟩
  induction j using Fin.lastCases with
  | last => rw [simplexLift_last]; linarith
  | cast i => rw [simplexLift_castSucc]; exact h i

/-- On the hyperplane `∑ x = 1` the lift is inverse to the projection. -/
theorem simplexLift_proj (n : ℕ) (x : Fin (n + 1) → ℝ) (hx : ∑ i, x i = 1) :
    simplexLift n (simplexProj n x) = x := by
  funext j
  induction j using Fin.lastCases with
  | last =>
    rw [simplexLift_last, simplexProj_ofLp]
    have h := Fin.sum_univ_castSucc x
    rw [hx] at h
    linarith [h]
  | cast i => rw [simplexLift_castSucc]; simp

/-- The form of `simplexLift_proj` for a point of the standard simplex. -/
theorem simplexLift_proj_stdSimplex (n : ℕ) (z : ↥(stdSimplex ℝ (Fin (n + 1)))) :
    simplexLift n (simplexProj n (z.1 : Fin (n + 1) → ℝ)) = (z.1 : Fin (n + 1) → ℝ) := by
  refine simplexLift_proj n (z.1 : Fin (n + 1) → ℝ) ?_
  exact z.2.2

/-- The projection is injective on the standard simplex: the last barycentric coordinate is
recovered as `1 - ∑ i < n`. -/
theorem simplexProj_injective (n : ℕ) {z z' : ↥(stdSimplex ℝ (Fin (n + 1)))}
    (h : simplexProj n z.1 = simplexProj n z'.1) : z = z' := by
  refine Subtype.ext ?_
  rw [← simplexLift_proj_stdSimplex n z, ← simplexLift_proj_stdSimplex n z', h]

/-! ## The corner body -/

/-- The corner body: the convex hull of the origin and the standard basis of `ℝⁿ`. -/
def cornerSimplex (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1}

theorem mem_cornerSimplex {n : ℕ} {y : EuclideanSpace ℝ (Fin n)} :
    y ∈ cornerSimplex n ↔ (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1 := Iff.rfl

/-- The projection of the standard simplex is the corner body. -/
theorem simplexProj_mem_cornerSimplex (n : ℕ) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ stdSimplex ℝ (Fin (n + 1))) : simplexProj n x ∈ cornerSimplex n := by
  refine ⟨fun i => hx.1 (Fin.castSucc i), ?_⟩
  have h := Fin.sum_univ_castSucc x
  rw [hx.2] at h
  have hlast : 0 ≤ x (Fin.last n) := hx.1 _
  have hsum : ∑ i, simplexProj n x i = ∑ i, x (Fin.castSucc i) := rfl
  rw [hsum]; linarith

theorem cornerSimplex_eq_image (n : ℕ) :
    cornerSimplex n = simplexProj n '' (stdSimplex ℝ (Fin (n + 1))) := by
  ext y
  constructor
  · intro hy
    refine ⟨simplexLift n y, simplexLift_mem_stdSimplex n hy.1 hy.2, ?_⟩
    exact simplexProj_lift n y
  · rintro ⟨x, hx, rfl⟩
    exact simplexProj_mem_cornerSimplex n hx

theorem cornerSimplex_convex (n : ℕ) : Convex ℝ (cornerSimplex n) := by
  rw [cornerSimplex_eq_image]
  exact (convex_stdSimplex ℝ (Fin (n + 1))).linear_image (simplexProj n)

theorem cornerSimplex_isCompact (n : ℕ) : IsCompact (cornerSimplex n) := by
  rw [cornerSimplex_eq_image]
  exact (isCompact_stdSimplex ℝ (Fin (n + 1))).image (continuous_simplexProj n)

theorem cornerSimplex_isClosed (n : ℕ) : IsClosed (cornerSimplex n) :=
  (cornerSimplex_isCompact n).isClosed

theorem cornerSimplex_isBounded (n : ℕ) : Bornology.IsBounded (cornerSimplex n) :=
  (cornerSimplex_isCompact n).isBounded

/-- In dimension `0` the corner body is the whole (one-point) space. -/
theorem cornerSimplex_zero : cornerSimplex 0 = univ := by
  ext y; simp [cornerSimplex]

/-- In dimension `0` the interior of the corner body is everything. -/
theorem interior_cornerSimplex_zero : interior (cornerSimplex 0) = univ := by
  rw [cornerSimplex_zero, interior_univ]

/-- The interior of the corner body is nonempty; conditional on the description of the interior
(`Submission/Work/Serre/cornerSimplex_interior.lean`), the point with all coordinates `1/(n+2)`
witnesses it. -/
theorem interior_cornerSimplex_nonempty (n : ℕ)
    (hint : interior (cornerSimplex n) =
      {y : EuclideanSpace ℝ (Fin n) | (∀ i, 0 < y i) ∧ ∑ i, y i < 1}) :
    (interior (cornerSimplex n)).Nonempty := by
  refine ⟨WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ) / (n + 2)), ?_⟩
  rw [hint, mem_ofPred_eq]
  constructor
  · intro i
    show (0 : ℝ) < (1 : ℝ) / (n + 2)
    positivity
  · have h : (∑ i : Fin n,
        (WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ) / (n + 2)) : EuclideanSpace ℝ (Fin n)) i)
        = ∑ _i : Fin n, (1 : ℝ) / (n + 2) := rfl
    rw [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div,
      div_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
    linarith

/-! ## The simplicial boundary -/

theorem isClosed_simplexBdry (n : ℕ) : IsClosed (simplexBdry n) := by
  have h : simplexBdry n = ⋃ j : Fin (n + 1),
      {z : ↥(stdSimplex ℝ (Fin (n + 1))) | z.1 j = 0} := by
    ext z; simp [mem_simplexBdry]
  rw [h]
  exact isClosed_iUnion_of_finite fun j =>
    isClosed_eq ((continuous_apply j).comp continuous_subtype_val) continuous_const

theorem simplexBdry_isCompact (n : ℕ) : IsCompact (simplexBdry n) := by
  haveI : CompactSpace ↥(stdSimplex ℝ (Fin (n + 1))) :=
    isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ (Fin (n + 1)))
  exact (isClosed_simplexBdry n).isCompact

/-! ## The boundary as a frontier -/

/-- **The projection carries the simplicial boundary onto the frontier of the corner body.**

The statement is conditional on the description of the interior of the corner body
(`Submission/Work/Serre/cornerSimplex_interior.lean`), which is the only analytic input. -/
theorem proj_mem_frontier_iff (n : ℕ)
    (hint : interior (cornerSimplex n) =
      {y : EuclideanSpace ℝ (Fin n) | (∀ i, 0 < y i) ∧ ∑ i, y i < 1})
    (z : ↥(stdSimplex ℝ (Fin (n + 1)))) :
    simplexProj n z.1 ∈ frontier (cornerSimplex n) ↔ z ∈ simplexBdry n := by
  have hfr : frontier (cornerSimplex n) = cornerSimplex n \ interior (cornerSimplex n) :=
    (cornerSimplex_isClosed n).frontier_eq
  have hmem : ∀ y : EuclideanSpace ℝ (Fin n), y ∈ interior (cornerSimplex n) ↔
      (∀ i, 0 < y i) ∧ ∑ i, y i < 1 := fun y => by rw [hint, mem_ofPred_eq]
  rw [hfr, Set.mem_sdiff]
  constructor
  · rintro ⟨-, hnot⟩
    by_contra hcon
    rw [mem_simplexBdry] at hcon
    push Not at hcon
    have hpos : ∀ j, 0 < z.1 j := fun j => lt_of_le_of_ne (z.2.1 j) (Ne.symm (hcon j))
    refine hnot ?_
    rw [hmem]
    refine ⟨fun i => hpos (Fin.castSucc i), ?_⟩
    have h := Fin.sum_univ_castSucc z.1
    rw [z.2.2] at h
    have hsum : ∑ i, simplexProj n z.1 i = ∑ i, z.1 (Fin.castSucc i) := rfl
    rw [hsum]; linarith [h, hpos (Fin.last n)]
  · intro hz
    refine ⟨?_, ?_⟩
    · refine ⟨fun i => z.2.1 (Fin.castSucc i), ?_⟩
      have h := Fin.sum_univ_castSucc z.1
      rw [z.2.2] at h
      have hlast : 0 ≤ z.1 (Fin.last n) := z.2.1 _
      have hsum : ∑ i, simplexProj n z.1 i = ∑ i, z.1 (Fin.castSucc i) := rfl
      rw [hsum]; linarith
    · rw [mem_simplexBdry] at hz
      obtain ⟨j, hj⟩ := hz
      intro hcon
      rw [hmem] at hcon
      induction j using Fin.lastCases with
      | last =>
        have hsum : ∑ i, simplexProj n z.1 i = ∑ i, z.1 (Fin.castSucc i) := rfl
        have h := Fin.sum_univ_castSucc z.1
        rw [z.2.2] at h
        rw [hsum] at hcon
        linarith [hcon.2, h, hj]
      | cast i =>
        have hi : simplexProj n z.1 i = 0 := by
          rw [show simplexProj n z.1 i = z.1 (Fin.castSucc i) from rfl, hj]
        linarith [hcon.1 i, hi]

/-- **The simplicial boundary is homeomorphic to the frontier of the corner body.**

Conditional on the description of `interior (cornerSimplex n)`. -/
theorem simplexBdry_homeo_frontier (n : ℕ)
    (hint : interior (cornerSimplex n) =
      {y : EuclideanSpace ℝ (Fin n) | (∀ i, 0 < y i) ∧ ∑ i, y i < 1}) :
    Nonempty (↥(simplexBdry n) ≃ₜ ↥(frontier (cornerSimplex n))) := by
  haveI : CompactSpace ↥(simplexBdry n) :=
    isCompact_iff_compactSpace.mp (simplexBdry_isCompact n)
  have key := proj_mem_frontier_iff n hint
  let F : ↥(simplexBdry n) → ↥(frontier (cornerSimplex n)) :=
    fun z => ⟨simplexProj n z.1, (key z).mpr z.2⟩
  have hFcont : Continuous F := by
    apply Continuous.subtype_mk
    have h : Continuous fun z : ↥(simplexBdry n) => (z.1 : Fin (n + 1) → ℝ) :=
      continuous_subtype_val.comp continuous_subtype_val
    exact (continuous_simplexProj n).comp h
  have hFinj : Function.Injective F := by
    intro z z' hzz'
    exact Subtype.ext (simplexProj_injective n (congrArg Subtype.val hzz'))
  have hFsurj : Function.Surjective F := by
    intro y
    have hy : y.1 ∈ cornerSimplex n :=
      (frontier_subset_iff_isClosed.mpr (cornerSimplex_isClosed n)) y.2
    have hstd : simplexLift n y.1 ∈ stdSimplex ℝ (Fin (n + 1)) :=
      simplexLift_mem_stdSimplex n hy.1 hy.2
    have hbd : (⟨simplexLift n y.1, hstd⟩ : ↥(stdSimplex ℝ (Fin (n + 1)))) ∈ simplexBdry n :=
      (key ⟨simplexLift n y.1, hstd⟩).mp (by rw [simplexProj_lift]; exact y.2)
    exact ⟨⟨⟨simplexLift n y.1, hstd⟩, hbd⟩, Subtype.ext (simplexProj_lift n y.1)⟩
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F ⟨hFinj, hFsurj⟩) hFcont⟩

end

end Work.Serre
