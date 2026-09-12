import Mathlib.Analysis.Convex.Body
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.MetricSpace.Closeds

namespace Commons.Geometry.Convex

open scoped Topology
open Set Filter TopologicalSpace Metric

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Distance between two affine combinations, bounded by the convex combination of the
pointwise distances. -/
lemma dist_affine_le (x y x' y' : V) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    dist (a • x + b • y) (a • x' + b • y') ≤ a * dist x x' + b * dist y y' := by
  calc
    dist (a • x + b • y) (a • x' + b • y') = ‖(a • x + b • y) - (a • x' + b • y')‖ :=
      dist_eq_norm _ _
    _ = ‖a • (x - x') + b • (y - y')‖ := by
      rw [show (a • x + b • y) - (a • x' + b • y') = (a • x - a • x') + (b • y - b • y') by abel,
          ← smul_sub, ← smul_sub]
    _ ≤ ‖a • (x - x')‖ + ‖b • (y - y')‖ := norm_add_le _ _
    _ = |a| * ‖x - x'‖ + |b| * ‖y - y'‖ := by simp [norm_smul]
    _ = a * ‖x - x'‖ + b * ‖y - y'‖ := by rw [abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * dist x x' + b * dist y y' := by rw [← dist_eq_norm, ← dist_eq_norm]

omit [NormedSpace ℝ V] in
/-- The Hausdorff edistance between two nonempty compact sets is finite. -/
lemma hausdorffEDist_ne_top_nonemptyCompacts (C K : NonemptyCompacts V) :
    hausdorffEDist (C : Set V) (K : Set V) ≠ ⊤ :=
  hausdorffEDist_ne_top_of_nonempty_of_bounded C.nonempty K.nonempty
    C.isCompact.isBounded K.isCompact.isBounded

/-- A Hausdorff limit of convex compact sets (i.e. a point in the closure of the set of convex
compact sets) is convex. -/
lemma convex_of_mem_closure_nonemptyCompacts {C : NonemptyCompacts V}
    (hC : C ∈ closure {C : NonemptyCompacts V | Convex ℝ (C : Set V)}) :
    Convex ℝ (C : Set V) := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  let z : V := a • x + b • y
  have hzmem : z ∈ (C : Set V) := by
    -- z ∈ closure C and C is closed
    have hδ : ∀ δ : ℝ, 0 < δ → ∃ w ∈ (C : Set V), dist z w < δ := by
      intro δ hδ
      let η : ℝ := δ / 3
      have hη : 0 < η := by dsimp [η]; linarith
      -- approximate C by a convex compact set K within Hausdorff distance η
      obtain ⟨K, hKconv, hCK⟩ := (Metric.mem_closure_iff.1 hC) η hη
      have hCKhd : hausdorffDist (C : Set V) (K : Set V) < η := by
        simpa [Metric.NonemptyCompacts.dist_eq] using hCK
      have hfin : hausdorffEDist (C : Set V) (K : Set V) ≠ ⊤ :=
        hausdorffEDist_ne_top_nonemptyCompacts C K
      -- approximate x and y by points x', y' of K
      obtain ⟨x', hxK, hxx'⟩ := exists_dist_lt_of_hausdorffDist_lt hx hCKhd hfin
      obtain ⟨y', hyK, hyy'⟩ := exists_dist_lt_of_hausdorffDist_lt hy hCKhd hfin
      -- z' := a • x' + b • y' belongs to K (convexity of K)
      have hzK : a • x' + b • y' ∈ (K : Set V) := by
        exact (convex_iff_add_mem.mp hKconv hxK hyK) ha hb hab
      -- and is close to a point w of C
      have hKC : hausdorffDist (K : Set V) (C : Set V) < η := by
        simpa [hausdorffDist_comm] using hCKhd
      have hfin' : hausdorffEDist (K : Set V) (C : Set V) ≠ ⊤ := by
        simpa [hausdorffEDist_comm] using hfin
      obtain ⟨w, hwC, hzw⟩ := exists_dist_lt_of_hausdorffDist_lt hzK hKC hfin'
      have hzz' : dist (a • x + b • y) (a • x' + b • y') ≤ a * dist x x' + b * dist y y' :=
        dist_affine_le x y x' y' ha hb
      have h1 : a * dist x x' ≤ a * η := mul_le_mul_of_nonneg_left (le_of_lt hxx') ha
      have h2 : b * dist y y' ≤ b * η := mul_le_mul_of_nonneg_left (le_of_lt hyy') hb
      have hzz'η : dist (a • x + b • y) (a • x' + b • y') ≤ η := by
        calc
          dist (a • x + b • y) (a • x' + b • y') ≤ a * dist x x' + b * dist y y' := hzz'
          _ ≤ a * η + b * η := add_le_add h1 h2
          _ = η := by rw [← add_mul, hab]; simp
      refine ⟨w, hwC, ?_⟩
      calc
        dist z w ≤ dist z (a • x' + b • y') + dist (a • x' + b • y') w := dist_triangle _ _ _
        _ < η + η := add_lt_add_of_le_of_lt hzz'η hzw
        _ = 2 * η := by ring
        _ < δ := by dsimp [η] at *; linarith
    have hzcl : z ∈ closure (C : Set V) := Metric.mem_closure_iff.2 hδ
    rw [← C.isCompact.isClosed.closure_eq]
    exact hzcl
  simpa [z] using hzmem

/-- In the Hausdorff metric on nonempty compact sets, convexity is a closed condition. -/
lemma isClosed_convex_nonemptyCompacts :
    IsClosed {C : NonemptyCompacts V | Convex ℝ (C : Set V)} := by
  rw [← closure_subset_iff_isClosed]
  intro C hC
  exact convex_of_mem_closure_nonemptyCompacts hC

/-- The canonical embedding of convex bodies into the nonempty compact sets of `V`. -/
def convexBody_toNonemptyCompacts (K : ConvexBody V) : NonemptyCompacts V :=
  { toCompacts := { carrier := (K : Set V), isCompact' := K.isCompact }
    nonempty' := K.nonempty }

@[simp] lemma coe_convexBody_toNonemptyCompacts (K : ConvexBody V) :
    ((convexBody_toNonemptyCompacts K : NonemptyCompacts V) : Set V) = (K : Set V) :=
  rfl

/-- The embedding preserves the (Hausdorff) distance. -/
lemma dist_convexBody_toNonemptyCompacts (K L : ConvexBody V) :
    dist (convexBody_toNonemptyCompacts K) (convexBody_toNonemptyCompacts L) = dist K L := by
  rw [Metric.NonemptyCompacts.dist_eq, coe_convexBody_toNonemptyCompacts,
    coe_convexBody_toNonemptyCompacts]
  exact (ConvexBody.hausdorffDist_coe K L).symm

/-- The embedding of convex bodies into nonempty compact sets is an isometry. -/
lemma isometry_convexBody_toNonemptyCompacts :
    Isometry (convexBody_toNonemptyCompacts (V := V)) := by
  intro K L
  rw [edist_dist, edist_dist]
  exact congrArg ENNReal.ofReal (dist_convexBody_toNonemptyCompacts K L)

/-- The image of the embedding is exactly the set of convex compact sets. -/
lemma range_convexBody_toNonemptyCompacts :
    range (convexBody_toNonemptyCompacts (V := V)) =
      {C : NonemptyCompacts V | Convex ℝ (C : Set V)} := by
  ext C
  constructor
  · rintro ⟨K, rfl⟩
    simpa using (K.convex : Convex ℝ (K : Set V))
  · intro hconv
    refine ⟨⟨(C : Set V), hconv, C.isCompact, C.nonempty⟩, ?_⟩
    ext x
    simp

/-- The image of `ConvexBody V` inside the (complete) space of nonempty compact sets is closed. -/
lemma isClosed_range_convexBody_toNonemptyCompacts :
    IsClosed (range (convexBody_toNonemptyCompacts (V := V))) := by
  simpa [range_convexBody_toNonemptyCompacts] using (isClosed_convex_nonemptyCompacts (V := V))

end

open scoped Topology

/-- `ConvexBody V`, equipped with the Hausdorff metric, is complete whenever `V` is a complete
normed space. -/
theorem convexBody_complete
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] :
    CompleteSpace (ConvexBody V) := by
  rw [completeSpace_iff_isComplete_range
    (isometry_convexBody_toNonemptyCompacts (V := V)).isUniformInducing]
  exact (isClosed_range_convexBody_toNonemptyCompacts (V := V)).isComplete

end Commons.Geometry.Convex