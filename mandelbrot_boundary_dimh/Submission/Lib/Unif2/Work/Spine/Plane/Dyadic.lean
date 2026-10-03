import Mathlib
import Submission.Lib.Unif2.Commons.Topology.Plane.exists_dyadic_exhaustion_of_isOpen_complex
import Submission.Lib.Unif2.Commons.Topology.Plane.dyadicPolyomino_deformationRetract
import Submission.Lib.Unif2.Commons.Topology.Homotopy.homotopyEquiv_of_deformationRetract
import Submission.Lib.Unif2.Commons.Topology.CWComplex.finiteUnionSegments_oneDimCWComplex
import Submission.Lib.Unif2.Commons.AlgebraicTopology.FundamentalGroup.pi1_equiv_of_homotopyEquiv

set_option linter.style.haveILetI false

set_option maxHeartbeats 800000

/-!
# The dyadic exhaustion of a plane domain and the polyomino spines

This module fixes *one* canonically chosen dyadic exhaustion of an open set `U ⊆ ℂ`, and its
polyomino spines, and records the API that the spine theorem for plane domains consumes.

The one geometric statement that is *not* proved here is the nesting
`Work.Spine.Plane.spine_mono` (delegated): `spine U hU n ⊆ spine U hU (n+1)`.
-/

open scoped Topology

open Set

namespace Work.Spine.Plane

open Commons.Topology.Plane

noncomputable section

variable {U : Set ℂ}

/-- The canonical dyadic exhaustion of an open set. -/
def exh (U : Set ℂ) (hU : IsOpen U) : ℕ → Set ℂ :=
  Classical.choose (exists_dyadic_exhaustion_of_isOpen_complex U hU)

/-- The canonical level-`n` cell index set of the exhaustion. -/
def cells (U : Set ℂ) (hU : IsOpen U) (n : ℕ) : Finset (ℤ × ℤ) :=
  Classical.choose
    ((Classical.choose_spec (exists_dyadic_exhaustion_of_isOpen_complex U hU)).2.2.2 n)

theorem exh_mono (U : Set ℂ) (hU : IsOpen U) (n : ℕ) : exh U hU n ⊆ exh U hU (n + 1) :=
  (Classical.choose_spec (exists_dyadic_exhaustion_of_isOpen_complex U hU)).1 n

theorem exh_subset (U : Set ℂ) (hU : IsOpen U) (n : ℕ) : exh U hU n ⊆ U :=
  (Classical.choose_spec (exists_dyadic_exhaustion_of_isOpen_complex U hU)).2.1 n

theorem exh_covers (U : Set ℂ) (hU : IsOpen U) {x : ℂ} (hx : x ∈ U) :
    ∃ n : ℕ, ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ exh U hU n :=
  (Classical.choose_spec (exists_dyadic_exhaustion_of_isOpen_complex U hU)).2.2.1 x hx

theorem exh_eq (U : Set ℂ) (hU : IsOpen U) (n : ℕ) :
    exh U hU n = ⋃ p ∈ cells U hU n, dyadicCell n p :=
  Classical.choose_spec
    ((Classical.choose_spec (exists_dyadic_exhaustion_of_isOpen_complex U hU)).2.2.2 n)

theorem exh_mono_le (U : Set ℂ) (hU : IsOpen U) {m n : ℕ} (h : m ≤ n) :
    exh U hU m ⊆ exh U hU n := by
  induction h with
  | refl => exact subset_rfl
  | @step k _ ih => exact ih.trans (exh_mono U hU k)

/-- The level-`n` polyomino `K n`. -/
def polyK (U : Set ℂ) (hU : IsOpen U) (n : ℕ) : Set ℂ :=
  ⋃ p ∈ cells U hU n, dSq n p

theorem polyK_eq_exh (U : Set ℂ) (hU : IsOpen U) (n : ℕ) : polyK U hU n = exh U hU n := by
  rw [polyK, exh_eq]
  rfl

theorem polyK_mono (U : Set ℂ) (hU : IsOpen U) (n : ℕ) : polyK U hU n ⊆ polyK U hU (n + 1) := by
  rw [polyK_eq_exh, polyK_eq_exh]
  exact exh_mono U hU n

theorem polyK_mono_le (U : Set ℂ) (hU : IsOpen U) {m n : ℕ} (h : m ≤ n) :
    polyK U hU m ⊆ polyK U hU n := by
  rw [polyK_eq_exh, polyK_eq_exh]
  exact exh_mono_le U hU h

theorem polyK_subset (U : Set ℂ) (hU : IsOpen U) (n : ℕ) : polyK U hU n ⊆ U := by
  rw [polyK_eq_exh]; exact exh_subset U hU n

/-- The level of a point of `U` in the exhaustion, and the radius of a ball around it inside that
level (both chosen canonically). -/
def coverN (U : Set ℂ) (hU : IsOpen U) (x : ℂ) (hx : x ∈ U) : ℕ :=
  Classical.choose (exh_covers U hU hx)

def coverR (U : Set ℂ) (hU : IsOpen U) (x : ℂ) (hx : x ∈ U) : ℝ :=
  Classical.choose (Classical.choose_spec (exh_covers U hU hx))

theorem coverR_pos (U : Set ℂ) (hU : IsOpen U) (x : ℂ) (hx : x ∈ U) : 0 < coverR U hU x hx :=
  (Classical.choose_spec (Classical.choose_spec (exh_covers U hU hx))).1

theorem cover_ball_subset (U : Set ℂ) (hU : IsOpen U) (x : ℂ) (hx : x ∈ U) :
    Metric.ball x (coverR U hU x hx) ⊆ polyK U hU (coverN U hU x hx) := by
  rw [polyK_eq_exh]
  exact (Classical.choose_spec (Classical.choose_spec (exh_covers U hU hx))).2

/-- **Every compact subset of `U` lies in some polyomino `K n`.**  Consequently every loop in `U`
lies in some `K n`, and every homotopy of loops in `U` lies in some `K n`. -/
theorem exists_polyK_superset_of_compact (U : Set ℂ) (hU : IsOpen U) {C : Set ℂ}
    (hC : IsCompact C) (hCU : C ⊆ U) : ∃ n : ℕ, C ⊆ polyK U hU n := by
  classical
  have hcov : C ⊆ ⋃ x : C, Metric.ball (x : ℂ) (coverR U hU (x : ℂ) (hCU x.2)) := by
    intro y hy
    exact mem_iUnion.2 ⟨⟨y, hy⟩, Metric.mem_ball_self (coverR_pos U hU y (hCU hy))⟩
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover
    (fun x : C => Metric.ball (x : ℂ) (coverR U hU (x : ℂ) (hCU x.2)))
    (fun _ => Metric.isOpen_ball) hcov
  refine ⟨t.sup (fun x : C => coverN U hU (x : ℂ) (hCU x.2)), fun y hy => ?_⟩
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (ht hy)
  exact polyK_mono_le U hU (Finset.le_sup (f := fun x : C => coverN U hU (x : ℂ) (hCU x.2)) hxt)
    (cover_ball_subset U hU (x : ℂ) (hCU x.2) hyx)

/-- The polyomino spine: the union of the `U`-shapes of the cells of `K n`. -/
def spine (U : Set ℂ) (hU : IsOpen U) (n : ℕ) : Set ℂ := YSet n (cells U hU n) (cells U hU n)

theorem spine_subset_polyK (U : Set ℂ) (hU : IsOpen U) (n : ℕ) :
    spine U hU n ⊆ polyK U hU n := by
  rw [spine, polyK, ← YSet_empty]
  exact YSet_antitone n (cells U hU n) (Finset.empty_subset _)

/-- **The polyomino `K n` strongly deformation retracts onto its spine.** -/
theorem spine_deformationRetract (U : Set ℂ) (hU : IsOpen U) (n : ℕ) :
    ∃ (G : Set ↥(polyK U hU n)) (hC : @Topology.CWComplex ↥(polyK U hU n) _ G)
      (H : ↥(polyK U hU n) × ↥(Set.Icc (0:ℝ) 1) → ↥(polyK U hU n)),
      (∀ m : ℕ, 2 ≤ m → IsEmpty (@Topology.CWComplex.cell ↥(polyK U hU n) _ G hC m)) ∧
      Continuous H ∧ (∀ x, H (x, 0) = x) ∧ (∀ x, H (x, 1) ∈ G) ∧
      (∀ x, x ∈ G → ∀ t, H (x, t) = x) := by
  have h := dyadicPolyomino_deformationRetract n (cells U hU n)
  dsimp only [polyK]
  exact h

/-- The spine, as an explicit finite union of segments. -/
theorem ySet_eq_segments_spine (U : Set ℂ) (hU : IsOpen U) (n : ℕ) :
    spine U hU n = ((gVerts n (cells U hU n) : Set ℂ) ∪
      ⋃ e ∈ gEdges n (cells U hU n), segment ℝ e.1 e.2) :=
  YSet_eq_segments n (cells U hU n)

theorem isClosed_spine (U : Set ℂ) (hU : IsOpen U) (n : ℕ) : IsClosed (spine U hU n) := by
  rw [ySet_eq_segments_spine]
  refine IsClosed.union ?_ ?_
  · exact (gVerts n (cells U hU n)).finite_toSet.isClosed
  · exact isClosed_biUnion_finset fun e _ => (Commons.Topology.CWComplex.isCompact_segment e.1 e.2).isClosed


/-- **Every path in `U` is carried by a single polyomino.** -/
theorem exists_polyK_superset_of_path (U : Set ℂ) (hU : IsOpen U) {z w : U} (γ : Path z w) :
    ∃ n : ℕ, ∀ t : Set.Icc (0:ℝ) 1, (γ t : ℂ) ∈ polyK U hU n := by
  have hcomp : IsCompact ((Subtype.val : U → ℂ) '' Set.range γ) :=
    (isCompact_range γ.continuous).image continuous_subtype_val
  have hsub : ((Subtype.val : U → ℂ) '' Set.range γ) ⊆ U := by
    rintro y ⟨x, -, rfl⟩; exact x.2
  obtain ⟨n, hn⟩ := exists_polyK_superset_of_compact U hU hcomp hsub
  refine ⟨n, fun t => hn ⟨γ t, ⟨t, rfl⟩, rfl⟩⟩

/-- **Every homotopy of paths in `U` is carried by a single polyomino.**  Together with
`exists_polyK_superset_of_path` this says that the filtration `π₁ (K n, z) → π₁ (U, z)` is
cofinal: `π₁(U,z)` is the filtered union of the images of the `π₁(K n, z)`. -/
theorem exists_polyK_superset_of_homotopy (U : Set ℂ) (hU : IsOpen U) {z w : U}
    {γ₁ γ₂ : Path z w} (F : Path.Homotopy γ₁ γ₂) :
    ∃ n : ℕ, ∀ q : Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1, ((F q : U) : ℂ) ∈ polyK U hU n := by
  have hcomp : IsCompact ((Subtype.val : U → ℂ) '' Set.range F) :=
    (isCompact_range F.continuous).image continuous_subtype_val
  have hsub : ((Subtype.val : U → ℂ) '' Set.range F) ⊆ U := by
    rintro y ⟨x, -, rfl⟩; exact x.2
  obtain ⟨n, hn⟩ := exists_polyK_superset_of_compact U hU hcomp hsub
  exact ⟨n, fun q => hn ⟨F q, ⟨q, rfl⟩, rfl⟩⟩

end

end Work.Spine.Plane
