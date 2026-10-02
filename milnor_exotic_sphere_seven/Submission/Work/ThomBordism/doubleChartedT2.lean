import Mathlib
import Submission.Work.ThomBordism.doubleDefs
import Submission.Work.Surgery.Gluing
import Submission.Work.Surgery.GluingPointSet
import Submission.Work.Surgery.glue_t2Space
import Submission.Work.ThomBordism.doubleCharted

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The double `M ∪_∂M M` is Hausdorff

The double `Work.ThomBordism.Double n M = M ∪_∂M M` of a `C¹` manifold with boundary `M`
(gluing two copies of `M` along the identity of the boundary,
`Submission/Work/ThomBordism/doubleDefs.lean`) is a topological manifold without boundary which is
Hausdorff.

This file proves the **Hausdorff** half, `Work.ThomBordism.DblT2.t2Space_double`.  The
charted-space half is `Work.ThomBordism.doubleCharted`
(`Submission/Work/ThomBordism/doubleCharted.lean`).

## The argument

The gluing is along the identity, so for *every* open `U ⊆ M` the set
`S(U) = q '' (inl '' U ∪ inr '' U)` is open in the double (its preimage under the quotient map is
`inl '' U ∪ inr '' U`), and for disjoint open `U`, `V` the sets `S(U)`, `S(V)` are disjoint.
Hence two points represented by `M ⊕ M`-elements with **different** underlying points of `M` are
separated by `S(U)`, `S(V)` for disjoint open neighbourhoods `U`, `V` of those points in `M`
(which exist by the Hausdorff property of `M`).

The remaining case is a pair `q (inl x)`, `q (inr x)` with the same underlying point `x ∈ M`.
If `x` is a boundary point these two points are *equal*; hence for distinct points `x` lies in the
interior, and then `q '' (inl '' int M)` and `q '' (inr '' int M)` are disjoint open neighbourhoods
(`inl '' int M` and `inr '' int M` are disjoint summands, and the interior is disjoint from the
boundary).
-/

open scoped Manifold Topology
open Function Set

namespace Work.ThomBordism

noncomputable section

namespace DblT2

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

/-- The boundary of a `C¹` manifold with boundary is closed. -/
theorem isClosed_boundary_one [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] :
    IsClosed ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :=
  ModelWithCorners.isClosed_boundary
    (I := modelWithCornersEuclideanHalfSpace (n + 1)) (M := M)
    (n := (1 : WithTop ℕ∞)) (by norm_num)

/-- The underlying point of an element of `M ⊕ M`. -/
def projD : M ⊕ M → M := Sum.elim id id

@[simp] theorem projD_inl (x : M) : projD (Sum.inl x) = x := rfl

@[simp] theorem projD_inr (x : M) : projD (Sum.inr x) = x := rfl

/-! ## The saturated open sets of the double -/

/-- **The preimage of `S(U) = q '' (inl '' U ∪ inr '' U)`** is `inl '' U ∪ inr '' U`: the two
copies of `U` are saturated for the gluing relation. -/
theorem preimage_sat_eq (U : Set M) :
    doubleQ (n := n) (M := M) ⁻¹'
        (doubleQ (n := n) (M := M) '' (Sum.inl '' U ∪ Sum.inr '' U))
      = Sum.inl '' U ∪ Sum.inr '' U :=
  Work.Surgery.GlueData.preimage_image_eq (doubleData n M) (U := U) (V := U)
    (fun _ h => h)
    (fun p h => ⟨p, h, rfl⟩)

/-- The two copies of `U` match trivially for the identity gluing. -/
theorem match_self (U : Set M) : (doubleData n M).Match U U :=
  ⟨fun _ hp => hp, fun p hp => ⟨p, hp, rfl⟩⟩

/-- The two copies of `U` match the empty set when `U` avoids the boundary. -/
theorem match_empty_of (U : Set M)
    (hc : ∀ x ∈ U, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :
    (doubleData n M).Match U ∅ :=
  ⟨fun p hp => (hc p.1 hp p.2).elim, fun p hp => absurd hp (Set.notMem_empty p.1)⟩

/-- The empty set matches the two copies of `U` when `U` avoids the boundary. -/
theorem match_empty_of_right (U : Set M)
    (hc : ∀ x ∈ U, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :
    (doubleData n M).Match ∅ U :=
  ⟨fun p hp => absurd hp (Set.notMem_empty p.1),
    fun p hp => (hc p.1 hp p.2).elim⟩

/-- **`S(U)` is open** for every open `U ⊆ M`. -/
theorem isOpen_sat (U : Set M) (hU : IsOpen U) :
    IsOpen (doubleQ (n := n) (M := M) '' (Sum.inl '' U ∪ Sum.inr '' U)) :=
  Work.Surgery.GlueData.isOpen_gluing (doubleData n M) hU hU (match_self U)

/-- The preimage of `q '' (inl '' U)` when `U` avoids the boundary. -/
theorem preimage_inl_eq (U : Set M)
    (hc : ∀ x ∈ U, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :
    doubleQ (n := n) (M := M) ⁻¹' (doubleQ (n := n) (M := M) '' (Sum.inl '' U))
      = Sum.inl '' U := by
  change (doubleData n M).q ⁻¹' ((doubleData n M).q '' (Sum.inl '' U)) = Sum.inl '' U
  have h := Work.Surgery.GlueData.preimage_image_eq (doubleData n M) (U := U) (V := ∅)
    (fun p hp => (hc p.1 hp p.2).elim)
    (fun p hp => absurd hp (Set.notMem_empty p.1))
  simpa only [Set.image_empty, Set.union_empty] using h

/-- The preimage of `q '' (inr '' U)` when `U` avoids the boundary. -/
theorem preimage_inr_eq (U : Set M)
    (hc : ∀ x ∈ U, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :
    doubleQ (n := n) (M := M) ⁻¹' (doubleQ (n := n) (M := M) '' (Sum.inr '' U))
      = Sum.inr '' U := by
  change (doubleData n M).q ⁻¹' ((doubleData n M).q '' (Sum.inr '' U)) = Sum.inr '' U
  have h := Work.Surgery.GlueData.preimage_image_eq (doubleData n M) (U := ∅) (V := U)
    (fun p hp => absurd hp (Set.notMem_empty p.1))
    (fun p hp => ⟨p, (hc p.1 hp p.2).elim, rfl⟩)
  simpa only [Set.image_empty, Set.empty_union] using h

/-- `q '' (inl '' U)` is open when `U` avoids the boundary. -/
theorem isOpen_inl (U : Set M) (hU : IsOpen U)
    (hc : ∀ x ∈ U, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :
    IsOpen (doubleQ (n := n) (M := M) '' (Sum.inl '' U)) := by
  change IsOpen ((doubleData n M).q '' (Sum.inl '' U))
  have h := Work.Surgery.GlueData.isOpen_gluing (doubleData n M) hU isOpen_empty
    (match_empty_of (n := n) (M := M) U hc)
  simpa only [Set.image_empty, Set.union_empty] using h

/-- `q '' (inr '' U)` is open when `U` avoids the boundary. -/
theorem isOpen_inr (U : Set M) (hU : IsOpen U)
    (hc : ∀ x ∈ U, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :
    IsOpen (doubleQ (n := n) (M := M) '' (Sum.inr '' U)) := by
  change IsOpen ((doubleData n M).q '' (Sum.inr '' U))
  have h := Work.Surgery.GlueData.isOpen_gluing (doubleData n M) isOpen_empty hU
    (match_empty_of_right (n := n) (M := M) U hc)
  simpa only [Set.image_empty, Set.empty_union] using h

/-- **Disjoint open sets give disjoint open sets of the double.** -/
theorem disjoint_sat {U V : Set M} (h : Disjoint U V) :
    Disjoint (doubleQ (n := n) (M := M) '' (Sum.inl '' U ∪ Sum.inr '' U))
      (doubleQ (n := n) (M := M) '' (Sum.inl '' V ∪ Sum.inr '' V)) := by
  rw [Set.disjoint_left]
  rintro z ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
  have hbU : b ∈ Sum.inl '' U ∪ Sum.inr '' U := by
    rw [← preimage_sat_eq (n := n) (M := M) U]
    exact ⟨a, ha, hba.symm⟩
  rcases hbU with ⟨u, huU, hbu⟩ | ⟨u, huU, hbu⟩
  · rcases hb with ⟨v, hvV, hbv⟩ | ⟨v, hvV, hbv⟩
    · have huv : u = v := Sum.inl.inj (hbu.trans hbv.symm)
      exact (Set.disjoint_left.mp h huU) (huv ▸ hvV)
    · exact absurd (hbu.trans hbv.symm) Sum.inl_ne_inr
  · rcases hb with ⟨v, hvV, hbv⟩ | ⟨v, hvV, hbv⟩
    · exact absurd (hbu.trans hbv.symm) Sum.inr_ne_inl
    · have huv : u = v := Sum.inr.inj (hbu.trans hbv.symm)
      exact (Set.disjoint_left.mp h huU) (huv ▸ hvV)

/-- Away from the boundary, the two copies of `M` in the double are disjoint. -/
theorem disjoint_inl_inr_interior :
    Disjoint (doubleQ (n := n) (M := M) ''
        (Sum.inl '' (((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)ᶜ)))
      (doubleQ (n := n) (M := M) ''
        (Sum.inr '' (((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)ᶜ))) := by
  have hc : ∀ x ∈ (((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)ᶜ),
      x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M := fun x hx => hx
  rw [Set.disjoint_left]
  rintro z ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
  have hbU : b ∈ Sum.inl '' (((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)ᶜ) := by
    rw [← preimage_inl_eq (n := n) (M := M) _ hc]
    exact ⟨a, ha, hba.symm⟩
  rcases hbU with ⟨u, hu, hbu⟩
  rcases hb with ⟨v, hv, hbv⟩
  exact absurd (hbu.trans hbv.symm) Sum.inl_ne_inr

/-- The two representatives of a boundary point of `M` are the same point of the double. -/
theorem doubleQ_sides_eq (p : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :
    doubleQ (n := n) (M := M) (Sum.inl p.1) = doubleQ (Sum.inr p.1) := by
  rw [doubleQ_inl, doubleQ_inr]
  exact Work.Surgery.GlueData.ιM_eq_ιN (doubleData n M) p

/-! ## Separation of points -/

/-- Swap the two separating open sets. -/
theorem sep_symm {A B : Double n M}
    (h : ∃ u v : Set (Double n M), IsOpen u ∧ IsOpen v ∧ A ∈ u ∧ B ∈ v ∧ Disjoint u v) :
    ∃ u v : Set (Double n M), IsOpen u ∧ IsOpen v ∧ B ∈ u ∧ A ∈ v ∧ Disjoint u v := by
  obtain ⟨u, v, hu, hv, hA, hB, hd⟩ := h
  exact ⟨v, u, hv, hu, hB, hA, hd.symm⟩

/-- **Points of the double with different underlying points of `M` are separated.** -/
theorem sep_of_ne [T2Space M] {a b : M ⊕ M} (h : projD a ≠ projD b) :
    ∃ u v : Set (Double n M), IsOpen u ∧ IsOpen v ∧
      doubleQ (n := n) (M := M) a ∈ u ∧ doubleQ (n := n) (M := M) b ∈ v ∧ Disjoint u v := by
  obtain ⟨U, V, hU, hV, haU, hbV, hd⟩ := t2_separation h
  refine ⟨_, _, isOpen_sat U hU, isOpen_sat V hV, ?_, ?_, disjoint_sat hd⟩
  · rcases a with x | x
    · exact ⟨Sum.inl x, Or.inl ⟨x, haU, rfl⟩, rfl⟩
    · exact ⟨Sum.inr x, Or.inr ⟨x, haU, rfl⟩, rfl⟩
  · rcases b with y | y
    · exact ⟨Sum.inl y, Or.inl ⟨y, hbV, rfl⟩, rfl⟩
    · exact ⟨Sum.inr y, Or.inr ⟨y, hbV, rfl⟩, rfl⟩

/-- **The two representatives of an interior point are separated.** -/
theorem sep_diag [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] (x : M)
    (hx : x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :
    ∃ u v : Set (Double n M), IsOpen u ∧ IsOpen v ∧
      doubleQ (n := n) (M := M) (Sum.inl x) ∈ u ∧
      doubleQ (n := n) (M := M) (Sum.inr x) ∈ v ∧ Disjoint u v := by
  have hInt : IsOpen (((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)ᶜ) :=
    (isClosed_boundary_one (n := n) (M := M)).isOpen_compl
  exact ⟨_, _, isOpen_inl _ hInt (fun y hy => hy), isOpen_inr _ hInt (fun y hy => hy),
    ⟨Sum.inl x, ⟨x, hx, rfl⟩, rfl⟩, ⟨Sum.inr x, ⟨x, hx, rfl⟩, rfl⟩,
    disjoint_inl_inr_interior⟩

/-- **The double of a Hausdorff `C¹` manifold with boundary is Hausdorff.** -/
theorem t2Space_double [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M]
    [T2Space M] : T2Space (Double n M) := by
  rw [t2Space_iff]
  rintro z1 z2 hne
  obtain ⟨a1, rfl⟩ := Quotient.exists_rep z1
  obtain ⟨a2, rfl⟩ := Quotient.exists_rep z2
  rcases a1 with x1 | y1 <;> rcases a2 with x2 | y2
  · by_cases h : x1 = x2
    · subst h; exact absurd rfl hne
    · exact sep_of_ne (n := n) (M := M) (by simpa using h)
  · by_cases h : x1 = y2
    · subst h
      by_cases hb : x1 ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M
      · exact absurd (doubleQ_sides_eq (n := n) (M := M) ⟨x1, hb⟩) hne
      · exact sep_diag (n := n) (M := M) x1 hb
    · exact sep_of_ne (n := n) (M := M) (by simpa using h)
  · by_cases h : y1 = x2
    · subst h
      by_cases hb : y1 ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M
      · exact absurd (doubleQ_sides_eq (n := n) (M := M) ⟨y1, hb⟩).symm hne
      · exact sep_symm (sep_diag (n := n) (M := M) y1 hb)
    · exact sep_of_ne (n := n) (M := M) (by simpa using h)
  · by_cases h : y1 = y2
    · subst h; exact absurd rfl hne
    · exact sep_of_ne (n := n) (M := M) (by simpa using h)

end DblT2

/-- **The double of a `C¹` manifold with boundary is a charted space modelled on `ℝ^{n+1}` and is
Hausdorff.**  The charted space structure is `Work.ThomBordism.doubleCharted`
(`Submission/Work/ThomBordism/doubleCharted.lean`); the Hausdorff property is
`Work.ThomBordism.DblT2.t2Space_double` above. -/
theorem doubleChartedT2 (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] [T2Space M] :
    Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) (Work.ThomBordism.Double n M)) ∧
      T2Space (Work.ThomBordism.Double n M) :=
  ⟨doubleCharted n M, DblT2.t2Space_double (n := n) (M := M)⟩

end

end Work.ThomBordism
