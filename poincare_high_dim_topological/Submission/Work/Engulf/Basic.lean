import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Generic.Basic
import Submission.Work.PL.Generic.exists_mem_ball_notMem_iUnion_affineSubspace
import Submission.Work.PL.Generic.exists_ioc_smul_add_of_mem_convexHull_insert
import Submission.Work.Engulf.Defs

/-!
# Area A9: the elementary API

Standard geometry of simplices, sup-norm cubes and subcomplexes, in the vocabulary of
`Submission.Work.PL.Defs` and the definitions of `Submission.Work.Engulf.Defs`.
`PL.simp s` is the convex hull of the finite vertex set `s`, `PL.Cx N` is
`Geometry.SimplicialComplex ℝ (PL.E N)`, and `IsSubSp Γ S` says that `S` is a union of closed
faces of `Γ`.
-/

open Set Metric PL

namespace Work.Engulf

universe u

variable {n : ℕ} {M : Type*} [MetricSpace M] {N : ℕ}

/-! ## Simplices -/

section Simp

variable {N : ℕ}

@[simp] theorem simp_empty : simp (∅ : Finset (E N)) = ∅ := by simp [PL.simp]

theorem simp_eq_empty_iff {s : Finset (E N)} : simp s = ∅ ↔ s = ∅ := by
  rw [PL.simp, convexHull_eq_empty, Finset.coe_eq_empty]

@[simp] theorem simp_singleton (v : E N) : simp ({v} : Finset (E N)) = {v} := by
  simp [simp, convexHull_singleton]

theorem subset_simp {s : Finset (E N)} {x : E N} (hx : x ∈ s) : x ∈ simp s :=
  subset_convexHull ℝ (s : Set (E N)) (by simpa using hx)

theorem simp_mono {s t : Finset (E N)} (h : s ⊆ t) : simp s ⊆ simp t :=
  convexHull_mono (by simpa using h)

theorem simp_nonempty_iff {s : Finset (E N)} : (simp s).Nonempty ↔ s.Nonempty := by
  rw [← not_iff_not, Set.not_nonempty_iff_eq_empty, Finset.not_nonempty_iff_eq_empty,
    simp_eq_empty_iff]

theorem simp_nonempty {s : Finset (E N)} (h : s.Nonempty) : (simp s).Nonempty :=
  simp_nonempty_iff.2 h

theorem convex_simp (s : Finset (E N)) : Convex ℝ (simp s) := convex_convexHull ℝ _

theorem isClosed_simp (s : Finset (E N)) : IsClosed (simp s) :=
  Set.Finite.isClosed_convexHull ℝ (s.finite_toSet)

theorem isCompact_simp (s : Finset (E N)) : IsCompact (simp s) :=
  Set.Finite.isCompact_convexHull ℝ (s.finite_toSet)

/-- The simplices of two faces of a complex intersect in the simplex on the intersection of the
vertex sets. -/
theorem simp_inter {K : Cx N} {s t : Finset (E N)} (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
    simp s ∩ simp t = simp (s ∩ t) := by
  rw [PL.simp, PL.simp, PL.simp, K.convexHull_inter_convexHull hs ht, Finset.coe_inter]

theorem simp_subset_iff {K : Cx N} {s t : Finset (E N)} (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
    simp s ⊆ simp t ↔ s ⊆ t :=
  K.face_subset_face_iff hs ht

/-- A point of `simp (s ∪ {a})`, not in `simp s`, lies on a segment from `simp s` to `a`. -/
theorem exists_ioc_smul_add_of_mem_simp_insert {s : Finset (E N)} {a x : E N} (hs : s.Nonempty)
    (hx : x ∈ simp (s ∪ {a})) (hx' : x ∉ simp s) :
    ∃ μ ∈ Ioc (0 : ℝ) 1, ∃ p ∈ simp s, x = (1 - μ) • p + μ • a :=
  Work.PL.Generic.exists_ioc_smul_add_of_mem_convexHull_insert hs hx hx'

end Simp

/-! ## Sup-norm cubes -/

section Cubes

variable {N : ℕ}

theorem closedCube_mono {r r' : ℝ} (h : r ≤ r') :
    closedCube (n := N) r ⊆ closedCube (n := N) r' :=
  fun _ hx i => le_trans (hx i) h

theorem openCube_mono {r r' : ℝ} (h : r ≤ r') :
    openCube (n := N) r ⊆ openCube (n := N) r' :=
  fun _ hx i => lt_of_lt_of_le (hx i) h

theorem openCube_subset_closedCube (r : ℝ) : openCube (n := N) r ⊆ closedCube (n := N) r :=
  fun _ hx i => le_of_lt (hx i)

theorem closedCube_subset_openCube {r r' : ℝ} (h : r < r') :
    closedCube (n := N) r ⊆ openCube (n := N) r' :=
  fun _ hx i => lt_of_le_of_lt (hx i) h

theorem closedCube_eq_iInter (r : ℝ) :
    closedCube (n := N) r = ⋂ i, {x : E N | x i ∈ Icc (-r) r} := by
  ext x; simp [closedCube, abs_le]

theorem isClosed_closedCube (r : ℝ) : IsClosed (closedCube (n := N) r) := by
  rw [closedCube_eq_iInter]
  exact isClosed_iInter fun i =>
    isClosed_Icc.preimage (PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i)

theorem isCompact_closedCube (r : ℝ) : IsCompact (closedCube (n := N) r) := by
  have h : closedCube (n := N) r
      = (PiLp.homeomorph 2 (fun _ : Fin N => ℝ)) ⁻¹'
          (Set.pi univ (fun _ : Fin N => Icc (-r) r)) := by
    ext x
    simp only [mem_preimage, closedCube, mem_ofPred_eq, Set.mem_pi, mem_univ, true_implies,
      mem_Icc, abs_le]
    constructor
    · intro hx i; exact hx i
    · intro hx i; exact hx i
  rw [h]
  exact (PiLp.homeomorph 2 (fun _ : Fin N => ℝ)).isCompact_preimage.mpr
    (isCompact_univ_pi fun _ => isCompact_Icc)

theorem isOpen_openCube (r : ℝ) : IsOpen (openCube (n := N) r) := by
  have h : openCube (n := N) r = ⋂ i, {x : E N | |x i| < r} := by
    ext x; simp [openCube]
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).abs continuous_const

theorem convex_closedCube (r : ℝ) : Convex ℝ (closedCube (n := N) r) := by
  have h : closedCube (n := N) r
      = (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℝ)) ⁻¹'
          (Set.pi univ (fun _ : Fin N => Icc (-r) r)) := by
    ext x
    simp only [mem_preimage, closedCube, mem_ofPred_eq, Set.mem_pi, mem_univ, true_implies,
      mem_Icc, abs_le]
    constructor
    · intro hx i; exact hx i
    · intro hx i; exact hx i
  rw [h]
  exact (convex_pi fun _ _ => convex_Icc (-r) r).linear_preimage _

theorem closedCube_nonempty {r : ℝ} (h : 0 ≤ r) : (closedCube (n := N) r).Nonempty :=
  ⟨0, by simp [closedCube, h]⟩

theorem openCube_nonempty {r : ℝ} (h : 0 < r) : (openCube (n := N) r).Nonempty :=
  ⟨0, by simp [openCube, h]⟩

end Cubes

/-! ## Subcomplexes as sets -/

section IsSubSp

variable {N : ℕ} {Γ : Cx N} {S T : Set (E N)}

theorem IsSubSp.subset_space (h : IsSubSp Γ S) : S ⊆ Γ.space := h.1

theorem isSubSp_empty (Γ : Cx N) : IsSubSp Γ (∅ : Set (E N)) :=
  ⟨Set.empty_subset _, by simp⟩

theorem isSubSp_space (Γ : Cx N) : IsSubSp Γ Γ.space := by
  refine ⟨Subset.rfl, ?_⟩
  intro x hx
  rw [Geometry.SimplicialComplex.mem_space_iff] at hx
  obtain ⟨s, hs, hxs⟩ := hx
  exact ⟨s, hs, hxs, Geometry.SimplicialComplex.convexHull_subset_space hs⟩

theorem isSubSp_iff (Γ : Cx N) (S : Set (E N)) :
    IsSubSp Γ S ↔ ∃ T : Set (Finset (E N)), T ⊆ Γ.faces ∧ S = ⋃ s ∈ T, simp s := by
  constructor
  · intro h
    refine ⟨{s | s ∈ Γ.faces ∧ simp s ⊆ S}, fun s hs => hs.1, Subset.antisymm ?_ ?_⟩
    · intro x hx
      obtain ⟨s, hs, hxs, hsub⟩ := h.2 x hx
      exact mem_iUnion₂.2 ⟨s, ⟨hs, hsub⟩, hxs⟩
    · rintro x hx
      obtain ⟨s, ⟨hs, hsub⟩, hxs⟩ := mem_iUnion₂.1 hx
      exact hsub hxs
  · rintro ⟨T, hT, rfl⟩
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.1 hx
      exact Geometry.SimplicialComplex.convexHull_subset_space (hT hs) hxs
    · obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.1 hx
      exact ⟨s, hT hs, hxs, fun y hy => mem_iUnion₂.2 ⟨s, hs, hy⟩⟩

theorem isSubSp_of_faces {T : Set (Finset (E N))} (hT : T ⊆ Γ.faces) :
    IsSubSp Γ (⋃ s ∈ T, simp s) :=
  (isSubSp_iff Γ _).2 ⟨T, hT, rfl⟩

theorem isSubSp_union (hS : IsSubSp Γ S) (hT : IsSubSp Γ T) : IsSubSp Γ (S ∪ T) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rcases hx with hx | hx
    exacts [hS.subset_space hx, hT.subset_space hx]
  · rcases hx with hx | hx
    · obtain ⟨s, hs, hxs, hsub⟩ := hS.2 x hx
      exact ⟨s, hs, hxs, fun y hy => Or.inl (hsub hy)⟩
    · obtain ⟨s, hs, hxs, hsub⟩ := hT.2 x hx
      exact ⟨s, hs, hxs, fun y hy => Or.inr (hsub hy)⟩

theorem isSubSp_inter (hS : IsSubSp Γ S) (hT : IsSubSp Γ T) : IsSubSp Γ (S ∩ T) := by
  refine ⟨fun x hx => hS.subset_space hx.1, fun x hx => ?_⟩
  obtain ⟨s, hs, hxs, hSsub⟩ := hS.2 x hx.1
  obtain ⟨t, ht, hxt, hTsub⟩ := hT.2 x hx.2
  have hne : (s ∩ t).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have : x ∈ simp (∅ : Finset (E N)) := by
      rw [← hemp, ← simp_inter hs ht]; exact ⟨hxs, hxt⟩
    simpa using this
  have hst : s ∩ t ∈ Γ.faces := Γ.down_closed hs Finset.inter_subset_left hne
  refine ⟨s ∩ t, hst, ?_, ?_⟩
  · rw [← simp_inter hs ht]; exact ⟨hxs, hxt⟩
  · intro y hy
    rw [← simp_inter hs ht] at hy
    exact ⟨hSsub hy.1, hTsub hy.2⟩

end IsSubSp

/-! ## Compactness -/

section Compact

variable {N : ℕ} {Γ : Cx N} {S : Set (E N)}

theorem isCompact_space (hfin : Γ.faces.Finite) : IsCompact Γ.space := by
  rw [Geometry.SimplicialComplex.space]
  refine (hfin.isCompact_biUnion fun s _ => isCompact_simp s)

theorem isClosed_space (hfin : Γ.faces.Finite) : IsClosed Γ.space :=
  (isCompact_space hfin).isClosed

theorem isClosed_of_isSubSp (hfin : Γ.faces.Finite) (h : IsSubSp Γ S) : IsClosed S := by
  obtain ⟨T, hT, rfl⟩ := (isSubSp_iff Γ S).1 h
  have hTfin : (T ∩ Γ.faces).Finite := hfin.subset Set.inter_subset_right
  have h1 : (⋃ s ∈ T, simp s) = ⋃ s ∈ (T ∩ Γ.faces), simp s := by
    refine Subset.antisymm (fun x hx => ?_) (biUnion_mono Set.inter_subset_left fun _ _ => Subset.rfl)
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.1 hx
    exact mem_iUnion₂.2 ⟨s, ⟨hs, hT hs⟩, hxs⟩
  rw [h1]
  exact hTfin.isClosed_biUnion fun s _ => isClosed_simp s

theorem isCompact_of_isSubSp (hfin : Γ.faces.Finite) (h : IsSubSp Γ S) : IsCompact S :=
  (isCompact_space hfin).of_isClosed_subset (isClosed_of_isSubSp hfin h) h.subset_space

end Compact

end Work.Engulf
