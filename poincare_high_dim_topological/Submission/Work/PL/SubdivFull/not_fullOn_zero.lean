import Mathlib
import Submission.Work.PL.SubdivFull.Defs

/-!
# Fullness fails before any subdivision (`r = 0`)

`FullOn K' L` (see `Submission/Work/PL/SubdivFull/Defs.lean`) says that `L` is *full* in the
complex `K'`: the vertices of any face of `K'` which lie in `L` span a simplex contained in `L`.

The main results of the area `Work.PL.SubdivFull` (`sd_full`, `sdIter_full`) show that if `L` is a
union of closed faces of a complex `K`, then `L` is full in `sdIter r K` **for `r ≥ 1`**.  This
file records that the corresponding statement is *false at `r = 0`*: there is a complex `K` and a
union of closed faces `L` of `K` which is not full in `K` itself.

The counterexample is the smallest possible one.  Take `K` the full simplex on two vertices
`z2 = 0` and `e2v = single 0 1` of `E 2 = ℝ²` (its faces are the two vertices and the edge), and
take `L = {z2, e2v}` the union of the two vertex faces.  Then the edge `V2 = {z2, e2v}` is a face
of `K` all of whose vertices lie in `L`, but `PL.simp V2` is the whole segment `[z2, e2v]`, which
contains the midpoint `midpoint ℝ z2 e2v ∉ L`.  Hence `¬ FullOn K L`.
-/

open Set Metric
open PL

namespace Work.PL.SubdivFull

noncomputable section

/-! ## The counterexample complex -/

/-- The origin of `E 2 = ℝ²`. -/
def z2 : PL.E 2 := 0

/-- The first standard basis vector of `E 2 = ℝ²`. -/
def e2v : PL.E 2 := EuclideanSpace.single (0 : Fin 2) (1 : ℝ)

/-- The two-vertex set `{0, e2v}` of `E 2`. -/
def V2 : Finset (PL.E 2) := {z2, e2v}

lemma e2v_ne_z2 : e2v ≠ z2 := by
  unfold e2v z2
  intro h
  exact one_ne_zero ((PiLp.single_eq_zero_iff 2 (0 : Fin 2)).mp h)

lemma z2_ne_e2v : z2 ≠ e2v := e2v_ne_z2.symm

lemma mem_V2 (x : PL.E 2) : x ∈ V2 ↔ x = z2 ∨ x = e2v := by simp [V2]

/-- The two-point vertex set `{z2, e2v}` is affinely independent. -/
lemma V2_affineIndependent :
    AffineIndependent ℝ (Subtype.val : (↑V2 : Set (PL.E 2)) → PL.E 2) := by
  have h1 : AffineIndependent ℝ
      (Subtype.val : Set.range (![z2, e2v] : Fin 2 → PL.E 2) → PL.E 2) :=
    (affineIndependent_of_ne ℝ z2_ne_e2v).range
  rw [show Set.range (![z2, e2v] : Fin 2 → PL.E 2) = (↑V2 : Set (PL.E 2)) from by
    ext x; simp [V2]; tauto] at h1
  exact h1

/-- The full simplex on `{z2, e2v}`: all nonempty subsets of `V2` are faces. -/
def K2 : PL.Cx 2 where
  faces := {s : Finset (PL.E 2) | s ⊆ V2 ∧ s.Nonempty}
  isRelLowerSet_faces := by
    intro a ha
    refine ⟨ha.2, ?_⟩
    intro b hba hb
    exact ⟨hba.trans ha.1, hb⟩
  indep := by
    intro s hs
    exact V2_affineIndependent.mono (Finset.coe_subset.mpr hs.1)
  inter_subset_convexHull := by
    intro s t hs ht
    rw [V2_affineIndependent.convexHull_inter hs.1 ht.1]

lemma mem_K2_faces (s : Finset (PL.E 2)) :
    s ∈ K2.faces ↔ s ⊆ V2 ∧ s.Nonempty := Iff.rfl

lemma mem_K2_faces_of (s : Finset (PL.E 2)) (hsub : s ⊆ V2) (hne : s.Nonempty) :
    s ∈ K2.faces := ⟨hsub, hne⟩

/-- `L` is the union of the two vertex faces `{z2}` and `{e2v}`, i.e. the two-point set. -/
def L2 : Set (PL.E 2) := {z2, e2v}

lemma mem_L2 (x : PL.E 2) : x ∈ L2 ↔ x = z2 ∨ x = e2v := by simp [L2]

lemma singleton_mem_simp (x : PL.E 2) : x ∈ PL.simp ({x} : Finset (PL.E 2)) :=
  subset_convexHull ℝ _ (by simp)

lemma mem_K2_face_z2 : ({z2} : Finset (PL.E 2)) ∈ K2.faces :=
  mem_K2_faces_of _ (by rw [Finset.singleton_subset_iff, mem_V2]; exact Or.inl rfl)
    (Finset.singleton_nonempty z2)

lemma mem_K2_face_e2v : ({e2v} : Finset (PL.E 2)) ∈ K2.faces :=
  mem_K2_faces_of _ (by rw [Finset.singleton_subset_iff, mem_V2]; exact Or.inr rfl)
    (Finset.singleton_nonempty e2v)

/-! ## The two properties -/

/-- `L2 = {z2} ∪ {e2v}` is a union of closed faces of `K2`. -/
lemma isFaceUnion_K2_L2 : IsFaceUnion K2 L2 := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [mem_L2] at hx
    rcases hx with rfl | rfl
    · exact Geometry.SimplicialComplex.convexHull_subset_space mem_K2_face_z2
        (singleton_mem_simp z2)
    · exact Geometry.SimplicialComplex.convexHull_subset_space mem_K2_face_e2v
        (singleton_mem_simp e2v)
  · intro x hx
    rw [mem_L2] at hx
    rcases hx with rfl | rfl
    · exact ⟨{z2}, mem_K2_face_z2, singleton_mem_simp z2, fun y hy => by
        rw [mem_L2]
        exact Or.inl (by simpa [PL.simp] using hy)⟩
    · exact ⟨{e2v}, mem_K2_face_e2v, singleton_mem_simp e2v, fun y hy => by
        rw [mem_L2]
        exact Or.inr (by simpa [PL.simp] using hy)⟩

/-- The midpoint `midpoint ℝ z2 e2v` is not an endpoint. -/
lemma midpoint_ne_z2 : midpoint ℝ z2 e2v ≠ z2 := by
  intro hh
  have hmem : z2 ∈ openSegment ℝ z2 e2v := by
    have := midpoint_mem_openSegment (𝕜 := ℝ) z2 e2v
    rwa [hh] at this
  exact z2_ne_e2v ((left_mem_openSegment_iff (𝕜 := ℝ) (x := z2) (y := e2v)).mp hmem)

lemma midpoint_ne_e2v : midpoint ℝ z2 e2v ≠ e2v := by
  intro hh
  have hmem : e2v ∈ openSegment ℝ z2 e2v := by
    have := midpoint_mem_openSegment (𝕜 := ℝ) z2 e2v
    rwa [hh] at this
  exact z2_ne_e2v ((right_mem_openSegment_iff (𝕜 := ℝ) (x := z2) (y := e2v)).mp hmem)

/-- `L2` is **not** full in `K2`: the edge `V2` has both its vertices in `L2`, but its simplex
`PL.simp V2 = [z2, e2v]` contains the midpoint, which is not in `L2`. -/
lemma not_fullOn_K2_L2 : ¬ FullOn K2 L2 := by
  intro h
  -- the edge `V2` is a face, all of whose vertices lie in `L2`
  have hmemV2 : V2 ∈ K2.faces :=
    mem_K2_faces_of _ subset_rfl ⟨z2, (mem_V2 z2).mpr (Or.inl rfl)⟩
  have hsubLV2 : (↑V2 : Set (PL.E 2)) ⊆ L2 := by
    intro x hx
    rw [mem_L2]
    exact (mem_V2 x).mp (Finset.mem_coe.mp hx)
  -- fullness would force the whole edge into `L2`
  have hsub : PL.simp V2 ⊆ L2 :=
    h V2 hmemV2 V2 subset_rfl ⟨z2, (mem_V2 z2).mpr (Or.inl rfl)⟩ hsubLV2
  -- but the midpoint of the edge lies in the simplex and not in `L2`
  have hmid : midpoint ℝ z2 e2v ∈ PL.simp V2 := by
    show midpoint ℝ z2 e2v ∈ convexHull ℝ (↑V2 : Set (PL.E 2))
    rw [show (↑V2 : Set (PL.E 2)) = ({z2, e2v} : Set (PL.E 2)) from by
      ext x; rw [Finset.mem_coe, mem_V2, Set.mem_insert_iff, Set.mem_singleton_iff]]
    rw [convexHull_pair]
    exact midpoint_mem_segment (𝕜 := ℝ) z2 e2v
  have hmem := hsub hmid
  rw [mem_L2] at hmem
  rcases hmem with h1 | h2
  · exact midpoint_ne_z2 h1
  · exact midpoint_ne_e2v h2

/-- **Fullness is genuinely a property of subdivisions, not of `K` itself**: a union of closed
faces of a complex `K` need not be full in `K`. -/
theorem not_fullOn_zero :
    ∃ (K : PL.Cx 2) (L : Set (PL.E 2)), IsFaceUnion K L ∧ ¬ FullOn K L :=
  ⟨K2, L2, isFaceUnion_K2_L2, not_fullOn_K2_L2⟩

end

end Work.PL.SubdivFull
