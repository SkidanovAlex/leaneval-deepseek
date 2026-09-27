import Mathlib
import Submission.Work.PL.SubdivFull.Defs
import Submission.Work.PL.SubdivFull.subset_of_bary_mem_simp

/-!
# Fullness fails before any subdivision: the triangle counterexample

`FullOn K' L` (see `Submission.Work.PL.SubdivFull.Defs`) says that `L` is *full* in the complex
`K'`: the vertices of any face of `K'` which lie in `L` span a simplex contained in `L`.

The main results of the area `Work.PL.SubdivFull` (`sd_full`, `sdIter_full`) show that if `L` is a
union of closed faces of a complex `K`, then `L` is full in `sdIter r K` **for `r ≥ 1`**.  This
file records a *two-dimensional* counterexample at `r = 0`: there is a complex `K` (the filled
triangle on vertices `a2, b2, c2`), a union of closed faces `L` of `K` given by two of the three
edges, `L = [a2, b2] ∪ [b2, c2]`, such that

* the whole `2`-simplex `PL.simp {a2, b2, c2}` is **not** contained in `L`, and
* consequently `L` is **not** full in `K`.

The two edges `[a2, b2]` and `[b2, c2]` form a `V`; the point `p3 = midpoint a2 c2 = (1/2) c2`
lies in the filled triangle but on neither edge, which is detected by the linear functionals
`x ↦ x₀ + x₁` and `x ↦ x₁` (the point has `x₁ = 1/2 ≠ 0`, so it is not on `[a2, b2]`; and
`x₀ + x₁ = 1/2 ≠ 1`, so it is not on `[b2, c2]`).
-/

open Set Metric
open PL

namespace Work.PL.SubdivFull

noncomputable section

/-! ## The three vertices in `E 2 = ℝ²` -/

/-- The origin of `E 2 = ℝ²`. -/
def a2 : PL.E 2 := 0

/-- The first standard basis vector `(1, 0)` of `E 2 = ℝ²`. -/
def b2 : PL.E 2 := EuclideanSpace.single (0 : Fin 2) 1

/-- The second standard basis vector `(0, 1)` of `E 2 = ℝ²`. -/
def c2 : PL.E 2 := EuclideanSpace.single (1 : Fin 2) 1

/-- The three-vertex set `{a2, b2, c2}` of `E 2`. -/
def T3 : Finset (PL.E 2) := {a2, b2, c2}

lemma a2_ne_b2 : a2 ≠ b2 := by
  intro h
  have := congrArg (EuclideanSpace.projₗ (0 : Fin 2)) h
  simp [a2, b2, EuclideanSpace.single] at this

lemma b2_ne_c2 : b2 ≠ c2 := by
  intro h
  have := congrArg (EuclideanSpace.projₗ (0 : Fin 2)) h
  simp [b2, c2, EuclideanSpace.single] at this

lemma a2_ne_c2 : a2 ≠ c2 := by
  intro h
  have := congrArg (EuclideanSpace.projₗ (1 : Fin 2)) h
  simp [a2, c2, EuclideanSpace.single] at this

/-! ## Coordinate functionals -/

lemma proj1_a2 : (EuclideanSpace.projₗ (1 : Fin 2)) a2 = 0 := by simp [a2]
lemma proj1_b2 : (EuclideanSpace.projₗ (1 : Fin 2)) b2 = 0 := by simp [b2, EuclideanSpace.single]
lemma proj1_c2 : (EuclideanSpace.projₗ (1 : Fin 2)) c2 = 1 := by simp [c2, EuclideanSpace.single]
lemma proj0_a2 : (EuclideanSpace.projₗ (0 : Fin 2)) a2 = 0 := by simp [a2]
lemma proj0_b2 : (EuclideanSpace.projₗ (0 : Fin 2)) b2 = 1 := by simp [b2, EuclideanSpace.single]
lemma proj0_c2 : (EuclideanSpace.projₗ (0 : Fin 2)) c2 = 0 := by simp [c2, EuclideanSpace.single]

/-! ## The three points are affinely independent -/

/-- `a2, b2, c2` are affinely independent: `a2 ≠ b2`, both lie on the line `x₁ = 0`, while `c2`
does not. -/
lemma abc_affineIndependent : AffineIndependent ℝ (![a2, b2, c2] : Fin 3 → PL.E 2) := by
  refine affineIndependent_of_ne_of_mem_of_mem_of_notMem
    (s := (LinearMap.ker (EuclideanSpace.projₗ (1 : Fin 2))).toAffineSubspace) ?_ ?_ ?_ ?_
  · exact a2_ne_b2
  · rw [Submodule.mem_toAffineSubspace, LinearMap.mem_ker]; simp [a2]
  · rw [Submodule.mem_toAffineSubspace, LinearMap.mem_ker]; simp [b2, EuclideanSpace.single]
  · rw [Submodule.mem_toAffineSubspace, LinearMap.mem_ker]
    intro h
    simp [c2, EuclideanSpace.single] at h

lemma T3_affineIndependent :
    AffineIndependent ℝ (Subtype.val : (↑T3 : Set (PL.E 2)) → PL.E 2) := by
  have h1 : AffineIndependent ℝ
      (Subtype.val : Set.range (![a2, b2, c2] : Fin 3 → PL.E 2) → PL.E 2) :=
    abc_affineIndependent.range
  rw [show Set.range (![a2, b2, c2] : Fin 3 → PL.E 2) = (↑T3 : Set (PL.E 2)) from by
    ext x; simp [T3]; tauto] at h1
  exact h1

/-! ## The counterexample complex -/

/-- The full simplex on `{a2, b2, c2}`: all nonempty subsets of `T3` are faces. -/
def K3 : PL.Cx 2 where
  faces := {s : Finset (PL.E 2) | s ⊆ T3 ∧ s.Nonempty}
  isRelLowerSet_faces := by
    intro a ha
    exact ⟨ha.2, fun b hba hb => ⟨hba.trans ha.1, hb⟩⟩
  indep := by
    intro s hs
    exact T3_affineIndependent.mono (Finset.coe_subset.mpr hs.1)
  inter_subset_convexHull := by
    intro s t hs ht
    rw [T3_affineIndependent.convexHull_inter hs.1 ht.1]

lemma mem_K3_faces (s : Finset (PL.E 2)) :
    s ∈ K3.faces ↔ s ⊆ T3 ∧ s.Nonempty := Iff.rfl

lemma T3_mem_K3 : ({a2, b2, c2} : Finset (PL.E 2)) ∈ K3.faces := by
  rw [mem_K3_faces]
  exact ⟨Finset.Subset.refl _, ⟨a2, by simp⟩⟩

lemma fab_mem : ({a2, b2} : Finset (PL.E 2)) ∈ K3.faces := by
  rw [mem_K3_faces]
  refine ⟨?_, ⟨a2, Finset.mem_insert_self _ _⟩⟩
  intro x hx
  rw [T3]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  tauto

lemma fbc_mem : ({b2, c2} : Finset (PL.E 2)) ∈ K3.faces := by
  rw [mem_K3_faces]
  refine ⟨?_, ⟨b2, Finset.mem_insert_self _ _⟩⟩
  intro x hx
  rw [T3]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  tauto

/-! ## The union of the two edges, and the separating point -/

/-- `L3` is the union of the two edges `[a2, b2]` and `[b2, c2]`. -/
def L3 : Set (PL.E 2) :=
  PL.simp ({a2, b2} : Finset (PL.E 2)) ∪ PL.simp ({b2, c2} : Finset (PL.E 2))

/-- The midpoint of the "long" edge `[a2, c2]`: the point `(0, 1/2)`. -/
def p3 : PL.E 2 := midpoint ℝ a2 c2

/-- The sum of the two coordinate functionals, `x ↦ x₀ + x₁`. -/
def g3 : PL.E 2 →ₗ[ℝ] ℝ :=
  EuclideanSpace.projₗ (0 : Fin 2) + EuclideanSpace.projₗ (1 : Fin 2)

lemma g3_a2 : g3 a2 = 0 := by
  rw [g3, LinearMap.add_apply, proj0_a2, proj1_a2, add_zero]
lemma g3_b2 : g3 b2 = 1 := by
  rw [g3, LinearMap.add_apply, proj0_b2, proj1_b2, add_zero]
lemma g3_c2 : g3 c2 = 1 := by
  rw [g3, LinearMap.add_apply, proj0_c2, proj1_c2, zero_add]

lemma proj1_p3 : (EuclideanSpace.projₗ (1 : Fin 2)) p3 = 1/2 := by
  rw [p3, midpoint_eq_smul_add]
  simp only [map_smul, map_add, proj1_a2, proj1_c2, zero_add, smul_eq_mul]
  norm_num

lemma g3_p3 : g3 p3 = 1/2 := by
  rw [p3, midpoint_eq_smul_add]
  simp only [map_smul, map_add, g3_a2, g3_c2, zero_add, smul_eq_mul]
  norm_num

/-- A linear functional which agrees on the two endpoints of an edge agrees on the whole segment. -/
lemma lin_eq_on_simp_pair {f : PL.E 2 →ₗ[ℝ] ℝ} {c : ℝ} {u v : PL.E 2}
    (hu : f u = c) (hv : f v = c) {x : PL.E 2}
    (hx : x ∈ PL.simp ({u, v} : Finset (PL.E 2))) : f x = c := by
  have hsub : ({u, v} : Set (PL.E 2)) ⊆ f ⁻¹' ({c} : Set ℝ) := by
    rintro y (rfl | rfl) <;> assumption
  have h := convexHull_min hsub (Convex.linear_preimage (convex_singleton c) f)
  refine h ?_
  simpa only [PL.simp, Finset.coe_insert, Finset.coe_singleton, Set.mem_ofPred_eq] using hx

lemma p3_mem : p3 ∈ PL.simp ({a2, b2, c2} : Finset (PL.E 2)) := by
  have hmono : PL.simp ({a2, c2} : Finset (PL.E 2)) ⊆
      PL.simp ({a2, b2, c2} : Finset (PL.E 2)) :=
    convexHull_mono (by
      intro x hx
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      tauto)
  apply hmono
  rw [PL.simp, Finset.coe_insert, Finset.coe_singleton, convexHull_pair]
  exact midpoint_mem_segment (𝕜 := ℝ) (x := a2) (y := c2)

lemma p3_notin_fab : p3 ∉ PL.simp ({a2, b2} : Finset (PL.E 2)) := by
  intro h
  have := lin_eq_on_simp_pair (f := EuclideanSpace.projₗ (1 : Fin 2)) (c := 0) proj1_a2 proj1_b2 h
  rw [proj1_p3] at this
  norm_num at this

lemma p3_notin_fbc : p3 ∉ PL.simp ({b2, c2} : Finset (PL.E 2)) := by
  intro h
  have := lin_eq_on_simp_pair (f := g3) (c := 1) g3_b2 g3_c2 h
  rw [g3_p3] at this
  norm_num at this

lemma not_subset : ¬ PL.simp ({a2, b2, c2} : Finset (PL.E 2)) ⊆ L3 := by
  intro h
  rcases h p3_mem with h1 | h2
  · exact p3_notin_fab h1
  · exact p3_notin_fbc h2

/-! ## The two properties -/

lemma isFaceUnion_K3_L3 : IsFaceUnion K3 L3 := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases hx with hx | hx
    · exact Geometry.SimplicialComplex.convexHull_subset_space fab_mem hx
    · exact Geometry.SimplicialComplex.convexHull_subset_space fbc_mem hx
  · intro x hx
    rcases hx with hx | hx
    · exact ⟨{a2, b2}, fab_mem, hx, fun y hy => Or.inl hy⟩
    · exact ⟨{b2, c2}, fbc_mem, hx, fun y hy => Or.inr hy⟩

/-- A vertex of a finite vertex set lies in the simplex it spans. -/
lemma mem_simp_of_mem {s : Finset (PL.E 2)} {v : PL.E 2} (h : v ∈ s) : v ∈ PL.simp s :=
  subset_convexHull ℝ (s : Set (PL.E 2)) (Finset.mem_coe.mpr h)

lemma verts_triangle_subset_L3 :
    (↑({a2, b2, c2} : Finset (PL.E 2)) : Set (PL.E 2)) ⊆ L3 := by
  intro y hy
  rw [Finset.mem_coe] at hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl
  · exact Or.inl (mem_simp_of_mem (show a2 ∈ ({a2, b2} : Finset (PL.E 2)) by simp))
  · exact Or.inl (mem_simp_of_mem (show b2 ∈ ({a2, b2} : Finset (PL.E 2)) by simp))
  · exact Or.inr (mem_simp_of_mem (show c2 ∈ ({b2, c2} : Finset (PL.E 2)) by simp))

lemma not_fullOn_K3_L3 : ¬ FullOn K3 L3 := by
  intro h
  refine not_subset ?_
  exact h {a2, b2, c2} T3_mem_K3 {a2, b2, c2} (Finset.Subset.refl _)
    ⟨a2, by simp⟩ verts_triangle_subset_L3

/-- **Fullness is genuinely a property of subdivisions, not of `K` itself**, in dimension `2`:
the filled triangle `{a2, b2, c2}` has all its vertices in the union `L3 = [a2, b2] ∪ [b2, c2]` of
two of its edges, but `PL.simp {a2, b2, c2} ⊄ L3` and hence `L3` is not full in `K3`. -/
theorem not_fullOn_zero_triangle :
    ∃ (K : PL.Cx 2) (L : Set (PL.E 2)) (a b c : PL.E 2),
      IsFaceUnion K L ∧
        L = (PL.simp ({a, b} : Finset (PL.E 2)) ∪ PL.simp ({b, c} : Finset (PL.E 2))) ∧
        ({a, b, c} : Finset (PL.E 2)) ∈ K.faces ∧ ({a, b} : Finset (PL.E 2)) ∈ K.faces ∧
        ({b, c} : Finset (PL.E 2)) ∈ K.faces ∧
        ¬ PL.simp ({a, b, c} : Finset (PL.E 2)) ⊆ L ∧ ¬ FullOn K L :=
  ⟨K3, L3, a2, b2, c2, isFaceUnion_K3_L3, rfl, T3_mem_K3, fab_mem, fbc_mem,
    not_subset, not_fullOn_K3_L3⟩

end

end Work.PL.SubdivFull
