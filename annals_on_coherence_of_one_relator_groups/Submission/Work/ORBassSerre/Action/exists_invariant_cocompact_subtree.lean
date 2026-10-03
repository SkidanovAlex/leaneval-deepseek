import Mathlib
import Submission.Work.ORBassSerre.Action.Cocompact
import Submission.Work.ORBassSerre.Tree.Convex
import Submission.Work.ORBassSerre.Tree.IsTreeAPI
import Submission.Work.ORBassSerre.Tree.Geodesic.qpath_eq_of_isTree
import Submission.Work.ORBassSerre.Tree.Reduction.qpath_vertices_subset_of_reducesTo
import Submission.Work.ORBassSerre.Tree.Seg.reducedSpan_comm
import Submission.Work.ORBassSerre.Tree.Seg.reducedSpan_eq_union_of_mem
import Submission.Work.ORBassSerre.Tree.Seg.isConvexSet_reducedSpan
import Submission.Work.ORBassSerre.Tree.Seg.exists_median
import Submission.Work.ORBassSerre.Tree.Seg.smul_reducedSpan
import Submission.Work.ORBassSerre.Tree.Seg.arrow_subset_of_convex_cover
import Submission.Work.ORBassSerre.Tree.Seg.exists_finset_arrows

namespace Work.ORBassSerre.Action

open Quiver

section Prelim

variable {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-- In a tree, the geodesic segment from a vertex to itself is the singleton on that vertex. -/
theorem reducedSpan_self {hT : IsTree V} (x : V) : reducedSpan x x = {x} := by
  ext v
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨p, hp, hv⟩
    have hnil : p = Path.nil := hT.2 x p hp
    subst hnil
    simpa using hv
  · intro hv
    rw [hv]
    exact self_mem_reducedSpan x

/-- The starting point of a geodesic belongs to the corresponding reduced span. -/
theorem start_mem_reducedSpan {hT : IsTree V} (x y : V) : x ∈ reducedSpan x y :=
  ⟨hT.geodesic x y, hT.geodesic_isReduced x y, Path.start_mem_vertices _⟩

/-- The end point of a geodesic belongs to the corresponding reduced span. -/
theorem end_mem_reducedSpan {hT : IsTree V} (x y : V) : y ∈ reducedSpan x y :=
  ⟨hT.geodesic x y, hT.geodesic_isReduced x y, Path.end_mem_vertices _⟩

/-- A tree has no loops. -/
theorem not_nonempty_hom_self {hT : IsTree V} (x : V) : ¬ Nonempty (x ⟶ x) := by
  rintro ⟨f⟩
  have hlen : f.toPath.length < 2 := by rw [Path.length_toPath]; norm_num
  have hred : f.toPath.IsReduced := Path.IsReduced.of_length_lt_two (p := f.toPath) hlen
  have hnil : f.toPath = Path.nil := hT.2 x f.toPath hred
  have h0 : f.toPath.length = 0 := by rw [hnil]; rfl
  rw [Path.length_toPath] at h0
  exact Nat.one_ne_zero h0

/-- There is no arrow between two vertices of a tree that are equal. -/
theorem not_nonempty_hom_of_eq {hT : IsTree V} {a b : V} (h : a = b) : ¬ Nonempty (a ⟶ b) := by
  subst h
  exact not_nonempty_hom_self (hT := hT) a

/-- The reduced span between two vertices is a finite set of vertices. -/
theorem reducedSpan_finite {hT : IsTree V} (x y : V) : (reducedSpan x y).Finite := by
  refine Set.Finite.subset (List.finite_toSet (hT.geodesic x y).vertices) ?_
  intro v hv
  rw [hT.reducedSpan_eq x y] at hv
  exact hv

/-- The geodesic segment from `x` to `z` is covered by the two segments via an intermediate
vertex `y` (the median decomposition). -/
theorem reducedSpan_subset_union {hT : IsTree V} (x y z : V) :
    reducedSpan x z ⊆ reducedSpan x y ∪ reducedSpan y z := by
  intro v hv
  obtain ⟨m, hmxy, hmyz, hmzx⟩ := Work.ORBassSerre.Tree.Seg.exists_median (hT := hT) x y z
  have hmxz : m ∈ reducedSpan x z := by
    rw [Work.ORBassSerre.Tree.Seg.reducedSpan_comm x z]
    exact hmzx
  rw [Work.ORBassSerre.Tree.Seg.reducedSpan_eq_union_of_mem (hT := hT) hmxz] at hv
  rcases hv with hv | hv
  · exact Or.inl (IsConvexSet.reducedSpan_subset
      (Work.ORBassSerre.Tree.Seg.isConvexSet_reducedSpan (hT := hT) x y)
      (start_mem_reducedSpan (hT := hT) x y) hmxy hv)
  · exact Or.inr (IsConvexSet.reducedSpan_subset
      (Work.ORBassSerre.Tree.Seg.isConvexSet_reducedSpan (hT := hT) y z)
      hmyz (end_mem_reducedSpan (hT := hT) y z) hv)

/-- If `c` lies on the segment from `a` to `b`, then the segment from `a` to `c` is contained
in the segment from `a` to `b`. -/
theorem reducedSpan_subset_of_mem {hT : IsTree V} {a b c : V}
    (hc : c ∈ reducedSpan a b) : reducedSpan a c ⊆ reducedSpan a b :=
  IsConvexSet.reducedSpan_subset
    (Work.ORBassSerre.Tree.Seg.isConvexSet_reducedSpan (hT := hT) a b)
    (start_mem_reducedSpan (hT := hT) a b) hc

end Prelim

section Action

variable {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [GraphAction G V]

/-- The action of `G` on vertices is compatible with the action on the endpoints of an arrow. -/
@[simp] theorem smul_total_left (g : G) (e : Quiver.Total V) : (g • e).left = g • e.left :=
  GraphAction.smul_left g e

/-- The action of `G` on vertices is compatible with the action on the endpoints of an arrow. -/
@[simp] theorem smul_total_right (g : G) (e : Quiver.Total V) : (g • e).right = g • e.right :=
  GraphAction.smul_right g e

end Action

/-- A finitely generated subgroup of the automorphism group of a non-empty tree has a cocompact
invariant subtree: there is a non-empty convex `H`-invariant set of vertices on which `H` has
finitely many orbits of vertices and of edges. -/
theorem exists_invariant_cocompact_subtree {G : Type*} {V : Type*} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    [Nonempty V] (hT : Work.ORBassSerre.IsTree V) (H : Subgroup G) (hH : H.FG) :
    ∃ S : Set V, S.Nonempty ∧ Work.ORBassSerre.IsInvariantUnder H S ∧
      Work.ORBassSerre.IsConvexSet S ∧ Work.ORBassSerre.HasFinitelyManyOrbits H S ∧
      Work.ORBassSerre.HasFinitelyManyEdgeOrbits H S := by
  classical
  obtain ⟨v0⟩ := (inferInstance : Nonempty V)
  obtain ⟨gens, hgens⟩ := Subgroup.isMulFG_iff.mp hH
  -- The finite set of vertices consisting of the base point and the segments towards the
  -- images of the base point under the generators (and their inverses).
  set K : Set V := {v | v = v0 ∨ ∃ x ∈ (gens : Set G),
      v ∈ reducedSpan v0 (x • v0) ∨ v ∈ reducedSpan v0 (x⁻¹ • v0)} with hKdef
  have hKfin : K.Finite := by
    have h1 : (⋃ x ∈ (gens : Set G),
        (reducedSpan v0 (x • v0) ∪ reducedSpan v0 (x⁻¹ • v0))).Finite := by
      refine Set.Finite.biUnion gens.finite_toSet (fun x _ => ?_)
      exact (reducedSpan_finite (hT := hT) v0 (x • v0)).union
        (reducedSpan_finite (hT := hT) v0 (x⁻¹ • v0))
    refine Set.Finite.subset ((Set.finite_singleton v0).union h1) ?_
    intro v hv
    rw [hKdef] at hv
    rcases hv with hv | ⟨x, hx, hv⟩
    · exact Or.inl hv
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨x, hx, hv⟩)
  obtain ⟨F, hF⟩ := Work.ORBassSerre.Tree.Seg.exists_finset_arrows (hT := hT) K hKfin
  -- `A` is the `H`-saturation of `K`.
  set A : Set V := {v | ∃ g : G, g ∈ H ∧ ∃ k : V, k ∈ K ∧ g • k = v} with hAdef
  have mem_A : ∀ (k : V), k ∈ K → ∀ (g : G), g ∈ H → g • k ∈ A :=
    fun k hk g hg => ⟨g, hg, k, hk, rfl⟩
  have hK0 : v0 ∈ K := by
    rw [hKdef]
    exact Or.inl rfl
  -- The candidate invariant subtree: the union of the geodesics from `v0` to its `H`-translates.
  set S : Set V := ⋃ h : H, reducedSpan v0 ((h : G) • v0) with hSdef
  have mem_S : ∀ v : V, v ∈ S ↔ ∃ h : H, v ∈ reducedSpan v0 ((h : G) • v0) := by
    intro v
    rw [hSdef]
    exact Set.mem_iUnion
  have hgen : ∀ y ∈ (gens : Set G),
      reducedSpan v0 (y • v0) ⊆ K ∧ reducedSpan v0 (y⁻¹ • v0) ⊆ K := by
    intro y hy
    constructor
    · intro v hv
      rw [hKdef]
      exact Or.inr ⟨y, hy, Or.inl hv⟩
    · intro v hv
      rw [hKdef]
      exact Or.inr ⟨y, hy, Or.inr hv⟩
  -- Every vertex of `reducedSpan v0 (h • v0)` is an `H`-translate of an element of `K`.
  have vertex_key : ∀ h : G, h ∈ Subgroup.closure (gens : Set G) →
      ∀ g : G, g ∈ H → reducedSpan (g • v0) ((g * h) • v0) ⊆ A := by
    intro h hh
    refine Subgroup.closure_induction_right
      (p := fun h _ => ∀ g : G, g ∈ H → reducedSpan (g • v0) ((g * h) • v0) ⊆ A)
      ?_ ?_ ?_ hh
    · intro g hg v hv
      rw [mul_one, reducedSpan_self (hT := hT) (g • v0), Set.mem_singleton_iff] at hv
      subst hv
      exact mem_A v0 hK0 g hg
    · intro x hx y hy ih g hg v hv
      have hunion := reducedSpan_subset_union (hT := hT) (g • v0) ((g * x) • v0)
        ((g * (x * y)) • v0)
      rcases hunion hv with hv | hv
      · exact ih g hg hv
      · have h1 : (g * x)⁻¹ • v ∈ reducedSpan v0 (y • v0) := by
          refine (Work.ORBassSerre.Tree.Seg.smul_reducedSpan (g := g * x) v0 (y • v0) v).mp ?_
          simp only [mul_smul] at hv ⊢
          exact hv
        exact smul_inv_smul (g * x) v ▸
          mem_A ((g * x)⁻¹ • v) ((hgen y hy).1 h1) (g * x) (H.mul_mem hg (hgens.le hx))
    · intro x hx y hy ih g hg v hv
      have hunion := reducedSpan_subset_union (hT := hT) (g • v0) ((g * x) • v0)
        ((g * (x * y⁻¹)) • v0)
      rcases hunion hv with hv | hv
      · exact ih g hg hv
      · have h1 : (g * x)⁻¹ • v ∈ reducedSpan v0 (y⁻¹ • v0) := by
          refine (Work.ORBassSerre.Tree.Seg.smul_reducedSpan (g := g * x) v0 (y⁻¹ • v0) v).mp ?_
          simp only [mul_smul] at hv ⊢
          exact hv
        exact smul_inv_smul (g * x) v ▸
          mem_A ((g * x)⁻¹ • v) ((hgen y hy).2 h1) (g * x) (H.mul_mem hg (hgens.le hx))
  have vertex_key' : ∀ h : H, reducedSpan v0 ((h : G) • v0) ⊆ A := by
    intro h
    have hmem : (h : G) ∈ Subgroup.closure (gens : Set G) := hgens.symm ▸ h.2
    have h1 := vertex_key (h : G) hmem 1 H.one_mem
    simpa using h1
  -- Arrows whose endpoints lie in `reducedSpan (g • v0) ((g * y) • v0)` for a generator `y`
  -- are `H`-translates of elements of the finite set `F`.
  have edge_gen : ∀ (g : G), g ∈ H → ∀ y : G, reducedSpan v0 (y • v0) ⊆ K →
      ∀ e : Quiver.Total V,
        e.left ∈ reducedSpan (g • v0) ((g * y) • v0) →
        e.right ∈ reducedSpan (g • v0) ((g * y) • v0) →
        ∃ g' : G, g' ∈ H ∧ ∃ f ∈ F, g' • f = e := by
    intro g hg y hyK e h1 h2
    have h1' : g⁻¹ • e.left ∈ reducedSpan v0 (y • v0) := by
      refine (Work.ORBassSerre.Tree.Seg.smul_reducedSpan (g := g) v0 (y • v0) e.left).mp ?_
      simp only [mul_smul] at h1 ⊢
      exact h1
    have h2' : g⁻¹ • e.right ∈ reducedSpan v0 (y • v0) := by
      refine (Work.ORBassSerre.Tree.Seg.smul_reducedSpan (g := g) v0 (y • v0) e.right).mp ?_
      simp only [mul_smul] at h2 ⊢
      exact h2
    have hF' : g⁻¹ • e ∈ F := hF _ (by simpa using hyK h1') (by simpa using hyK h2')
    exact ⟨g, hg, g⁻¹ • e, hF', by rw [smul_inv_smul]⟩
  -- The same statement for a product of generators.
  have edge_key : ∀ h : G, h ∈ Subgroup.closure (gens : Set G) →
      ∀ g : G, g ∈ H → ∀ e : Quiver.Total V,
        e.left ∈ reducedSpan (g • v0) ((g * h) • v0) →
        e.right ∈ reducedSpan (g • v0) ((g * h) • v0) →
        ∃ g' : G, g' ∈ H ∧ ∃ f ∈ F, g' • f = e := by
    intro h hh
    refine Subgroup.closure_induction_right
      (p := fun h _ => ∀ g : G, g ∈ H → ∀ e : Quiver.Total V,
        e.left ∈ reducedSpan (g • v0) ((g * h) • v0) →
        e.right ∈ reducedSpan (g • v0) ((g * h) • v0) →
        ∃ g' : G, g' ∈ H ∧ ∃ f ∈ F, g' • f = e) ?_ ?_ ?_ hh
    · intro g hg e h1 h2
      rw [mul_one, reducedSpan_self (hT := hT) (g • v0), Set.mem_singleton_iff] at h1 h2
      exact absurd ⟨e.hom⟩ (not_nonempty_hom_of_eq (hT := hT) (h1.trans h2.symm))
    · intro x hx y hy ih g hg e h1 h2
      have hunion := reducedSpan_subset_union (hT := hT) (g • v0) ((g * x) • v0)
        ((g * (x * y)) • v0)
      have hz1 : (g * x) • v0 ∈ reducedSpan (g • v0) ((g * x) • v0) :=
        end_mem_reducedSpan (hT := hT) _ _
      have hz2 : (g * x) • v0 ∈ reducedSpan ((g * x) • v0) ((g * (x * y)) • v0) :=
        start_mem_reducedSpan (hT := hT) _ _
      rcases Work.ORBassSerre.Tree.Seg.arrow_subset_of_convex_cover (hT := hT)
        (Work.ORBassSerre.Tree.Seg.isConvexSet_reducedSpan (hT := hT) (g • v0) ((g * x) • v0))
        (Work.ORBassSerre.Tree.Seg.isConvexSet_reducedSpan (hT := hT) ((g * x) • v0)
          ((g * (x * y)) • v0))
        hz1 hz2 e.hom (hunion h1) (hunion h2) with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact ih g hg e ha hb
      · refine edge_gen (g * x) (H.mul_mem hg (hgens.le hx)) y (hgen y hy).1 e ?_ ?_
        · simpa only [mul_assoc] using ha
        · simpa only [mul_assoc] using hb
    · intro x hx y hy ih g hg e h1 h2
      have hunion := reducedSpan_subset_union (hT := hT) (g • v0) ((g * x) • v0)
        ((g * (x * y⁻¹)) • v0)
      have hz1 : (g * x) • v0 ∈ reducedSpan (g • v0) ((g * x) • v0) :=
        end_mem_reducedSpan (hT := hT) _ _
      have hz2 : (g * x) • v0 ∈ reducedSpan ((g * x) • v0) ((g * (x * y⁻¹)) • v0) :=
        start_mem_reducedSpan (hT := hT) _ _
      rcases Work.ORBassSerre.Tree.Seg.arrow_subset_of_convex_cover (hT := hT)
        (Work.ORBassSerre.Tree.Seg.isConvexSet_reducedSpan (hT := hT) (g • v0) ((g * x) • v0))
        (Work.ORBassSerre.Tree.Seg.isConvexSet_reducedSpan (hT := hT) ((g * x) • v0)
          ((g * (x * y⁻¹)) • v0))
        hz1 hz2 e.hom (hunion h1) (hunion h2) with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact ih g hg e ha hb
      · refine edge_gen (g * x) (H.mul_mem hg (hgens.le hx)) y⁻¹ (hgen y hy).2 e ?_ ?_
        · simpa only [mul_assoc] using ha
        · simpa only [mul_assoc] using hb
  have edge_key' : ∀ h : H, ∀ e : Quiver.Total V,
      e.left ∈ reducedSpan v0 ((h : G) • v0) → e.right ∈ reducedSpan v0 ((h : G) • v0) →
      ∃ g' : G, g' ∈ H ∧ ∃ f ∈ F, g' • f = e := by
    intro h e h1 h2
    have hmem : (h : G) ∈ Subgroup.closure (gens : Set G) := hgens.symm ▸ h.2
    have h1' : e.left ∈ reducedSpan ((1 : G) • v0) (((1 : G) * (h : G)) • v0) := by
      simpa using h1
    have h2' : e.right ∈ reducedSpan ((1 : G) • v0) (((1 : G) * (h : G)) • v0) := by
      simpa using h2
    exact edge_key (h : G) hmem 1 H.one_mem e h1' h2'
  refine ⟨S, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨v0, (mem_S v0).mpr ⟨1, by simpa using self_mem_reducedSpan v0⟩⟩
  · rw [isInvariantUnder_iff]
    intro h v hv
    rw [mem_S] at hv ⊢
    obtain ⟨h', hh'⟩ := hv
    have h2 : (h : G) • v ∈ reducedSpan ((h : G) • v0) (((h : G) * h') • v0) := by
      have h3 := (Work.ORBassSerre.Tree.Seg.smul_reducedSpan (g := (h : G)) v0
        ((h' : G) • v0) ((h : G) • v)).mpr (by simpa using hh')
      simpa only [mul_smul] using h3
    have hunion := reducedSpan_subset_union (hT := hT) ((h : G) • v0) v0
      (((h : G) * h') • v0)
    rcases hunion h2 with h3 | h3
    · refine ⟨h, ?_⟩
      rw [Work.ORBassSerre.Tree.Seg.reducedSpan_comm ((h : G) • v0) v0] at h3
      exact h3
    · exact ⟨⟨(h : G) * h', H.mul_mem h.2 h'.2⟩, h3⟩
  · intro a ha b hb p hp w hw
    have hmem : w ∈ reducedSpan a b := ⟨p, hp, hw⟩
    rw [mem_S] at ha hb
    obtain ⟨h₁, hh₁⟩ := ha
    obtain ⟨h₂, hh₂⟩ := hb
    obtain ⟨m, hmab, hmbv, hmv0a⟩ :=
      Work.ORBassSerre.Tree.Seg.exists_median (hT := hT) a b v0
    have hsplit : reducedSpan a b = reducedSpan a m ∪ reducedSpan m b :=
      Work.ORBassSerre.Tree.Seg.reducedSpan_eq_union_of_mem (hT := hT) hmab
    have hsub : reducedSpan a b ⊆ S := by
      rw [hsplit]
      rintro w' (hw' | hw')
      · rw [mem_S]
        refine ⟨h₁, ?_⟩
        have hmS : m ∈ reducedSpan v0 ((h₁ : G) • v0) :=
          IsConvexSet.reducedSpan_subset
            (Work.ORBassSerre.Tree.Seg.isConvexSet_reducedSpan (hT := hT) v0 ((h₁ : G) • v0))
            (start_mem_reducedSpan (hT := hT) v0 ((h₁ : G) • v0)) hh₁ hmv0a
        exact IsConvexSet.reducedSpan_subset
          (Work.ORBassSerre.Tree.Seg.isConvexSet_reducedSpan (hT := hT) v0 ((h₁ : G) • v0))
          hh₁ hmS hw'
      · rw [mem_S]
        refine ⟨h₂, ?_⟩
        have hmS : m ∈ reducedSpan v0 ((h₂ : G) • v0) :=
          IsConvexSet.reducedSpan_subset
            (Work.ORBassSerre.Tree.Seg.isConvexSet_reducedSpan (hT := hT) v0 ((h₂ : G) • v0))
            hh₂ (start_mem_reducedSpan (hT := hT) v0 ((h₂ : G) • v0)) hmbv
        exact IsConvexSet.reducedSpan_subset
          (Work.ORBassSerre.Tree.Seg.isConvexSet_reducedSpan (hT := hT) v0 ((h₂ : G) • v0))
          hmS hh₂ hw'
    exact hsub hmem
  · refine ⟨hKfin.toFinset, ?_⟩
    intro v hv
    rw [mem_S] at hv
    obtain ⟨h, hh⟩ := hv
    obtain ⟨g, hg, k, hk, hgk⟩ := vertex_key' h hh
    exact ⟨g, hg, k, (Set.Finite.mem_toFinset hKfin).mpr hk, hgk⟩
  · refine ⟨F, ?_⟩
    intro e he1 he2
    rw [mem_S] at he1 he2
    obtain ⟨h₁, hh₁⟩ := he1
    obtain ⟨h₂, hh₂⟩ := he2
    rcases Work.ORBassSerre.Tree.Seg.arrow_subset_of_convex_cover (hT := hT)
      (Work.ORBassSerre.Tree.Seg.isConvexSet_reducedSpan (hT := hT) v0 ((h₁ : G) • v0))
      (Work.ORBassSerre.Tree.Seg.isConvexSet_reducedSpan (hT := hT) v0 ((h₂ : G) • v0))
      (start_mem_reducedSpan (hT := hT) v0 ((h₁ : G) • v0))
      (start_mem_reducedSpan (hT := hT) v0 ((h₂ : G) • v0))
      e.hom (Or.inl hh₁) (Or.inr hh₂) with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact edge_key' h₁ e ha hb
    · exact edge_key' h₂ e ha hb

end Work.ORBassSerre.Action
