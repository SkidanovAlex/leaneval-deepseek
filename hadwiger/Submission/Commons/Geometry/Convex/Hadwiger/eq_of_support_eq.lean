import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation

namespace Commons.Geometry.Convex.Hadwiger

open Filter
open scoped Topology

/-! A convex body in a finite-dimensional real inner product space is determined
by its support function `u ↦ sSup {⟨u, x⟩ | x ∈ K}`. -/

theorem eq_of_support_eq
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    (K L : ConvexBody V)
    (h : ∀ u : V, sSup ((fun x : V => inner ℝ u x) '' (K : Set V)) =
                   sSup ((fun x : V => inner ℝ u x) '' (L : Set V))) :
    (K : Set V) = (L : Set V) := by
  have incl : ∀ A B : ConvexBody V,
      (∀ u : V, sSup ((fun x : V => inner ℝ u x) '' (A : Set V)) =
                 sSup ((fun x : V => inner ℝ u x) '' (B : Set V))) →
      (A : Set V) ⊆ (B : Set V) := by
    intro A B hAB x hxA
    by_contra hxnB
    -- Strictly separate the point `x` from the closed convex body `B`.
    obtain ⟨f, u, hBf, hfx⟩ :=
      geometric_hahn_banach_closed_point (E := V) (s := (B : Set V)) (x := x) B.convex B.isClosed hxnB
    -- Represent the dual functional `f` by an inner product with a vector `w`.
    let w : V := (InnerProductSpace.toDual ℝ V).symm f
    have hw : ∀ y : V, inner ℝ w y = f y := by
      intro y
      exact InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := V) (x := y) (y := f)
    have hcont : Continuous (fun y : V => inner ℝ w y) := by
      simpa [w, hw] using f.continuous
    have hsep : ∀ y ∈ (B : Set V), inner ℝ w y < inner ℝ w x := by
      intro y hyB
      calc
        inner ℝ w y = f y := hw y
        _ < f x := lt_trans (hBf y hyB) hfx
        _ = inner ℝ w x := (hw x).symm
    -- The maximum of `⟨w, ·⟩` on the compact set `A` bounds its image above.
    have hbddA : BddAbove ((fun x : V => inner ℝ w x) '' (A : Set V)) := by
      obtain ⟨y₀, hy₀A, hmax⟩ := A.isCompact.exists_isMaxOn (s := (A : Set V)) A.nonempty
        (f := fun y : V => inner ℝ w y) (hf := hcont.continuousOn)
      refine ⟨inner ℝ w y₀, ?_⟩
      rintro b ⟨y, hyA, rfl⟩
      exact hmax hyA
    have hx_le_supA : inner ℝ w x ≤ sSup ((fun x : V => inner ℝ w x) '' (A : Set V)) := by
      exact le_csSup hbddA (Set.mem_image_of_mem (fun x : V => inner ℝ w x) hxA)
    -- Since `B` is compact, the supremum over `B` is attained, hence it is
    -- strictly smaller than `⟨w, x⟩` by the strict separation inequality.
    have hsupB_lt : sSup ((fun x : V => inner ℝ w x) '' (B : Set V)) < inner ℝ w x := by
      obtain ⟨y₀, hy₀B, hmax⟩ := B.isCompact.exists_isMaxOn (s := (B : Set V)) B.nonempty
        (f := fun y : V => inner ℝ w y) (hf := hcont.continuousOn)
      refine lt_of_le_of_lt ?_ (hsep y₀ hy₀B)
      refine csSup_le ?_ ?_
      · exact Set.image_nonempty.mpr B.nonempty
      · rintro b ⟨y, hyB, rfl⟩
        exact hmax hyB
    -- But `x ∈ A` forces `⟨w, x⟩ ≤ sup over A = sup over B`, contradiction.
    have hx_le_supB : inner ℝ w x ≤ sSup ((fun x : V => inner ℝ w x) '' (B : Set V)) := by
      calc
        inner ℝ w x ≤ sSup ((fun x : V => inner ℝ w x) '' (A : Set V)) := hx_le_supA
        _ = sSup ((fun x : V => inner ℝ w x) '' (B : Set V)) := hAB w
    exact (not_lt_of_ge hx_le_supB) hsupB_lt
  apply Set.Subset.antisymm
  · exact incl K L h
  · exact incl L K (fun u => (h u).symm)

end Commons.Geometry.Convex.Hadwiger