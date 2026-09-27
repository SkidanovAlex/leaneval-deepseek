import Mathlib
import Submission.Work.Noncompact.CompressionTube.LineBuild.nested_canals

/-!
# Separation of the arcs of one spine

For a single strand `b` of the routing (`SpineData`), the arc `γ b i` is confined to the shell
`K (i+2) \ K i`:  `γ b i '' Icc ⊆ interior (K (i+2))` and `γ b i '' Icc ∩ K i = ∅`.

Hence for `i + 2 ≤ j` the arc at level `i` lies *inside* `K (i+2)` while the arc at level `j`
misses `K j ⊇ K (i+2)`: the two arcs of one strand at levels differing by at least two are
disjoint.  The same computation shows that the arc at level `m ≥ i+2` misses the whole *interior*
of `K (i+2)`; consequently a neighbourhood of the next junction `q b (i+1)` contained in that
interior (which exists because `q b (i+1) ∈ interior (K (i+2))` for `i + 1 > lev b`) meets none of
the later arcs.  This is what allows one to keep a small neighbourhood of the next junction *out*
of the obstacle of the line construction while still forcing each piece to avoid all future arcs.
-/

namespace Work.Noncompact.CompressionTube

open Set Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]

/-- The arcs of one strand at levels differing by at least two are disjoint. -/
theorem nc_arc_disjoint_of_two_le (K : ℕ → Set M) (hKmono : Monotone K) (B : Set M) (lev : B → ℕ)
    (q : B → ℕ → M) (γ : B → ℕ → ℝ → M) (h : SpineData K B lev q γ) {b : B} {i j : ℕ}
    (hi : lev b ≤ i) (hj : lev b ≤ j) (hij : i + 2 ≤ j) :
    Disjoint (γ b i '' Set.Icc (0:ℝ) 1) (γ b j '' Set.Icc (0:ℝ) 1) := by
  refine Set.disjoint_left.mpr fun x hx hy => ?_
  obtain ⟨t, ht, rfl⟩ := hx
  have hxK : γ b i t ∈ K j := hKmono hij (interior_subset (h.image_sub b i hi t ht))
  exact Set.disjoint_left.mp (h.disjoint_K b j hj) hy hxK

/-- An arc at level `m ≥ i + 2` misses the interior of `K (i+2)`. -/
theorem nc_arc_avoid_interior (K : ℕ → Set M) (hKmono : Monotone K) (B : Set M) (lev : B → ℕ)
    (q : B → ℕ → M) (γ : B → ℕ → ℝ → M) (h : SpineData K B lev q γ) {b : B} {i m : ℕ}
    (hm : lev b ≤ m) (him : i + 2 ≤ m) :
    Disjoint (γ b m '' Set.Icc (0:ℝ) 1) (interior (K (i + 2))) := by
  refine Set.disjoint_left.mpr fun x hx hy => ?_
  have hxK : x ∈ K m := hKmono him (interior_subset hy)
  exact Set.disjoint_left.mp (h.disjoint_K b m hm) hx hxK

/-- Any set contained in `interior (K (i+2))` (for instance a small neighbourhood of the junction
`q b (i+1)`) meets none of the arcs at level `≥ i + 2`. -/
theorem nc_set_in_interior_avoids_later_arcs (K : ℕ → Set M) (hKmono : Monotone K) (B : Set M)
    (lev : B → ℕ) (q : B → ℕ → M) (γ : B → ℕ → ℝ → M) (h : SpineData K B lev q γ) {b : B}
    {i m : ℕ} {U : Set M} (hU : U ⊆ interior (K (i + 2))) (hm : lev b ≤ m) (him : i + 2 ≤ m) :
    Disjoint (γ b m '' Set.Icc (0:ℝ) 1) U :=
  (nc_arc_avoid_interior K hKmono B lev q γ h hm him).mono_right hU

end Work.Noncompact.CompressionTube
