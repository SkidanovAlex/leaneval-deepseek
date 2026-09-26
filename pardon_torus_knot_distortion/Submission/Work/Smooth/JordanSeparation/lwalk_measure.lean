import Mathlib
import Submission.Work.Smooth.JordanSeparation.lwalk_lexmin

/-!
# The termination measure of the peel

The peel of a closed lattice walk proceeds by two moves: at a simple walk it moves the
lexicographically maximal vertex to the opposite corner of the cell it spans (keeping the number of
edges), and at a non-simple walk it cuts at a double point (decreasing the number of edges).  The
measure below decreases under both:

* `peelMeasure N W = W.n * (BND N + 1) + (BND N - lexRank W)`, where `lexRank W` counts the lattice
  points of the box of radius `3 * W.n` around the lex-minimal vertex that lie lexicographically
  above the lex-maximal vertex.

A corner move keeps `W.n` and the lex-min vertex (`lexmin_le_vmax_sub_one`) and strictly decreases
the lex-max vertex, hence strictly increases `lexRank`; a cut strictly decreases `W.n`, which
dominates everything else because `lexRank ≤ BND`.
-/

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The lattice points of the box of radius `R` around `q`, as a finset. -/
def boxFinset (q : ℤ × ℤ) (R : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (q.1 - (R : ℤ)) (q.1 + (R : ℤ)) ×ˢ
    Finset.Icc (q.2 - (R : ℤ)) (q.2 + (R : ℤ))

theorem mem_boxFinset {q a : ℤ × ℤ} {R : ℕ} :
    a ∈ boxFinset q R ↔ a.1 ∈ Finset.Icc (q.1 - (R : ℤ)) (q.1 + (R : ℤ)) ∧
      a.2 ∈ Finset.Icc (q.2 - (R : ℤ)) (q.2 + (R : ℤ)) :=
  Finset.mem_product

theorem card_boxFinset (q : ℤ × ℤ) (R : ℕ) : (boxFinset q R).card = (2 * R + 1) ^ 2 := by
  rw [boxFinset, Finset.card_product, Int.card_Icc, Int.card_Icc]
  have h1 : (q.1 + (R : ℤ) + 1 - (q.1 - (R : ℤ))).toNat = 2 * R + 1 := by omega
  have h2 : (q.2 + (R : ℤ) + 1 - (q.2 - (R : ℤ))).toNat = 2 * R + 1 := by omega
  rw [h1, h2]
  ring

/-- The number of lattice points of the box of radius `3 * W.n` around the lex-minimal vertex of
`W` that lie lexicographically above the lex-maximal vertex of `W`. -/
def lexRank (W : LWalk) : ℕ :=
  ((boxFinset (vmin W) (3 * W.n)).filter (fun q => LexLt (vmax W) q)).card

theorem lexRank_le (W : LWalk) : lexRank W ≤ (6 * W.n + 1) ^ 2 := by
  refine le_trans ((boxFinset (vmin W) (3 * W.n)).card_filter_le _) ?_
  rw [card_boxFinset]
  ring_nf
  exact le_rfl

/-! ### Vertices lie in the box around the lex-minimal vertex -/

theorem vmin1_ge (W : LWalk) : (W.v 0).1 - (W.n : ℤ) ≤ vmin1 W := by
  obtain ⟨j, hj, hj'⟩ := exists_vmin1 W
  rw [← hj']
  have := coord_bound_left W j hj
  omega

theorem vmax1_le (W : LWalk) : vmax1 W ≤ (W.v 0).1 + (W.n : ℤ) := by
  obtain ⟨j, hj, hj'⟩ := exists_vmax1 W
  rw [← hj']
  have := coord_bound_right W j hj
  omega

theorem vmin2_ge (W : LWalk) : (W.v 0).2 - (W.n : ℤ) ≤ vmin2 W := by
  obtain ⟨j, hj, hj'⟩ := Finset.exists_mem_eq_inf' (filter_vmin1_nonempty W) (fun k => (W.v k).2)
  have hjn : j ≤ W.n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
  have h : vmin2 W = (W.v j).2 := hj'
  have := coord_bound_left2 W j hjn
  omega

theorem vmax2_le (W : LWalk) : vmax2 W ≤ (W.v 0).2 + (W.n : ℤ) := by
  obtain ⟨j, hj, hj'⟩ := Finset.exists_mem_eq_sup' (filter_vmax1_nonempty W) (fun k => (W.v k).2)
  have hjn : j ≤ W.n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
  have h : vmax2 W = (W.v j).2 := hj'
  have := coord_bound_right2 W j hjn
  omega

theorem vmin1_le_v0 (W : LWalk) : vmin1 W ≤ (W.v 0).1 := vmin1_le W (Nat.zero_le W.n)

theorem vmin2_le_v0 (W : LWalk) : vmin2 W ≤ (W.v 0).2 + (W.n : ℤ) := by
  obtain ⟨j, hj, hj'⟩ := Finset.exists_mem_eq_inf' (filter_vmin1_nonempty W) (fun k => (W.v k).2)
  have hjn : j ≤ W.n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
  have h : vmin2 W = (W.v j).2 := hj'
  have := coord_bound_right2 W j hjn
  omega

theorem vertex_mem_box (W : LWalk) {k : ℕ} (hk : k ≤ W.n) :
    W.v k ∈ boxFinset (vmin W) (3 * W.n) := by
  rw [mem_boxFinset, Finset.mem_Icc, Finset.mem_Icc]
  push_cast
  have h1 := coord_bound_left W k hk
  have h2 := coord_bound_right W k hk
  have h3 := coord_bound_left2 W k hk
  have h4 := coord_bound_right2 W k hk
  have h5 := vmin1_ge W
  have h6 := vmin2_ge W
  have h7 := le_vmax1 W hk
  have h8 := vmin1_le_v0 W
  have h9 := vmin2_le_v0 W
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · change vmin1 W - 3 * (W.n : ℤ) ≤ (W.v k).1
    omega
  · change (W.v k).1 ≤ vmin1 W + 3 * (W.n : ℤ)
    omega
  · change vmin2 W - 3 * (W.n : ℤ) ≤ (W.v k).2
    omega
  · change (W.v k).2 ≤ vmin2 W + 3 * (W.n : ℤ)
    omega

/-! ### Monotonicity of the measure -/

/-- A corner move keeps the number of edges and the lex-min vertex and strictly decreases the
lex-max vertex, hence strictly increases `lexRank`. -/
theorem lexRank_lt {W W' : LWalk} (hn : W'.n = W.n) (hvmin : vmin W' = vmin W)
    (hvmax : LexLt (vmax W') (vmax W)) : lexRank W < lexRank W' := by
  classical
  have hsub : (boxFinset (vmin W) (3 * W.n)).filter (fun q => LexLt (vmax W) q) ⊆
      (boxFinset (vmin W') (3 * W'.n)).filter (fun q => LexLt (vmax W') q) := by
    intro q hq
    rw [Finset.mem_filter] at hq ⊢
    exact ⟨by rw [hvmin, hn]; exact hq.1, lexLt_trans hvmax hq.2⟩
  have hmem : vmax W ∈ (boxFinset (vmin W') (3 * W'.n)).filter (fun q => LexLt (vmax W') q) := by
    rw [Finset.mem_filter]
    refine ⟨?_, hvmax⟩
    obtain ⟨k, hk, hk'⟩ := exists_vmax W
    have h := vertex_mem_box W hk
    rw [hvmin, hn, ← hk']
    exact h
  have hnot : vmax W ∉ (boxFinset (vmin W) (3 * W.n)).filter (fun q => LexLt (vmax W) q) :=
    fun h => lexLt_irrefl (vmax W) (Finset.mem_filter.mp h).2
  exact Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hnot (h ▸ hmem)⟩)

/-- The uniform bound for `lexRank` of walks with at most `N` edges. -/
def bnd (N : ℕ) : ℕ := (6 * N + 1) ^ 2 + 1

theorem lexRank_le_bnd {W : LWalk} {N : ℕ} (hN : W.n ≤ N) : lexRank W ≤ bnd N := by
  refine le_trans (lexRank_le W) ?_
  rw [bnd]
  have : 6 * W.n + 1 ≤ 6 * N + 1 := by omega
  exact le_trans (Nat.pow_le_pow_left this 2) (Nat.le_succ _)

/-- The termination measure of the peel. -/
def peelMeasure (N : ℕ) (W : LWalk) : ℕ := W.n * (bnd N + 1) + (bnd N - lexRank W)

/-- A corner move strictly decreases the measure. -/
theorem peelMeasure_corner {W W' : LWalk} {N : ℕ} (hN : W.n ≤ N) (hN' : W'.n ≤ N)
    (hn : W'.n = W.n) (hvmin : vmin W' = vmin W) (hvmax : LexLt (vmax W') (vmax W)) :
    peelMeasure N W' < peelMeasure N W := by
  have h1 := lexRank_lt hn hvmin hvmax
  have h2 := lexRank_le_bnd hN
  have h3 := lexRank_le_bnd hN'
  rw [peelMeasure, peelMeasure, hn]
  omega

/-- A cut strictly decreases the measure. -/
theorem peelMeasure_cut {W W' : LWalk} {N : ℕ} (hN : W.n ≤ N) (hN' : W'.n ≤ N)
    (hlt : W'.n < W.n) : peelMeasure N W' < peelMeasure N W := by
  have h3 : bnd N - lexRank W' ≤ bnd N := Nat.sub_le _ _
  have h4 : W'.n ≤ W.n - 1 := by omega
  have hfive : (W.n - 1) * (bnd N + 1) + bnd N < W.n * (bnd N + 1) := by
    have h6 : 1 ≤ W.n := by omega
    have h7 : W.n * (bnd N + 1) = (W.n - 1) * (bnd N + 1) + (bnd N + 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel h6]
      rw [Nat.add_mul, one_mul]
    omega
  rw [peelMeasure]
  calc W'.n * (bnd N + 1) + (bnd N - lexRank W')
      ≤ (W.n - 1) * (bnd N + 1) + bnd N := Nat.add_le_add (Nat.mul_le_mul_right _ h4) h3
    _ < W.n * (bnd N + 1) := hfive
    _ ≤ W.n * (bnd N + 1) + (bnd N - lexRank W) := Nat.le_add_right _ _

end

end Work.Smooth.JordanSeparation
