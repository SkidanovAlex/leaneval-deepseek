import Submission.Work.Whitney.PathTools.GridGeom

/-!
# Geometry of the mesh grid, II

Cell/edge geometry used to feed `exists_chain_avoiding_union`: finiteness of the cells meeting a
compact set, disjointness of the two cell complexes of two compact sets at distance `> 8 h √2`,
the corresponding `star` condition, and the fact that an edge outside `edgeSet (cellSet h K)` has
its closed segment disjoint from `K`.
-/

namespace Work.Whitney.PathTools.Grid

noncomputable section

open scoped BigOperators

/-! ## Coordinate bounds -/

theorem dist_le_of_coord {x y : Pt} {C : ℝ} (h0 : |x 0 - y 0| ≤ C) (h1 : |x 1 - y 1| ≤ C) :
    dist x y ≤ C * Real.sqrt 2 := by
  have hC : 0 ≤ C := (abs_nonneg _).trans h0
  have e0 : dist (x.ofLp 0) (y.ofLp 0) = |x 0 - y 0| := by simp [Real.dist_eq]
  have e1 : dist (x.ofLp 1) (y.ofLp 1) = |x 1 - y 1| := by simp [Real.dist_eq]
  have key : dist x y ^ 2 ≤ (C * Real.sqrt 2) ^ 2 := by
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.sq_sqrt (by positivity), e0, e1, mul_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have k0 : |x 0 - y 0| ^ 2 ≤ C ^ 2 := by
      rw [sq_le_sq, abs_abs, abs_of_nonneg hC]; exact h0
    have k1 : |x 1 - y 1| ^ 2 ≤ C ^ 2 := by
      rw [sq_le_sq, abs_abs, abs_of_nonneg hC]; exact h1
    linarith
  have h2 := sq_le_sq.mp key
  rwa [abs_of_nonneg dist_nonneg, abs_of_nonneg (mul_nonneg hC (Real.sqrt_nonneg 2))] at h2

/-- `|a - b| ≤ 2` when `a` and `b` are each within `1` of a common point. -/
lemma abs_sub_le_two {a b z : ℝ} (h1 : |a - z| ≤ 1) (h2 : |z - b| ≤ 1) : |a - b| ≤ 2 := by
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

lemma gsq_fst {h : ℝ} {c : Cell} {x : Pt} (hx : x ∈ gsq h c) : h * (c.1 : ℝ) ≤ x 0 := hx.1

lemma gsq_fst' {h : ℝ} {c : Cell} {x : Pt} (hx : x ∈ gsq h c) : x 0 ≤ h * ((c.1 : ℝ) + 1) := hx.2.1

lemma gsq_snd {h : ℝ} {c : Cell} {x : Pt} (hx : x ∈ gsq h c) : h * (c.2 : ℝ) ≤ x 1 := hx.2.2.1

lemma gsq_snd' {h : ℝ} {c : Cell} {x : Pt} (hx : x ∈ gsq h c) : x 1 ≤ h * ((c.2 : ℝ) + 1) := hx.2.2.2

lemma abs_coord_le_norm (x : Pt) (i : Fin 2) : |x i| ≤ ‖x‖ := by
  have h := PiLp.norm_apply_le x i
  simpa [Real.norm_eq_abs] using h

/-- Coordinate bound for two points of two cells whose index pairs differ by at most `k`. -/
lemma dist_le_of_cell_diff {h : ℝ} (hh : 0 < h) {c₁ c₂ : Cell} {x y : Pt} {k : ℕ}
    (hx : x ∈ gsq h c₁) (hy : y ∈ gsq h c₂)
    (h1 : |(c₁.1 : ℝ) - (c₂.1 : ℝ)| ≤ (k : ℝ))
    (h2 : |(c₁.2 : ℝ) - (c₂.2 : ℝ)| ≤ (k : ℝ)) :
    dist x y ≤ ((k : ℝ) + 1) * h * Real.sqrt 2 := by
  have hx0 := gsq_fst hx; have hx0' := gsq_fst' hx
  have hy0 := gsq_fst hy; have hy0' := gsq_fst' hy
  have hx1 := gsq_snd hx; have hx1' := gsq_snd' hx
  have hy1 := gsq_snd hy; have hy1' := gsq_snd' hy
  refine dist_le_of_coord (C := ((k : ℝ) + 1) * h) ?_ ?_
  · rw [abs_le] at h1 ⊢; constructor <;> nlinarith [h1.1, h1.2]
  · rw [abs_le] at h2 ⊢; constructor <;> nlinarith [h2.1, h2.2]

private lemma abs_cast_sub_le_one {c₁ c₂ : Cell} {e : Edge} (h₁ : e ∈ cellEdges c₁)
    (h₂ : e ∈ cellEdges c₂) :
    |(c₁.1 : ℝ) - (c₂.1 : ℝ)| ≤ (1 : ℝ) ∧ |(c₁.2 : ℝ) - (c₂.2 : ℝ)| ≤ (1 : ℝ) := by
  rw [← mem_edgeCells_iff] at h₁ h₂
  obtain ⟨b, i, j⟩ := e
  cases b
  · simp only [edgeCells, Finset.mem_insert, Finset.mem_singleton] at h₁ h₂
    rcases h₁ with h | h <;> rcases h₂ with h' | h' <;>
      rw [h, h'] <;> push_cast <;> refine ⟨?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> linarith
  · simp only [edgeCells, Finset.mem_insert, Finset.mem_singleton] at h₁ h₂
    rcases h₁ with h | h <;> rcases h₂ with h' | h' <;>
      rw [h, h'] <;> push_cast <;> refine ⟨?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> linarith

lemma dist_le_of_share_edge {h : ℝ} (hh : 0 < h) {c₁ c₂ : Cell} {e : Edge}
    (h₁ : e ∈ cellEdges c₁) (h₂ : e ∈ cellEdges c₂) {x y : Pt}
    (hx : x ∈ gsq h c₁) (hy : y ∈ gsq h c₂) : dist x y ≤ 2 * h * Real.sqrt 2 := by
  have hc := abs_cast_sub_le_one h₁ h₂
  have key := dist_le_of_cell_diff (k := 1) hh hx hy (by simpa using hc.1) (by simpa using hc.2)
  rwa [show ((1 : ℕ) : ℝ) + 1 = 2 by norm_num] at key

/-! ## The "base cell" of an edge -/

/-- The lower-left cell of an edge. -/
def eCell (e : Edge) : Cell := (e.2.1, e.2.2)

lemma mem_cellEdges_eCell (e : Edge) : e ∈ cellEdges (eCell e) := by
  obtain ⟨b, i, j⟩ := e
  cases b <;> simp [eCell, cellEdges]

lemma gseg_subset_gsq {h : ℝ} (hh : 0 < h) (e : Edge) : gseg h e ⊆ gsq h (eCell e) := by
  rw [gseg, segment_eq_image]
  rintro z ⟨t, ht, rfl⟩
  obtain ⟨b, i, j⟩ := e
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  cases b
  · simp only [eCell, gsq, Set.mem_ofPred_eq, eTail_false, eHead_false,
      gptH_apply_zero, gptH_apply_one, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Int.cast_add, Int.cast_one]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [ht0, ht1, hh]
  · simp only [eCell, gsq, Set.mem_ofPred_eq, eTail_true, eHead_true,
      gptH_apply_zero, gptH_apply_one, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Int.cast_add, Int.cast_one]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [ht0, ht1, hh]

/-! ## Finiteness of the cells meeting a compact set -/

lemma cellSet_finite {h : ℝ} (hh : 0 < h) {K : Set Pt} (hK : IsCompact K) :
    (cellSet h K).Finite := by
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Pt)).mp hK.isBounded
  set R : ℝ := max R₀ 0 with hRdef
  have hR : K ⊆ Metric.closedBall (0 : Pt) R :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (R + h) / h ≤ (N : ℝ) := ⟨⌈(R + h) / h⌉₊, Nat.le_ceil _⟩
  have hbox : cellSet h K ⊆
      ((Finset.Icc (-(N : ℤ)) (N : ℤ)) ×ˢ (Finset.Icc (-(N : ℤ)) (N : ℤ)) : Finset Cell) := by
    rintro c ⟨x, hxg, hxK⟩
    have hxR : ‖x‖ ≤ R := by
      have := hR hxK; rwa [Metric.mem_closedBall, dist_zero_right] at this
    have hx0 : |x 0| ≤ R := (abs_coord_le_norm x 0).trans hxR
    have hx1 : |x 1| ≤ R := (abs_coord_le_norm x 1).trans hxR
    have key : ∀ {a : ℤ} {y : ℝ}, |y| ≤ R → h * (a : ℝ) ≤ y → y ≤ h * ((a : ℝ) + 1) →
        |(a : ℝ)| ≤ (N : ℝ) := by
      intro a y hy hy1 hy2
      have h4 : |h * (a : ℝ)| ≤ R + h := by
        rw [abs_le] at hy ⊢; constructor <;> nlinarith [hy1, hy2, hy.1, hy.2]
      have h5 : |(a : ℝ)| = |h * (a : ℝ)| / h := by
        rw [abs_mul, abs_of_pos hh, mul_div_cancel_left₀ _ (ne_of_gt hh)]
      rw [h5]
      calc |h * (a : ℝ)| / h ≤ (R + h) / h := div_le_div_of_nonneg_right h4 hh.le
        _ ≤ (N : ℝ) := hN
    have hc0 : |(c.1 : ℝ)| ≤ (N : ℝ) := key hx0 (gsq_fst hxg) (gsq_fst' hxg)
    have hc1 : |(c.2 : ℝ)| ≤ (N : ℝ) := key hx1 (gsq_snd hxg) (gsq_snd' hxg)
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_Icc]
    constructor
    · rw [abs_le] at hc0; exact ⟨by exact_mod_cast hc0.1, by exact_mod_cast hc0.2⟩
    · rw [abs_le] at hc1; exact ⟨by exact_mod_cast hc1.1, by exact_mod_cast hc1.2⟩
  exact Set.Finite.subset (Finset.finite_toSet _) hbox

/-! ## `cellSet_geometry` -/

theorem cellSet_geometry {h : ℝ} (hh : 0 < h) {K₁ K₂ : Set Pt}
    (hK₁ : IsCompact K₁) (hK₂ : IsClosed K₂)
    (hsep : ∀ x ∈ K₁, ∀ y ∈ K₂, 8 * h * Real.sqrt 2 < dist x y) :
    (cellSet h K₁).Finite ∧
    Disjoint (edgeSet (cellSet h K₁)) (edgeSet (cellSet h K₂)) ∧
    (∀ c, c ∈ starCells (cellSet h K₁) → c ∈ starCells (cellSet h K₂) → c ∈ cellSet h K₁) ∧
    (∀ e : Edge, e ∉ edgeSet (cellSet h K₁) → Disjoint (gseg h e) K₁) := by
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨cellSet_finite hh hK₁, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro e he₁ he₂
    obtain ⟨c₁, hc₁, hec₁⟩ := he₁
    obtain ⟨c₂, hc₂, hec₂⟩ := he₂
    obtain ⟨x, hxg₁, hxK₁⟩ := hc₁
    obtain ⟨y, hxg₂, hyK₂⟩ := hc₂
    have h2 : dist x y ≤ 2 * h * Real.sqrt 2 := dist_le_of_share_edge hh hec₁ hec₂ hxg₁ hxg₂
    have h3 := hsep x hxK₁ y hyK₂
    nlinarith [h2, h3, hsqrt2, hh]
  · intro c hc₁ hc₂
    obtain ⟨c₁, hc₁', e₁, he₁c, he₁c₁⟩ := hc₁
    obtain ⟨c₂, hc₂', e₂, he₂c, he₂c₂⟩ := hc₂
    obtain ⟨x, hxg₁, hxK₁⟩ := hc₁'
    obtain ⟨y, hxg₂, hyK₂⟩ := hc₂'
    have hA := abs_cast_sub_le_one he₁c₁ he₁c
    have hB := abs_cast_sub_le_one he₂c he₂c₂
    have hk1 : |(c₁.1 : ℝ) - (c₂.1 : ℝ)| ≤ (2 : ℝ) := abs_sub_le_two hA.1 hB.1
    have hk2 : |(c₁.2 : ℝ) - (c₂.2 : ℝ)| ≤ (2 : ℝ) := abs_sub_le_two hA.2 hB.2
    have h2 : dist x y ≤ 3 * h * Real.sqrt 2 := by
      have h0 : |x 0 - y 0| ≤ 3 * h := by
        rw [abs_le] at hk1 ⊢
        constructor <;> nlinarith [hk1.1, hk1.2, gsq_fst hxg₁, gsq_fst' hxg₁,
          gsq_fst hxg₂, gsq_fst' hxg₂]
      have h1 : |x 1 - y 1| ≤ 3 * h := by
        rw [abs_le] at hk2 ⊢
        constructor <;> nlinarith [hk2.1, hk2.2, gsq_snd hxg₁, gsq_snd' hxg₁,
          gsq_snd hxg₂, gsq_snd' hxg₂]
      exact dist_le_of_coord h0 h1
    have h3 := hsep x hxK₁ y hyK₂
    nlinarith [h2, h3, hsqrt2, hh]
  · intro e he
    rw [Set.disjoint_left]
    intro z hz1 hz2
    exact he ⟨eCell e, ⟨z, gseg_subset_gsq hh e hz1, hz2⟩, mem_cellEdges_eCell e⟩


/-! ## Walks and chains -/

/-- Mod-two cancellation of a shared vertex. -/
lemma add_pair_eq (a b c x : ℤ × ℤ) :
    ((if x = a then (1 : ZMod 2) else 0) + (if x = b then 1 else 0))
      + ((if x = b then 1 else 0) + (if x = c then 1 else 0))
    = (if x = a then 1 else 0) + (if x = c then 1 else 0) := by
  have hff : (if x = b then (1 : ZMod 2) else 0) + (if x = b then 1 else 0) = 0 :=
    CharTwo.add_self_eq_zero _
  rw [show ((if x = a then (1 : ZMod 2) else 0) + (if x = b then 1 else 0))
      + ((if x = b then 1 else 0) + (if x = c then 1 else 0))
      = (if x = a then 1 else 0) + ((if x = b then 1 else 0) + (if x = b then 1 else 0))
        + (if x = c then 1 else 0) from by abel, hff]
  abel

end

end Work.Whitney.PathTools.Grid
