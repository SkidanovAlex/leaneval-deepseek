import Mathlib

/-!
# "Tame tips" of arcs in a smooth manifold

This file sets up the vocabulary for the construction of a smooth, injective, proper line
`γ : ℝ → M` inside an open set `W` from a *pocket-free exhaustion* of `W`.

The construction extends a chain of arcs step by step.  At each step the chain has a *tame tip*:
there is a chart ball around the current endpoint in which the whole chain is exactly a straight
segment of the chart, ending at the endpoint.  The next piece must leave that endpoint in a free
direction and must not meet the chain elsewhere.  The vocabulary below records this.

* `TameTip O p` : the chart data (a chart, a radius, a direction) describing a tame tip at `p`;
* `TameTip.ball`, `TameTip.seg` : the associated chart ball and straight segment;
* `HasTameTip O Λ p` : the set `Λ` meets a chart ball around `p` exactly in a straight segment;
* `HasFreeBall O Λ q` : there is a chart ball around `q`, inside `O`, on which `Λ` is empty.
-/

namespace Work.Noncompact.ProperLine

open Set Topology

/-- The chart data describing a tame tip at `p`: a chart `c`, a radius `ρ` with the closed chart
ball of radius `ρ` around `p` contained in the target of `c` and with image in `O`, and a
direction `v ≠ 0`. -/
structure TameTip (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (O : Set M) (p : M) where
  /-- the chart -/
  c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))
  /-- the radius of the chart ball -/
  ρ : ℝ
  hρ : 0 < ρ
  hp : p ∈ c.source
  hclosed : Metric.closedBall (c p) ρ ⊆ c.target
  hsub : c.symm '' Metric.closedBall (c p) ρ ⊆ O
  /-- the direction in which the tip points -/
  v : EuclideanSpace ℝ (Fin n)
  hv : v ≠ 0

namespace TameTip

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
variable {O : Set M} {p : M} (t : TameTip n O p)

/-- The chart ball around `p`. -/
def ball : Set M := t.c.symm '' Metric.closedBall (t.c p) t.ρ

/-- The straight segment of the chart from `p` in the direction `-v`. -/
def seg : Set M :=
  t.c.symm '' {w | w ∈ Metric.closedBall (t.c p) t.ρ ∧
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ w = t.c p - s • t.v}

lemma ball_subset : t.ball ⊆ O := t.hsub

lemma p_mem_ball : p ∈ t.ball :=
  ⟨t.c p, Metric.mem_closedBall_self t.hρ.le, t.c.left_inv t.hp⟩

lemma seg_subset_ball : t.seg ⊆ t.ball := by
  rintro x ⟨w, hw, rfl⟩
  exact ⟨w, hw.1, rfl⟩

lemma p_mem_seg : p ∈ t.seg :=
  ⟨t.c p, ⟨Metric.mem_closedBall_self t.hρ.le, 0, le_rfl, by simp⟩, t.c.left_inv t.hp⟩

end TameTip

/-- `Λ` has a *tame tip* at `p` inside `O`: there is a chart ball around `p`, contained in `O`, in
which `Λ` is exactly a straight segment of the chart ending at `p`. -/
def HasTameTip (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (O Λ : Set M) (p : M) : Prop :=
  ∃ t : TameTip n O p, Λ ∩ t.ball = t.seg

/-- `q` is a *free target* for `Λ` inside `O`: there is a chart ball around `q`, inside `O`, on
which `Λ` is empty. -/
def HasFreeBall (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (O Λ : Set M) (q : M) : Prop :=
  ∃ t : TameTip n O q, Λ ∩ t.ball = ∅

lemma HasTameTip.mem {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {O Λ : Set M} {p : M}
    (h : HasTameTip n O Λ p) : p ∈ Λ := by
  obtain ⟨t, ht⟩ := h
  have : p ∈ Λ ∩ t.ball := by rw [ht]; exact t.p_mem_seg
  exact this.1

lemma HasFreeBall.notMem {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {O Λ : Set M} {q : M}
    (h : HasFreeBall n O Λ q) : q ∉ Λ := by
  obtain ⟨t, ht⟩ := h
  intro hq
  have : q ∈ Λ ∩ t.ball := ⟨hq, t.p_mem_ball⟩
  rw [ht] at this
  exact this

/-- The tame tip is preserved when the chain is enlarged by a set contained in it. -/
lemma HasTameTip.union {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {O Λ B : Set M} {p : M}
    (h : HasTameTip n O Λ p) (hB : B ⊆ Λ) : HasTameTip n O (Λ ∪ B) p := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t, ?_⟩
  have hsub : B ∩ t.ball ⊆ t.seg := by
    intro x hx
    have : x ∈ Λ ∩ t.ball := ⟨hB hx.1, hx.2⟩
    rwa [ht] at this
  rw [Set.union_inter_distrib_right, ht]
  exact Set.union_eq_left.mpr hsub

section FreeBall

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- **A free chart ball at a point, avoiding a compact obstacle.**

If `q` is a point of the open set `O` which is not in the compact set `Λ`, then there is a
`TameTip n O q` whose ball is disjoint from `Λ` (and contained in `O`). -/
theorem exists_freeBall (hn : 2 ≤ n) {O Λ : Set M} (hO : IsOpen O) (hΛc : IsCompact Λ) {q : M}
    (hq : q ∈ O) (hqΛ : q ∉ Λ) :
    ∃ t : TameTip n O q, Λ ∩ t.ball = ∅ ∧ t.ball ⊆ O := by
  classical
  set c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) q with hc
  have hqsrc : q ∈ c.source := hc ▸ mem_chart_source _ q
  have hqtgt : c q ∈ c.target := c.map_source hqsrc
  have hsymm : c.symm (c q) = q := c.left_inv hqsrc
  have hcont : ContinuousWithinAt c.symm c.target (c q) :=
    c.continuousOn_symm.continuousWithinAt hqtgt
  have hmemΛ : Λᶜ ∈ 𝓝 (c.symm (c q)) := by
    rw [hsymm]; exact hΛc.isClosed.isOpen_compl.mem_nhds hqΛ
  obtain ⟨ε₁, hε₁, hε₁'⟩ := Metric.mem_nhdsWithin_iff.mp (hcont.preimage_mem_nhdsWithin hmemΛ)
  have hmemO : O ∈ 𝓝 (c.symm (c q)) := by rw [hsymm]; exact hO.mem_nhds hq
  obtain ⟨ε₂, hε₂, hε₂'⟩ := Metric.mem_nhdsWithin_iff.mp (hcont.preimage_mem_nhdsWithin hmemO)
  obtain ⟨ε₃, hε₃, hε₃'⟩ := Metric.mem_nhds_iff.mp (c.open_target.mem_nhds hqtgt)
  set r : ℝ := min (min ε₁ ε₂) ε₃ / 2 with hr
  have hminpos : 0 < min (min ε₁ ε₂) ε₃ := lt_min (lt_min hε₁ hε₂) hε₃
  have hrpos : 0 < r := by rw [hr]; positivity
  have hr₁ : r < ε₁ := by
    rw [hr]
    have h : min (min ε₁ ε₂) ε₃ ≤ ε₁ := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hr₂ : r < ε₂ := by
    rw [hr]
    have h : min (min ε₁ ε₂) ε₃ ≤ ε₂ := le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have hr₃ : r < ε₃ := by
    rw [hr]
    have h : min (min ε₁ ε₂) ε₃ ≤ ε₃ := min_le_right _ _
    linarith
  have hball : Metric.closedBall (c q) r ⊆ c.target := by
    intro w hw
    exact hε₃' (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hw) hr₃))
  have hmem₁ : ∀ w, w ∈ Metric.closedBall (c q) r → c.symm w ∈ O := by
    intro w hw
    have hwt := hball hw
    have hwb : w ∈ Metric.ball (c q) ε₂ :=
      Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hw) hr₂)
    have := hε₂' ⟨hwb, hwt⟩
    simpa using this
  have hmem₂ : ∀ w, w ∈ Metric.closedBall (c q) r → c.symm w ∉ Λ := by
    intro w hw
    have hwt := hball hw
    have hwb : w ∈ Metric.ball (c q) ε₁ :=
      Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hw) hr₁)
    have := hε₁' ⟨hwb, hwt⟩
    simp only [Set.mem_preimage, Set.mem_compl_iff] at this
    exact this
  have hv : EuclideanSpace.single (⟨0, by omega⟩ : Fin n) (1 : ℝ) ≠ 0 := by
    intro h0
    have hnorm : ‖EuclideanSpace.single (⟨0, by omega⟩ : Fin n) (1 : ℝ)‖ = 1 := by
      rw [PiLp.norm_single]; simp
    rw [h0] at hnorm
    simp at hnorm
  refine ⟨⟨c, r, hrpos, hqsrc, hball, ?_, EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ), hv⟩,
    ?_, ?_⟩
  · intro y hy
    obtain ⟨w, hw, rfl⟩ := hy
    exact hmem₁ w hw
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxΛ, hxball⟩
    obtain ⟨w, hw, rfl⟩ := hxball
    exact hmem₂ w hw hxΛ
  · intro y hy
    obtain ⟨w, hw, rfl⟩ := hy
    exact hmem₁ w hw

end FreeBall

section DeepTarget

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- **A deep target with a free chart ball.**

Let `K` be an exhaustion of the open set `W` with the *escape* property (the component of `x` in
`W \ K i` meets `W \ K (i+1)`), let `x ∈ W` with `x ∉ K L`, and let `Λ` be a compact subset of the
component `C` of `x` in `W \ K L` with empty interior.  Then there is a point `q` of `C` which is
outside `K (L+1)` and outside `Λ`, and which has a free chart ball for `Λ` inside `C`. -/
theorem exists_deep_target_with_freeBall (hn : 2 ≤ n) {W : Set M} (hW : IsOpen W)
    {K : ℕ → Set M} (hKc : ∀ i, IsCompact (K i))
    (hescc : ∀ i (y : M), y ∈ W → y ∉ K i →
      (connectedComponentIn (W \ K i) y ∩ (W \ K (i + 1))).Nonempty)
    {L : ℕ} {x : M} (hxW : x ∈ W) (hxL : x ∉ K L)
    {Λ : Set M} (hΛc : IsCompact Λ) (hΛint : interior Λ = ∅)
    (hΛsub : Λ ⊆ connectedComponentIn (W \ K L) x) :
    ∃ q : M, q ∈ connectedComponentIn (W \ K L) x ∧ q ∉ K (L + 1) ∧ q ∉ Λ ∧
      HasFreeBall n (connectedComponentIn (W \ K L) x) Λ q := by
  classical
  haveI : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  have hCopen : IsOpen (connectedComponentIn (W \ K L) x) :=
    (hW.sdiff (hKc L).isClosed).connectedComponentIn
  obtain ⟨q₀, hq₀C, hq₀K⟩ := hescc L x hxW hxL
  have hUopen : IsOpen (connectedComponentIn (W \ K L) x \ K (L + 1)) :=
    hCopen.sdiff (hKc (L + 1)).isClosed
  have hUne : (connectedComponentIn (W \ K L) x \ K (L + 1)).Nonempty := ⟨q₀, hq₀C, hq₀K.2⟩
  have hnotsub : ¬ (connectedComponentIn (W \ K L) x \ K (L + 1)) ⊆ Λ := by
    intro hsub
    have hsub' : connectedComponentIn (W \ K L) x \ K (L + 1) ⊆ interior Λ :=
      interior_maximal hsub hUopen
    rw [hΛint] at hsub'
    exact hUne.ne_empty (Set.eq_empty_iff_forall_notMem.mpr (fun y hy => hsub' hy))
  obtain ⟨q, hqU, hqΛ⟩ := Set.not_subset.mp hnotsub
  obtain ⟨t, ht, -⟩ := exists_freeBall hn hCopen hΛc hqU.1 hqΛ
  exact ⟨q, hqU.1, hqU.2, hqΛ, t, ht⟩

end DeepTarget

end Work.Noncompact.ProperLine
