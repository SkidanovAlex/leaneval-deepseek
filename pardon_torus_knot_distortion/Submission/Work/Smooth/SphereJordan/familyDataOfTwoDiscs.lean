import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Topology.SphereSlicing.exists_rank_of_strict_order

/-!
# Standard position of a finite family of two-disc curves on the Riemann sphere

`Work.Smooth.SphereJordan.TwoDiscs c` says that a simple closed curve `c` of the Riemann sphere
is the common boundary of two complementary embedded closed discs.  Here we show that for a
*finite* family of pairwise disjoint such curves, and a point `x₀` off all of them, the discs can
be chosen consistently (each curve is given the disc *not* containing `x₀`) and the resulting
family is in **standard position**: the relation "the curve `j` lies inside the disc of `i`" is a
strict partial order on the index type, whence a nesting rank exists
(`Work.Topology.SphereSlicing.exists_rank_of_strict_order`).

The geometric content is contained in the key lemma `hM` of the proof of
`familyDataOfTwoDiscs`: if the whole curve `j` lies in the inner (i.e. `x₀`-free) disc `U i` of
`i`, then the outer (i.e. `x₀`-containing) disc `V i` of `i` is contained in the outer disc `V j`
of `j`.  Indeed `V i` is preconnected, contains `x₀ ∈ V j`, and avoids the curve `j` (which lies in
`U i`), so it cannot leave the component `V j` of the complement of `j`.  This gives transitivity
directly; the antisymmetry of the relation (mutual nesting is impossible) follows because equal
outer discs have equal frontiers, and the frontier of `V i` is the curve `c i`.
-/

open Set
open Filter

namespace Work.Smooth.SphereJordan

noncomputable section

variable {c : ℝ → RiemannSphere}

namespace TwoDiscs

/-- Every point of the model disc has norm at most one. -/
theorem disc_norm_le_one (z : Disc) : ‖(z : ℂ)‖ ≤ 1 := by
  have := z.2
  rwa [Metric.mem_closedBall, dist_zero_right] at this

/-- The boundary point `circlePoint θ` has norm one. -/
theorem circlePoint_norm (θ : ℝ) : ‖((circlePoint θ : Disc) : ℂ)‖ = 1 := by
  rw [Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]

/-- Points of the open disc arbitrarily close to a given boundary point. -/
theorem exists_norm_lt_dist_lt (w₀ : Disc) (hw₀ : ‖(w₀ : ℂ)‖ = 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ dist z w₀ < δ := by
  set t : ℝ := min δ 1 / 2 with ht
  have htpos : 0 < t := by
    have : 0 < min δ 1 := lt_min hδ one_pos
    positivity
  have htle : t ≤ 1 / 2 := by
    have : min δ 1 ≤ 1 := min_le_right _ _
    linarith
  have htlt : t < δ := by
    have : min δ 1 ≤ δ := min_le_left _ _
    linarith
  refine ⟨⟨(1 - t) • (w₀ : ℂ), ?_⟩, ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, hw₀, mul_one]
    rw [abs_le]; constructor <;> linarith
  · rw [norm_smul, Real.norm_eq_abs, hw₀, mul_one, abs_of_nonneg (by linarith)]
    linarith
  · rw [Subtype.dist_eq, dist_eq_norm]
    change ‖(1 - t) • (w₀ : ℂ) - (w₀ : ℂ)‖ < δ
    have hmove : (1 - t) • (w₀ : ℂ) - (w₀ : ℂ) = (-t) • (w₀ : ℂ) := by module
    rw [hmove, norm_smul, Real.norm_eq_abs, hw₀, mul_one, abs_neg, abs_of_pos htpos]
    exact htlt

/-- The open unit disc of the model disc. -/
def openUnitDisc : Set Disc := {z : Disc | ‖(z : ℂ)‖ < 1}

theorem isPreconnected_openUnitDisc : IsPreconnected (openUnitDisc : Set Disc) := by
  rw [← (Topology.IsInducing.subtypeVal (t := Metric.closedBall (0 : ℂ) 1)).isPreconnected_image]
  have himg : (Subtype.val '' openUnitDisc : Set ℂ) = Metric.ball (0 : ℂ) 1 := by
    ext w
    simp only [Set.mem_image, openUnitDisc, Metric.mem_ball, dist_zero_right]
    constructor
    · rintro ⟨z, hz, rfl⟩; exact hz
    · intro hw
      exact ⟨⟨w, by simpa only [Metric.mem_closedBall, dist_zero_right] using le_of_lt hw⟩,
        hw, rfl⟩
  rw [himg]
  exact Metric.isPreconnected_ball

/-! ## Choosing the disc containing `x₀` and the one not containing it -/

/-- The disc of `T` that contains the point `x₀` (when `x₀` is off the curve). -/
def outer (T : TwoDiscs c) (x₀ : RiemannSphere) : C(Disc, RiemannSphere) := by
  classical
  exact if x₀ ∈ Set.range T.e then T.e else T.e'

/-- The disc of `T` that does not contain the point `x₀` (when `x₀` is off the curve). -/
def inner (T : TwoDiscs c) (x₀ : RiemannSphere) : C(Disc, RiemannSphere) := by
  classical
  exact if x₀ ∈ Set.range T.e then T.e' else T.e

/-- The open side of the disc containing `x₀`. -/
def outSide (T : TwoDiscs c) (x₀ : RiemannSphere) : Set RiemannSphere :=
  {x : RiemannSphere | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ T.outer x₀ z = x}

/-- The open side of the disc not containing `x₀`. -/
def inSide (T : TwoDiscs c) (x₀ : RiemannSphere) : Set RiemannSphere :=
  {x : RiemannSphere | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ T.inner x₀ z = x}

variable (T : TwoDiscs c) (x₀ : RiemannSphere)

theorem outer_eq_of_mem (h : x₀ ∈ Set.range T.e) : T.outer x₀ = T.e := by
  unfold outer; exact if_pos h

theorem outer_eq_of_notMem (h : x₀ ∉ Set.range T.e) : T.outer x₀ = T.e' := by
  unfold outer; exact if_neg h

theorem inner_eq_of_mem (h : x₀ ∈ Set.range T.e) : T.inner x₀ = T.e' := by
  unfold inner; exact if_pos h

theorem inner_eq_of_notMem (h : x₀ ∉ Set.range T.e) : T.inner x₀ = T.e := by
  unfold inner; exact if_neg h

theorem outer_injective : Function.Injective (T.outer x₀) := by
  by_cases h : x₀ ∈ Set.range T.e
  · rw [outer_eq_of_mem T x₀ h]; exact T.inj
  · rw [outer_eq_of_notMem T x₀ h]; exact T.inj'

theorem inner_injective : Function.Injective (T.inner x₀) := by
  by_cases h : x₀ ∈ Set.range T.e
  · rw [inner_eq_of_mem T x₀ h]; exact T.inj'
  · rw [inner_eq_of_notMem T x₀ h]; exact T.inj

theorem outer_boundary (θ : ℝ) : T.outer x₀ (circlePoint θ) = c θ := by
  by_cases h : x₀ ∈ Set.range T.e
  · rw [outer_eq_of_mem T x₀ h]; exact T.boundary θ
  · rw [outer_eq_of_notMem T x₀ h]; exact T.boundary' θ

theorem inner_boundary (θ : ℝ) : T.inner x₀ (circlePoint θ) = c θ := by
  by_cases h : x₀ ∈ Set.range T.e
  · rw [inner_eq_of_mem T x₀ h]; exact T.boundary' θ
  · rw [inner_eq_of_notMem T x₀ h]; exact T.boundary θ

theorem isOpen_outSide : IsOpen (T.outSide x₀) := by
  by_cases h : x₀ ∈ Set.range T.e
  · have hset : T.outSide x₀ = {x : RiemannSphere | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ T.e z = x} := by
      unfold outSide; rw [outer_eq_of_mem T x₀ h]
    rw [hset]; exact T.open_interior
  · have hset : T.outSide x₀ =
        {x : RiemannSphere | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ T.e' z = x} := by
      unfold outSide; rw [outer_eq_of_notMem T x₀ h]
    rw [hset]; exact T.open_interior'

theorem isOpen_inSide : IsOpen (T.inSide x₀) := by
  by_cases h : x₀ ∈ Set.range T.e
  · have hset : T.inSide x₀ =
        {x : RiemannSphere | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ T.e' z = x} := by
      unfold inSide; rw [inner_eq_of_mem T x₀ h]
    rw [hset]; exact T.open_interior'
  · have hset : T.inSide x₀ = {x : RiemannSphere | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ T.e z = x} := by
      unfold inSide; rw [inner_eq_of_notMem T x₀ h]
    rw [hset]; exact T.open_interior

theorem range_outer_eq : Set.range (T.outer x₀) = T.outSide x₀ ∪ Set.range c := by
  ext x; constructor
  · rintro ⟨z, rfl⟩
    by_cases hz : ‖(z : ℂ)‖ < 1
    · exact Or.inl ⟨z, hz, rfl⟩
    · refine Or.inr ?_
      have hz1 : ‖(z : ℂ)‖ = 1 := le_antisymm (disc_norm_le_one z) (not_lt.mp hz)
      obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z hz1
      refine ⟨θ, ?_⟩
      rw [← T.outer_boundary x₀ θ]
      exact congrArg (T.outer x₀) hθ
  · rintro (⟨z, hz, rfl⟩ | ⟨θ, hθ⟩)
    · exact ⟨z, rfl⟩
    · exact ⟨circlePoint θ, by rw [T.outer_boundary x₀ θ]; exact hθ⟩

theorem range_inner_eq : Set.range (T.inner x₀) = T.inSide x₀ ∪ Set.range c := by
  ext x; constructor
  · rintro ⟨z, rfl⟩
    by_cases hz : ‖(z : ℂ)‖ < 1
    · exact Or.inl ⟨z, hz, rfl⟩
    · refine Or.inr ?_
      have hz1 : ‖(z : ℂ)‖ = 1 := le_antisymm (disc_norm_le_one z) (not_lt.mp hz)
      obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z hz1
      refine ⟨θ, ?_⟩
      rw [← T.inner_boundary x₀ θ]
      exact congrArg (T.inner x₀) hθ
  · rintro (⟨z, hz, rfl⟩ | ⟨θ, hθ⟩)
    · exact ⟨z, rfl⟩
    · exact ⟨circlePoint θ, by rw [T.inner_boundary x₀ θ]; exact hθ⟩

theorem disjoint_inSide_range : Disjoint (T.inSide x₀) (Set.range c) := by
  rw [Set.disjoint_left]
  intro x hx hxc
  obtain ⟨z, hz, hzx⟩ := hx
  obtain ⟨θ, hθ⟩ := hxc
  have h1 : T.inner x₀ z = T.inner x₀ (circlePoint θ) := by
    rw [T.inner_boundary x₀ θ]; exact hzx.trans hθ.symm
  have h2 : z = circlePoint θ := T.inner_injective x₀ h1
  have h3 : ‖(z : ℂ)‖ = 1 := by rw [h2]; exact circlePoint_norm θ
  rw [h3] at hz
  exact absurd hz (lt_irrefl 1)

theorem disjoint_outSide_range : Disjoint (T.outSide x₀) (Set.range c) := by
  rw [Set.disjoint_left]
  intro x hx hxc
  obtain ⟨z, hz, hzx⟩ := hx
  obtain ⟨θ, hθ⟩ := hxc
  have h1 : T.outer x₀ z = T.outer x₀ (circlePoint θ) := by
    rw [T.outer_boundary x₀ θ]; exact hzx.trans hθ.symm
  have h2 : z = circlePoint θ := T.outer_injective x₀ h1
  have h3 : ‖(z : ℂ)‖ = 1 := by rw [h2]; exact circlePoint_norm θ
  rw [h3] at hz
  exact absurd hz (lt_irrefl 1)

theorem meet_range : Set.range (T.inner x₀) ∩ Set.range (T.outer x₀) = Set.range c := by
  by_cases h : x₀ ∈ Set.range T.e
  · rw [inner_eq_of_mem T x₀ h, outer_eq_of_mem T x₀ h, Set.inter_comm, T.meet]
  · rw [inner_eq_of_notMem T x₀ h, outer_eq_of_notMem T x₀ h, T.meet]

theorem cover_range : Set.range (T.inner x₀) ∪ Set.range (T.outer x₀) = Set.univ := by
  by_cases h : x₀ ∈ Set.range T.e
  · rw [inner_eq_of_mem T x₀ h, outer_eq_of_mem T x₀ h, Set.union_comm, T.cover]
  · rw [inner_eq_of_notMem T x₀ h, outer_eq_of_notMem T x₀ h, T.cover]

theorem disjoint_inSide_outSide : Disjoint (T.inSide x₀) (T.outSide x₀) := by
  rw [Set.disjoint_left]
  intro x hxin hxout
  have hK : x ∈ Set.range c := by
    obtain ⟨z₁, hz₁, hz₁x⟩ := hxin
    obtain ⟨z₂, hz₂, hz₂x⟩ := hxout
    have hmem : x ∈ Set.range (T.inner x₀) ∩ Set.range (T.outer x₀) :=
      ⟨⟨z₁, hz₁x⟩, ⟨z₂, hz₂x⟩⟩
    rwa [meet_range T x₀] at hmem
  exact (Set.disjoint_left.mp (disjoint_inSide_range T x₀)) hxin hK

theorem inSide_union_range_union_outSide :
    T.inSide x₀ ∪ Set.range c ∪ T.outSide x₀ = Set.univ := by
  have h : T.inSide x₀ ∪ Set.range c ∪ T.outSide x₀
      = Set.range (T.inner x₀) ∪ Set.range (T.outer x₀) := by
    rw [range_inner_eq T x₀, range_outer_eq T x₀]
    ext x; simp only [Set.mem_union]; tauto
  rw [h, cover_range T x₀]

theorem inSide_or_range_or_outSide (x : RiemannSphere) :
    x ∈ T.inSide x₀ ∨ x ∈ Set.range c ∨ x ∈ T.outSide x₀ := by
  have hmem : x ∈ T.inSide x₀ ∪ Set.range c ∪ T.outSide x₀ := by
    rw [inSide_union_range_union_outSide T x₀]; trivial
  simp only [Set.mem_union] at hmem
  tauto

theorem compl_inSide : (T.inSide x₀)ᶜ = Set.range c ∪ T.outSide x₀ := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [Set.mem_compl_iff] at hx
    rcases inSide_or_range_or_outSide T x₀ x with h1 | h1 | h1
    · exact absurd h1 hx
    · exact Or.inl h1
    · exact Or.inr h1
  · intro x hx
    rw [Set.mem_compl_iff]
    rcases hx with h1 | h1
    · exact fun hxin => (Set.disjoint_left.mp (disjoint_inSide_range T x₀)) hxin h1
    · exact fun hxin => (Set.disjoint_left.mp (disjoint_inSide_outSide T x₀)) hxin h1

theorem mem_outSide_self (hx₀ : x₀ ∉ Set.range c) : x₀ ∈ T.outSide x₀ := by
  by_cases h : x₀ ∈ Set.range T.e
  · rw [outSide, outer_eq_of_mem T x₀ h]
    obtain ⟨z, hz⟩ := h
    refine ⟨z, ?_, hz⟩
    by_contra hzlt
    have hz1 : ‖(z : ℂ)‖ = 1 := le_antisymm (disc_norm_le_one z) (not_lt.mp hzlt)
    obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z hz1
    exact hx₀ ⟨θ, by rw [← hz, ← hθ, T.boundary θ]⟩
  · have h' : x₀ ∈ Set.range T.e' := by
      have hun : x₀ ∈ Set.range T.e ∪ Set.range T.e' := by rw [T.cover]; trivial
      exact hun.resolve_left h
    rw [outSide, outer_eq_of_notMem T x₀ h]
    obtain ⟨z, hz⟩ := h'
    refine ⟨z, ?_, hz⟩
    by_contra hzlt
    have hz1 : ‖(z : ℂ)‖ = 1 := le_antisymm (disc_norm_le_one z) (not_lt.mp hzlt)
    obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z hz1
    exact hx₀ ⟨θ, by rw [← hz, ← hθ, T.boundary' θ]⟩

theorem outSide_preconnected : IsPreconnected (T.outSide x₀) := by
  have himg : T.outSide x₀ = T.outer x₀ '' (openUnitDisc : Set Disc) := by
    ext x; constructor
    · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
  rw [himg]
  exact isPreconnected_openUnitDisc.image (T.outer x₀) (T.outer x₀).continuous.continuousOn

theorem range_subset_closure_outSide : Set.range c ⊆ closure (T.outSide x₀) := by
  rintro x ⟨θ, rfl⟩
  rw [← T.outer_boundary x₀ θ, mem_closure_iff]
  intro o ho hxo
  have hpre : (T.outer x₀) ⁻¹' o ∈ nhds (circlePoint θ) :=
    (ho.preimage (T.outer x₀).continuous).mem_nhds hxo
  rw [Metric.mem_nhds_iff] at hpre
  obtain ⟨ε, hεpos, hε⟩ := hpre
  obtain ⟨z, hzlt, hzdist⟩ := exists_norm_lt_dist_lt (circlePoint θ) (circlePoint_norm θ) hεpos
  exact ⟨T.outer x₀ z, hε (Metric.mem_ball.mpr hzdist), ⟨z, hzlt, rfl⟩⟩

theorem closure_outSide : closure (T.outSide x₀) = (T.inSide x₀)ᶜ := by
  apply Set.Subset.antisymm
  · have hsub : T.outSide x₀ ⊆ (T.inSide x₀)ᶜ := by
      intro y hy
      rw [Set.mem_compl_iff]
      exact fun hyin => (Set.disjoint_left.mp (disjoint_inSide_outSide T x₀)) hyin hy
    exact closure_minimal hsub (isClosed_compl_iff.mpr (isOpen_inSide T x₀))
  · intro y hy
    rw [compl_inSide T x₀] at hy
    rcases hy with h | h
    · exact range_subset_closure_outSide T x₀ h
    · exact subset_closure h

theorem frontier_outSide : frontier (T.outSide x₀) = Set.range c := by
  rw [frontier, closure_outSide T x₀, (isOpen_outSide T x₀).interior_eq, compl_inSide T x₀]
  ext y
  rw [Set.mem_sdiff, Set.mem_union]
  constructor
  · rintro ⟨h | h, hnot⟩
    · exact h
    · exact absurd h hnot
  · intro hy
    exact ⟨Or.inl hy,
      fun hout => (Set.disjoint_left.mp (disjoint_outSide_range T x₀)) hout hy⟩

end TwoDiscs

/-! ## The main theorem -/

open Work.Topology.SphereSlicing

theorem familyDataOfTwoDiscs {ι : Type} [Fintype ι] {c : ι → ℝ → RiemannSphere}
    (hs : ∀ i, IsSimpleClosedCurve (c i))
    (hd : Pairwise fun i j : ι => Disjoint (Set.range (c i)) (Set.range (c j)))
    (h : ∀ i, TwoDiscs (c i)) (x₀ : RiemannSphere) (hx₀ : ∀ i, x₀ ∉ Set.range (c i)) :
    Nonempty (FamilyData c) := by
  classical
  let inn : ι → C(Disc, RiemannSphere) := fun i => (h i).inner x₀
  let out : ι → C(Disc, RiemannSphere) := fun i => (h i).outer x₀
  let U : ι → Set RiemannSphere := fun i => (h i).inSide x₀
  let V : ι → Set RiemannSphere := fun i => (h i).outSide x₀
  let K : ι → Set RiemannSphere := fun i => Set.range (c i)
  have hUopen : ∀ i, IsOpen (U i) := fun i => TwoDiscs.isOpen_inSide (h i) x₀
  have hVopen : ∀ i, IsOpen (V i) := fun i => TwoDiscs.isOpen_outSide (h i) x₀
  have hUdisjK : ∀ i, Disjoint (U i) (K i) := fun i => TwoDiscs.disjoint_inSide_range (h i) x₀
  have hVdisjK : ∀ i, Disjoint (V i) (K i) := fun i => TwoDiscs.disjoint_outSide_range (h i) x₀
  have hUVdisj : ∀ i, Disjoint (U i) (V i) := fun i => TwoDiscs.disjoint_inSide_outSide (h i) x₀
  have hUKV : ∀ i, U i ∪ K i ∪ V i = Set.univ :=
    fun i => TwoDiscs.inSide_union_range_union_outSide (h i) x₀
  have hmem_split : ∀ i x, x ∈ U i ∨ x ∈ K i ∨ x ∈ V i := fun i x =>
    TwoDiscs.inSide_or_range_or_outSide (h i) x₀ x
  have hx0V : ∀ i, x₀ ∈ V i := fun i => TwoDiscs.mem_outSide_self (h i) x₀ (hx₀ i)
  have hVpre : ∀ i, IsPreconnected (V i) := fun i => TwoDiscs.outSide_preconnected (h i) x₀
  have hKpre : ∀ i, IsPreconnected (K i) :=
    fun i => (isConnected_range (hs i).continuous).isPreconnected
  have hKne : ∀ i, (K i).Nonempty := fun i => ⟨c i 0, ⟨0, rfl⟩⟩
  have hfrontier : ∀ i, frontier (V i) = K i := fun i => TwoDiscs.frontier_outSide (h i) x₀
  have hdisj : ∀ i j, i ≠ j → ∀ x, x ∈ K i → x ∈ K j → False :=
    fun i j hij x hx hy => (Set.disjoint_left.mp (hd hij)) hx hy
  have hdisjV : ∀ i x, x ∈ U i → x ∈ V i → False :=
    fun i x hu hv => (Set.disjoint_left.mp (hUVdisj i)) hu hv
  let R : ι → ι → Prop := fun i j => ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ inn i z ∈ K j
  have hirr : ∀ i, ¬ R i i := by
    intro i hRi
    obtain ⟨z, hz, hzK⟩ := hRi
    exact (Set.disjoint_left.mp (hUdisjK i)) ⟨z, hz, rfl⟩ hzK
  -- a curve meeting the inner disc of `i` lies wholly in it
  have hKsub : ∀ i j, R i j → K j ⊆ U i := by
    intro i j hij
    have hijne : i ≠ j := fun h => hirr i (h.symm ▸ hij)
    refine IsPreconnected.subset_left_of_subset_union (hUopen i) (hVopen i)
      (hUVdisj i) ?_ ?_ (hKpre j)
    · intro x hx
      rcases hmem_split i x with h1 | h1 | h1
      · exact Or.inl h1
      · exact (hdisj i j hijne x h1 hx).elim
      · exact Or.inr h1
    · obtain ⟨z, hz, hzK⟩ := hij
      exact ⟨inn i z, hzK, ⟨z, hz, rfl⟩⟩
  -- the key geometric lemma
  have hM : ∀ i j, K j ⊆ U i → V i ⊆ V j := by
    intro i j hKj
    refine IsPreconnected.subset_left_of_subset_union (hVopen j) (hUopen j)
      (hUVdisj j).symm ?_ ?_ (hVpre i)
    · intro x hx
      rcases hmem_split j x with h1 | h1 | h1
      · exact Or.inr h1
      · exact (hdisjV i x (hKj h1) hx).elim
      · exact Or.inl h1
    · exact ⟨x₀, hx0V i, hx0V j⟩
  -- mutual nesting is impossible
  have hanti : ∀ i j, R i j → R j i → False := by
    intro i j hij hji
    have hijne : i ≠ j := fun h => hirr i (h.symm ▸ hij)
    have hKj : K j ⊆ U i := hKsub i j hij
    have hKi : K i ⊆ U j := hKsub j i hji
    have hVij : V i ⊆ V j := hM i j hKj
    have hVji : V j ⊆ V i := hM j i hKi
    have hVeq : V i = V j := Set.Subset.antisymm hVij hVji
    have hKiKj : K i = K j := by rw [← hfrontier i, ← hfrontier j, hVeq]
    obtain ⟨x, hxK⟩ := hKne i
    have hxj : x ∈ K j := by rw [← hKiKj]; exact hxK
    exact hdisj i j hijne x hxK hxj
  have htrans : ∀ i j k, R i j → R j k → R i k := by
    intro i j k hij hjk
    by_cases hik : i = k
    · rw [← hik] at hjk ⊢
      exact (hanti i j hij hjk).elim
    · have hKj : K j ⊆ U i := hKsub i j hij
      have hKk : K k ⊆ U j := hKsub j k hjk
      have hVij : V i ⊆ V j := hM i j hKj
      have step : K k ⊆ U i ∪ K i := by
        intro x hx
        have hxnotVi : x ∉ V i := fun hv => hdisjV j x (hKk hx) (hVij hv)
        rcases hmem_split i x with h1 | h1 | h1
        · exact Or.inl h1
        · exact Or.inr h1
        · exact absurd h1 hxnotVi
      have hKkU : K k ⊆ U i := by
        intro x hx
        rcases step hx with h1 | h1
        · exact h1
        · exact (hdisj i k hik x h1 hx).elim
      obtain ⟨x, hxK⟩ := hKne k
      obtain ⟨z, hz, hzx⟩ := hKkU hxK
      exact ⟨z, hz, by rw [hzx]; exact hxK⟩
  obtain ⟨rank, hrank⟩ := exists_rank_of_strict_order R hirr htrans
  exact ⟨{
    e := inn
    e' := out
    rank := rank
    inj := fun i => TwoDiscs.inner_injective (h i) x₀
    inj' := fun i => TwoDiscs.outer_injective (h i) x₀
    boundary := fun i θ => TwoDiscs.inner_boundary (h i) x₀ θ
    boundary' := fun i θ => TwoDiscs.outer_boundary (h i) x₀ θ
    open_interior := fun i => TwoDiscs.isOpen_inSide (h i) x₀
    open_interior' := fun i => TwoDiscs.isOpen_outSide (h i) x₀
    cover := fun i => TwoDiscs.cover_range (h i) x₀
    meet := fun i => TwoDiscs.meet_range (h i) x₀
    nested := fun i j hmem => hrank i j hmem }⟩

end

end Work.Smooth.SphereJordan
