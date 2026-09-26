import Mathlib
import Submission.Work.Smooth.JordanSeparation.arc_not_separate
import Submission.Work.Smooth.SphereJordan.interior_range_empty_of_injOn_Icc
import Submission.Work.Smooth.JordanSeparation.componentIn_inter_componentIn
import Submission.Work.Spike.janiszewski_pointInter

/-!
# The "spike" containment: `K ∪ range β` does not separate the plane

The target is `Work.Spike.spikePreconnected`: if `K ⊆ ℂ` is compact with preconnected complement
and `β : [0,1] → ℂ` is an injective arc with `β 0 ∈ K` and `β t ∉ K` for `t > 0` (a *slit with a
free end* attached to `K`), then `(K ∪ Set.range β)ᶜ` is preconnected.

## Provenance of the imported tools

`Work.Smooth.JordanSeparation.arc_not_separate` (an arc does not separate the plane) is re-derived
below as `range_compl_preconnected`, because its module's import closure also defines
`Work.Smooth.JordanSeparation.isPreconnected_insert_of_mem_closure`, which clashes with the copy in
`Submission/Work/Smooth/JordanSeparation/exists_continuum_separating.lean`; the local restatements
avoid that clash.  `Work.Smooth.JordanSeparation.componentIn_inter_componentIn` (the *disjoint*
Phragmén–Brouwer theorem for compact plane sets) is imported directly.
-/

namespace Work.Spike

open Set

noncomputable section

/-- An open subset of a preconnected set that is closed in it is empty or everything. -/
theorem eq_empty_or_subset_of_clopen {Ω S : Set ℂ} (hΩ : IsOpen Ω) (hS : IsPreconnected S)
    (hsub : Ω ⊆ S) (hcl : closure Ω ∩ S ⊆ Ω) : Ω = ∅ ∨ S ⊆ Ω := by
  rcases hS.subset_or_subset hΩ isClosed_closure.isOpen_compl
      (Set.disjoint_left.mpr fun z hz1 hz2 => hz2 (subset_closure hz1)) (fun z hz => by
        by_cases hzΩ : z ∈ Ω
        · exact Or.inl hzΩ
        · exact Or.inr fun hzcl => hzΩ (hcl ⟨hzcl, hz⟩)) with h | h
  · exact Or.inr h
  · left
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    exact h (hsub hz) (subset_closure hz)

/-- The arc `β`, read on `ℝ` by clamping the parameter into `[0,1]`. -/
def clampFun (β : C(Set.Icc (0 : ℝ) 1, ℂ)) (t : ℝ) : ℂ :=
  β ⟨max 0 (min 1 t), Set.mem_Icc.mpr
    ⟨le_max_left 0 (min 1 t), max_le (by norm_num) (min_le_left 1 t)⟩⟩

theorem clampFun_continuous (β : C(Set.Icc (0 : ℝ) 1, ℂ)) : Continuous (clampFun β) :=
  β.continuous.comp (Continuous.subtype_mk
    ((continuous_const.max (continuous_const.min continuous_id) :
      Continuous fun t : ℝ => max 0 (min 1 t))) _)

theorem clampFun_eq (β : C(Set.Icc (0 : ℝ) 1, ℂ)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    clampFun β t = β ⟨t, ht⟩ := by
  simp only [clampFun]
  congr 1
  exact Subtype.ext (by
    show max 0 (min 1 t) = t
    rw [min_eq_right ht.2, max_eq_right ht.1])

theorem clampFun_range (β : C(Set.Icc (0 : ℝ) 1, ℂ)) :
    clampFun β '' Set.Icc (0 : ℝ) 1 = Set.range β := by
  ext z; constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, (clampFun_eq β ht).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨(u : ℝ), u.2, clampFun_eq β u.2⟩

theorem clampFun_injOn {β : C(Set.Icc (0 : ℝ) 1, ℂ)} (hβ : Function.Injective β) :
    Set.InjOn (clampFun β) (Set.Icc (0 : ℝ) 1) := by
  intro s hs t ht hst
  rw [clampFun_eq β hs, clampFun_eq β ht] at hst
  exact congrArg Subtype.val (hβ hst)

/-- A compact set misses points of arbitrarily large norm. -/
theorem exists_norm_gt_notMem' {C : Set ℂ} (hC : IsCompact C) (R : ℝ) :
    ∃ z : ℂ, R < ‖z‖ ∧ z ∉ C := by
  obtain ⟨r, hr⟩ := hC.isBounded.subset_ball (0 : ℂ)
  refine ⟨((|R| + |r| + 1 : ℝ) : ℂ), ?_, ?_⟩
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h1 : R ≤ |R| := le_abs_self R
    have h2 : (0:ℝ) ≤ |r| := abs_nonneg r
    linarith
  · intro hmem
    have hb := hr hmem
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)] at hb
    have h1 : r ≤ |r| := le_abs_self r
    have h2 : (0:ℝ) ≤ |R| := abs_nonneg R
    linarith

/-- The complement of the trace of an injective arc in the plane is preconnected. -/
theorem range_compl_preconnected {β : C(Set.Icc (0 : ℝ) 1, ℂ)} (hβ : Function.Injective β) :
    IsPreconnected (Set.range β)ᶜ := by
  rw [← clampFun_range β]
  exact (Work.Smooth.JordanSeparation.arc_not_separate (clampFun_continuous β)
    (clampFun_injOn hβ)).isConnected.isPreconnected

/-- The trace of an injective arc has empty interior. -/
theorem range_interior_empty {β : C(Set.Icc (0 : ℝ) 1, ℂ)} (hβ : Function.Injective β) :
    interior (Set.range β) = ∅ := by
  rw [← clampFun_range β]
  exact Work.Smooth.SphereJordan.interior_range_empty_of_injOn_Icc (by norm_num)
    (clampFun_continuous β) (clampFun_injOn hβ)

/-- The complement of the trace of an injective arc is dense. -/
theorem closure_range_compl {β : C(Set.Icc (0 : ℝ) 1, ℂ)} (hβ : Function.Injective β) :
    closure (Set.range β)ᶜ = univ := by
  rw [closure_compl, range_interior_empty hβ, compl_empty]

/-- The open sub-arc `β '' (0,1]` of the trace. -/
def openArc (β : C(Set.Icc (0 : ℝ) 1, ℂ)) : Set ℂ :=
  β '' {t : Set.Icc (0 : ℝ) 1 | 0 < (t : ℝ)}

theorem mem_openArc_iff {β : C(Set.Icc (0 : ℝ) 1, ℂ)} {z : ℂ} :
    z ∈ openArc β ↔ ∃ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) ∧ β t = z := by
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩

theorem range_eq_openArc_insert {β : C(Set.Icc (0 : ℝ) 1, ℂ)} :
    Set.range β = insert (β ⟨0, by norm_num⟩) (openArc β) := by
  ext z
  rw [Set.mem_range, Set.mem_insert_iff, mem_openArc_iff]
  constructor
  · rintro ⟨t, rfl⟩
    rcases eq_or_lt_of_le t.2.1 with h | h
    · left; congr 1; exact Subtype.ext h.symm
    · right; exact ⟨t, h, rfl⟩
  · rintro (rfl | ⟨t, -, rfl⟩)
    · exact ⟨⟨0, by norm_num⟩, rfl⟩
    · exact ⟨t, rfl⟩

/-- The complement of the open sub-arc is preconnected: it is the complement of the trace together
with the base point. -/
theorem openArc_compl_preconnected {β : C(Set.Icc (0 : ℝ) 1, ℂ)}
    (hβ : Function.Injective β) : IsPreconnected (openArc β)ᶜ := by
  have hset : (openArc β)ᶜ = insert (β ⟨0, by norm_num⟩) (Set.range β)ᶜ := by
    ext z; constructor
    · intro hz
      by_cases hzr : z ∈ Set.range β
      · obtain ⟨t, ht⟩ := hzr
        by_cases ht0 : (t : ℝ) = 0
        · left; rw [← ht]; congr 1; exact Subtype.ext ht0
        · exact absurd (mem_openArc_iff.mpr ⟨t, lt_of_le_of_ne t.2.1 (Ne.symm ht0), ht⟩) hz
      · exact Or.inr hzr
    · rintro (rfl | hzr)
      · intro hcon
        obtain ⟨t, ht, htz⟩ := mem_openArc_iff.mp hcon
        exact absurd (hβ htz) (by rw [Subtype.ext_iff]; exact ne_of_gt ht)
      · exact fun hcon => hzr (by
          rw [range_eq_openArc_insert]
          exact Set.mem_insert_iff.mpr (Or.inr hcon))
  rw [hset]
  refine (range_compl_preconnected hβ).subset_closure (Set.subset_insert _ _) ?_
  rw [closure_range_compl hβ]
  exact Set.subset_univ _

/-- `K ∩ openArc β = ∅` in the spike setting. -/
theorem disjoint_K_openArc {K : Set ℂ} {β : C(Set.Icc (0 : ℝ) 1, ℂ)}
    (hint : ∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → β t ∉ K) :
    Disjoint K (openArc β) := by
  rw [Set.disjoint_left]
  intro z hzK hzA
  obtain ⟨t, ht, rfl⟩ := mem_openArc_iff.mp hzA
  exact hint t ht hzK

/-! ## Polygonal chains in an open connected planar set

The first step towards "open connected subsets of `ℂ` are arc-connected": polygonal chains with all
their segments inside the set. -/

/-- A polygonal chain in `V` from `a` to `b` with `n` straight segments, given by its `n+1`
vertices. -/
def IsChain (V : Set ℂ) (a b : ℂ) (n : ℕ) (q : Fin (n+1) → ℂ) : Prop :=
  q 0 = a ∧ q (Fin.last n) = b ∧ ∀ i : Fin n, segment ℝ (q i.castSucc) (q i.succ) ⊆ V

/-- `b` is reachable from `a` by a polygonal chain inside `V`, both endpoints lying in `V`. -/
def PolyReach (V : Set ℂ) (a b : ℂ) : Prop :=
  a ∈ V ∧ b ∈ V ∧ ∃ n : ℕ, ∃ q : Fin (n+1) → ℂ, IsChain V a b n q

theorem polyReach_refl {V : Set ℂ} {a : ℂ} (ha : a ∈ V) : PolyReach V a a :=
  ⟨ha, ha, 0, fun _ => a, rfl, rfl, fun i => i.elim0⟩

/-- Appending one more vertex to a chain. -/
theorem polyReach_append {V : Set ℂ} {a b b' : ℂ} (h : PolyReach V a b)
    (hseg : segment ℝ b b' ⊆ V) : PolyReach V a b' := by
  obtain ⟨ha, hb, n, q, h0, hlast, hsegm⟩ := h
  have hb' : b' ∈ V := hseg (right_mem_segment ℝ b b')
  refine ⟨ha, hb', n+1, Fin.snoc (α := fun _ => ℂ) (fun i : Fin (n+1) => q i) b', ?_, ?_, ?_⟩
  · show Fin.snoc (α := fun _ => ℂ) (fun i : Fin (n+1) => q i) b' 0 = a
    rw [show (0 : Fin (n+1+1)) = (0 : Fin (n+1)).castSucc from rfl, Fin.snoc_castSucc]
    exact h0
  · exact Fin.snoc_last (α := fun _ => ℂ) b' _
  · intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
      exact hsegm j
    · have h1 : ((Fin.last n).succ : Fin (n+2)) = Fin.last (n+1) := rfl
      rw [Fin.snoc_castSucc, h1, Fin.snoc_last, hlast]
      exact hseg

/-- The set of points reachable from `a` by polygonal chains is open. -/
theorem isOpen_polyReach {V : Set ℂ} (hVo : IsOpen V) {a : ℂ} (ha : a ∈ V) :
    IsOpen {b : ℂ | PolyReach V a b} := by
  rw [isOpen_iff_mem_nhds]
  intro b hb
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hVo b hb.2.1
  refine Filter.mem_of_superset (Metric.ball_mem_nhds b hr) ?_
  intro b' hb'
  exact polyReach_append hb
    ((Convex.segment_subset (convex_ball b r) (Metric.mem_ball_self hr) hb').trans hball)

/-- .. and it is closed inside `V`. -/
theorem closure_polyReach_subset {V : Set ℂ} (hVo : IsOpen V) {a : ℂ} (ha : a ∈ V) :
    closure {b : ℂ | PolyReach V a b} ∩ V ⊆ {b : ℂ | PolyReach V a b} := by
  rintro b ⟨hbcl, hbV⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hVo b hbV
  obtain ⟨b', hb', hb'dist⟩ := Metric.mem_closure_iff.mp hbcl r hr
  have hb'ball : b' ∈ Metric.ball b r := by
    rw [Metric.mem_ball, dist_comm]; exact hb'dist
  exact polyReach_append hb'
    ((Convex.segment_subset (convex_ball b r) hb'ball (Metric.mem_ball_self hr)).trans hball)

/-- In an open preconnected planar set any two points are joined by a polygonal chain. -/
theorem polyReach_of_isPreconnected {V : Set ℂ} (hVo : IsOpen V) (hVc : IsPreconnected V)
    {a b : ℂ} (ha : a ∈ V) (hb : b ∈ V) : PolyReach V a b := by
  have hΩo : IsOpen {b : ℂ | PolyReach V a b} := isOpen_polyReach hVo ha
  have hsub : {b : ℂ | PolyReach V a b} ⊆ V := fun x hx => hx.2.1
  have hcl : closure {b : ℂ | PolyReach V a b} ∩ V ⊆ {b : ℂ | PolyReach V a b} :=
    closure_polyReach_subset hVo ha
  rcases eq_empty_or_subset_of_clopen hΩo hVc hsub hcl with h | h
  · exfalso
    have hne : ({b : ℂ | PolyReach V a b} : Set ℂ).Nonempty := ⟨a, polyReach_refl ha⟩
    rw [h] at hne
    exact Set.not_nonempty_empty hne
  · exact h hb

/-- The straight-line path from `x` to `y`. -/
def segPath (x y : ℂ) : Path x y :=
  Path.mk ⟨fun t : unitInterval => (1 - (t : ℝ)) • x + (t : ℝ) • y, by fun_prop⟩ (by simp) (by simp)

theorem range_segPath (x y : ℂ) : Set.range (segPath x y) = segment ℝ x y := by
  rw [segment_eq_image]
  ext z; constructor
  · rintro ⟨t, rfl⟩
    exact ⟨(t : ℝ), t.2, rfl⟩
  · rintro ⟨θ, hθ, rfl⟩
    exact ⟨⟨θ, hθ⟩, rfl⟩

/-- The polygonal path through the vertices `q 0, …, q n`. -/
noncomputable def chainPath : {n : ℕ} → (q : Fin (n+1) → ℂ) → Path (q 0) (q (Fin.last n))
  | 0, q => Path.refl (q 0)
  | (n+1), q =>
      ((chainPath (fun i : Fin (n+1) => q i.castSucc)).trans
        (segPath (q (Fin.castSucc (Fin.last n))) (q (Fin.last (n+1))))).cast
        (show q 0 = q (Fin.castSucc (0 : Fin (n+1))) from rfl) rfl

/-- The image of a polygonal path is covered by its segments and its starting point. -/
theorem range_chainPath_subset {V : Set ℂ} : {n : ℕ} → {q : Fin (n+1) → ℂ} →
    (∀ i : Fin n, segment ℝ (q i.castSucc) (q i.succ) ⊆ V) → q 0 ∈ V →
    Set.range (chainPath q) ⊆ V
  | 0, q, hseg, h0 => by
      rw [show chainPath (n := 0) q = Path.refl (q 0) from rfl, Path.refl_range]
      simpa using h0
  | (n+1), q, hseg, h0 => by
      rw [show chainPath (n := n+1) q =
        ((chainPath (fun i : Fin (n+1) => q i.castSucc)).trans
          (segPath (q (Fin.castSucc (Fin.last n))) (q (Fin.last (n+1))))).cast
          (show q 0 = q (Fin.castSucc (0 : Fin (n+1))) from rfl) rfl from rfl]
      rw [Path.cast_coe, Path.trans_range]
      intro z hz
      rcases hz with hz | hz
      · exact range_chainPath_subset (fun i : Fin n => by
          simpa only [Fin.succ_castSucc] using hseg i.castSucc) h0 hz
      · rw [range_segPath] at hz
        exact hseg (Fin.last n) hz



/-! ## The exhaustion of the slit by sub-arcs -/

/-- The closed sub-arc `β '' [δ,1]` of the trace of `β`. -/
def subArc (β : C(Set.Icc (0 : ℝ) 1, ℂ)) (δ : ℝ) : Set ℂ :=
  β '' {t : Set.Icc (0 : ℝ) 1 | δ ≤ (t : ℝ)}

/-- The initial open piece `β '' (0,δ)` of the trace of `β`. -/
def slitPiece (β : C(Set.Icc (0 : ℝ) 1, ℂ)) (δ : ℝ) : Set ℂ :=
  β '' {t : Set.Icc (0 : ℝ) 1 | 0 < (t : ℝ) ∧ (t : ℝ) < δ}

theorem subArc_subset_range (β : C(Set.Icc (0 : ℝ) 1, ℂ)) (δ : ℝ) :
    subArc β δ ⊆ Set.range β := fun _ ⟨t, _, ht⟩ => ⟨t, ht⟩

theorem slitPiece_subset_range (β : C(Set.Icc (0 : ℝ) 1, ℂ)) (δ : ℝ) :
    slitPiece β δ ⊆ Set.range β := fun _ ⟨t, _, ht⟩ => ⟨t, ht⟩

theorem isCompact_subArc (β : C(Set.Icc (0 : ℝ) 1, ℂ)) (δ : ℝ) : IsCompact (subArc β δ) := by
  have h : IsCompact {t : Set.Icc (0 : ℝ) 1 | δ ≤ (t : ℝ)} :=
    (isClosed_le continuous_const continuous_subtype_val).isCompact
  exact h.image β.continuous

theorem subArc_compl_preconnected {β : C(Set.Icc (0 : ℝ) 1, ℂ)} (hβ : Function.Injective β)
    (δ : ℝ) : IsPreconnected (subArc β δ)ᶜ :=
  IsPreconnected.subset_closure (range_compl_preconnected hβ)
    (fun z hz h => hz (subArc_subset_range β δ h))
    (fun z _ => by rw [closure_range_compl hβ]; exact Set.mem_univ z)

/-- The complement of a compact sub-arc of the slit is **path**-connected (it is open, and it is
preconnected because `subArc β δ ⊆ range β` and `(range β)ᶜ` is preconnected and dense).

This is the "slide the crossing to the free end" input: a path can be routed around any *compact*
piece of the slit. -/
theorem isPathConnected_compl_subArc {β : C(Set.Icc (0 : ℝ) 1, ℂ)} (hβ : Function.Injective β)
    (δ : ℝ) : IsPathConnected (subArc β δ)ᶜ := by
  have hopen : IsOpen (subArc β δ)ᶜ := (isCompact_subArc β δ).isClosed.isOpen_compl
  refine hopen.isConnected_iff_isPathConnected.mp ⟨?_, subArc_compl_preconnected hβ δ⟩
  obtain ⟨z, -, hz⟩ := exists_norm_gt_notMem' (isCompact_subArc β δ) 0
  exact ⟨z, hz⟩

/-- **Phragmén–Brouwer, assembled form.** -/
theorem isPreconnected_compl_union_of_disjoint {A B : Set ℂ} (hA : IsCompact A) (hB : IsCompact B)
    (hd : Disjoint A B) (hAc : IsPreconnected Aᶜ) (hBc : IsPreconnected Bᶜ) :
    IsPreconnected (A ∪ B)ᶜ := by
  obtain ⟨x, _, hx⟩ := exists_norm_gt_notMem' (hA.union hB) 0
  have hxA : x ∈ Aᶜ := fun h => hx (Or.inl h)
  have hxB : x ∈ Bᶜ := fun h => hx (Or.inr h)
  rw [Set.compl_union]
  have h := Work.Smooth.JordanSeparation.componentIn_inter_componentIn hA hB hd hxA hxB
  rwa [hAc.connectedComponentIn hxA, hBc.connectedComponentIn hxB] at h

theorem isPreconnected_slit_compl {K : Set ℂ} (hK : IsCompact K) (hconn : IsPreconnected Kᶜ)
    {β : C(Set.Icc (0 : ℝ) 1, ℂ)} (hβ : Function.Injective β)
    (hint : ∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → β t ∉ K) {δ : ℝ} (hδ : 0 < δ) :
    IsPreconnected (K ∪ subArc β δ)ᶜ := by
  refine isPreconnected_compl_union_of_disjoint hK (isCompact_subArc β δ) ?_ hconn
    (subArc_compl_preconnected hβ δ)
  rw [Set.disjoint_left]
  rintro z hzK ⟨t, ht, rfl⟩
  exact hint t (lt_of_lt_of_le hδ ht) hzK

theorem compl_subArc_eq {K : Set ℂ} {β : C(Set.Icc (0 : ℝ) 1, ℂ)} (hβ : Function.Injective β)
    (hint : ∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → β t ∉ K)
    (h₀ : β ⟨0, by norm_num⟩ ∈ K) {δ : ℝ} (hδ : 0 < δ) :
    (K ∪ subArc β δ)ᶜ = (K ∪ Set.range β)ᶜ ∪ slitPiece β δ := by
  ext z; constructor
  · intro hz
    have hzK : z ∉ K := fun h => hz (Or.inl h)
    have hzA : z ∉ subArc β δ := fun h => hz (Or.inr h)
    by_cases hzr : z ∈ Set.range β
    · obtain ⟨t, ht_eq⟩ := hzr
      have hlt : (t : ℝ) < δ := by
        by_contra hle
        exact hzA ⟨t, not_lt.mp hle, ht_eq⟩
      have hpos : 0 < (t : ℝ) := by
        rcases eq_or_lt_of_le t.2.1 with h0 | h0
        · exfalso
          have h1 : (t : ℝ) = 0 := h0.symm
          have ht0 : t = ⟨0, by norm_num⟩ := Subtype.ext (by simp [h1])
          exact hzK (ht_eq ▸ (ht0 ▸ h₀))
        · exact h0
      exact Or.inr ⟨t, ⟨hpos, hlt⟩, ht_eq⟩
    · exact Or.inl (fun h => h.elim hzK hzr)
  · rintro (hzX | ⟨t, ⟨hpos, hlt⟩, ht_eq⟩)
    · rintro (h | h)
      · exact hzX (Or.inl h)
      · exact hzX (Or.inr (subArc_subset_range β δ h))
    · rintro (h | h)
      · exact hint t hpos (ht_eq ▸ h)
      · obtain ⟨s, hs, hs_eq⟩ := h
        have hst : (t : ℝ) = (s : ℝ) :=
          congrArg Subtype.val (hβ (ht_eq.trans hs_eq.symm))
        exact not_le.mpr (hst ▸ hlt) hs

/-- Every point of the slit with positive parameter lies in the closure of
`(K ∪ Set.range β)ᶜ`. -/
theorem mem_closure_compl_range {K : Set ℂ} (hK : IsCompact K)
    {β : C(Set.Icc (0 : ℝ) 1, ℂ)} (hβ : Function.Injective β)
    (hint : ∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → β t ∉ K)
    {t : Set.Icc (0 : ℝ) 1} (ht : 0 < (t : ℝ)) : β t ∈ closure (K ∪ Set.range β)ᶜ := by
  rw [Metric.mem_closure_iff]
  intro η hη
  by_contra hcon
  push_neg at hcon
  have hsub : Metric.ball (β t) η ⊆ K ∪ Set.range β := by
    intro y hy
    by_contra hyX
    have h1 : dist (β t) y < η := by rw [dist_comm]; exact Metric.mem_ball.mp hy
    have h2 : η ≤ dist (β t) y := hcon y hyX
    linarith
  have hβt : β t ∈ closure (Metric.ball (β t) η \ Set.range β) := by
    rw [Metric.mem_closure_iff]
    intro ξ hξ
    by_contra hcon2
    push_neg at hcon2
    have hsub2 : Metric.ball (β t) (min ξ η) ⊆ Set.range β := by
      intro y hy
      by_contra hyr
      have hyball : y ∈ Metric.ball (β t) η :=
        Metric.ball_subset_ball (min_le_right ξ η) hy
      have hdist : dist (β t) y < ξ := by
        rw [dist_comm]
        exact lt_of_lt_of_le (Metric.mem_ball.mp hy) (min_le_left ξ η)
      exact (not_lt.mpr (hcon2 y ⟨hyball, hyr⟩)) hdist
    have hint2 : β t ∈ interior (Set.range β) :=
      interior_maximal hsub2 Metric.isOpen_ball (Metric.mem_ball_self (lt_min hξ hη))
    rw [range_interior_empty hβ] at hint2
    exact absurd hint2 (by simp)
  have hsubK : Metric.ball (β t) η \ Set.range β ⊆ K := by
    rintro y ⟨hyb, hyr⟩
    rcases hsub hyb with h | h
    · exact h
    · exact absurd h hyr
  have hmem : β t ∈ closure K := closure_mono hsubK hβt
  rw [hK.isClosed.closure_eq] at hmem
  exact hint t ht hmem

/-- **(F2)** -/
theorem closure_meets_slitPiece {K : Set ℂ} (hK : IsCompact K) (hconn : IsPreconnected Kᶜ)
    {β : C(Set.Icc (0 : ℝ) 1, ℂ)} (hβ : Function.Injective β)
    (hint : ∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → β t ∉ K)
    (h₀ : β ⟨0, by norm_num⟩ ∈ K)
    {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩsub : Ω ⊆ (K ∪ Set.range β)ᶜ)
    (hΩcl : closure Ω ∩ (K ∪ Set.range β)ᶜ ⊆ Ω) (hΩne : Ω.Nonempty)
    {δ : ℝ} (hδ : 0 < δ) : (closure Ω ∩ slitPiece β δ).Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have hXδ : IsPreconnected (K ∪ subArc β δ)ᶜ := isPreconnected_slit_compl hK hconn hβ hint hδ
  have hsub : Ω ⊆ (K ∪ subArc β δ)ᶜ := fun z hz h => by
    rcases h with hk | ha
    · exact (hΩsub hz) (Or.inl hk)
    · exact (hΩsub hz) (Or.inr (subArc_subset_range β δ ha))
  have hcl : closure Ω ∩ (K ∪ subArc β δ)ᶜ ⊆ Ω := by
    rintro z ⟨hzcl, hzδ⟩
    have hzunion : z ∈ (K ∪ Set.range β)ᶜ ∪ slitPiece β δ := by
      rw [← compl_subArc_eq hβ hint h₀ hδ]
      exact hzδ
    rcases hzunion with h | h
    · exact hΩcl ⟨hzcl, h⟩
    · have hmem2 : z ∈ closure Ω ∩ slitPiece β δ := ⟨hzcl, h⟩
      rw [hempty] at hmem2
      exact absurd hmem2 (Set.notMem_empty z)
  rcases eq_empty_or_subset_of_clopen hΩo hXδ hsub hcl with h | h
  · exact hΩne.ne_empty h
  · have ha'1 : min δ 1 / 2 < δ := by
      have h := min_le_left δ (1:ℝ); linarith
    have ha'0 : 0 < min δ 1 / 2 := by
      have h := lt_min hδ (by norm_num : (0:ℝ) < 1); linarith
    have hmem : β ⟨min δ 1 / 2, by
        constructor
        · linarith
        · have h := min_le_right δ (1:ℝ); linarith⟩ ∈ slitPiece β δ :=
      ⟨⟨min δ 1 / 2, by
          constructor
          · linarith
          · have h := min_le_right δ (1:ℝ); linarith⟩, ⟨ha'0, ha'1⟩, rfl⟩
    have hX : β ⟨min δ 1 / 2, by
        constructor
        · linarith
        · have h := min_le_right δ (1:ℝ); linarith⟩ ∈ (K ∪ subArc β δ)ᶜ := by
      rw [compl_subArc_eq hβ hint h₀ hδ]
      exact Or.inr hmem
    exact (hΩsub (h hX)) (Or.inr (Set.mem_range_self _))

/-- **A ball with a compact set of preconnected complement removed is preconnected.** -/
theorem isPreconnected_ball_sdiff_of_isPreconnected_compl {C : Set ℂ} (hC : IsCompact C)
    (hCc : IsPreconnected Cᶜ) {p : ℂ} {ε : ℝ} (hε : 0 < ε) (hsub : C ⊆ Metric.ball p ε) :
    IsPreconnected (Metric.ball p ε \ C) := by
  obtain ⟨ρ, hρ0, hρlt, hCρ⟩ : ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < ε ∧ C ⊆ Metric.closedBall p ρ := by
    rcases C.eq_empty_or_nonempty with hC0 | hCne
    · exact ⟨ε / 2, by linarith, by linarith, by simp [hC0]⟩
    · obtain ⟨c, hc, hmax⟩ := hC.exists_isMaxOn hCne
        (show ContinuousOn (fun z : ℂ => ‖z - p‖) C from by fun_prop)
      refine ⟨‖c - p‖, norm_nonneg _, ?_, fun z hz => ?_⟩
      · have h := hsub hc
        rw [Metric.mem_ball, dist_eq_norm] at h
        exact h
      · rw [Metric.mem_closedBall, dist_eq_norm]
        exact hmax hz
  set R : ℝ := ‖p‖ + ε with hRdef
  have hR : Metric.ball p ε ⊆ Metric.closedBall (0 : ℂ) R := fun z hz => by
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [Metric.mem_closedBall, dist_zero_right, hRdef]
    calc ‖z‖ = ‖z - p + p‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - p‖ + ‖p‖ := norm_add_le (z - p) p
      _ ≤ ‖p‖ + ε := by linarith
  set x : ℂ := p + (((ρ + ε) / 2 : ℝ) : ℂ) with hxdef
  have hx : x ∈ Metric.ball p ε \ C := by
    constructor
    · rw [Metric.mem_ball, dist_eq_norm]
      have h2 : x - p = (((ρ + ε) / 2 : ℝ) : ℂ) := by rw [hxdef]; ring
      rw [h2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    · intro hxC
      have h1 := hCρ hxC
      rw [Metric.mem_closedBall, dist_eq_norm] at h1
      have h2 : x - p = (((ρ + ε) / 2 : ℝ) : ℂ) := by rw [hxdef]; ring
      rw [h2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at h1
      linarith
  set Q : Set ℂ := (Metric.ball p ε)ᶜ ∩ Metric.closedBall (0 : ℂ) R with hQdef
  have hQc : IsCompact Q := by
    rw [hQdef, Set.inter_comm]
    exact (ProperSpace.isCompact_closedBall (0 : ℂ) R).inter_right
      Metric.isOpen_ball.isClosed_compl
  have hd : Disjoint C Q := by
    rw [Set.disjoint_left]
    rintro z hzC ⟨hzB, -⟩
    exact hzB (hsub hzC)
  have hxC : x ∈ Cᶜ := fun h => hx.2 h
  have hxQ : x ∈ Qᶜ := fun h => h.1 hx.1
  have hPB := Work.Smooth.JordanSeparation.componentIn_inter_componentIn hC hQc hd hxC hxQ
  have hCcomp : connectedComponentIn Cᶜ x = Cᶜ := hCc.connectedComponentIn hxC
  have hQcomp : connectedComponentIn Qᶜ x = Metric.ball p ε := by
    refine Subset.antisymm ?_ ?_
    · have h1 : IsOpen (Metric.ball p ε) := Metric.isOpen_ball
      have h2 : IsOpen ((Metric.closedBall (0 : ℂ) R)ᶜ) :=
        Metric.isClosed_closedBall.isOpen_compl
      have h3 : Disjoint (Metric.ball p ε) ((Metric.closedBall (0 : ℂ) R)ᶜ) := by
        rw [Set.disjoint_left]
        intro z hz hz'
        exact hz' (hR hz)
      have h4 : Qᶜ ⊆ Metric.ball p ε ∪ ((Metric.closedBall (0 : ℂ) R)ᶜ) := by
        intro z hz
        rw [hQdef, Set.compl_inter, compl_compl] at hz
        exact hz
      intro y hy
      have h4' : connectedComponentIn Qᶜ x ⊆
          Metric.ball p ε ∪ ((Metric.closedBall (0 : ℂ) R)ᶜ) :=
        fun z hz => h4 (connectedComponentIn_subset Qᶜ x hz)
      rcases (isPreconnected_connectedComponentIn (x := x) (F := Qᶜ)).subset_or_subset
        h1 h2 h3 h4' with h | h
      · exact h hy
      · exfalso
        have hz := h (mem_connectedComponentIn hxQ)
        have hzR : R < ‖x‖ := by
          simpa [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right] using hz
        have hxb : ‖x - p‖ < ε := by
          have h1 := hx.1
          rwa [Metric.mem_ball, dist_eq_norm] at h1
        have h2' : ‖x‖ ≤ ‖x - p‖ + ‖p‖ := by
          calc ‖x‖ = ‖x - p + p‖ := by rw [sub_add_cancel]
            _ ≤ ‖x - p‖ + ‖p‖ := norm_add_le (x - p) p
        rw [hRdef] at hzR
        linarith
    · exact (convex_ball p ε).isPreconnected.subset_connectedComponentIn hx.1 (fun z hz => by
        rw [hQdef]
        exact fun h => h.1 hz)
  rw [hCcomp, hQcomp] at hPB
  simpa [Set.sdiff_eq, Set.inter_comm] using hPB

/-- **The free end of the slit is isolated from `K`, and the slit's tail stays near it.** -/
theorem freeEndBall {K : Set ℂ} (hK : IsCompact K)
    {β : C(Set.Icc (0 : ℝ) 1, ℂ)} (h₁ : β ⟨1, by norm_num⟩ ∉ K) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.closedBall (β ⟨1, by norm_num⟩) ε ∩ K = ∅ ∧
      ∃ a : ℝ, 0 ≤ a ∧ a < 1 ∧
        ∀ t : Set.Icc (0 : ℝ) 1, a ≤ (t : ℝ) → β t ∈ Metric.ball (β ⟨1, by norm_num⟩) ε := by
  have hKcl : IsClosed K := hK.isClosed
  obtain ⟨r, hr, hrK⟩ := Metric.isOpen_iff.mp hKcl.isOpen_compl _
    (show β ⟨1, by norm_num⟩ ∈ Kᶜ from h₁)
  have hε₁ : 0 < r / 2 := by linarith
  have hε₁K : Metric.closedBall (β ⟨1, by norm_num⟩) (r / 2) ∩ K = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hz, hzK⟩
    exact hrK (Metric.closedBall_subset_ball (by linarith) hz) hzK
  obtain ⟨η, hη, hηβ⟩ : ∃ η : ℝ, 0 < η ∧ ∀ t : Set.Icc (0 : ℝ) 1,
      dist t ⟨1, by norm_num⟩ < η → dist (β t) (β ⟨1, by norm_num⟩) < r / 2 :=
    Metric.continuousAt_iff.mp β.continuous.continuousAt (r / 2) (by linarith)
  refine ⟨r / 2, hε₁, hε₁K, 1 - min (η / 2) (1 / 2), ?_, ?_, ?_⟩
  · have h := min_le_right (η / 2) (1 / 2); linarith
  · have h : 0 < min (η / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
    linarith
  intro t ht
  rw [Metric.mem_ball]
  apply hηβ t
  have hd : dist t ⟨1, by norm_num⟩ = 1 - (t : ℝ) := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith [t.2.2])]
    ring
  rw [hd]
  have h1 := min_le_left (η / 2) (1 / 2)
  linarith

/-! ## Trimming the path: piece 1 — the parameter of a point of the trace

`β` is injective and continuous out of the compact interval, hence a closed embedding into `ℂ`; that
makes `Set.range β` canonically homeomorphic to the parameter interval, giving a *continuous* inverse
`paramOf : Set.range β → Set.Icc 0 1` ("the parameter of a trace point").  This is the input for
factorising a path that runs along the slit through the parameter interval. -/

theorem isClosedEmbedding_coe {β : C(Set.Icc (0 : ℝ) 1, ℂ)} (hβ : Function.Injective β) :
    Topology.IsClosedEmbedding (β : Set.Icc (0 : ℝ) 1 → ℂ) :=
  β.continuous.isClosedEmbedding hβ

/-- The trace of `β` is canonically homeomorphic to the parameter interval. -/
noncomputable def rangeHomeomorph {β : C(Set.Icc (0 : ℝ) 1, ℂ)} (hβ : Function.Injective β) :
    Set.Icc (0 : ℝ) 1 ≃ₜ Set.range β :=
  (isClosedEmbedding_coe hβ).toIsEmbedding.toHomeomorph

/-- **The parameter of a point of the trace.** -/
noncomputable def paramOf {β : C(Set.Icc (0 : ℝ) 1, ℂ)} (hβ : Function.Injective β)
    (z : Set.range β) : Set.Icc (0 : ℝ) 1 :=
  (rangeHomeomorph hβ).symm z

theorem paramOf_apply {β : C(Set.Icc (0 : ℝ) 1, ℂ)} (hβ : Function.Injective β)
    (z : Set.range β) : β (paramOf hβ z) = (z : ℂ) :=
  congrArg Subtype.val ((rangeHomeomorph hβ).apply_symm_apply z)

theorem paramOf_eq_iff {β : C(Set.Icc (0 : ℝ) 1, ℂ)} (hβ : Function.Injective β)
    {t : Set.Icc (0 : ℝ) 1} : paramOf hβ ⟨β t, Set.mem_range_self t⟩ = t := by
  have h : (⟨β t, Set.mem_range_self t⟩ : Set.range β) = rangeHomeomorph hβ t := rfl
  rw [paramOf, h, Homeomorph.symm_apply_apply]

theorem continuous_paramOf {β : C(Set.Icc (0 : ℝ) 1, ℂ)} (hβ : Function.Injective β) :
    Continuous (paramOf hβ) :=
  (rangeHomeomorph hβ).continuous_symm

/-- **Trimming, piece 3 (factorisation).**  A path into the trace is the composition of its
(continuous) parameter map with `β`. -/
theorem eq_comp_paramOf {β : C(Set.Icc (0 : ℝ) 1, ℂ)} (hβ : Function.Injective β)
    {X : Type*} [TopologicalSpace X] {f : X → ℂ} (hf : ∀ x, f x ∈ Set.range β) :
    f = fun x => β (paramOf hβ ⟨f x, hf x⟩) := by
  funext x
  exact (paramOf_apply hβ ⟨f x, hf x⟩).symm

/-- **The local core of the sliding step.**

Given the free-end joining property `hsides` for the ball `ball (β s) r` (all of whose points are in
`Kᶜ`), any two points of `ball (β s) r \ Set.range β` are joined by a path inside `Kᶜ \ Set.range β`:
if they lie on the same side of the slit they are joined inside their (open, preconnected, hence
path-connected) component, and if they lie on opposite sides this is exactly `hsides`. -/
theorem exists_path_of_ball {K : Set ℂ} {β : C(Set.Icc (0 : ℝ) 1, ℂ)} {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) {r : ℝ} (hball : Metric.ball (β ⟨s, hs.1.le, hs.2.le⟩) r ⊆ Kᶜ)
    (hsides : ∀ u ∈ Metric.ball (β ⟨s, hs.1.le, hs.2.le⟩) r, u ∉ Set.range β →
      ∀ v ∈ Metric.ball (β ⟨s, hs.1.le, hs.2.le⟩) r, v ∉ Set.range β →
      v ∉ connectedComponentIn (Metric.ball (β ⟨s, hs.1.le, hs.2.le⟩) r \ Set.range β) u →
      ∃ γ : Path u v, Set.range γ ⊆ Kᶜ \ Set.range β)
    {u v : ℂ} (hu : u ∈ Metric.ball (β ⟨s, hs.1.le, hs.2.le⟩) r) (huβ : u ∉ Set.range β)
    (hv : v ∈ Metric.ball (β ⟨s, hs.1.le, hs.2.le⟩) r) (hvβ : v ∉ Set.range β) :
    ∃ γ : Path u v, Set.range γ ⊆ Kᶜ \ Set.range β := by
  by_cases hcomp : v ∈ connectedComponentIn
    (Metric.ball (β ⟨s, hs.1.le, hs.2.le⟩) r \ Set.range β) u
  · have hopen : IsOpen (Metric.ball (β ⟨s, hs.1.le, hs.2.le⟩) r \ Set.range β) := by
      rw [Set.sdiff_eq]
      exact Metric.isOpen_ball.inter
        (isCompact_range β.continuous).isClosed.isOpen_compl
    have hCopen := hopen.connectedComponentIn (x := u)
    have hCne : (connectedComponentIn
        (Metric.ball (β ⟨s, hs.1.le, hs.2.le⟩) r \ Set.range β) u).Nonempty :=
      ⟨u, mem_connectedComponentIn ⟨hu, huβ⟩⟩
    have hCpath : IsPathConnected
        (connectedComponentIn (Metric.ball (β ⟨s, hs.1.le, hs.2.le⟩) r \ Set.range β) u) :=
      hCopen.isConnected_iff_isPathConnected.mp
        ⟨hCne, isPreconnected_connectedComponentIn⟩
    obtain ⟨γ, hγ⟩ := hCpath.joinedIn u (mem_connectedComponentIn ⟨hu, huβ⟩) v hcomp
    refine ⟨γ, fun z hz => ?_⟩
    obtain ⟨w, rfl⟩ := hz
    have hzC : γ w ∈ connectedComponentIn
        (Metric.ball (β ⟨s, hs.1.le, hs.2.le⟩) r \ Set.range β) u := hγ w
    obtain ⟨hzb, hzβ⟩ := connectedComponentIn_subset
      (Metric.ball (β ⟨s, hs.1.le, hs.2.le⟩) r \ Set.range β) u hzC
    exact ⟨hball hzb, hzβ⟩
  · exact hsides u hu huβ v hv hvβ hcomp

/-- **The single-crossing replacement (Step B, one crossing).**

Let `σ : Path x y` lie in `Kᶜ` and hit the slit point `β s` only *outside* the parameter range
`[A,B]` (hypotheses `hav1`, `hav2`), with `σ A` and `σ B` inside the free-end ball
`ball (β s) r ∖ Set.range β`.  Then `σ` can be replaced on `[A,B]` by a path inside
`Kᶜ ∖ Set.range β` (e.g. the one produced by `exists_path_of_ball`), yielding a path from `x` to `y`
in `Kᶜ` that misses `β s`. -/
theorem glue_replacement {K : Set ℂ} {β : C(Set.Icc (0 : ℝ) 1, ℂ)} {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) {r : ℝ}
    (hball : Metric.ball (β ⟨s, hs.1.le, hs.2.le⟩) r ⊆ Kᶜ)
    (hsides : ∀ u ∈ Metric.ball (β ⟨s, hs.1.le, hs.2.le⟩) r, u ∉ Set.range β →
      ∀ v ∈ Metric.ball (β ⟨s, hs.1.le, hs.2.le⟩) r, v ∉ Set.range β →
      v ∉ connectedComponentIn (Metric.ball (β ⟨s, hs.1.le, hs.2.le⟩) r \ Set.range β) u →
      ∃ γ : Path u v, Set.range γ ⊆ Kᶜ \ Set.range β)
    {x y : ℂ} (σ : Path x y) (hσ : Set.range σ ⊆ Kᶜ) {A B : Set.Icc (0 : ℝ) 1}
    (hAB : (A : ℝ) ≤ (B : ℝ))
    (hAX : σ A ∈ Metric.ball (β ⟨s, hs.1.le, hs.2.le⟩) r) (hAβ : σ A ∉ Set.range β)
    (hBX : σ B ∈ Metric.ball (β ⟨s, hs.1.le, hs.2.le⟩) r) (hBβ : σ B ∉ Set.range β)
    (hav1 : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ≤ (A : ℝ) → σ t ≠ β ⟨s, hs.1.le, hs.2.le⟩)
    (hav2 : ∀ t : Set.Icc (0 : ℝ) 1, (B : ℝ) ≤ (t : ℝ) → σ t ≠ β ⟨s, hs.1.le, hs.2.le⟩) :
    ∃ σ' : Path x y, Set.range σ' ⊆ Kᶜ ∧ β ⟨s, hs.1.le, hs.2.le⟩ ∉ Set.range σ' := by
  obtain ⟨γ, hγ⟩ := exists_path_of_ball hs hball hsides hAX hAβ hBX hBβ
  have hmem1 : ∀ t : Set.Icc (0 : ℝ) 1, (A : ℝ) * (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    fun t => ⟨mul_nonneg A.2.1 t.2.1, by nlinarith [A.2.1, A.2.2, t.2.1, t.2.2]⟩
  have hmem2 : ∀ t : Set.Icc (0 : ℝ) 1, (B : ℝ) + (1 - (B : ℝ)) * (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    fun t => ⟨by nlinarith [B.2.1, B.2.2, t.2.1, t.2.2],
      by nlinarith [B.2.1, B.2.2, t.2.1, t.2.2]⟩
  have hcont1 : Continuous fun t : Set.Icc (0 : ℝ) 1 => σ ⟨(A : ℝ) * (t : ℝ), hmem1 t⟩ :=
    σ.continuous.comp (Continuous.subtype_mk (by fun_prop) _)
  have hcont2 : Continuous fun t : Set.Icc (0 : ℝ) 1 =>
      σ ⟨(B : ℝ) + (1 - (B : ℝ)) * (t : ℝ), hmem2 t⟩ :=
    σ.continuous.comp (Continuous.subtype_mk (by fun_prop) _)
  have h0 : (⟨(A : ℝ) * (((0 : Set.Icc (0 : ℝ) 1)) : ℝ), hmem1 0⟩ : Set.Icc (0 : ℝ) 1) = 0 :=
    Subtype.ext (by simp)
  have h1 : (⟨(A : ℝ) * (((1 : Set.Icc (0 : ℝ) 1)) : ℝ), hmem1 1⟩ : Set.Icc (0 : ℝ) 1) = A :=
    Subtype.ext (by simp)
  have h2 : (⟨(B : ℝ) + (1 - (B : ℝ)) * (((0 : Set.Icc (0 : ℝ) 1)) : ℝ), hmem2 0⟩ :
      Set.Icc (0 : ℝ) 1) = B := Subtype.ext (by simp)
  have h3 : (⟨(B : ℝ) + (1 - (B : ℝ)) * (((1 : Set.Icc (0 : ℝ) 1)) : ℝ), hmem2 1⟩ :
      Set.Icc (0 : ℝ) 1) = 1 := Subtype.ext (by simp)
  let p1 : Path x (σ A) :=
    ⟨⟨fun t : Set.Icc (0 : ℝ) 1 => σ ⟨(A : ℝ) * (t : ℝ), hmem1 t⟩, hcont1⟩,
      (by simpa [h0] using Path.source σ), (by simp [h1])⟩
  let p3 : Path (σ B) y :=
    ⟨⟨fun t : Set.Icc (0 : ℝ) 1 => σ ⟨(B : ℝ) + (1 - (B : ℝ)) * (t : ℝ), hmem2 t⟩, hcont2⟩,
      (by simp [h2]), (by simpa [h3] using Path.target σ)⟩
  refine ⟨(p1.trans γ).trans p3, ?_, ?_⟩
  · intro z hz
    rw [Path.trans_range] at hz
    rcases hz with hz | hz
    · rw [Path.trans_range] at hz
      rcases hz with hz | hz
      · obtain ⟨t, rfl⟩ := hz
        exact hσ ⟨⟨(A : ℝ) * (t : ℝ), hmem1 t⟩, rfl⟩
      · exact (hγ hz).1
    · obtain ⟨t, rfl⟩ := hz
      exact hσ ⟨⟨(B : ℝ) + (1 - (B : ℝ)) * (t : ℝ), hmem2 t⟩, rfl⟩
  · intro hcon
    rw [Path.trans_range] at hcon
    rcases hcon with hcon | hcon
    · rw [Path.trans_range] at hcon
      rcases hcon with hcon | hcon
      · obtain ⟨t, ht⟩ := hcon
        rw [show p1 t = σ ⟨(A : ℝ) * (t : ℝ), hmem1 t⟩ from rfl] at ht
        exact hav1 ⟨(A : ℝ) * (t : ℝ), hmem1 t⟩ (by nlinarith [A.2.1, t.2.2]) ht
      · exact (hγ hcon).2 (Set.mem_range_self _)
    · obtain ⟨t, ht⟩ := hcon
      rw [show p3 t = σ ⟨(B : ℝ) + (1 - (B : ℝ)) * (t : ℝ), hmem2 t⟩ from rfl] at ht
      exact hav2 ⟨(B : ℝ) + (1 - (B : ℝ)) * (t : ℝ), hmem2 t⟩
        (by nlinarith [B.2.1, B.2.2, t.2.1]) ht

/-- **The endpoint contradiction of the descent.**

If a path lying in `Kᶜ` meets the slit arbitrarily close to the base point (i.e. it meets
`β '' (0, 1/(n+1))` for every `n`), then — because `β 0 = p` lies in `K` — the path must pass
through `p`, which is impossible.  This is the terminating step of the descent: iterating the
sliding step would force any path joining two points of `X` in different components to have this
property. -/
theorem not_forall_meets_slit_near_base {K : Set ℂ}
    {β : C(Set.Icc (0 : ℝ) 1, ℂ)} (h₀ : β ⟨0, by norm_num⟩ ∈ K) {x y : ℂ} (σ : Path x y)
    (hσ : Set.range σ ⊆ Kᶜ)
    (h : ∀ n : ℕ, ∃ s : Set.Icc (0 : ℝ) 1, (s : ℝ) < 1 / ((n : ℝ) + 1) ∧ β s ∈ Set.range σ) :
    False := by
  choose s hs hβs using h
  choose a ha using hβs
  obtain ⟨b, -, φ, hφ, hlim⟩ :=
    isCompact_univ.tendsto_subseq (x := a) (fun n => Set.mem_univ _)
  have hsa : Filter.Tendsto (fun n : ℕ => ((s (φ n) : Set.Icc (0 : ℝ) 1) : ℝ))
      Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun n => (s (φ n)).2.1) (fun n => ?_)
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
    exact (hs (φ n)).le
  have hsb : Filter.Tendsto (fun n : ℕ => s (φ n)) Filter.atTop (nhds ⟨0, by norm_num⟩) := by
    rw [tendsto_subtype_rng]
    exact hsa
  have hb : Filter.Tendsto (fun n : ℕ => β (s (φ n))) Filter.atTop (nhds (β ⟨0, by norm_num⟩)) :=
    β.continuous.continuousAt.tendsto.comp hsb
  have h1 : Filter.Tendsto (fun n : ℕ => σ (a (φ n))) Filter.atTop (nhds (σ b)) :=
    σ.continuous.continuousAt.tendsto.comp hlim
  have h2 : (fun n : ℕ => σ (a (φ n))) = fun n : ℕ => β (s (φ n)) := by
    funext n
    exact ha (φ n)
  have h3 : σ b = β ⟨0, by norm_num⟩ := tendsto_nhds_unique h1 (by rw [h2]; exact hb)
  exact (hσ ⟨b, rfl⟩) (h3 ▸ h₀)

/-! ## The final assembly: Janiszewski's theorem with a single-point intersection

`Work.Spike.janiszewski_pointInter` (delegated, proved in
`Submission/Work/Spike/janiszewski_pointInter.lean`) is the borderline case of Janiszewski's theorem:
for **compact** `A, B ⊆ ℂ` meeting in a single point `z`, two points joined both in `Aᶜ` and in `Bᶜ`
are joined in `(A ∪ B)ᶜ`.  It applies verbatim here with `A := K` and `B := Set.range β`, since
`K ∩ Set.range β = {β 0}` and both `Kᶜ` (hypothesis) and `(Set.range β)ᶜ` (an arc does not separate
the plane) are preconnected.
-/

/-- The trace of `β` meets `K` in the single point `β 0`. -/
theorem inter_range_eq_singleton {K : Set ℂ} {β : C(Set.Icc (0 : ℝ) 1, ℂ)}
    (h₀ : β ⟨0, by norm_num⟩ ∈ K)
    (hint : ∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → β t ∉ K) :
    K ∩ Set.range β = {β ⟨0, by norm_num⟩} := by
  refine Set.Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨hzK, t, rfl⟩ := hz
    have ht : (t : ℝ) = 0 := by
      by_contra hnt
      exact hint t (lt_of_le_of_ne t.2.1 (Ne.symm hnt)) hzK
    rw [Set.mem_singleton_iff]
    exact congrArg β (Subtype.ext ht)
  · rw [Set.mem_singleton_iff] at hz
    exact ⟨hz ▸ h₀, hz ▸ Set.mem_range_self _⟩

theorem spikePreconnected {K : Set ℂ} (hK : IsCompact K) (hconn : IsPreconnected Kᶜ)
    {β : C(Set.Icc (0 : ℝ) 1, ℂ)} (hβ : Function.Injective β) (h₀ : β ⟨0, by norm_num⟩ ∈ K)
    (hint : ∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → β t ∉ K) :
    IsPreconnected (K ∪ Set.range β)ᶜ := by
  have hβc : IsCompact (Set.range β) := isCompact_range β.continuous
  have harc : IsPreconnected ((Set.range β)ᶜ : Set ℂ) := range_compl_preconnected hβ
  have hinter : K ∩ Set.range β = {β ⟨0, by norm_num⟩} := inter_range_eq_singleton h₀ hint
  obtain ⟨p, -, hp⟩ := exists_norm_gt_notMem' (hK.union hβc) 0
  have hpY : p ∈ (K ∪ Set.range β)ᶜ := hp
  rw [show (K ∪ Set.range β)ᶜ = connectedComponentIn (K ∪ Set.range β)ᶜ p from
    Set.Subset.antisymm (fun q hq => ?_) (connectedComponentIn_subset _ _)]
  exact isPreconnected_connectedComponentIn
  have hpK : p ∈ Kᶜ := fun h => hpY (Or.inl h)
  have hpβ : p ∈ (Set.range β)ᶜ := fun h => hpY (Or.inr h)
  have hqK : q ∈ Kᶜ := fun h => hq (Or.inl h)
  have hqβ : q ∈ (Set.range β)ᶜ := fun h => hq (Or.inr h)
  exact janiszewski_pointInter hK hβc hinter hpY hq
    (hconn.subset_connectedComponentIn hpK subset_rfl hqK)
    (harc.subset_connectedComponentIn hpβ subset_rfl hqβ)

end

end Work.Spike
