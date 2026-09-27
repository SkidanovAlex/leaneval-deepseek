import Mathlib

/-!
# A totally disconnected hyperplane slice through a countable union of arcs

Given `n ≥ 3`, a countable family `g i : ℝ → ℝ^n` of continuous injective maps whose images of
`[0,1]` have compact union `K`, and a point `x ∉ K`, there is a nonzero vector `u` such that the
slice of `K` by the hyperplane through `x` orthogonal to `u` is totally disconnected.

The proof has three parts.

* The set of "bad" directions `u`, for which some arc `g i` lies in the hyperplane on a nondegenerate
  interval `[a,b]`, is a countable union of proper closed subspaces of `ℝ^n`, hence meager; since
  `ℝ^n` is Baire we find `u ≠ 0` outside all of them (`exists_good_direction`).
* For such a `u`, each individual slice is totally disconnected: it is the homeomorphic image of a
  closed subset of `[0,1]` with empty interior (`isTotallyDisconnected_sliceSet`).
* A compact metric space that is a countable union of compact totally disconnected subsets is
  totally disconnected.  Otherwise Baire's theorem produces a nonempty open totally disconnected
  subset of a nondegenerate compact continuum, and such a set cannot exist
  (`no_open_totallyDisconnected_subset`).
-/

open Set Metric Topology Filter
open scoped Topology

namespace Work.Whitney.PathTools

variable {n : ℕ} {ι : Type*}

/-! ## Bad directions -/

/-- The directions `u` for which the arc `g i` lies in the hyperplane `{z | ⟪z - x, u⟫ = 0}` on the
whole interval `[a,b]`. -/
noncomputable def badSub (g : ι → ℝ → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n))
    (i : ι) (a b : ℚ) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  ⨅ (t : ↥(Set.Icc (a:ℝ) (b:ℝ))), LinearMap.ker ((innerSL ℝ (g i (t:ℝ) - x)).toLinearMap)

lemma mem_badSub (g : ι → ℝ → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n))
    (i : ι) (a b : ℚ) (u : EuclideanSpace ℝ (Fin n)) :
    u ∈ badSub g x i a b ↔ ∀ t ∈ Set.Icc (a:ℝ) (b:ℝ), inner ℝ (g i t - x) u = 0 := by
  rw [badSub]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h t ht
    have := h ⟨t, ht⟩
    simpa [inner_sub_left] using this
  · intro h t
    have := h t.1 t.2
    simpa [inner_sub_left] using this

lemma coe_badSub (g : ι → ℝ → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n))
    (i : ι) (a b : ℚ) :
    (badSub g x i a b : Set (EuclideanSpace ℝ (Fin n)))
      = {u | ∀ t ∈ Set.Icc (a:ℝ) (b:ℝ), inner ℝ (g i t - x) u = 0} := by
  ext u
  exact mem_badSub g x i a b u

lemma isClosed_badSub (g : ι → ℝ → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n))
    (i : ι) (a b : ℚ) : IsClosed (badSub g x i a b : Set (EuclideanSpace ℝ (Fin n))) := by
  rw [coe_badSub]
  have hset : {u : EuclideanSpace ℝ (Fin n) |
        ∀ t ∈ Set.Icc (a:ℝ) (b:ℝ), inner ℝ (g i t - x) u = 0}
      = ⋂ t ∈ Set.Icc (a:ℝ) (b:ℝ),
          {u : EuclideanSpace ℝ (Fin n) | inner ℝ (g i t - x) u = 0} := by
    ext u
    simp
  rw [hset]
  exact isClosed_biInter fun t _ =>
    isClosed_singleton.preimage (continuous_const.inner continuous_id)

/-- There is a nonzero vector in `EuclideanSpace ℝ (Fin n)` as soon as `n ≥ 1`. -/
lemma nontrivial_euclidean (hn : 1 ≤ n) : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
  let i : Fin n := ⟨0, by omega⟩
  have h0 : ((WithLp.equiv 2 (Fin n → ℝ)) (0 : EuclideanSpace ℝ (Fin n))) i = 0 := by simp
  refine ⟨0, (WithLp.equiv 2 (Fin n → ℝ)).symm (Pi.single i (1:ℝ)), fun h => ?_⟩
  have h1 : ((WithLp.equiv 2 (Fin n → ℝ))
      ((WithLp.equiv 2 (Fin n → ℝ)).symm (Pi.single i (1:ℝ)))) i = 1 := by
    rw [Equiv.apply_symm_apply]; simp
  have hcong := congrArg (fun v : EuclideanSpace ℝ (Fin n) =>
    (WithLp.equiv 2 (Fin n → ℝ)) v i) h
  rw [h1, h0] at hcong
  exact zero_ne_one hcong

lemma badSub_ne_top {g : ι → ℝ → EuclideanSpace ℝ (Fin n)} {x : EuclideanSpace ℝ (Fin n)}
    {i : ι} {a b : ℚ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (hx : x ∉ g i '' Set.Icc (0:ℝ) 1) : badSub g x i a b ≠ ⊤ := by
  intro h
  have hmem : (g i (a:ℝ) - x) ∈ badSub g x i a b := by rw [h]; trivial
  rw [mem_badSub] at hmem
  have ha : (a:ℝ) ∈ Set.Icc (a:ℝ) (b:ℝ) := ⟨le_rfl, by exact_mod_cast hab⟩
  have hzero := hmem (a:ℝ) ha
  rw [inner_self_eq_zero, sub_eq_zero] at hzero
  exact hx ⟨(a:ℝ), ⟨by exact_mod_cast ha0, by exact_mod_cast le_trans hab hb1⟩, hzero⟩

lemma not_nonempty_interior_badSub {g : ι → ℝ → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin n)} {i : ι} {a b : ℚ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (hx : x ∉ g i '' Set.Icc (0:ℝ) 1) :
    ¬ (interior (badSub g x i a b : Set (EuclideanSpace ℝ (Fin n)))).Nonempty :=
  fun hne => badSub_ne_top ha0 hab hb1 hx (Submodule.eq_top_of_nonempty_interior' _ hne)

/-- An index for the family of "bad" direction sets: either the origin, or a pair consisting of an
index `i` and a rational interval `[a,b] ⊆ [0,1]`. -/
abbrev BadIdx (ι : Type*) : Type _ :=
  Option (ι × {q : ℚ × ℚ // 0 ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ 1})

/-- The family of bad direction sets.  The `none` index carries the origin. -/
noncomputable def badFamily (g : ι → ℝ → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : BadIdx ι → Set (EuclideanSpace ℝ (Fin n))
  | none => {0}
  | some p => badSub g x p.1 p.2.val.1 p.2.val.2

/-- There is a nonzero direction `u` such that for every `i` the function
`t ↦ ⟪g i t - x, u⟫` is not identically zero on any nondegenerate rational interval contained in
`[0,1]`. -/
theorem exists_good_direction {n : ℕ} (hn : 1 ≤ n) {ι : Type*} [Countable ι]
    (g : ι → ℝ → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n))
    (hx : ∀ i, x ∉ g i '' Set.Icc (0:ℝ) 1) :
    ∃ u : EuclideanSpace ℝ (Fin n), u ≠ 0 ∧
      ∀ (i : ι) (a b : ℚ), 0 ≤ a → a < b → b ≤ 1 →
        ∃ t ∈ Set.Icc (a:ℝ) (b:ℝ), inner ℝ (g i t - x) u ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hcover : (⋃ p : BadIdx ι, badFamily g x p) = Set.univ := by
    rw [eq_univ_iff_forall]
    intro u
    by_cases hu : u = 0
    · exact mem_iUnion.mpr ⟨none, by simp [badFamily, hu]⟩
    · rcases hcon u hu with ⟨i, a, b, ha0, hab, hb1, hzero⟩
      exact mem_iUnion.mpr ⟨some ⟨i, ⟨(a, b), ha0, le_of_lt hab, hb1⟩⟩, by
        simp only [badFamily]
        exact (mem_badSub g x i a b u).mpr hzero⟩
  have hclosed : ∀ p : BadIdx ι, IsClosed (badFamily g x p) := by
    intro p
    cases p with
    | none => simp only [badFamily]; exact isClosed_singleton
    | some q => simp only [badFamily]; exact isClosed_badSub g x q.1 q.2.val.1 q.2.val.2
  have hnot : ∀ p : BadIdx ι, ¬ (interior (badFamily g x p)).Nonempty := by
    intro p
    cases p with
    | none =>
      simp only [badFamily]
      haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) := nontrivial_euclidean hn
      intro h
      have htop : (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) = ⊤ :=
        Submodule.eq_top_of_nonempty_interior' _ (by simpa using h)
      have hsub : Subsingleton (EuclideanSpace ℝ (Fin n)) := ⟨fun a b => by
        have ha : a ∈ (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) := htop ▸ Submodule.mem_top
        have hb : b ∈ (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) := htop ▸ Submodule.mem_top
        rw [Submodule.mem_bot] at ha hb
        rw [ha, hb]⟩
      exact not_subsingleton_iff_nontrivial.mpr ‹Nontrivial (EuclideanSpace ℝ (Fin n))› hsub
    | some q =>
      simp only [badFamily]
      exact not_nonempty_interior_badSub q.2.property.1 q.2.property.2.1 q.2.property.2.2 (hx q.1)
  obtain ⟨p, hp⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  exact hnot p hp

/-! ## An open totally disconnected subset of a continuum is empty -/

/-- A nondegenerate compact preconnected Hausdorff space has no nonempty open totally disconnected
subset. -/
theorem no_open_totallyDisconnected_subset {C : Type*} [TopologicalSpace C]
    [T2Space C] [CompactSpace C] [PreconnectedSpace C] [Nontrivial C]
    {U : Set C} (hU : IsOpen U) (htd : IsTotallyDisconnected U) : U = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hUne : U ≠ Set.univ := by
    intro hUu
    haveI : TotallyDisconnectedSpace C := ⟨hUu ▸ htd⟩
    haveI : Subsingleton C := subsingleton_of_preconnected_totallyDisconnected
    exact not_subsingleton_iff_nontrivial.mpr ‹Nontrivial C› ‹Subsingleton C›
  have hy : ∃ y, y ∉ U := by
    contrapose! hUne
    rwa [Set.eq_univ_iff_forall]
  obtain ⟨y, hy⟩ := hy
  have hUn : U ∈ 𝓝 x := hU.mem_nhds hx
  obtain ⟨V, ⟨hxV, hVo⟩, hVU⟩ := (hasBasis_opens_closure x).mem_iff.mp hUn
  have hcl : IsClosed (closure V) := isClosed_closure
  have hcV : IsCompact (closure V) := hcl.isCompact
  haveI : CompactSpace ↥(closure V) := isCompact_iff_compactSpace.mp hcV
  have htdV : IsTotallyDisconnected (closure V) :=
    fun t ht hpre => htd t (ht.trans hVU) hpre
  haveI : TotallyDisconnectedSpace ↥(closure V) := totallyDisconnectedSpace_subtype_iff.mpr htdV
  have hxcl : x ∈ closure V := subset_closure hxV
  obtain ⟨W', hW'cl, hxW', hW'V⟩ :=
    compact_exists_isClopen_in_isOpen (x := (⟨x, hxcl⟩ : ↥(closure V)))
      (U := Subtype.val ⁻¹' V) (hVo.preimage continuous_subtype_val) (by simpa using hxV)
  set W : Set C := Subtype.val '' W' with hWdef
  have hWclosed : IsClosed W :=
    (IsClosed.isClosedEmbedding_subtypeVal hcl).isClosedMap W' hW'cl.1
  have hWopen : IsOpen W := by
    obtain ⟨O, hOo, hOW⟩ :=
      (isOpen_induced_iff (f := (Subtype.val : ↥(closure V) → C))).mp hW'cl.2
    have hsub : O ∩ closure V ⊆ V := by
      rintro c ⟨hcO, hccl⟩
      have hmem : c ∈ Subtype.val '' (Subtype.val ⁻¹' O) := ⟨⟨c, hccl⟩, hcO, rfl⟩
      rw [hOW] at hmem
      obtain ⟨s, hs, hsc⟩ := hmem
      rw [← hsc]
      exact hW'V hs
    have hWeq : W = O ∩ V := by
      have hWcl : W = O ∩ closure V := by
        rw [hWdef, ← hOW]
        exact Set.image_preimage_eq_inter_range.trans (by rw [Subtype.range_coe])
      rw [hWcl]
      exact Set.Subset.antisymm (fun c hc => ⟨hc.1, hsub hc⟩)
        (fun c hc => ⟨hc.1, subset_closure hc.2⟩)
    rw [hWeq]
    exact hOo.inter hVo
  have hxW : x ∈ W := ⟨⟨x, hxcl⟩, hxW', rfl⟩
  have hWU : W ⊆ U := by
    rintro c ⟨s, hs, rfl⟩
    exact hVU (subset_closure (hW'V hs))
  have hWne : W ≠ Set.univ := by
    intro h
    exact hy (hWU (h ▸ trivial))
  have hWclopen : IsClopen W := ⟨hWclosed, hWopen⟩
  rcases (isClopen_iff.mp hWclopen) with h | h
  · rw [h] at hxW; exact hxW
  · exact hWne h

/-! ## The slices -/

/-- The parameter set of the slice of the `i`-th arc by the hyperplane through `x` orthogonal
to `u`. -/
noncomputable def sliceParam (g : ι → ℝ → EuclideanSpace ℝ (Fin n))
    (x u : EuclideanSpace ℝ (Fin n)) (i : ι) : Set ℝ :=
  {τ : ℝ | τ ∈ Set.Icc (0:ℝ) 1 ∧ inner ℝ (g i τ - x) u = 0}

/-- The slice of the `i`-th arc by the hyperplane through `x` orthogonal to `u`. -/
noncomputable def sliceSet (g : ι → ℝ → EuclideanSpace ℝ (Fin n))
    (x u : EuclideanSpace ℝ (Fin n)) (i : ι) : Set (EuclideanSpace ℝ (Fin n)) :=
  g i '' sliceParam g x u i

lemma isClosed_sliceParam {g : ι → ℝ → EuclideanSpace ℝ (Fin n)}
    {x u : EuclideanSpace ℝ (Fin n)} {i : ι} (hg : Continuous (g i)) :
    IsClosed (sliceParam g x u i) := by
  rw [sliceParam]
  exact isClosed_Icc.inter
    (isClosed_eq ((hg.sub continuous_const).inner continuous_const) continuous_const)

lemma isCompact_sliceParam {g : ι → ℝ → EuclideanSpace ℝ (Fin n)}
    {x u : EuclideanSpace ℝ (Fin n)} {i : ι} (hg : Continuous (g i)) :
    IsCompact (sliceParam g x u i) :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_sliceParam hg) (fun τ hτ => hτ.1)

lemma isCompact_sliceSet {g : ι → ℝ → EuclideanSpace ℝ (Fin n)}
    {x u : EuclideanSpace ℝ (Fin n)} {i : ι} (hg : Continuous (g i)) :
    IsCompact (sliceSet g x u i) := by
  rw [sliceSet]
  exact (isCompact_sliceParam hg).image hg

lemma sliceSet_subset {g : ι → ℝ → EuclideanSpace ℝ (Fin n)}
    (x u : EuclideanSpace ℝ (Fin n)) (i : ι) :
    sliceSet g x u i ⊆ g i '' Set.Icc (0:ℝ) 1 := by
  rintro z ⟨τ, hτ, rfl⟩
  exact ⟨τ, hτ.1, rfl⟩

lemma iUnion_sliceSet_eq {g : ι → ℝ → EuclideanSpace ℝ (Fin n)}
    (x u : EuclideanSpace ℝ (Fin n)) :
    (⋃ i, sliceSet g x u i)
      = (⋃ i, g i '' Set.Icc (0:ℝ) 1) ∩ {z : EuclideanSpace ℝ (Fin n) | inner ℝ (z - x) u = 0} := by
  ext z
  constructor
  · intro hz
    rw [Set.mem_iUnion] at hz
    obtain ⟨i, hi⟩ := hz
    rw [sliceSet, Set.mem_image] at hi
    obtain ⟨τ, hτ, hgτ⟩ := hi
    refine ⟨?_, by rw [← hgτ]; exact hτ.2⟩
    rw [Set.mem_iUnion]
    exact ⟨i, by rw [Set.mem_image]; exact ⟨τ, hτ.1, hgτ⟩⟩
  · intro hz
    rw [Set.mem_inter_iff, Set.mem_iUnion] at hz
    obtain ⟨⟨i, hi⟩, hz2⟩ := hz
    rw [Set.mem_image] at hi
    obtain ⟨τ, hτ, hgτ⟩ := hi
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    rw [sliceSet, Set.mem_image]
    exact ⟨τ, ⟨hτ, by rw [hgτ]; exact hz2⟩, hgτ⟩

/-- A closed subset of `[0,1]` with empty interior is totally disconnected. -/
lemma isTotallyDisconnected_sliceParam {g : ι → ℝ → EuclideanSpace ℝ (Fin n)}
    {x u : EuclideanSpace ℝ (Fin n)} {i : ι}
    (hu : ∀ (a b : ℚ), 0 ≤ a → a < b → b ≤ 1 →
      ∃ t ∈ Set.Icc (a:ℝ) (b:ℝ), inner ℝ (g i t - x) u ≠ 0) :
    IsTotallyDisconnected (sliceParam g x u i) := by
  rw [isTotallyDisconnected_iff_lt]
  intro p hp q hq hpq
  by_contra hcon
  push_neg at hcon
  have hsub : Set.Ioo p q ⊆ sliceParam g x u i := by
    intro z hz
    by_contra hzn
    exact hcon z hzn hz
  obtain ⟨a, hpa, haq⟩ := exists_rat_btwn hpq
  obtain ⟨b, hab, hbq⟩ := exists_rat_btwn haq
  have ha0 : (0:ℚ) ≤ a := by
    have h : (0:ℝ) ≤ (a:ℝ) := le_of_lt (lt_of_le_of_lt hp.1.1 hpa)
    exact_mod_cast h
  have hb1 : b ≤ 1 := by
    have h : (b:ℝ) ≤ 1 := le_of_lt (lt_of_lt_of_le hbq hq.1.2)
    exact_mod_cast h
  have habq : a < b := by exact_mod_cast hab
  obtain ⟨t, ht, hne⟩ := hu a b ha0 habq hb1
  exact hne (hsub ⟨lt_of_lt_of_le hpa ht.1, lt_of_le_of_lt ht.2 hbq⟩).2

/-- The slice of a single arc by a hyperplane is totally disconnected, provided the arc does not
lie in the hyperplane on any nondegenerate rational subinterval of `[0,1]`. -/
lemma isTotallyDisconnected_sliceSet {g : ι → ℝ → EuclideanSpace ℝ (Fin n)}
    {x u : EuclideanSpace ℝ (Fin n)} {i : ι}
    (hg : Continuous (g i)) (hginj : Set.InjOn (g i) (Set.Icc (0:ℝ) 1))
    (hu : ∀ (a b : ℚ), 0 ≤ a → a < b → b ≤ 1 →
      ∃ t ∈ Set.Icc (a:ℝ) (b:ℝ), inner ℝ (g i t - x) u ≠ 0) :
    IsTotallyDisconnected (sliceSet g x u i) := by
  haveI : CompactSpace ↥(sliceParam g x u i) :=
    isCompact_iff_compactSpace.mp (isCompact_sliceParam hg)
  have hcont : Continuous fun τ : ↥(sliceParam g x u i) => g i (τ : ℝ) :=
    hg.comp continuous_subtype_val
  have hinj : Function.Injective fun τ : ↥(sliceParam g x u i) => g i (τ : ℝ) :=
    fun a b hab => Subtype.ext (hginj a.2.1 b.2.1 hab)
  have hclosedmap : IsClosedMap fun τ : ↥(sliceParam g x u i) => g i (τ : ℝ) := by
    intro s hs
    exact (hs.isCompact.image hcont).isClosed
  have hemb : Topology.IsEmbedding fun τ : ↥(sliceParam g x u i) => g i (τ : ℝ) :=
    (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap hcont hinj hclosedmap).isEmbedding
  have hrange : (fun τ : ↥(sliceParam g x u i) => g i (τ : ℝ)) '' Set.univ
      = sliceSet g x u i := by
    rw [sliceSet, sliceParam]
    ext z
    constructor
    · rintro ⟨τ, -, rfl⟩
      exact ⟨τ, τ.2, rfl⟩
    · rintro ⟨τ, hτ, rfl⟩
      exact ⟨⟨τ, hτ⟩, trivial, rfl⟩
  rw [← hrange]
  haveI : TotallyDisconnectedSpace ↥(sliceParam g x u i) :=
    totallyDisconnectedSpace_subtype_iff.mpr (isTotallyDisconnected_sliceParam hu)
  exact (hemb.isTotallyDisconnected_image (s := Set.univ)).mpr
    TotallyDisconnectedSpace.isTotallyDisconnected_univ

/-! ## The main theorem -/

theorem exists_hyperplane_slice_isTotallyDisconnected {n : ℕ} (hn : 3 ≤ n)
    {ι : Type*} [Countable ι] {g : ι → ℝ → EuclideanSpace ℝ (Fin n)}
    (hg : ∀ i, Continuous (g i)) (hginj : ∀ i, Set.InjOn (g i) (Set.Icc (0:ℝ) 1))
    {x : EuclideanSpace ℝ (Fin n)} (hx : ∀ i, x ∉ g i '' Set.Icc (0:ℝ) 1)
    (hc : IsCompact (⋃ i, g i '' Set.Icc (0:ℝ) 1)) :
    ∃ u : EuclideanSpace ℝ (Fin n), u ≠ 0 ∧
      IsTotallyDisconnected ((⋃ i, g i '' Set.Icc (0:ℝ) 1) ∩
        {z : EuclideanSpace ℝ (Fin n) | inner ℝ (z - x) u = 0}) := by
  obtain ⟨u, hu0, hu⟩ := exists_good_direction (n := n) (by omega : 1 ≤ n) g x hx
  refine ⟨u, hu0, ?_⟩
  rw [← iUnion_sliceSet_eq (g := g) x u]
  have hslicetd : ∀ i, IsTotallyDisconnected (sliceSet g x u i) :=
    fun i => isTotallyDisconnected_sliceSet (hg i) (hginj i)
      (fun a b ha0 hab hb1 => hu i a b ha0 hab hb1)
  have hZclosed : IsClosed (⋃ i, sliceSet g x u i) := by
    rw [iUnion_sliceSet_eq]
    exact hc.isClosed.inter
      (isClosed_eq ((continuous_id.sub continuous_const).inner continuous_const) continuous_const)
  intro t ht htp
  intro p hp q hq
  by_contra hpq
  have hCZ : closure t ⊆ ⋃ i, sliceSet g x u i := hZclosed.closure_subset_iff.mpr ht
  have hCcompact : IsCompact (closure t) := by
    refine IsCompact.of_isClosed_subset hc isClosed_closure ?_
    intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hCZ hz)
    exact Set.mem_iUnion.mpr ⟨i, sliceSet_subset x u i hi⟩
  haveI : CompactSpace ↥(closure t) := isCompact_iff_compactSpace.mp hCcompact
  haveI : PreconnectedSpace ↥(closure t) :=
    isPreconnected_iff_preconnectedSpace.mp htp.closure
  haveI : Nontrivial ↥(closure t) :=
    ⟨⟨p, subset_closure hp⟩, ⟨q, subset_closure hq⟩, fun h => hpq (Subtype.ext_iff.mp h)⟩
  have hFclosed : ∀ i, IsClosed {c : ↥(closure t) |
      (c : EuclideanSpace ℝ (Fin n)) ∈ sliceSet g x u i} :=
    fun i => (isCompact_sliceSet (hg i)).isClosed.preimage continuous_subtype_val
  have hFcover : (⋃ i, {c : ↥(closure t) |
      (c : EuclideanSpace ℝ (Fin n)) ∈ sliceSet g x u i}) = Set.univ := by
    rw [eq_univ_iff_forall]
    intro c
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hCZ c.2)
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨i₀, hne⟩ := nonempty_interior_of_iUnion_of_closed hFclosed hFcover
  have hUtd : IsTotallyDisconnected (interior {c : ↥(closure t) |
      (c : EuclideanSpace ℝ (Fin n)) ∈ sliceSet g x u i₀}) := by
    refine IsEmbedding.subtypeVal.isTotallyDisconnected (s := interior {c : ↥(closure t) |
      (c : EuclideanSpace ℝ (Fin n)) ∈ sliceSet g x u i₀}) ?_
    intro τ hτ hpre
    refine hslicetd i₀ τ ?_ hpre
    intro z hz
    obtain ⟨c, hc, rfl⟩ := hτ hz
    exact interior_subset (s := {c : ↥(closure t) |
      (c : EuclideanSpace ℝ (Fin n)) ∈ sliceSet g x u i₀}) hc
  have hempty := no_open_totallyDisconnected_subset isOpen_interior hUtd
  rw [hempty] at hne
  exact Set.not_nonempty_empty hne

end Work.Whitney.PathTools
