import Mathlib
import Submission.Work.BoxShrink.PinchOff.NonCutPoint.Basic

/-!
# The non-cut point theorem for compact connected `T1` spaces

Every nonempty compact connected `T1` space has a point whose removal leaves a preconnected
space; equivalently, there is no compact connected `T1` "cut-point space".

The proof follows Whyburn (Wilder, *Topology of Manifolds*, Thm. 12.15; Honari–Bahrampour,
*Cut-point spaces*, Proc. AMS 127 (1999), Thm. 3.9).  Assume every point is a cut point.  A set `U`
is *good* if it is open, its closure is `U` plus a single point, and it is not everything; such a
`U` is one side of a separation of `{x}ᶜ`, so `closure U = U ∪ {x}` is a continuum.  Every good set
has a strict upper bound for the order `U ≤ V ↔ U = V ∨ closure U ⊆ V` (take a point outside
`closure U` and use the separation it gives).  A Zorn-maximal chain `K` has no maximal element, so
each `U ∈ K` has `V ∈ K` with `closure U ⊆ V`; hence `⋃K = ⋃_{U∈K} closure U` is a union of a
directed family of continua, so it is preconnected.  If some `z` were outside it, the separation at
`z` would give a good `C` with `closure U ⊆ C` for all `U ∈ K`, making `K ∪ {C}` a bigger chain.
Thus `⋃K = univ`, and `K` is an open cover without finite subcover — contradicting compactness.
-/

open Set

namespace Work.BoxShrink.PinchOff

variable {X : Type*} [TopologicalSpace X]

/-- A "good" set: open, its closure is itself plus one point, and it is not everything. -/
def Good (U : Set X) : Prop :=
  IsOpen U ∧ (∃ x : X, closure U = U ∪ {x} ∧ x ∉ U) ∧ closure U ≠ univ

/-- The order on good sets: `U ≤ V` iff `U = V` or `closure U ⊆ V`. -/
def GLe (U V : Set X) : Prop := U = V ∨ closure U ⊆ V

/-- A `GLe`-chain: a family of sets any two of which are `GLe`-comparable. -/
def IsGChain (K : Set (Set X)) : Prop := ∀ U ∈ K, ∀ V ∈ K, GLe U V ∨ GLe V U

lemma gLe_trans {U V W : Set X} (h1 : GLe U V) (h2 : GLe V W) : GLe U W := by
  rcases h1 with rfl | h1
  · exact h2
  · rcases h2 with rfl | h2
    · exact Or.inr h1
    · exact Or.inr (h1.trans (subset_closure.trans h2))

lemma gLe_antisymm {U V : Set X} (h1 : GLe U V) (h2 : GLe V U) : U = V := by
  rcases h1 with h | h
  · exact h
  · rcases h2 with h2 | h2
    · exact h2.symm
    · exact le_antisymm (subset_closure.trans h) (subset_closure.trans h2)

lemma gLe_closure_subset {U V : Set X} (h : GLe U V) (hne : U ≠ V) : closure U ⊆ V :=
  h.resolve_left hne

lemma gLe_closure_mono {U V : Set X} (h : GLe U V) : closure U ⊆ closure V := by
  rcases h with rfl | h
  · exact Subset.rfl
  · exact h.trans subset_closure

lemma subset_of_gLe {U V : Set X} (h : GLe U V) : U ⊆ V := by
  rcases h with rfl | h
  · exact Subset.rfl
  · exact subset_closure.trans h

/-- A good set is nonempty. -/
lemma Good.nonempty {U : Set X} (hU : Good U) : U.Nonempty := by
  obtain ⟨-, ⟨x, hcl, hxU⟩, -⟩ := hU
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  rw [h, closure_empty, Set.empty_union] at hcl
  exact (singleton_nonempty x).ne_empty hcl.symm

/-- A separation of `{x}ᶜ` in terms of two open sets. -/
lemma exists_sep_of_not_preconnected [T1Space X] {x : X}
    (h : ¬ IsPreconnected ({x}ᶜ : Set X)) :
    ∃ C D : Set X, IsOpen C ∧ IsOpen D ∧ C.Nonempty ∧ D.Nonempty ∧ Disjoint C D ∧
      C ∪ D = {x}ᶜ := by
  rw [IsPreconnected] at h
  push_neg at h
  obtain ⟨u, v, hu, hv, huv, hnu, hnv, hne⟩ := h
  have hco : IsOpen ({x}ᶜ : Set X) := isClosed_singleton.isOpen_compl
  refine ⟨({x}ᶜ : Set X) ∩ u, ({x}ᶜ : Set X) ∩ v, hco.inter hu, hco.inter hv, hnu, hnv, ?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro y ⟨hy1, hy2⟩ ⟨hy3, hy4⟩
    have hmem : y ∈ ({x}ᶜ : Set X) ∩ (u ∩ v) := ⟨hy1, hy2, hy4⟩
    rw [hne] at hmem
    exact hmem
  · ext y
    constructor
    · rintro (⟨hy, hyu⟩ | ⟨hy, hyv⟩)
      · exact hy
      · exact hy
    · intro hy
      rcases huv hy with h | h
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨hy, h⟩

/-- One side of a separation of `{x}ᶜ` is a good set. -/
lemma good_of_sep (hX : IsPreconnected (univ : Set X)) {x : X} {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hdisj : Disjoint A B) (hunion : A ∪ B = {x}ᶜ) : Good A := by
  have hcl := closure_eq_union_singleton_of_sep hX hA hB hAne hBne hdisj hunion
  refine ⟨hA, ⟨x, hcl, ?_⟩, ?_⟩
  · intro hxA
    have hmem : x ∈ A ∪ B := Or.inl hxA
    rw [hunion] at hmem
    exact hmem (mem_singleton x)
  · rw [hcl]
    intro h
    obtain ⟨w, hw⟩ := hBne
    have hw' : w ∈ A ∪ {x} := by rw [h]; exact mem_univ w
    rcases hw' with h1 | h1
    · exact (Set.disjoint_left.mp hdisj h1) hw
    · rw [mem_singleton_iff] at h1
      have hwx : w ∈ ({x}ᶜ : Set X) := by rw [← hunion]; exact Or.inr hw
      rw [h1] at hwx
      exact hwx rfl

/-- The closure of a good set is preconnected. -/
lemma good_closure_preconnected [T1Space X] (hX : IsPreconnected (univ : Set X)) {U : Set X}
    (hU : Good U) : IsPreconnected (closure U) := by
  have hUo : IsOpen U := hU.1
  obtain ⟨x, hcl, hxU⟩ := hU.2.1
  have hUniv : closure U ≠ univ := hU.2.2
  have hUne : U.Nonempty := hU.nonempty
  have hBopen : IsOpen ((closure U)ᶜ) := isClosed_closure.isOpen_compl
  have hBne : ((closure U)ᶜ).Nonempty := nonempty_compl.mpr hUniv
  have hdisj : Disjoint U (closure U)ᶜ := disjoint_compl_right.mono_left subset_closure
  have hunion : U ∪ (closure U)ᶜ = {x}ᶜ := by
    have hcd : closure U \ U = {x} := by
      rw [hcl]
      ext y
      simp only [mem_diff, mem_union, mem_singleton_iff]
      constructor
      · rintro ⟨hy, hyU⟩
        rcases hy with h | h
        · exact absurd h hyU
        · exact h
      · rintro rfl
        exact ⟨Or.inr rfl, hxU⟩
    rw [← Set.compl_sdiff, hcd]
  rw [hcl]
  exact isPreconnected_union_singleton_of_sep hX hUo hBopen hUne hBne hdisj hunion

/-- Every good set has a strict upper bound for `GLe`. -/
lemma exists_good_upper [T1Space X] (hX : IsPreconnected (univ : Set X))
    (hcut : ∀ x : X, ¬ IsPreconnected ({x}ᶜ : Set X)) {U : Set X} (hU : Good U) :
    ∃ V : Set X, Good V ∧ GLe U V ∧ U ≠ V := by
  have hpre : IsPreconnected (closure U) := good_closure_preconnected hX hU
  have hUuniv : closure U ≠ univ := hU.2.2
  obtain ⟨z, hz⟩ := (nonempty_compl.mpr hUuniv : ((closure U)ᶜ : Set X).Nonempty)
  obtain ⟨C, D, hCo, hDo, hCne, hDne, hCdisj, hCunion⟩ := exists_sep_of_not_preconnected (hcut z)
  have hsub : closure U ⊆ C ∪ D := by
    intro y hy
    rw [hCunion, mem_compl_iff, mem_singleton_iff]
    intro hyz
    exact hz (hyz ▸ hy)
  rcases hpre.subset_or_subset hCo hDo hCdisj hsub with hCU | hDU
  · have hCgood : Good C := good_of_sep hX hCo hDo hCne hDne hCdisj hCunion
    refine ⟨C, hCgood, Or.inr hCU, fun hUC => hz ?_⟩
    rw [hUC, closure_eq_union_singleton_of_sep hX hCo hDo hCne hDne hCdisj hCunion]
    exact Or.inr (mem_singleton z)
  · have hDunion : D ∪ C = {z}ᶜ := by rw [union_comm]; exact hCunion
    have hclD := closure_eq_union_singleton_of_sep hX hDo hCo hDne hCne hCdisj.symm hDunion
    have hDgood : Good D := good_of_sep hX hDo hCo hDne hCne hCdisj.symm hDunion
    refine ⟨D, hDgood, Or.inr hDU, fun hUD => hz ?_⟩
    rw [hUD, hclD]
    exact Or.inr (mem_singleton z)

/-- A finite subset of a `GLe`-chain has a greatest element. -/
lemma exists_max_of_finset (K : Set (Set X)) (hchain : IsGChain K) :
    ∀ t : Finset (Set X), (∀ i ∈ t, i ∈ K) → t.Nonempty → ∃ m ∈ t, ∀ i ∈ t, GLe i m := by
  intro t
  induction t using Finset.induction_on with
  | empty => intro _ hne; exact absurd hne (by simp)
  | insert a s ha ih =>
    intro ht hne
    rcases s.eq_empty_or_nonempty with hs | hs
    · rw [hs] at ht hne ⊢
      refine ⟨a, by simp, ?_⟩
      intro i hi
      have hi' : i = a := by simpa using hi
      rw [hi']
      exact Or.inl rfl
    · obtain ⟨m, hm, hmle⟩ := ih (fun i hi => ht i (Finset.mem_insert_of_mem hi)) hs
      rcases hchain a (ht a (Finset.mem_insert_self a s)) m
        (ht m (Finset.mem_insert_of_mem hm)) with h | h
      · refine ⟨m, Finset.mem_insert_of_mem hm, fun i hi => ?_⟩
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · exact h
        · exact hmle i hi'
      · refine ⟨a, Finset.mem_insert_self a s, fun i hi => ?_⟩
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · exact Or.inl rfl
        · exact gLe_trans (hmle i hi') h

/-- **The non-cut point theorem.** A nonempty compact connected `T1` space has a point whose
removal leaves a preconnected space. -/
theorem exists_isPreconnected_compl_singleton_of_compact [T1Space X] [CompactSpace X] [Nonempty X]
    (hX : IsPreconnected (univ : Set X)) : ∃ x : X, IsPreconnected ({x}ᶜ : Set X) := by
  classical
  by_contra hcon
  push_neg at hcon
  set GoodChain : Set (Set (Set X)) :=
    {K : Set (Set X) | (∀ U ∈ K, Good U) ∧ IsGChain K} with hGC
  have hZorn : ∀ c ⊆ GoodChain, IsChain (· ⊆ ·) c →
      ∃ ub ∈ GoodChain, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hchain
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => subset_sUnion_of_mem hs⟩
    · intro U hU
      rcases mem_sUnion.mp hU with ⟨K, hKc, hUK⟩
      exact (hc hKc).1 U hUK
    · intro U hU V hV
      rcases mem_sUnion.mp hU with ⟨K₁, hK₁c, hUK₁⟩
      rcases mem_sUnion.mp hV with ⟨K₂, hK₂c, hVK₂⟩
      rcases eq_or_ne K₁ K₂ with heq | hne
      · subst heq
        exact (hc hK₁c).2 U hUK₁ V hVK₂
      · rcases hchain hK₁c hK₂c hne with h | h
        · exact (hc hK₂c).2 U (h hUK₁) V hVK₂
        · exact (hc hK₁c).2 U hUK₁ V (h hVK₂)
  obtain ⟨K, hKmax⟩ := zorn_subset GoodChain hZorn
  have hKgood : ∀ U ∈ K, Good U := hKmax.1.1
  have hKchain : IsGChain K := hKmax.1.2
  -- `K` has no upper bound in itself, hence no maximal element
  have hnomax : ¬ ∃ M ∈ K, ∀ V ∈ K, GLe V M := by
    rintro ⟨M, hM, hub⟩
    obtain ⟨M', hM'good, hMM', hMM'ne⟩ := exists_good_upper hX hcon (hKgood M hM)
    have hchain' : IsGChain (K ∪ {M'}) := by
      intro a ha b hb
      rcases ha with ha | rfl
      · rcases hb with hb | rfl
        · exact hKchain a ha b hb
        · exact Or.inl (gLe_trans (hub a ha) hMM')
      · rcases hb with hb | rfl
        · exact Or.inr (gLe_trans (hub b hb) hMM')
        · exact Or.inl (Or.inl rfl)
    have hmem : K ∪ {M'} ∈ GoodChain :=
      ⟨fun U hU => by rcases hU with hU | rfl; exacts [hKgood U hU, hM'good], hchain'⟩
    have hsub : K ∪ {M'} ⊆ K := hKmax.2 hmem subset_union_left
    have hM'K : M' ∈ K := hsub (mem_union_right K (mem_singleton M'))
    exact hMM'ne (gLe_antisymm hMM' (hub M' hM'K))
  have hupper : ∀ U ∈ K, ∃ V ∈ K, GLe U V ∧ U ≠ V := by
    intro U hU
    by_contra hc
    push_neg at hc
    refine hnomax ⟨U, hU, fun V hV => ?_⟩
    rcases hKchain U hU V hV with h | h
    · rw [hc V hV h]
      exact Or.inl rfl
    · exact h
  -- the union `𝒱` of the chain
  set 𝒱 : Set X := ⋃₀ K with h𝒱def
  have hVsub : ∀ U ∈ K, closure U ⊆ 𝒱 := by
    intro U hU
    obtain ⟨V, hVK, hUV, hne⟩ := hupper U hU
    rw [h𝒱def]
    exact (gLe_closure_subset hUV hne).trans (subset_sUnion_of_mem hVK)
  have hVeq : 𝒱 = ⋃₀ (closure '' K) := by
    refine le_antisymm ?_ ?_
    · intro y hy
      rcases mem_sUnion.mp hy with ⟨U, hU, hyU⟩
      exact mem_sUnion.mpr ⟨closure U, ⟨U, hU, rfl⟩, subset_closure hyU⟩
    · intro y hy
      rcases mem_sUnion.mp hy with ⟨H, ⟨U, hU, rfl⟩, hyH⟩
      exact hVsub U hU hyH
  have hVpre : IsPreconnected 𝒱 := by
    rw [hVeq]
    refine IsPreconnected.sUnion_directed ?_ ?_
    · rintro A ⟨U, hU, rfl⟩ B ⟨V, hV, rfl⟩
      rcases hKchain U hU V hV with h | h
      · exact ⟨closure V, ⟨V, hV, rfl⟩, gLe_closure_mono h, Subset.rfl⟩
      · exact ⟨closure U, ⟨U, hU, rfl⟩, Subset.rfl, gLe_closure_mono h⟩
    · rintro A ⟨U, hU, rfl⟩
      exact good_closure_preconnected hX (hKgood U hU)
  -- `𝒱` is everything
  have key : ∀ S : Set X, Good S → 𝒱 ⊆ S → False := by
    intro S hSgood hVS
    have hchain' : IsGChain (K ∪ {S}) := by
      intro a ha b hb
      rcases ha with ha | rfl
      · rcases hb with hb | rfl
        · exact hKchain a ha b hb
        · exact Or.inl (Or.inr ((hVsub a ha).trans hVS))
      · rcases hb with hb | rfl
        · exact Or.inr (Or.inr ((hVsub b hb).trans hVS))
        · exact Or.inl (Or.inl rfl)
    have hmem : K ∪ {S} ∈ GoodChain :=
      ⟨fun U hU => by rcases hU with hU | rfl; exacts [hKgood U hU, hSgood], hchain'⟩
    have hsub : K ∪ {S} ⊆ K := hKmax.2 hmem subset_union_left
    have hSK : S ∈ K := hsub (mem_union_right K (mem_singleton S))
    exact hnomax ⟨S, hSK, fun V hV => Or.inr ((hVsub V hV).trans hVS)⟩
  have hVuniv : 𝒱 = univ := by
    by_contra hne
    obtain ⟨z, hz⟩ := (nonempty_compl.mpr hne : (𝒱ᶜ : Set X).Nonempty)
    obtain ⟨C, D, hCo, hDo, hCne, hDne, hCdisj, hCunion⟩ :=
      exists_sep_of_not_preconnected (hcon z)
    have hsub : 𝒱 ⊆ C ∪ D := by
      intro y hy
      rw [hCunion, mem_compl_iff, mem_singleton_iff]
      intro hyz
      exact hz (hyz ▸ hy)
    have hCgood : Good C := good_of_sep hX hCo hDo hCne hDne hCdisj hCunion
    have hDunion : D ∪ C = {z}ᶜ := by rw [union_comm]; exact hCunion
    have hDgood : Good D := good_of_sep hX hDo hCo hDne hCne hCdisj.symm hDunion
    rcases hVpre.subset_or_subset hCo hDo hCdisj hsub with hVC | hVD
    · exact key C hCgood hVC
    · exact key D hDgood hVD
  -- compactness
  have hcover : univ ⊆ ⋃ i ∈ K, (i : Set X) := by
    intro x _
    have hxV : x ∈ 𝒱 := by rw [hVuniv]; exact mem_univ x
    rcases mem_sUnion.mp (h𝒱def ▸ hxV) with ⟨U, hUK, hxU⟩
    exact mem_biUnion hUK hxU
  obtain ⟨b', hb'sub, hb'fin, hb'cov⟩ := isCompact_univ.elim_finite_subcover_image
    (b := K) (c := fun U : Set X => U) (fun i hi => (hKgood i hi).1) hcover
  set t : Finset (Set X) := hb'fin.toFinset with htdef
  have htK : ∀ i ∈ t, i ∈ K := by
    intro i hi
    refine hb'sub ?_
    rwa [htdef, Set.Finite.mem_toFinset] at hi
  have htcov : univ ⊆ ⋃ i ∈ (t : Set (Set X)), i := by
    rw [htdef, Set.Finite.coe_toFinset]
    exact hb'cov
  rcases t.eq_empty_or_nonempty with ht | htne
  · rw [ht] at htcov
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    exact absurd (htcov (mem_univ x)) (by simp)
  · obtain ⟨m, hmt, hmle⟩ := exists_max_of_finset K hKchain t htK htne
    have hm_univ : m = univ := by
      refine eq_univ_of_univ_subset ?_
      intro x _
      have hx : x ∈ ⋃ i ∈ (t : Set (Set X)), i := htcov (mem_univ x)
      rcases (Set.mem_iUnion₂.mp hx) with ⟨i, hit, hxi⟩
      exact subset_of_gLe (hmle i hit) hxi
    have hmK : m ∈ K := htK m hmt
    have hmne := (hKgood m hmK).2.2
    rw [hm_univ] at hmne
    exact hmne closure_univ

end Work.BoxShrink.PinchOff
