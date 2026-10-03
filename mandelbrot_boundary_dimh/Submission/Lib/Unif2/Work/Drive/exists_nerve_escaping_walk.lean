import Mathlib

set_option linter.style.haveILetI false
set_option warn.classDefReducibility false
set_option linter.unusedVariables false

/-!
# The nerve graph of a locally finite open cover

Mathlib has König's infinity lemma in the form `exists_seq_forall_proj_of_forall_finite`, but not
the graph-theoretic corollary that an infinite locally finite connected graph has an injective walk
starting at every vertex; we prove that here.  We then show that the nerve graph of a locally finite
open cover of a connected space is connected and locally finite, and deduce that it has a walk which
eventually leaves every finite set.

Everything here is self-contained and only imports `Mathlib`.
-/

namespace Work.Drive

open Set

/-! ## Two graph-theoretic lemmas -/

/-- In a locally finite graph, the closed ball of radius `n` around `c` (in the graph metric
`G.edist`, which is `⊤` for unreachable vertices) is finite. -/
theorem edist_ball_finite {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] (c : V) (n : ℕ) :
    {w : V | G.edist c w ≤ (n : ℕ∞)}.Finite := by
  induction n with
  | zero =>
      have h : {w : V | G.edist c w ≤ ((0 : ℕ) : ℕ∞)} = {c} := by
        ext w
        constructor
        · intro hw
          have h0 : G.edist c w = 0 := le_antisymm hw zero_le
          exact (SimpleGraph.edist_eq_zero_iff.mp h0).symm
        · rintro rfl
          simp
      rw [h]
      exact Set.finite_singleton c
  | succ n ih =>
      have hnb : (⋃ u ∈ {w : V | G.edist c w ≤ (n : ℕ∞)}, G.neighborSet u).Finite :=
        ih.biUnion fun u _ => Set.finite_coe_iff.mp (inferInstance : Finite (G.neighborSet u))
      refine (ih.union hnb).subset ?_
      intro w hw
      have hw' : G.edist c w ≤ ((n + 1 : ℕ) : ℕ∞) := hw
      by_cases hle : G.edist c w ≤ (n : ℕ∞)
      · exact Or.inl hle
      · refine Or.inr ?_
        have hlt : (n : ℕ∞) < G.edist c w := not_le.mp hle
        have hne : G.edist c w ≠ ⊤ := by
          intro htop
          rw [htop] at hw'
          exact absurd hw' (not_le.mpr (ENat.natCast_lt_top (n + 1)))
        have hval : G.edist c w = ((n + 1 : ℕ) : ℕ∞) := by
          refine le_antisymm hw' ?_
          have h1 : n < (G.edist c w).toNat := by
            have h2 : (n : ℕ∞) < (((G.edist c w).toNat : ℕ) : ℕ∞) := by
              rwa [← ENat.natCast_toNat hne] at hlt
            exact ENat.natCast_lt_natCast.mp h2
          rw [← ENat.natCast_toNat hne]
          exact ENat.natCast_le_natCast.mpr (Nat.succ_le_of_lt h1)
        obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_eq_coe (G := G) (u := c) (v := w) hval
        have hmem : G.edist c (p.getVert n) ≤ (n : ℕ∞) := by
          have h := SimpleGraph.edist_le (p.take n)
          rw [SimpleGraph.Walk.take_length, hp, Nat.min_eq_left (Nat.le_succ n)] at h
          exact h
        have hadj0 : G.Adj (p.getVert n) (p.getVert (n + 1)) := p.adj_getVert_succ (by omega)
        have h1 : p.getVert (n + 1) = w := by
          rw [← hp]
          exact p.getVert_length
        rw [h1] at hadj0
        exact Set.mem_biUnion hmem (by rwa [SimpleGraph.mem_neighborSet])

/-! ## Padding simple paths -/

/-- The type of "padded simple paths of length `i` from `c`": functions `ℕ → ℕ` which start at `c`,
step `i` times along `G`, are zero past `i` and are injective on `{0, …, i}`.  The padding makes the
`i = 0` case a subsingleton and makes the "one step extension" fibres finite. -/
def KanSet (G : SimpleGraph ℕ) (c : ℕ) (i : ℕ) : Type :=
  { f : ℕ → ℕ //
    f 0 = c ∧
      (∀ k : ℕ, k + 1 ≤ i → G.Adj (f k) (f (k + 1))) ∧
      (∀ k : ℕ, i < k → f k = 0) ∧
      (∀ a b : ℕ, a ≤ i → b ≤ i → f a = f b → a = b) }

/-- Truncating a padded simple path of length `j` at `i ≤ j` (and re-padding with zeros). -/
def KanProj (G : SimpleGraph ℕ) (c : ℕ) {i j : ℕ} (_hij : i ≤ j) (f : KanSet G c j) :
    KanSet G c i :=
  ⟨fun k => if k ≤ i then f.1 k else 0, by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [f.2.1]
    · intro k hk
      simp only [if_pos (le_trans (Nat.le_succ k) hk), if_pos hk]
      exact f.2.2.1 k (le_trans hk _hij)
    · intro k hk
      simp only [if_neg (not_le.mpr hk)]
    · intro a b ha hb hab
      simp only [if_pos ha, if_pos hb] at hab
      exact f.2.2.2.2 a b (le_trans ha _hij) (le_trans hb _hij) hab⟩

@[simp]
theorem KanProj_apply (G : SimpleGraph ℕ) (c : ℕ) {i j : ℕ} (hij : i ≤ j) (f : KanSet G c j)
    (k : ℕ) : (KanProj G c hij f).1 k = if k ≤ i then f.1 k else 0 := rfl

theorem KanProj_apply_of_le (G : SimpleGraph ℕ) (c : ℕ) {i j : ℕ} (hij : i ≤ j)
    (f : KanSet G c j) (k : ℕ) (hk : k ≤ i) : (KanProj G c hij f).1 k = f.1 k := by
  rw [KanProj_apply, if_pos hk]

theorem KanProj_apply_of_not_le (G : SimpleGraph ℕ) (c : ℕ) {i j : ℕ} (hij : i ≤ j)
    (f : KanSet G c j) (k : ℕ) (hk : ¬ k ≤ i) : (KanProj G c hij f).1 k = 0 := by
  rw [KanProj_apply, if_neg hk]

/-- `KanSet G c i` is nonempty: by local finiteness the ball of radius `i` around `c` is finite, so
some vertex is farther than `i` away; a shortest walk to it contains a simple path of length `i`. -/
theorem kanSet_nonempty (G : SimpleGraph ℕ) [G.LocallyFinite] (hconn : G.Preconnected) (c : ℕ)
    (i : ℕ) : Nonempty (KanSet G c i) := by
  classical
  obtain ⟨m, hm⟩ := (edist_ball_finite G c i).exists_notMem
  have hlt : (i : ℕ∞) < G.edist c m := not_le.mp hm
  have hne : G.edist c m ≠ ⊤ := SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn c m)
  have hval : G.edist c m = (((G.edist c m).toNat : ℕ) : ℕ∞) := (ENat.natCast_toNat hne).symm
  have hik : i < (G.edist c m).toNat := by
    have h2 : (i : ℕ∞) < (((G.edist c m).toNat : ℕ) : ℕ∞) := by rw [← hval]; exact hlt
    exact ENat.natCast_lt_natCast.mp h2
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_eq_coe (G := G) (u := c) (v := m) hval
  let q : G.Walk c m := ↑(p.toPath)
  have hqpath : q.IsPath := (p.toPath).isPath
  have hkq : (G.edist c m).toNat ≤ q.length := by
    have h := SimpleGraph.edist_le q
    rw [hval] at h
    exact ENat.natCast_le_natCast.mp h
  have hlen : i ≤ q.length := le_trans (le_of_lt hik) hkq
  refine ⟨⟨fun t => if t ≤ i then q.getVert t else 0, ?_, ?_, ?_, ?_⟩⟩
  · simp only [if_pos (Nat.zero_le i)]
    exact q.getVert_zero
  · intro k hk
    simp only [if_pos (le_trans (Nat.le_succ k) hk), if_pos hk]
    exact q.adj_getVert_succ (lt_of_lt_of_le (Nat.lt_succ_self k) (le_trans hk hlen))
  · intro k hk
    simp only [if_neg (not_le.mpr hk)]
  · intro a b ha hb hab
    simp only [if_pos ha, if_pos hb] at hab
    exact hqpath.getVert_injOn (le_trans ha hlen) (le_trans hb hlen) hab

/-- In a locally finite preconnected graph on `ℕ` there is, from any vertex, an injective walk. -/
theorem exists_injective_walk_escape (G : SimpleGraph ℕ) [G.LocallyFinite] (hconn : G.Preconnected)
    (c : ℕ) :
    ∃ v : ℕ → ℕ, v 0 = c ∧ Function.Injective v ∧ ∀ k : ℕ, G.Adj (v k) (v (k + 1)) := by
  classical
  haveI : Subsingleton (KanSet G c 0) :=
    ⟨fun a b => Subtype.ext <| funext fun k => by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; rw [a.2.1, b.2.1]
      · rw [a.2.2.2.1 k hk, b.2.2.2.1 k hk]⟩
  haveI : ∀ i, Nonempty (KanSet G c i) := fun i => kanSet_nonempty G hconn c i
  obtain ⟨f, hf⟩ :=
    exists_seq_forall_proj_of_forall_finite (α := KanSet G c)
      (fun {i j} hij => KanProj G c hij)
      (fun {i} a => by
        refine Subtype.ext (funext fun k => ?_)
        by_cases hk : k ≤ i
        · rw [KanProj_apply_of_le G c rfl.le a k hk]
        · rw [KanProj_apply_of_not_le G c rfl.le a k hk]
          exact (a.2.2.2.1 k (not_le.mp hk)).symm)
      (fun {i j k} hij hjk a => by
        refine Subtype.ext (funext fun t => ?_)
        by_cases ht : t ≤ i
        · rw [KanProj_apply_of_le G c hij (KanProj G c hjk a) t ht,
            KanProj_apply_of_le G c hjk a t (le_trans ht hij),
            KanProj_apply_of_le G c (hij.trans hjk) a t ht]
        · rw [KanProj_apply_of_not_le G c hij (KanProj G c hjk a) t ht,
            KanProj_apply_of_not_le G c (hij.trans hjk) a t ht])
      (fun i a => by
        have hnb : (G.neighborSet (a.1 i)).Finite :=
          Set.finite_coe_iff.mp (inferInstance : Finite (G.neighborSet (a.1 i)))
        refine Set.Finite.of_finite_image (f := fun b : KanSet G c (i + 1) => b.1 (i + 1))
          (hnb.subset ?_) ?_
        · rintro x ⟨b, hb, rfl⟩
          have hbi : b.1 i = a.1 i := by
            have h := congrArg (fun x : KanSet G c i => x.1 i) hb
            rw [KanProj_apply_of_le G c (Nat.le_add_right i 1) b i (le_refl i)] at h
            exact h
          rw [SimpleGraph.mem_neighborSet, ← hbi]
          exact b.2.2.1 i (le_refl (i + 1))
        · rintro b hb b' hb' h
          refine Subtype.ext (funext fun t => ?_)
          by_cases ht : t ≤ i
          · have h1 : b.1 t = a.1 t := by
              have h := congrArg (fun x : KanSet G c i => x.1 t) hb
              rw [KanProj_apply_of_le G c (Nat.le_add_right i 1) b t ht] at h
              exact h
            have h2 : b'.1 t = a.1 t := by
              have h := congrArg (fun x : KanSet G c i => x.1 t) hb'
              rw [KanProj_apply_of_le G c (Nat.le_add_right i 1) b' t ht] at h
              exact h
            rw [h1, h2]
          · rcases lt_or_eq_of_le (Nat.succ_le_of_lt (not_le.mp ht)) with hlt | heq
            · rw [b.2.2.2.1 t hlt, b'.2.2.2.1 t hlt]
            · subst heq; exact h)
  refine ⟨fun k => (f (k + 1)).1 k, (f 1).2.1, ?_, ?_⟩
  · show Function.Injective (fun k : ℕ => (f (k + 1)).1 k)
    have key : ∀ a b : ℕ, a < b → (f (a + 1)).1 a ≠ (f (b + 1)).1 b := by
      intro a b hab h
      have hco : (f (a + 1)).1 a = (f (b + 1)).1 a := by
        have h1 := congrArg (fun x : KanSet G c (a + 1) => x.1 a)
          (hf (Nat.succ_le_succ hab.le))
        rw [KanProj_apply_of_le G c _ (f (b + 1)) a (Nat.le_succ a)] at h1
        exact h1.symm
      have heq : (f (b + 1)).1 a = (f (b + 1)).1 b := by rw [← hco]; exact h
      exact hab.ne ((f (b + 1)).2.2.2.2 a b (le_trans hab.le (Nat.le_succ b)) (Nat.le_succ b) heq)
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key a b h hab
    · exact key b a h hab.symm
  · show ∀ k : ℕ, G.Adj ((f (k + 1)).1 k) ((f (k + 2)).1 (k + 1))
    intro k
    have h2 : (f (k + 1)).1 k = (f (k + 2)).1 k := by
      have h1 := congrArg (fun x : KanSet G c (k + 1) => x.1 k) (hf (Nat.le_succ (k + 1)))
      rw [KanProj_apply_of_le G c _ (f (k + 2)) k (Nat.le_succ k)] at h1
      exact h1.symm
    rw [h2]
    exact (f (k + 2)).2.2.1 k (Nat.le_succ (k + 1))

/-! ## The nerve graph of a family of sets -/

/-- The nerve graph of a family `U` of sets: two *distinct* indices are adjacent when the
corresponding sets meet. -/
def nerveGraph {X : Type*} (U : ℕ → Set X) : SimpleGraph ℕ where
  Adj m n := m ≠ n ∧ (U m ∩ U n).Nonempty
  symm := ⟨fun _ _ h => ⟨h.1.symm, ⟨h.2.some, h.2.some_mem.2, h.2.some_mem.1⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- For a set `C` of indices that is closed under the nerve adjacency, the union of the
corresponding members of a cover is clopen: its complement is the union of the members indexed by
the complement of `C`. -/
theorem nerveGraph_isClopen {X : Type*} [TopologicalSpace X] {U : ℕ → Set X}
    (hUo : ∀ n, IsOpen (U n)) (hcov : (⋃ n, U n) = Set.univ) {C : Set ℕ}
    (hC : ∀ k ∈ C, ∀ l : ℕ, (nerveGraph U).Adj k l → l ∈ C) :
    IsClopen (⋃ k ∈ C, U k) := by
  have hcoh : ∀ x : X, ∃ n, x ∈ U n := by
    intro x
    have hx : x ∈ (⋃ n, U n) := by rw [hcov]; trivial
    simpa using hx
  have hopen : IsOpen (⋃ k ∈ C, U k) := isOpen_iUnion fun k => isOpen_iUnion fun _ => hUo k
  have hcompl_open : IsOpen (⋃ k ∉ C, U k) := isOpen_iUnion fun k => isOpen_iUnion fun _ => hUo k
  have heq : (⋃ k ∈ C, U k)ᶜ = ⋃ k ∉ C, U k := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion]
    constructor
    · rintro hx
      obtain ⟨k, hk⟩ := hcoh x
      exact ⟨k, fun hkC => hx ⟨k, hkC, hk⟩, hk⟩
    · rintro ⟨k, hkC, hkx⟩ ⟨l, hlC, hlx⟩
      have hkl : k ≠ l := by rintro rfl; exact hkC hlC
      exact hkC (hC l hlC k ⟨hkl.symm, ⟨x, hlx, hkx⟩⟩)
  refine ⟨?_, hopen⟩
  have hclosed := hcompl_open.isClosed_compl
  rwa [← heq, compl_compl] at hclosed

/-- The nerve graph of a locally finite open cover of a connected space is connected. -/
theorem nerveGraph_preconnected {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {U : ℕ → Set X} (hne : ∀ n, (U n).Nonempty) (hUo : ∀ n, IsOpen (U n))
    (hcov : (⋃ n, U n) = Set.univ) : (nerveGraph U).Preconnected := by
  have key : ∀ n₀ m : ℕ, (nerveGraph U).Reachable n₀ m := by
    intro n₀ m
    have hsymm : ∀ a b : ℕ, (nerveGraph U).Reachable a b → (nerveGraph U).Reachable b a :=
      fun a b => (SimpleGraph.reachable_is_equivalence (nerveGraph U)).symm
    have htrans : ∀ a b c : ℕ, (nerveGraph U).Reachable a b →
        (nerveGraph U).Reachable b c → (nerveGraph U).Reachable a c :=
      fun a b c => (SimpleGraph.reachable_is_equivalence (nerveGraph U)).trans
    have hC : ∀ k ∈ {k : ℕ | (nerveGraph U).Reachable n₀ k}, ∀ l : ℕ,
        (nerveGraph U).Adj k l → l ∈ {k : ℕ | (nerveGraph U).Reachable n₀ k} :=
      fun k hk l hkl => htrans n₀ k l hk hkl.reachable
    have hclopen := nerveGraph_isClopen hUo hcov hC
    have hne' : (⋃ k ∈ {k : ℕ | (nerveGraph U).Reachable n₀ k}, U k).Nonempty :=
      ⟨(hne n₀).some, Set.mem_biUnion (SimpleGraph.Reachable.refl n₀) (hne n₀).some_mem⟩
    have huniv := hclopen.eq_univ hne'
    obtain ⟨x, hx⟩ := hne m
    have hxU : x ∈ (⋃ k ∈ {k : ℕ | (nerveGraph U).Reachable n₀ k}, U k) := by
      rw [huniv]; trivial
    simp only [Set.mem_iUnion] at hxU
    obtain ⟨k, hkC, hkx⟩ := hxU
    by_cases hmk : m = k
    · rw [hmk]; exact hkC
    · have hadj : (nerveGraph U).Adj k m := ⟨fun h => hmk h.symm, ⟨x, hkx, hx⟩⟩
      exact htrans n₀ k m hkC hadj.reachable
  intro u v
  exact (SimpleGraph.reachable_is_equivalence (nerveGraph U)).symm (key v u)

/-- The nerve graph of a locally finite family of sets with compact closures is locally finite. -/
noncomputable def nerveGraph_locallyFinite {X : Type*} [TopologicalSpace X] {U : ℕ → Set X}
    (hlf : LocallyFinite U) (hcl : ∀ n, IsCompact (closure (U n))) :
    (nerveGraph U).LocallyFinite := by
  intro m
  have hfin : ((nerveGraph U).neighborSet m).Finite := by
    refine (hlf.finite_nonempty_inter_compact (hcl m)).subset ?_
    rintro n ⟨hmn, hx⟩
    exact ⟨hx.some, hx.some_mem.2, subset_closure hx.some_mem.1⟩
  exact hfin.fintype

/-! ## The target -/

/-- The nerve graph on `ℕ` (`m ~ n` iff `U m ∩ U n` is nonempty) is connected (the union of the
open components of a locally finite open cover of a connected space is clopen) and locally finite
(`hcl` + `hlf`: each `closure (U m)` is compact and hence meets only finitely many members of the
cover, so each vertex has finite degree).  A connected, locally finite, infinite graph has an
injective walk starting at any vertex (König's argument on the tree of simple paths out of `n₀`,
which has arbitrarily long members because balls of finite radius in a locally finite graph are
finite); such a walk eventually exceeds every `M`. -/
theorem exists_nerve_escaping_walk {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (hX : ¬ CompactSpace X) {U : ℕ → Set X} (hne : ∀ n, (U n).Nonempty) (hUo : ∀ n, IsOpen (U n))
    (hcov : (⋃ n, U n) = Set.univ) (hlf : LocallyFinite U) (hcl : ∀ n, IsCompact (closure (U n)))
    (n₀ : ℕ) :
    ∃ v : ℕ → ℕ, v 0 = n₀ ∧ (∀ k : ℕ, (U (v k) ∩ U (v (k + 1))).Nonempty) ∧
      (∀ M : ℕ, ∃ K : ℕ, ∀ k : ℕ, K ≤ k → M ≤ v k) := by
  classical
  haveI hGLF : (nerveGraph U).LocallyFinite := nerveGraph_locallyFinite hlf hcl
  obtain ⟨v, hv0, hvinj, hadj⟩ :=
    exists_injective_walk_escape (nerveGraph U) (nerveGraph_preconnected hne hUo hcov) n₀
  refine ⟨v, hv0, fun k => (hadj k).2, ?_⟩
  intro M
  have hS : {k : ℕ | v k < M}.Finite := by
    refine (Set.finite_Iio M).preimage (f := v) ?_
    intro a _ b _ hab
    exact hvinj hab
  obtain ⟨K, hK⟩ := hS.bddAbove
  exact ⟨K + 1, fun k hk => by
    by_contra hlt
    exact absurd (hK (show k ∈ {j : ℕ | v j < M} from Nat.lt_of_not_le hlt)) (by omega)⟩

end Work.Drive
