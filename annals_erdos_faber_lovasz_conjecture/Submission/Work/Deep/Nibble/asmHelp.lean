import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.asmDefs
import Submission.Work.Deep.Nibble.asmObj

/-!
# Auxiliary lemmas for the §7 assembly step
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

local notation "Hypergraph" => ErdosFaberLovaszConjecture.Hypergraph

noncomputable section

variable {n D K : ℕ}

theorem ncard_setOf_mem_finset {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    ({a : α | a ∈ s ∧ p a} : Set α).ncard = (s.filter p).card := by
  rw [← Set.ncard_coe_finset (s.filter p)]
  congr 1
  ext a
  simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter]

theorem ncard_biUnion_le_card {ι α : Type*} [Finite α] (s : Finset ι) (f : ι → Set α)
    (h : ∀ i ∈ s, (f i).ncard ≤ 1) :
    (⋃ i ∈ s, f i).ncard ≤ s.card := by
  classical
  rcases s.eq_empty_or_nonempty with hemp | ⟨i₀, hi₀⟩
  · rw [hemp]
    have : (⋃ i ∈ (∅ : Finset ι), f i) = ∅ := by
      ext x; simp
    rw [this]; simp
  · let g : α → ι := fun x => if hx : ∃ i ∈ s, x ∈ f i then hx.choose else i₀
    have hg : ∀ x ∈ (⋃ i ∈ s, f i), g x ∈ s ∧ x ∈ f (g x) := by
      intro x hx
      have hex : ∃ i ∈ s, x ∈ f i := by simpa only [Set.mem_iUnion, exists_prop] using hx
      rw [show g x = hex.choose from dif_pos hex]
      exact hex.choose_spec
    have hinj : Set.InjOn g (⋃ i ∈ s, f i) := by
      intro x hx y hy hxy
      obtain ⟨hx1, hx2⟩ := hg x hx
      obtain ⟨hy1, hy2⟩ := hg y hy
      have h1 : (f (g x)).ncard ≤ 1 := h (g x) hx1
      rw [Set.ncard_le_one] at h1
      exact h1 x hx2 y (by rwa [← hxy] at hy2)
    have hres := Set.ncard_le_ncard_of_injOn g (fun x hx => (hg x hx).1) hinj
    rwa [Set.ncard_coe_finset] at hres

/-! ## Degrees of 2-graphs -/

theorem vpair_injective (v : Fin n) : Function.Injective (fun w => ({v, w} : Set (Fin n))) := by
  intro w w' h
  have h' : ({v, w} : Set (Fin n)) = ({v, w'} : Set (Fin n)) := by simpa using h
  have h1 : w ∈ ({v, w'} : Set (Fin n)) := by
    rw [← h']
    exact Set.mem_insert_iff.mpr (Or.inr rfl)
  have h2 : w' ∈ ({v, w} : Set (Fin n)) := by
    rw [h']
    exact Set.mem_insert_iff.mpr (Or.inr rfl)
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact h1.trans h2.symm
  · exact h2.symm
  · exact h1
  · exact h1

theorem degAt_eq_ncard_edges (R : Hypergraph (Fin n))
    (hR2 : ∀ e ∈ R, edgeSize e = 2) (v : Fin n) :
    degAt R v = ({e ∈ R | v ∈ e} : Set (Set (Fin n))).ncard := by
  classical
  have himg : (fun w : Fin n => ({v, w} : Set (Fin n))) ''
      ({w : Fin n | ({v, w} : Set (Fin n)) ∈ R}) = ({e ∈ R | v ∈ e} : Set (Set (Fin n))) := by
    ext e
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨hw, Set.mem_insert_iff.mpr (Or.inl rfl)⟩
    · rintro ⟨heR, hve⟩
      have hsz : e.ncard = 2 := by rw [← edgeSize_eq_ncard]; exact hR2 e heR
      obtain ⟨w, hw, hwv⟩ := Set.exists_ne_of_one_lt_ncard (show 1 < e.ncard by omega) v
      have hsub : ({v, w} : Set (Fin n)) ⊆ e := by
        intro x hx
        rcases hx with rfl | rfl
        · exact hve
        · exact hw
      have heq : ({v, w} : Set (Fin n)) = e :=
        Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_pair hwv.symm, hsz])
      refine ⟨w, ?_, heq⟩
      show ({v, w} : Set (Fin n)) ∈ R
      rw [heq]; exact heR
  rw [degAt, nbrs, ← himg]
  exact (Set.ncard_image_of_injective _ (vpair_injective v)).symm

theorem pow2_pow2 (𝓜 : MultiHypergraph n) :
    Hypergraph.pow2 (MultiHypergraph.pow2 𝓜) = MultiHypergraph.pow2 𝓜 := by
  ext e
  simp only [Hypergraph.powFam, Set.mem_setOf_eq, MultiHypergraph.mem_pow2]
  tauto

theorem degAt_incidentTwo_pow2 (𝓗 : MultiHypergraph n) {U : Set (Fin n)} {u : Fin n}
    (hu : u ∈ U) :
    degAt (incidentTwo (MultiHypergraph.pow2 𝓗) U) u = degAt (MultiHypergraph.pow2 𝓗) u := by
  rw [degAt, degAt, nbrs_incidentTwo_of_mem (𝓗 := MultiHypergraph.pow2 𝓗) hu, pow2_pow2]

/-! ## Unions -/

theorem disjoint_of_mem_famVert {A B : Set (Set (Fin n))} (hd : Disjoint (famVert A) (famVert B))
    {e e' : Set (Fin n)} (he : e ∈ A) (he' : e' ∈ B) : Disjoint e e' := by
  rw [Set.disjoint_left]
  intro x hx hx'
  exact Set.disjoint_left.mp hd (mem_famVert.mpr ⟨e, he, hx⟩) (mem_famVert.mpr ⟨e', he', hx'⟩)

theorem MultiHypergraph.IsMatching.union {𝓜 : MultiHypergraph n} {A B : Set (Set (Fin n))}
    (hA : 𝓜.IsMatching A) (hB : 𝓜.IsMatching B) (hd : Disjoint (famVert A) (famVert B)) :
    𝓜.IsMatching (A ∪ B) := by
  refine ⟨?_, ?_⟩
  · rintro e (he | he)
    · exact hA.1 he
    · exact hB.1 he
  · intro e he e' he' hne
    rw [Set.mem_union] at he he'
    rcases he with he | he <;> rcases he' with he' | he'
    · exact hA.2 he he' hne
    · exact disjoint_of_mem_famVert hd he he'
    · exact disjoint_of_mem_famVert hd.symm he he'
    · exact hB.2 he he' hne

theorem nonsing_union (A B : Set (Set (Fin n))) :
    nonsing (A ∪ B) = nonsing A ∪ nonsing B := by
  ext e
  simp only [nonsing, Set.mem_setOf_eq, Set.mem_union]
  tauto

theorem edgeDisjointFam_union {A B C D' : Set (Set (Fin n))}
    (h1 : EdgeDisjointFam A C) (h2 : EdgeDisjointFam A D')
    (h3 : EdgeDisjointFam B C) (h4 : EdgeDisjointFam B D') :
    EdgeDisjointFam (A ∪ B) (C ∪ D') := by
  rw [EdgeDisjointFam, Set.disjoint_left] at h1 h2 h3 h4 ⊢
  rintro e he he'
  simp only [nonsing, Set.mem_setOf_eq] at he he'
  rcases he with ⟨he, he2⟩
  rcases he' with ⟨he', he2'⟩
  rw [Set.mem_union] at he he'
  rcases he with he | he <;> rcases he' with he' | he'
  · exact h1 ⟨he, he2⟩ ⟨he', he2'⟩
  · exact h2 ⟨he, he2⟩ ⟨he', he2'⟩
  · exact h3 ⟨he, he2⟩ ⟨he', he2'⟩
  · exact h4 ⟨he, he2⟩ ⟨he', he2'⟩

/-! ## `R` versus `𝓗'` -/

theorem edgeSize_two_of_mem_incidentTwo {𝓗 : Hypergraph (Fin n)} {U : Set (Fin n)}
    {e : Set (Fin n)} (he : e ∈ incidentTwo 𝓗 U) : edgeSize e = 2 :=
  (mem_pow2.mp he.1).2

theorem edgeSet_not_mem_of_out {𝓗' : MultiHypergraph n} {R : Hypergraph (Fin n)}
    (hout : ∀ e ∈ 𝓗'.edges, e ∉ R) (hR2 : ∀ e ∈ R, edgeSize e = 2) :
    ∀ e ∈ 𝓗'.edgeSet, e ∉ R := by
  intro e he
  rcases he with he | ⟨v, rfl, hv⟩
  · exact hout e he
  · intro hcon
    have h2 := hR2 _ hcon
    rw [edgeSize_eq_ncard, Set.ncard_singleton] at h2
    exact absurd h2 (by norm_num)

theorem mem_edges_of_edgeSet_two_le {𝓜 : MultiHypergraph n} {e : Set (Fin n)}
    (he : e ∈ 𝓜.edgeSet) (h2 : 2 ≤ e.ncard) : e ∈ 𝓜.edges :=
  MultiHypergraph.mem_edges_of_edgeSet_of_not_singleton he
    (by rintro ⟨v, rfl⟩; rw [Set.ncard_singleton] at h2; omega)

/-! ## `Proc` along one step -/

theorem Proc_disjoint_block {I : Fin K → Finset (Fin D)} {j : ℕ} (hj : j < K)
    (hIdisj : ∀ i j', i ≠ j' → Disjoint (I i) (I j')) :
    ∀ c ∈ Proc I j, c ∉ I ⟨j, hj⟩ := by
  intro c hc hck
  rw [mem_Proc] at hc
  obtain ⟨k', hk', hck'⟩ := hc
  have hne : k' ≠ ⟨j, hj⟩ := by
    intro h
    rw [h] at hk'
    exact absurd hk' (by simp)
  exact (Finset.disjoint_left.mp (hIdisj k' ⟨j, hj⟩ hne)) hck' hck

theorem card_Proc_succ {I : Fin K → Finset (Fin D)} {j : ℕ} (hj : j < K)
    (hIdisj : ∀ i j', i ≠ j' → Disjoint (I i) (I j')) :
    (Proc I (j+1)).card = (Proc I j).card + (I ⟨j, hj⟩).card := by
  classical
  rw [Proc_succ I hj]
  refine Finset.card_union_of_disjoint ?_
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb hab
  exact Proc_disjoint_block hj hIdisj a ha (hab ▸ hb)

theorem iUnion_Proc_succ_extend {I : Fin K → Finset (Fin D)} {j : ℕ} (hj : j < K)
    (hIdisj : ∀ i j', i ≠ j' → Disjoint (I i) (I j'))
    (Nf : Fin D → Set (Set (Fin n)))
    (Nabs : Fin (I ⟨j, hj⟩).card → Set (Set (Fin n))) :
    (⋃ c ∈ Proc I (j+1), extend Nf I ⟨j, hj⟩ Nabs c)
      = (⋃ c ∈ Proc I j, Nf c) ∪ (⋃ i : Fin (I ⟨j, hj⟩).card, Nabs i) := by
  classical
  ext x
  simp only [Set.mem_iUnion, Set.mem_union, exists_prop]
  constructor
  · rintro ⟨c, hc, hxc⟩
    have hc' : c ∈ Proc I j ∨ c ∈ I ⟨j, hj⟩ := by
      rw [← Finset.mem_union, ← Proc_succ I hj]; exact hc
    rcases hc' with hcj | hck
    · exact Or.inl ⟨c, hcj, by
        rwa [extend_of_not_mem (Proc_disjoint_block hj hIdisj c hcj)] at hxc⟩
    · exact Or.inr ⟨(blockEquiv I ⟨j, hj⟩).symm ⟨c, hck⟩, by rwa [extend_of_mem hck] at hxc⟩
  · rintro (⟨c, hc, hxc⟩ | ⟨i, hxi⟩)
    · refine ⟨c, ?_, ?_⟩
      · rw [Proc_succ I hj, Finset.mem_union]; exact Or.inl hc
      · rwa [extend_of_not_mem (Proc_disjoint_block hj hIdisj c hc)]
    · refine ⟨blockColour I ⟨j, hj⟩ i, ?_, ?_⟩
      · rw [Proc_succ I hj, Finset.mem_union]; exact Or.inr (blockColour_mem I ⟨j, hj⟩ i)
      · rwa [extend_blockColour]

theorem asmSinglesSum_succ {𝓗' : MultiHypergraph n} (P : EdgePartition 𝓗' K) {j : ℕ}
    (hj : j < K) (w : Fin n) :
    asmSinglesSum 𝓗' P (j+1) w
      = asmSinglesSum 𝓗' P j w + (((P.part ⟨j, hj⟩).singles w : ℕ) : ℝ) := by
  classical
  simp only [asmSinglesSum, procParts_succ hj]
  rw [Finset.sum_insert (by rw [mem_procParts]; simp)]
  ring

/-! ## The parts of an `EdgePartition` -/

theorem EdgePartition.part_edgeSet_subset {𝓗' : MultiHypergraph n} {P : EdgePartition 𝓗' K}
    (i : Fin K) : (P.part i).edgeSet ⊆ 𝓗'.edgeSet :=
  MultiHypergraph.edgeSet_mono (P.le i)

theorem EdgePartition.parts_edges_disjoint {𝓗' : MultiHypergraph n} {P : EdgePartition 𝓗' K}
    {i i' : Fin K} (h : i ≠ i') : Disjoint (P.part i).edges (P.part i').edges := by
  rw [Set.disjoint_left]
  intro e he he'
  have hc : e ∈ 𝓗'.edges := MultiHypergraph.edges_mono (P.le i) he
  obtain ⟨i₀, hi₀, huniq⟩ := P.edges_cover e hc
  have h1 : i = i₀ := huniq i he
  have h2 : i' = i₀ := huniq i' he'
  exact h (h1.trans h2.symm)

/-! ## Monotonicity of `PseudoRandomFam` -/

theorem PseudoRandomFam.mono_kappa {N : Set (Set (Fin n))} {𝓕V : Set (Set (Fin n))}
    {γ κ κ' : ℝ} (h : PseudoRandomFam N 𝓕V γ κ) (hκ : κ ≤ κ') :
    PseudoRandomFam N 𝓕V γ κ' := by
  intro A hA
  have := h A hA
  have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hle : κ * (n:ℝ) ≤ κ' * (n:ℝ) := mul_le_mul_of_nonneg_right hκ hn
  rw [abs_le] at this ⊢
  constructor <;> linarith [this.1, this.2]

theorem leftover_bound {n D' : ℕ} {𝓜 : MultiHypergraph n}
    (N : Fin D' → Set (EdgeObj 𝓜)) (w : Fin n) {βp κ γp : ℝ}
    (hleft : ∀ F ∈ ({objThrough 𝓜 w | w : Fin n} : Set (Set (EdgeObj 𝓜))),
      (({x ∈ F | ∀ c : Fin D', x ∉ N c}).ncard : ℝ) ≤
        γp * (F.ncard : ℝ) + κ * max (F.ncard : ℝ) (D' : ℝ))
    (hdegw : |((𝓜.deg w : ℝ)) - (D' : ℝ)| ≤ βp * (D' : ℝ))
    (hγp0 : 0 ≤ γp) (hκ0 : 0 ≤ κ) (hβp0 : 0 ≤ βp)
    (hβpκ : 10 * βp ≤ κ) (hγp1 : γp ≤ 1) (hκ1 : κ ≤ 1) :
    (({x ∈ objThrough 𝓜 w | ∀ c : Fin D', x ∉ N c}).ncard : ℝ) ≤
      (γp + 2 * κ) * (D' : ℝ) := by
  have hL := hleft _ ⟨w, rfl⟩
  have hdegR : ((objThrough 𝓜 w).ncard : ℝ) = (𝓜.deg w : ℝ) := by rw [objThrough_ncard]
  rw [hdegR] at hL
  set m : ℝ := (𝓜.deg w : ℝ) with hmdef
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ (D' : ℝ) := Nat.cast_nonneg _
  have habs := hdegw
  rw [abs_le] at habs
  have h1 : (D' : ℝ) - m ≤ βp * (D' : ℝ) := by linarith [habs.1]
  have h2 : m ≤ (1 + βp) * (D' : ℝ) := by linarith [habs.2]
  have h3 : max m (D' : ℝ) ≤ (1 + βp) * (D' : ℝ) := by
    refine max_le h2 ?_
    linarith [hβp0, hD0]
  have hβp1 : βp ≤ κ / 10 := by linarith
  have hb2 : γp * βp ≤ κ / 10 := by nlinarith [hβp1, hγp1, hκ0, hγp0]
  have hb3 : κ * βp ≤ κ / 10 := by nlinarith [hβp1, hκ1, hκ0]
  have hkey : βp + γp * βp + κ * βp ≤ κ := by linarith
  nlinarith [hL, h1, h2, h3, hkey, hm0, hγp0, hκ0, hD0]

/-! ## The disjointness of an old family from the new batch -/

theorem edgeDisjointFam_old_new {I : Fin K → Finset (Fin D)} {M : Fin D → Set (Set (Fin n))}
    {Nf : Fin D → Set (Set (Fin n))} {R Rcur : Hypergraph (Fin n)}
    {𝓗' : MultiHypergraph n} {P : EdgePartition 𝓗' K} {k : Fin K} {j : ℕ}
    {A B : Set (Set (Fin n))} {c c' : Fin D}
    (hne : c ≠ c') (hneProc : c' ∉ Proc I j) (hRcurSub : Rcur ⊆ R)
    (hAR : ∀ e ∈ A, e ∈ R → ∃ c'' ∈ Proc I j, e ∈ Nf c'')
    (hA : ∀ e ∈ A, e ∈ M c ∨ e ∈ R ∨ (∃ c'' ∈ Proc I j, e ∈ Nf c'')
        ∨ (∃ k' ∈ procParts K j, e ∈ (P.part k').edgeSet))
    (hNfdec : ∀ c'' ∈ Proc I j, ∀ e ∈ Nf c'', e ∈ M c'' ∨ e ∈ R
        ∨ (∃ k' ∈ procParts K j, e ∈ (P.part k').edgeSet))
    (hB : ∀ f ∈ B, f ∈ M c' ∨ f ∈ Rcur ∨ f ∈ (P.part k).edgeSet)
    (hMdisj : ∀ i j', i ≠ j' → EdgeDisjointFam (M i) (M j'))
    (hMR : ∀ i, ∀ e ∈ M i, e ∉ R)
    (hMout : ∀ i, ∀ e ∈ M i, e ∉ 𝓗'.edgeSet)
    (hout : ∀ e ∈ 𝓗'.edges, e ∉ R)
    (hRcur : ∀ e ∈ Rcur, ∀ c'' ∈ Proc I j, e ∉ Nf c'')
    (hpartedges : ∀ k' ∈ procParts K j, (P.part k').edges ⊆ 𝓗'.edges)
    (hPartK : (P.part k).edges ⊆ 𝓗'.edges)
    (hpartsdisj : ∀ k' ∈ procParts K j, Disjoint (P.part k').edges (P.part k).edges) :
    EdgeDisjointFam A B := by
  rw [EdgeDisjointFam, Set.disjoint_left]
  intro e heA2 heB2
  simp only [Set.mem_setOf_eq] at heA2 heB2
  obtain ⟨heA, he2⟩ := heA2
  obtain ⟨heB, he2'⟩ := heB2
  rcases hA e heA with heM | heR | ⟨c'', hc'', heNf⟩ | ⟨k', hk', heK⟩
  · rcases hB e heB with hfM | hfRcur | hfK
    · exact Set.disjoint_left.mp (hMdisj c c' hne) ⟨heM, he2⟩ ⟨hfM, he2'⟩
    · exact hMR c e heM (hRcurSub hfRcur)
    · exact hMout c e heM (MultiHypergraph.edges_subset_edgeSet 𝓗' (hPartK (mem_edges_of_edgeSet_two_le hfK he2')))
  · obtain ⟨c'', hc'', heNf⟩ := hAR e heA heR
    rcases hB e heB with hfM | hfRcur | hfK
    · exact hMR c' e hfM heR
    · exact hRcur e hfRcur c'' hc'' heNf
    · exact hout e (hPartK (mem_edges_of_edgeSet_two_le hfK he2')) heR
  · have hcc : c'' ≠ c' := fun h => hneProc (h ▸ hc'')
    rcases hNfdec c'' hc'' e heNf with heM | heR | ⟨k₂, hk₂, heK₂⟩
    · rcases hB e heB with hfM | hfRcur | hfK
      · exact Set.disjoint_left.mp (hMdisj c'' c' hcc) ⟨heM, he2⟩ ⟨hfM, he2'⟩
      · exact hMR c'' e heM (hRcurSub hfRcur)
      · exact hMout c'' e heM (MultiHypergraph.edges_subset_edgeSet 𝓗' (hPartK (mem_edges_of_edgeSet_two_le hfK he2')))
    · rcases hB e heB with hfM | hfRcur | hfK
      · exact hMR c' e hfM heR
      · exact hRcur e hfRcur c'' hc'' heNf
      · exact hout e (hPartK (mem_edges_of_edgeSet_two_le hfK he2')) heR
    · rcases hB e heB with hfM | hfRcur | hfK
      · exact hMout c' e hfM
          (MultiHypergraph.edges_subset_edgeSet 𝓗'
            (hpartedges k₂ hk₂ (mem_edges_of_edgeSet_two_le heK₂ he2)))
      · exact hout e (hpartedges k₂ hk₂ (mem_edges_of_edgeSet_two_le heK₂ he2))
          (hRcurSub hfRcur)
      · exact Set.disjoint_left.mp (hpartsdisj k₂ hk₂)
          (mem_edges_of_edgeSet_two_le heK₂ he2) (mem_edges_of_edgeSet_two_le hfK he2')
  · rcases hB e heB with hfM | hfRcur | hfK
    · exact hMout c' e hfM
        (MultiHypergraph.edges_subset_edgeSet 𝓗'
          (hpartedges k' hk' (mem_edges_of_edgeSet_two_le heK he2)))
    · exact hout e (hpartedges k' hk' (mem_edges_of_edgeSet_two_le heK he2)) (hRcurSub hfRcur)
    · exact Set.disjoint_left.mp (hpartsdisj k' hk')
        (mem_edges_of_edgeSet_two_le heK he2) (mem_edges_of_edgeSet_two_le hfK he2')

end

end Work.Deep.Nibble
