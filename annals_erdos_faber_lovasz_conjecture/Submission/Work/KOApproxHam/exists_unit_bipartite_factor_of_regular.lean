import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.RegVocab

/-!
# König's perfect-matching fact for regular bipartite pairs

A bipartite graph that is `r`-regular between two disjoint finite parts `A`, `B` (every
`v ∈ A` has exactly `r` neighbours in `B`, and conversely), with `r ≥ 1`, contains a
perfect matching between `A` and `B`.

The proof is Hall's theorem.  The degree count (see `card_le_card_biUnion_nbrFinset`)
gives, for every `S ⊆ A`, the inequality `|S| ≤ |N_B(S)|`: counting the edges from `S`
to `B` on the `A`-side gives `r|S|` and on the `B`-side at most `r|N_B(S)|`, so the
generic bound `r ≥ 1` may be cancelled.  Hall then produces an injective partner map
`f : A → B` with `f a ∼ a` for all `a ∈ A`; applying the same statement with `A` and
`B` exchanged gives `|B| ≤ |A|`, so `|A| = |B|` and the partner map is a bijection
onto `B`.  The matching is then read off from the partner map; because it is
bijective, both sides are saturated.
-/

namespace Work.KOApproxHam

/-- **The degree count of a regular bipartite pair** (Hall's condition).  If every vertex of
`X` has exactly `r` neighbours in `Y` and every vertex of `Y` exactly `r` in `X`, with
`r ≥ 1`, then every `S ⊆ X` has at least `|S|` neighbours in `Y`.

The proof counts the edges between `S` and `Y` twice: on the `X`-side there are exactly
`r * |S|` of them, on the `Y`-side they are all incident with a vertex of
`T = ⋃_{x ∈ S} N_B(x)` and contribute at most `r * |T|`.  Cancelling `r ≥ 1` gives the
claim. -/
lemma card_le_card_biUnion_nbrFinset {n : ℕ} (G : SimpleGraph (Fin n)) (X Y S : Finset (Fin n))
    {r : ℕ} (hS : S ⊆ X) (hr : 1 ≤ r)
    (hX : ∀ v ∈ X, Work.Deep.GKO.degIn G v Y = r)
    (hY : ∀ v ∈ Y, Work.Deep.GKO.degIn G v X = r) :
    S.card ≤ (S.biUnion fun x => Work.Deep.GKO.nbrFinset G x Y).card := by
  classical
  set T := S.biUnion fun x => Work.Deep.GKO.nbrFinset G x Y with hT
  have hTY : T ⊆ Y := by
    intro y hy
    rw [hT, Finset.mem_biUnion] at hy
    obtain ⟨x, -, hx⟩ := hy
    exact (Work.Deep.GKO.mem_nbrFinset.mp hx).1
  have hsum1 : (∑ x ∈ S, Work.Deep.GKO.degIn G x Y) = r * S.card := by
    rw [Finset.sum_congr rfl (fun x hx => hX x (hS hx)), Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hsum2 : (∑ x ∈ S, Work.Deep.GKO.degIn G x Y)
      = ∑ y ∈ Y, (S.filter fun x => G.Adj x y).card := by
    have hL : ∀ x, Work.Deep.GKO.degIn G x Y = ∑ y ∈ Y, (if G.Adj x y then 1 else 0) := by
      intro x
      rw [Work.Deep.GKO.degIn, Work.Deep.GKO.nbrFinset, Finset.card_filter]
    have hR : ∀ y : Fin n, (S.filter fun x => G.Adj x y).card
        = ∑ x ∈ S, (if G.Adj x y then 1 else 0) := by
      intro y
      rw [Finset.card_filter]
    simp only [hL, hR]
    exact Finset.sum_comm
  have hsum3 : (∑ y ∈ Y, (S.filter fun x => G.Adj x y).card)
      = ∑ y ∈ T, (S.filter fun x => G.Adj x y).card := by
    refine (Finset.sum_subset hTY ?_).symm
    intro y hyY hyT
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hxS hadj
    exact hyT (by
      rw [hT, Finset.mem_biUnion]
      exact ⟨x, hxS, Work.Deep.GKO.mem_nbrFinset.mpr ⟨hyY, hadj⟩⟩)
  have hsum4 : (∑ y ∈ T, (S.filter fun x => G.Adj x y).card) ≤ r * T.card := by
    calc (∑ y ∈ T, (S.filter fun x => G.Adj x y).card)
        ≤ ∑ _y ∈ T, r := by
          apply Finset.sum_le_sum
          intro y hyT
          have hyY : y ∈ Y := hTY hyT
          calc (S.filter fun x => G.Adj x y).card
              ≤ (X.filter fun x => G.Adj x y).card :=
                Finset.card_le_card (Finset.filter_subset_filter (fun x => G.Adj x y) hS)
            _ = (X.filter fun x => G.Adj y x).card := by
                rw [Finset.filter_congr (fun x _ => G.adj_comm x y)]
            _ = Work.Deep.GKO.degIn G y X := rfl
            _ = r := hY y hyY
      _ = r * T.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hchain : r * S.card ≤ r * T.card := by
    calc r * S.card = ∑ x ∈ S, Work.Deep.GKO.degIn G x Y := hsum1.symm
      _ = ∑ y ∈ Y, (S.filter fun x => G.Adj x y).card := hsum2
      _ = ∑ y ∈ T, (S.filter fun x => G.Adj x y).card := hsum3
      _ ≤ r * T.card := hsum4
  exact Nat.le_of_mul_le_mul_left hchain (by omega)

/-- **Hall's theorem as a partner map.**  A pair `(X, Y)` in which every vertex of `X` has
exactly `r ≥ 1` neighbours in `Y` and conversely admits an injective map `f : X → Y` whose
graph is contained in the edge set of `G`. -/
lemma exists_injective_partner {n : ℕ} (G : SimpleGraph (Fin n)) (X Y : Finset (Fin n))
    {r : ℕ} (hr : 1 ≤ r) (hX : ∀ v ∈ X, Work.Deep.GKO.degIn G v Y = r)
    (hY : ∀ v ∈ Y, Work.Deep.GKO.degIn G v X = r) :
    ∃ f : ↥X → Fin n, Function.Injective f ∧ ∀ a : ↥X, f a ∈ Work.Deep.GKO.nbrFinset G a.1 Y := by
  classical
  refine (Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun a : ↥X => Work.Deep.GKO.nbrFinset G a.1 Y)).mp ?_
  intro s
  have hsub : s.image Subtype.val ⊆ X := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
    exact a.2
  have h := card_le_card_biUnion_nbrFinset G X Y (s.image Subtype.val) hsub hr hX hY
  rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.image_biUnion] at h
  exact h

/-- **König's perfect-matching fact**: a bipartite graph that is `r`-regular between two
disjoint finite parts `A`, `B` (every `v ∈ A` has exactly `r` neighbours in `B`, and conversely),
with `r ≥ 1`, contains a perfect matching between `A` and `B`.  The matching is produced as a
subgraph `M ≤ G` whose only edges run between `A` and `B`, and it saturates both sides: every
`v ∈ A` has exactly one `M`-neighbour in `B`, every `v ∈ B` exactly one in `A`.  This is the
case `k = 1` of the bipartite `k`-factor statement, i.e. the induction step that peels off one
regular spanning subgraph of degree `1`. -/
theorem exists_unit_bipartite_factor_of_regular {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (hAB : Disjoint A B) {r : ℕ} (hr : 1 ≤ r)
    (hregA : ∀ v ∈ A, Work.Deep.GKO.degIn G v B = r)
    (hregB : ∀ v ∈ B, Work.Deep.GKO.degIn G v A = r) :
    ∃ M : SimpleGraph (Fin n), M ≤ G ∧
      (∀ v, v ∉ A ∪ B → ∀ w, ¬ M.Adj v w) ∧
      (∀ v, v ∈ A → ∀ w, w ∈ A → ¬ M.Adj v w) ∧
      (∀ v, v ∈ B → ∀ w, w ∈ B → ¬ M.Adj v w) ∧
      (∀ v ∈ A, Work.Deep.GKO.degIn M v B = 1) ∧
      (∀ v ∈ B, Work.Deep.GKO.degIn M v A = 1) := by
  classical
  -- Hall on both sides: injective partner maps `A → B` and `B → A`
  obtain ⟨f, hf_inj, hf_mem⟩ := exists_injective_partner G A B hr hregA hregB
  obtain ⟨fB, hfB_inj, hfB_mem⟩ := exists_injective_partner G B A hr hregB hregA
  -- the partner map extended by the identity off `A`
  let g : Fin n → Fin n := fun x => if h : x ∈ A then f ⟨x, h⟩ else x
  have g_eq : ∀ x (hx : x ∈ A), g x = f ⟨x, hx⟩ := by
    intro x hx
    simp only [g]
    exact dif_pos hx
  have g_mem : ∀ x ∈ A, g x ∈ B := by
    intro x hx
    rw [g_eq x hx]
    exact (Work.Deep.GKO.mem_nbrFinset.mp (hf_mem ⟨x, hx⟩)).1
  have g_adj : ∀ x ∈ A, G.Adj x (g x) := by
    intro x hx
    rw [g_eq x hx]
    exact (Work.Deep.GKO.mem_nbrFinset.mp (hf_mem ⟨x, hx⟩)).2
  have g_inj : ∀ x ∈ A, ∀ y ∈ A, g x = g y → x = y := by
    intro x hx y hy hxy
    rw [g_eq x hx, g_eq y hy] at hxy
    exact Subtype.ext_iff.mp (hf_inj hxy)
  -- `|A| ≤ |B|` and `|B| ≤ |A|`, hence `|A| = |B|`
  have hA_le_B : A.card ≤ B.card := by
    have hsub : (Finset.univ.image f) ⊆ B := by
      intro b hb
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hb
      exact (Work.Deep.GKO.mem_nbrFinset.mp (hf_mem a)).1
    calc A.card = (Finset.univ : Finset ↥A).card := by
            rw [Finset.card_univ, Fintype.card_coe]
      _ = (Finset.univ.image f).card := (Finset.card_image_of_injective _ hf_inj).symm
      _ ≤ B.card := Finset.card_le_card hsub
  have hB_le_A : B.card ≤ A.card := by
    have hsub : (Finset.univ.image fB) ⊆ A := by
      intro b hb
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hb
      exact (Work.Deep.GKO.mem_nbrFinset.mp (hfB_mem a)).1
    calc B.card = (Finset.univ : Finset ↥B).card := by
            rw [Finset.card_univ, Fintype.card_coe]
      _ = (Finset.univ.image fB).card := (Finset.card_image_of_injective _ hfB_inj).symm
      _ ≤ A.card := Finset.card_le_card hsub
  have hcard : A.card = B.card := le_antisymm hA_le_B hB_le_A
  -- hence the partner map covers `B`
  have hcardimg : (A.image g).card = B.card := by
    rw [Finset.card_image_of_injOn (fun x hx y hy hxy => g_inj x hx y hy hxy), hcard]
  have himage : A.image g = B :=
    Finset.eq_of_subset_of_card_le
      (by
        intro b hb
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
        exact g_mem a ha)
      (le_of_eq hcardimg.symm)
  have hcover : ∀ y ∈ B, ∃ x ∈ A, g x = y := by
    intro y hy
    rw [← himage] at hy
    exact Finset.mem_image.mp hy
  -- the matching
  let M : SimpleGraph (Fin n) :=
    { Adj := fun v w => (v ∈ A ∧ g v = w) ∨ (w ∈ A ∧ g w = v)
      symm := ⟨by
        rintro v w (h | h)
        · exact Or.inr h
        · exact Or.inl h⟩
      loopless := ⟨by
        rintro v (⟨hvA, hg⟩ | ⟨hvA, hg⟩)
        · exact (Finset.disjoint_left.mp hAB) hvA (hg ▸ g_mem v hvA)
        · exact (Finset.disjoint_left.mp hAB) hvA (hg ▸ g_mem v hvA)⟩ }
  have M_adj : ∀ v w : Fin n, M.Adj v w ↔ (v ∈ A ∧ g v = w) ∨ (w ∈ A ∧ g w = v) :=
    fun v w => Iff.rfl
  refine ⟨M, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `M ≤ G`
    intro v w hvw
    rw [M_adj] at hvw
    rcases hvw with ⟨hvA, hgv⟩ | ⟨hwA, hgw⟩
    · rw [← hgv]; exact g_adj v hvA
    · rw [← hgw]; exact (g_adj w hwA).symm
  · -- no edges at vertices outside `A ∪ B`
    intro v hv w hvw
    rw [M_adj] at hvw
    rcases hvw with ⟨hvA, -⟩ | ⟨hwA, hgw⟩
    · exact hv (Finset.mem_union.mpr (Or.inl hvA))
    · exact hv (Finset.mem_union.mpr (Or.inr (hgw ▸ g_mem w hwA)))
  · -- no edges inside `A`
    intro v hvA w hwA hvw
    rw [M_adj] at hvw
    rcases hvw with ⟨-, hgv⟩ | ⟨-, hgw⟩
    · exact (Finset.disjoint_left.mp hAB) hwA (hgv ▸ g_mem v hvA)
    · exact (Finset.disjoint_left.mp hAB) hvA (hgw.symm ▸ g_mem w hwA)
  · -- no edges inside `B`
    intro v hvB w hwB hvw
    rw [M_adj] at hvw
    rcases hvw with ⟨hvA, -⟩ | ⟨hwA, -⟩
    · exact (Finset.disjoint_left.mp hAB) hvA hvB
    · exact (Finset.disjoint_left.mp hAB) hwA hwB
  · -- every `v ∈ A` has exactly one `M`-neighbour in `B`
    intro v hvA
    have hBmem : g v ∈ B := g_mem v hvA
    have hnb : Work.Deep.GKO.nbrFinset M v B = {g v} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      refine ⟨Work.Deep.GKO.mem_nbrFinset.mpr ⟨hBmem, Or.inl ⟨hvA, rfl⟩⟩, ?_⟩
      intro w hw
      rw [Work.Deep.GKO.mem_nbrFinset] at hw
      obtain ⟨hwB, hAdj⟩ := hw
      rw [M_adj] at hAdj
      rcases hAdj with ⟨-, hgv⟩ | ⟨hwA, hgw⟩
      · exact hgv.symm
      · exact absurd ((hgw.symm ▸ g_mem w hwA) : v ∈ B) ((Finset.disjoint_left.mp hAB) hvA)
    rw [Work.Deep.GKO.degIn, hnb, Finset.card_singleton]
  · -- every `v ∈ B` has exactly one `M`-neighbour in `A`
    intro v hvB
    obtain ⟨x₀, hx₀A, hx₀⟩ := hcover v hvB
    have huniq : ∀ x ∈ A, g x = v → x = x₀ := by
      intro x hxA hx
      exact g_inj x hxA x₀ hx₀A (by rw [hx, hx₀])
    have hnb : Work.Deep.GKO.nbrFinset M v A = {x₀} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      refine ⟨Work.Deep.GKO.mem_nbrFinset.mpr ⟨hx₀A, Or.inr ⟨hx₀A, hx₀⟩⟩, ?_⟩
      intro w hw
      rw [Work.Deep.GKO.mem_nbrFinset] at hw
      obtain ⟨hwA, hAdj⟩ := hw
      rw [M_adj] at hAdj
      rcases hAdj with ⟨hvA, -⟩ | ⟨-, hgw⟩
      · exact absurd hvB ((Finset.disjoint_left.mp hAB) hvA)
      · exact huniq w hwA hgw
    rw [Work.Deep.GKO.degIn, hnb, Finset.card_singleton]

end Work.KOApproxHam
