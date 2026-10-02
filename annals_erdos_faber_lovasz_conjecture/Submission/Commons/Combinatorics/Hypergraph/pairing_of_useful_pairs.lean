import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.CompletePartialOrder

set_option linter.style.haveILetI false

/-!
# Pairing of useful pairs

We formalise the combinatorial core of the proof of Proposition 5.3 of
Kang–Kelly–Kühn–Methuku–Osthus, *A proof of the Erdős–Faber–Lovász conjecture*
(Annals of Math. 198 (2023)).

Given a hypergraph `𝓗` on the vertex set `Fin n` and `2t` pairwise intersecting
distinct hyperedges `a i 0, a i 1` (`i : Fin t`) such that each pair `{a i 0, a i 1}`
is *useful* (at most `n - 2` further edges of `𝓗` meet both of them), and
provided `𝓗` has at least `n + t` edges, there exists an injective family
`σ : Fin t → Fin 2 → 𝓗` with `σ i 0` disjoint from `σ i 1` for every `i`.

In other words, the *disjointness graph* on the edges of `𝓗` has a matching of
size `t`: for each `i` we pick a "private" partner `z i ∈ 𝓗` meeting at most one
of `a i 0, a i 1`, and use `{z i, a i b}` as the `i`-th matching edge.
-/

namespace Commons.Combinatorics.Hypergraph

open Classical

/-- **Hall's theorem, selection form.**  If `S : ι → Finset α` are finite sets each of
cardinality at least `|ι|`, then there is an injective selection `f` with `f i ∈ S i`
for all `i`. -/
lemma exists_injective_of_card_le {ι α : Type*} [Fintype ι] [DecidableEq α] (S : ι → Finset α)
    (h : ∀ i, Fintype.card ι ≤ (S i).card) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ i, f i ∈ S i := by
  classical
  refine (Finset.all_card_le_biUnion_card_iff_exists_injective S).mp ?_
  intro s
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · simp
  · calc s.card ≤ Fintype.card ι := Finset.card_le_univ s
      _ ≤ (S x).card := h x
      _ ≤ (s.biUnion S).card := Finset.card_le_card (Finset.subset_biUnion_of_mem S hx)

/-- If two subsets of `Fin n` are distinct and intersect, then `Fin n` has at least two
elements. -/
lemma two_le_of_ne_of_nonempty_inter {n : ℕ} {s t : Set (Fin n)} (hne : s ≠ t)
    (h : (s ∩ t).Nonempty) : 2 ≤ n := by
  obtain ⟨x, hx⟩ := h
  have hx1 : x ∈ s := hx.1
  have hx2 : x ∈ t := hx.2
  have hcases : (∃ y, y ∈ s ∧ y ∉ t) ∨ (∃ y, y ∈ t ∧ y ∉ s) := by
    by_contra hc
    rw [not_or] at hc
    obtain ⟨hc1, hc2⟩ := hc
    push Not at hc1 hc2
    exact hne (Set.Subset.antisymm (fun y hy => hc1 y hy) (fun y hy => hc2 y hy))
  rcases hcases with ⟨y, hy1, hy2⟩ | ⟨y, hy1, hy2⟩
  · have hxy : x ≠ y := fun hh => hy2 (hh ▸ hx2)
    have hc : ({x, y} : Finset (Fin n)).card ≤ (Finset.univ : Finset (Fin n)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    rw [Finset.card_pair hxy, Finset.card_univ, Fintype.card_fin] at hc
    exact hc
  · have hxy : x ≠ y := fun hh => hy2 (hh ▸ hx1)
    have hc : ({x, y} : Finset (Fin n)).card ≤ (Finset.univ : Finset (Fin n)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    rw [Finset.card_pair hxy, Finset.card_univ, Fintype.card_fin] at hc
    exact hc

theorem pairing_of_useful_pairs {n : ℕ} (𝓗 : Set (Set (Fin n))) (t : ℕ)
    (a : Fin t → Fin 2 → {e : Set (Fin n) // e ∈ 𝓗})
    (hinj : Function.Injective (fun p : Fin t × Fin 2 => a p.1 p.2))
    (hinter : ∀ p q : Fin t × Fin 2, p ≠ q →
      (((a p.1 p.2).1 : Set (Fin n)) ∩ ((a q.1 q.2).1)).Nonempty)
    (huseful : ∀ i : Fin t,
      Nat.card {g : {e : Set (Fin n) // e ∈ 𝓗} //
          g ≠ a i 0 ∧ g ≠ a i 1 ∧ (g.1 ∩ (a i 0).1).Nonempty ∧
            (g.1 ∩ (a i 1).1).Nonempty} ≤ n - 2)
    (hcard : n + t ≤ Nat.card {e : Set (Fin n) // e ∈ 𝓗}) :
    ∃ σ : Fin t → Fin 2 → {e : Set (Fin n) // e ∈ 𝓗},
      Function.Injective (fun p : Fin t × Fin 2 => σ p.1 p.2) ∧
      (∀ i : Fin t, Disjoint ((σ i 0).1 : Set (Fin n)) ((σ i 1).1 : Set (Fin n))) := by
  classical
  by_cases ht : t = 0
  · subst ht
    refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
    · intro p q _
      exact Fin.elim0 p.1
    · intro i
      exact Fin.elim0 i
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht
    haveI : Fintype {e : Set (Fin n) // e ∈ 𝓗} :=
      Fintype.subtype (Finset.univ.filter (fun e : Set (Fin n) => e ∈ 𝓗)) (by intro x; simp)
    have hcardE : n + t ≤ Fintype.card {e : Set (Fin n) // e ∈ 𝓗} := by
      rw [← Nat.card_eq_fintype_card]; exact hcard
    let i₀ : Fin t := ⟨0, htpos⟩
    have hpair : ∀ i : Fin t,
        (((a i 0).1 : Set (Fin n)) ∩ ((a i 1).1 : Set (Fin n))).Nonempty :=
      fun i => hinter (i, 0) (i, 1) (by simp)
    have h2n : 2 ≤ n := by
      have hne : (a i₀ 0).1 ≠ (a i₀ 1).1 := by
        intro heq
        have h1 : (i₀, (0 : Fin 2)) = (i₀, (1 : Fin 2)) := hinj (Subtype.ext heq)
        exact absurd (Prod.mk.inj h1).2 (by decide)
      exact two_le_of_ne_of_nonempty_inter hne (hpair i₀)
    let B : Fin t → Finset {e : Set (Fin n) // e ∈ 𝓗} := fun i =>
      Finset.univ.filter (fun g => ((g.1 : Set (Fin n)) ∩ (a i 0).1).Nonempty ∧
        ((g.1 : Set (Fin n)) ∩ (a i 1).1).Nonempty)
    let Fb : Fin t → Finset {e : Set (Fin n) // e ∈ 𝓗} := fun i =>
      Finset.univ.filter (fun g => g ≠ a i 0 ∧ g ≠ a i 1 ∧
        ((g.1 : Set (Fin n)) ∩ (a i 0).1).Nonempty ∧
        ((g.1 : Set (Fin n)) ∩ (a i 1).1).Nonempty)
    have hFb : ∀ i : Fin t, (Fb i).card ≤ n - 2 := by
      intro i
      have h := huseful i
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
      simpa only [Fb] using h
    have hB : ∀ i : Fin t, (B i).card ≤ n := by
      intro i
      have hsub : B i ⊆ insert (a i 0) (insert (a i 1) (Fb i)) := by
        intro g hg
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hg
        obtain ⟨hg0, hg1⟩ := hg
        by_cases h0 : g = a i 0
        · simp [h0]
        by_cases h1 : g = a i 1
        · simp [h1]
        simp only [Finset.mem_insert, h0, h1, false_or]
        simp only [Fb, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨h0, h1, hg0, hg1⟩
      have hle : (B i).card ≤ (Fb i).card + 2 := by
        calc (B i).card ≤ (insert (a i 0) (insert (a i 1) (Fb i))).card := Finset.card_le_card hsub
          _ ≤ (insert (a i 1) (Fb i)).card + 1 := Finset.card_insert_le _ _
          _ ≤ ((Fb i).card + 1) + 1 := Nat.add_le_add_right (Finset.card_insert_le _ _) 1
          _ = (Fb i).card + 2 := by omega
      have := hFb i
      omega
    let S : Fin t → Finset {e : Set (Fin n) // e ∈ 𝓗} := fun i => Finset.univ \ B i
    have hS : ∀ i : Fin t, t ≤ (S i).card := by
      intro i
      have h1 : (S i).card = Fintype.card {e : Set (Fin n) // e ∈ 𝓗} - (B i).card := by
        simp [S, Finset.card_sdiff, Finset.inter_univ]
      have := hB i
      omega
    obtain ⟨z, hzinj, hzmem⟩ := exists_injective_of_card_le S (by
      intro i; simpa using hS i)
    have hznotB : ∀ i : Fin t, z i ∉ B i := by
      intro i
      have h := hzmem i
      simp only [S, Finset.mem_sdiff, Finset.mem_univ, true_and] at h
      exact h
    have hallB : ∀ i j : Fin t, ∀ b : Fin 2, a j b ∈ B i := by
      intro i j b
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rcases eq_or_ne (j, b) (i, 0) with h | h
        · have h1 : a j b = a i 0 := by
            simpa using congrArg (fun p : Fin t × Fin 2 => a p.1 p.2) h
          rw [h1]
          simpa [Set.inter_self] using (hpair i).mono Set.inter_subset_left
        · exact hinter (j, b) (i, 0) h
      · rcases eq_or_ne (j, b) (i, 1) with h | h
        · have h1 : a j b = a i 1 := by
            simpa using congrArg (fun p : Fin t × Fin 2 => a p.1 p.2) h
          rw [h1]
          simpa [Set.inter_self] using (hpair i).mono Set.inter_subset_right
        · exact hinter (j, b) (i, 1) h
    have hznotboth : ∀ i : Fin t,
        ¬(((z i).1 ∩ (a i 0).1).Nonempty ∧ ((z i).1 ∩ (a i 1).1).Nonempty) := by
      intro i h
      exact hznotB i (by
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
        exact h)
    let c : Fin t → Fin 2 := fun i => if ((z i).1 ∩ (a i 0).1).Nonempty then 1 else 0
    let σ : Fin t → Fin 2 → {e : Set (Fin n) // e ∈ 𝓗} :=
      fun i b => if b = 0 then z i else a i (c i)
    have hσ0 : ∀ i, σ i 0 = z i := by intro i; simp [σ]
    have hσ1 : ∀ i, σ i 1 = a i (c i) := by
      intro i
      simp only [σ]
      rw [if_neg (by decide : ¬((1 : Fin 2) = 0))]
    refine ⟨σ, ?_, ?_⟩
    · rintro ⟨i, b⟩ ⟨j, b'⟩ hab
      rcases eq_or_ne b 0 with hb | hb
      · rcases eq_or_ne b' 0 with hb' | hb'
        · subst hb; subst hb'
          simp [σ] at hab
          have hij : i = j := hzinj hab
          rw [hij]
        · subst hb
          simp [σ, hb'] at hab
          exfalso
          exact hznotB i (by rw [hab]; exact hallB i j (c j))
      · rcases eq_or_ne b' 0 with hb' | hb'
        · subst hb'
          simp [σ, hb] at hab
          exfalso
          exact hznotB j (by rw [← hab]; exact hallB j i (c i))
        · simp [σ, hb, hb'] at hab
          have hij : (i, c i) = (j, c j) := hinj hab
          have hij' : i = j := (Prod.mk.inj hij).1
          rw [hij', Fin.eq_one_of_ne_zero b hb, Fin.eq_one_of_ne_zero b' hb']
    · intro i
      have hdisj : Disjoint ((z i).1 : Set (Fin n)) ((a i (c i)).1 : Set (Fin n)) := by
        by_cases h0 : ((z i).1 ∩ (a i 0).1).Nonempty
        · have h1 : ¬((z i).1 ∩ (a i 1).1).Nonempty := fun h1 => hznotboth i ⟨h0, h1⟩
          have he : (z i).1 ∩ (a i 1).1 = ∅ := Set.not_nonempty_iff_eq_empty.mp h1
          have hc : c i = 1 := by simp [c, h0]
          rw [hc, Set.disjoint_iff_inter_eq_empty]
          exact he
        · have he : (z i).1 ∩ (a i 0).1 = ∅ := Set.not_nonempty_iff_eq_empty.mp h0
          have hc : c i = 0 := by simp [c, h0]
          rw [hc, Set.disjoint_iff_inter_eq_empty]
          exact he
      rw [hσ0 i, hσ1 i]
      exact hdisj

end Commons.Combinatorics.Hypergraph