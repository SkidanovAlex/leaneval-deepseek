import Submission.Work.Deep.Nibble.Defs

namespace Work.Deep.Nibble

open scoped BigOperators
open ErdosFaberLovaszConjecture

open Classical in
-- Counting helper: in a finite type, a set is counted by the indicator sum of
-- its membership predicate.
private theorem ncard_eq_sum_ite {α : Type*} [Fintype α] [DecidableEq α] (s : Set α) :
    s.ncard = ∑ a : α, if a ∈ s then (1 : ℕ) else 0 := by
  classical
  have hs : s.Finite := Set.toFinite s
  have hfinset : hs.toFinset = (Finset.univ : Finset α).filter (fun a => a ∈ s) := by
    ext a
    simp
  rw [Set.ncard_eq_toFinset_card s hs, Finset.card_eq_sum_ones, hfinset,
    ← Finset.sum_filter (p := fun a => a ∈ s) (f := fun _ => (1 : ℕ))]

/-- Double counting in a uniform hypergraph: the sum of the degrees over the
vertices equals the number of edges times the uniform edge size. -/
theorem sum_hdeg_eq_card_mul {M r : ℕ} {𝓖 : ErdosFaberLovaszConjecture.Hypergraph (Fin M)}
    (huni : ∀ f ∈ 𝓖, f.ncard = r) :
    (∑ w : Fin M, ErdosFaberLovaszConjecture.MultiHypergraph.hdeg 𝓖 w) =
      Nat.card {f : Set (Fin M) // f ∈ 𝓖} * r := by
  classical
  -- `𝓖` is a set of subsets of the finite type `Fin M`, hence finite.
  have hs : 𝓖.Finite := Set.toFinite 𝓖
  -- the degree of a vertex is the number of the edges of `𝓖` through it
  have hdegT : ∀ w : Fin M,
      ErdosFaberLovaszConjecture.MultiHypergraph.hdeg 𝓖 w
        = (hs.toFinset.filter (fun e => w ∈ e)).card := by
    intro w
    have hfin : ({e ∈ 𝓖 | w ∈ e} : Set (Set (Fin M))).Finite :=
      hs.subset (fun e he => he.1)
    have hfil : hfin.toFinset = hs.toFinset.filter (fun e => w ∈ e) := by
      ext e
      simp
    show ({e ∈ 𝓖 | w ∈ e} : Set (Set (Fin M))).ncard
        = (hs.toFinset.filter (fun e => w ∈ e)).card
    rw [Set.ncard_eq_toFinset_card _ hfin, hfil]
  -- double counting
  have hmain : (∑ w : Fin M, ErdosFaberLovaszConjecture.MultiHypergraph.hdeg 𝓖 w)
      = hs.toFinset.card * r := by
    calc ∑ w : Fin M, ErdosFaberLovaszConjecture.MultiHypergraph.hdeg 𝓖 w
        = ∑ w : Fin M, (hs.toFinset.filter (fun e => w ∈ e)).card :=
          Finset.sum_congr rfl fun w _ => hdegT w
      _ = ∑ w : Fin M, ∑ e ∈ hs.toFinset, if w ∈ e then (1 : ℕ) else 0 := by
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      _ = ∑ e ∈ hs.toFinset, ∑ w : Fin M, if w ∈ e then (1 : ℕ) else 0 :=
          Finset.sum_comm
      _ = ∑ e ∈ hs.toFinset, e.ncard := by
          refine Finset.sum_congr rfl fun e _ => ?_
          exact (ncard_eq_sum_ite e).symm
      _ = ∑ e ∈ hs.toFinset, r := by
          refine Finset.sum_congr rfl fun e he => ?_
          rw [huni e ((Set.Finite.mem_toFinset hs).mp he)]
      _ = hs.toFinset.card * r := by
          rw [Finset.sum_const, smul_eq_mul]
  -- the right-hand side: the number of edges of `𝓖` is the card of `𝓖`
  have hR : Nat.card {f : Set (Fin M) // f ∈ 𝓖} = hs.toFinset.card := by
    show Nat.card ↥𝓖 = hs.toFinset.card
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card 𝓖 hs]
  rw [hR, hmain]

end Work.Deep.Nibble
