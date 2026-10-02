import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.OneFact.N5.Basic

namespace Work.Deep.GKO.OneFact.N5

open Classical

/-- **The edge loss of the deletion is per-vertex.**  The `K`-edges between `S` and `T` either
survive in `remaining K P` or lie in `usedEdges P`; an edge `uv` of the second kind with `u ∈ S`
contributes to the `u`-th fibre of the set of *used* `K`-neighbours `usedNbrs K P u`.  Hence

  `e_K(S,T) ≤ e_{remaining K P}(S,T) + |S| · (m + L)`.

This is the quantitative form of "deleting the edges used by `P` costs at most `m + L` per
vertex of `S`". -/
private theorem crossEdges_remaining_add_used {n c : ℕ} (K : SimpleGraph (Fin n))
    (P : Fin c → SimpleGraph (Fin n)) (S T : Finset (Fin n)) {m L : ℕ}
    (hused : ∀ v, (usedNbrs K P v).card ≤ m + L) :
    Work.Deep.GKO.crossEdges K S T
      ≤ Work.Deep.GKO.crossEdges (remaining K P) S T + S.card * (m + L) := by
  classical
  -- split the `K`-pairs of `S × T` into the surviving ones and the used ones
  have hsub : ((S.product T).filter (fun p : Fin n × Fin n => K.Adj p.1 p.2))
      ⊆ ((S.product T).filter (fun p : Fin n × Fin n => (remaining K P).Adj p.1 p.2))
        ∪ ((S.product T).filter (fun p : Fin n × Fin n => p.2 ∈ usedNbrs K P p.1)) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    obtain ⟨hp1, hp2⟩ := hp
    by_cases h : s(p.1, p.2) ∈ usedEdges P
    · refine Or.inr ⟨hp1, ?_⟩
      rw [mem_usedNbrs]
      exact ⟨hp2, (mem_usedEdges.mp h)⟩
    · exact Or.inl ⟨hp1, (remaining_adj K P p.1 p.2).mpr ⟨hp2, h⟩⟩
  -- the used pairs number at most `∑_{u ∈ S} |usedNbrs K P u| ≤ |S| (m+L)`
  have hcard : ((S.product T).filter (fun p : Fin n × Fin n => p.2 ∈ usedNbrs K P p.1)).card
      ≤ S.card * (m + L) := by
    have h1 : ((S.product T).filter (fun p : Fin n × Fin n => p.2 ∈ usedNbrs K P p.1))
        ⊆ S.biUnion (fun u => (usedNbrs K P u).image (fun w => (u, w))) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      exact Finset.mem_biUnion.mpr ⟨p.1, (Finset.mem_product.mp hp.1).1,
        Finset.mem_image.mpr ⟨p.2, hp.2, rfl⟩⟩
    calc ((S.product T).filter (fun p : Fin n × Fin n => p.2 ∈ usedNbrs K P p.1)).card
        ≤ (S.biUnion (fun u => (usedNbrs K P u).image (fun w => (u, w)))).card :=
          Finset.card_le_card h1
      _ ≤ ∑ u ∈ S, ((usedNbrs K P u).image (fun w => (u, w))).card := Finset.card_biUnion_le
      _ = ∑ u ∈ S, (usedNbrs K P u).card := by
          refine Finset.sum_congr rfl fun u _ => ?_
          exact Finset.card_image_of_injective _ (fun a b h => ((Prod.mk.injEq u a u b).mp h).2)
      _ ≤ ∑ _u ∈ S, (m + L) := Finset.sum_le_sum fun u _ => hused u
      _ = S.card * (m + L) := by simp [Finset.sum_const]
  calc Work.Deep.GKO.crossEdges K S T
      = ((S.product T).filter (fun p : Fin n × Fin n => K.Adj p.1 p.2)).card := rfl
    _ ≤ (((S.product T).filter (fun p : Fin n × Fin n => (remaining K P).Adj p.1 p.2))
          ∪ ((S.product T).filter (fun p : Fin n × Fin n => p.2 ∈ usedNbrs K P p.1))).card :=
        Finset.card_le_card hsub
    _ ≤ ((S.product T).filter (fun p : Fin n × Fin n => (remaining K P).Adj p.1 p.2)).card
          + ((S.product T).filter (fun p : Fin n × Fin n => p.2 ∈ usedNbrs K P p.1)).card :=
        Finset.card_union_le _ _
    _ ≤ Work.Deep.GKO.crossEdges (remaining K P) S T + S.card * (m + L) :=
        add_le_add le_rfl hcard

/-- Lower-regularity survives the deletion of the cross edges already used by the family `P`, at
half the density `q`.  This is the input the completion step needs: the cross graph available for
the classes processed later must still be `BipLowerReg` with a positive density (the loss is
`usedNbrs`, bounded by `m + L`, which `hroomq` makes negligible against `q |S| |T|`). -/
theorem bipLowerRegRemaining {n : ℕ} (A B : Finset (Fin n)) (K : SimpleGraph (Fin n))
    {c : ℕ} (P : Fin c → SimpleGraph (Fin n)) {q ε : ℝ} {m L : ℕ}
    (hq : 0 < q)
    (hlr : Work.Deep.GKO.BipLowerReg K A B q ε)
    (hroomq : ((m + L : ℕ) : ℝ) ≤ q * ε * (n : ℝ) / 2)
    (hused : ∀ v, (Work.Deep.GKO.OneFact.N5.usedNbrs K P v).card ≤ m + L) :
    Work.Deep.GKO.BipLowerReg (Work.Deep.GKO.OneFact.N5.remaining K P) A B (q / 2) ε := by
  intro S hSA T hTB hεS hεT
  -- lower regularity of `K` on this pair
  have hreg := hlr S hSA T hTB hεS hεT
  -- `e_K(S,T) ≤ e_remaining(S,T) + |S| (m+L)`
  have hsplit := crossEdges_remaining_add_used K P S T hused
  have hsplitR : (Work.Deep.GKO.crossEdges K S T : ℝ)
      ≤ (Work.Deep.GKO.crossEdges (remaining K P) S T : ℝ)
        + (S.card : ℝ) * ((m + L : ℕ) : ℝ) := by
    have h1 : (Work.Deep.GKO.crossEdges K S T : ℝ)
        ≤ ((Work.Deep.GKO.crossEdges (remaining K P) S T + S.card * (m + L) : ℕ) : ℝ) := by
      exact_mod_cast hsplit
    have h2 : ((Work.Deep.GKO.crossEdges (remaining K P) S T + S.card * (m + L) : ℕ) : ℝ)
        = (Work.Deep.GKO.crossEdges (remaining K P) S T : ℝ)
          + (S.card : ℝ) * ((m + L : ℕ) : ℝ) := by
      push_cast
      ring
    linarith [h1, h2]
  -- the room hypothesis: `m + L ≤ (q/2) |T|`
  have hTL : ((m + L : ℕ) : ℝ) ≤ q / 2 * (T.card : ℝ) := by
    have h2 : (q / 2) * (ε * (n : ℝ)) ≤ (q / 2) * (T.card : ℝ) :=
      mul_le_mul_of_nonneg_left hεT (by linarith)
    nlinarith [hroomq, h2]
  -- hence the loss `|S| (m+L)` is absorbed by half of the density
  have hSZ : (S.card : ℝ) * ((m + L : ℕ) : ℝ) ≤ q / 2 * (S.card : ℝ) * (T.card : ℝ) := by
    have hS0 : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
    nlinarith [hTL, hS0]
  have hkey : q * (S.card : ℝ) * (T.card : ℝ)
      = 2 * (q / 2 * (S.card : ℝ) * (T.card : ℝ)) := by ring
  linarith [hreg, hsplitR, hSZ, hkey]

end Work.Deep.GKO.OneFact.N5
