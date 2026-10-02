import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.Pad

namespace Work.Deep.Kahn

open scoped BigOperators
open ErdosFaberLovaszConjecture

/-- An "old" vertex `Sum.inl x` of the padding lies on the padded edge of `e` exactly when
it lies on the original edge `e`: the fresh slots `padSlots` consist of `Sum.inr` vertices. -/
private theorem mem_padEdge_inl {n C : ℕ}
    {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} {x : Fin n} {e : 𝓗} :
    (Sum.inl x : PV n C 𝓗) ∈ padEdge C 𝓗 e ↔ x ∈ (e : Set (Fin n)) := by
  constructor
  · intro h
    rcases (Set.mem_union _ _ _).mp h with h1 | h1
    · obtain ⟨y, hy, hyx⟩ := h1
      exact Sum.inl_injective hyx ▸ hy
    · obtain ⟨p, -, -, hpv⟩ := mem_padSlots.mp h1
      exact absurd hpv Sum.inr_ne_inl
  · intro hx
    exact Set.mem_union_left _ ⟨x, hx, rfl⟩

/-- A "fresh" vertex `Sum.inr p` of the padding lies only on the padded edge of `p.1`. -/
private theorem eq_fst_of_mem_padEdge_inr {n C : ℕ}
    {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} {p : 𝓗 × Fin C} {e : 𝓗}
    (h : (Sum.inr p : PV n C 𝓗) ∈ padEdge C 𝓗 e) : e = p.1 := by
  rcases (Set.mem_union _ _ _).mp h with h1 | h1
  · obtain ⟨y, -, hyv⟩ := h1
    exact absurd hyv Sum.inl_ne_inr
  · obtain ⟨q, hq1, -, hqv⟩ := mem_padSlots.mp h1
    have hqp : q = p := Sum.inr_injective hqv
    rw [hqp] at hq1
    exact hq1.symm

/-- **Pointwise colour-degree bound for the padded hypergraph.**  If every colour degree of
the hypergraph `𝓗` is at most `D`, then the same holds for the `C`-uniform padding
`padHyp C 𝓗`: for every vertex `v` of the padding and every colour `γ'`, the number of padded
edges through `v` whose list contains `γ'` is at most `D`.  (The lists of the padded edges are
the images `(L e).image ρ` of the original lists under an injection `ρ`.) -/
theorem padColourDegLe {n c C D : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    {L : 𝓗 → Finset (Fin c)} (hD : 1 ≤ D)
    (hdeg : ∀ x : Fin n, ∀ γ : Fin c,
      Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} ≤ D)
    {c' : ℕ} {ρ : Fin c → Fin c'} (hρ : Function.Injective ρ) :
    ∀ (v : Work.Deep.Kahn.PV n C 𝓗) (γ' : Fin c'),
      Nat.card {e : 𝓗 // v ∈ Work.Deep.Kahn.padEdge C 𝓗 e ∧ γ' ∈ (L e).image ρ} ≤ D := by
  intro v γ'
  rcases v with x | p
  · -- an old vertex of the underlying hypergraph
    by_cases hex : ∃ γ : Fin c, ρ γ = γ'
    · -- `γ'` is in the range of `ρ`: transport along the (unique) preimage
      obtain ⟨γ, hγ⟩ := hex
      have himg : ∀ e : 𝓗, (γ' ∈ (L e).image ρ ↔ γ ∈ L e) := by
        intro e
        constructor
        · intro hmem
          rcases Finset.mem_image.mp hmem with ⟨δ, hδ, hδρ⟩
          have hδγ : δ = γ := hρ (hδρ.trans hγ.symm)
          rw [hδγ] at hδ
          exact hδ
        · intro hmem
          rw [← hγ]
          exact Finset.mem_image_of_mem ρ hmem
      have hequiv : {e : 𝓗 // (Sum.inl x : PV n C 𝓗) ∈ padEdge C 𝓗 e ∧ γ' ∈ (L e).image ρ}
          ≃ {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} :=
        Equiv.subtypeEquivRight (fun e => by
          rw [mem_padEdge_inl]
          exact and_congr_right (fun _ => himg e))
      rw [Nat.card_congr hequiv]
      exact hdeg x γ
    · -- `γ'` is not in the range of `ρ`: no padded edge carries it
      have hfalse : ∀ e : 𝓗, ¬ (γ' ∈ (L e).image ρ) := by
        intro e he
        rcases Finset.mem_image.mp he with ⟨δ, -, hδρ⟩
        exact hex ⟨δ, hδρ⟩
      have hsub : Subsingleton
          {e : 𝓗 // (Sum.inl x : PV n C 𝓗) ∈ padEdge C 𝓗 e ∧ γ' ∈ (L e).image ρ} :=
        ⟨fun a b => absurd a.2.2 (hfalse a.1)⟩
      exact (Finite.card_le_one_iff_subsingleton.mpr hsub).trans hD
  · -- a fresh vertex of the padding lies on at most one padded edge
    have hsub : Subsingleton
        {e : 𝓗 // (Sum.inr p : PV n C 𝓗) ∈ padEdge C 𝓗 e ∧ γ' ∈ (L e).image ρ} :=
      ⟨fun a b => Subtype.ext
        ((eq_fst_of_mem_padEdge_inr a.2.1).trans (eq_fst_of_mem_padEdge_inr b.2.1).symm)⟩
    exact (Finite.card_le_one_iff_subsingleton.mpr hsub).trans hD

end Work.Deep.Kahn
