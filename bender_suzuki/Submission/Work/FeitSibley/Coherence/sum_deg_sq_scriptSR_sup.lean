import Mathlib
import Submission.Work.FeitSibley.Coherence.Vocab
import Submission.Work.FeitSibley.Coherence.sum_deg_sq_scriptSR
import Submission.Work.FeitSibley.Coherence.sum_deg_sq_scriptSR_of_le_S
import Submission.Work.FeitSibley.Coherence.relIndex_sup_Q1_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The sum of squared degrees over `𝒮(S' ⊔ Q₂)`

Peterfalvi II, Appendice XII.  For the Feit–Sibley data `h : FSData G` and a subgroup
`Q₂ ≤ Q₁` normalised by `H`, the characters of `𝒮(S' ⊔ Q₂) = scriptSR h.H h.Q₁ (S' ⊔ Q₂)`
(with `S' = ⁅S,S⁆ = FSScomm h`) satisfy

`∑ χ(1)² = |D| · [S : S'] · (|Q₁| / |Q₂| - 1)`.

`Work.FeitSibley.Coherence.sum_deg_sq_scriptSR` evaluates the sum as the difference of indices
`[H : S' ⊔ Q₂] - [H : (S' ⊔ Q₂) · Q₁] = [H : S' ⊔ Q₂] - [H : S' · Q₁]` (since `Q₂ ≤ Q₁`),
and the content here is the arithmetic evaluation of that difference.  Because `S' ≤ S` and
`Q₂ ≤ Q₁`, the subgroups `S'` and `Q₂` commute elementwise and meet trivially, so
`|S' ⊔ Q₂| = |S'| · |Q₂|`; likewise `|S' ⊔ Q₁| = |S'| · |Q₁|`, and `|H| = |D| · |S| · |Q₁|`.
Writing `d, s, q, a, b` for `|D|, |S|, |Q₁|, |S'|, |Q₂|`, the index identity
`|·| · [H : ·] = |H|` gives

`[H : S' ⊔ Q₂] = d·s·q/(a·b)` and `[H : S' ⊔ Q₁] = d·s·q/(a·q) = d·s/a`,

whose difference is `d·(s/a)·(q/b - 1)`, the right-hand side.
-/

namespace Work.FeitSibley.Coherence

open Classical

noncomputable section

/-- `h.H` normalises the derived subgroup `S' = ⁅S,S⁆` of `S`: `S ⊴ H` and the commutator
subgroup is characteristic. -/
theorem H_le_normalizer_FSScomm {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G) :
    h.H ≤ Subgroup.normalizer (FSScomm h : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [FSScomm, Subgroup.map_commutator]
  have hgS : g ∈ Subgroup.normalizer (h.S : Set G) := h.S_normal_in_H hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hgS
  rw [hgS]

/-- `|S' ⊔ Q₂| = |S'| · |Q₂|` for `Q₂ ≤ Q₁`.  Indeed `S' ≤ S` and `Q₂ ≤ Q₁` commute
elementwise (`h.commute`) and meet trivially (`S ⊓ Q₁ = ⊥`). -/
theorem card_sup_FSScomm_Q2 {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    (Q2 : Subgroup G) (hQ2 : Q2 ≤ h.Q1) :
    Nat.card ↥(FSScomm h ⊔ Q2) = Nat.card ↥(FSScomm h) * Nat.card ↥Q2 := by
  have hAleS : FSScomm h ≤ h.S :=
    (Subgroup.commutator_le_sup h.S h.S).trans (le_of_eq (sup_idem h.S))
  refine card_sup_eq_card_mul_card_of_commute
    (fun a ha b hb => h.commute a (hAleS ha) b (hQ2 hb)) ?_
  refine le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨hxa, hxb⟩ := Subgroup.mem_inf.mp hx
  have hmem : x ∈ h.S ⊓ h.Q1 := Subgroup.mem_inf.mpr ⟨hAleS hxa, hQ2 hxb⟩
  rw [h.S_inf_Q1] at hmem
  simpa using hmem

/-- `|H| = |D| · |S| · |Q₁|`, since `H = Q ⋊ D` and `Q = S × Q₁`. -/
theorem card_H_eq {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G) :
    Nat.card ↥h.H = Nat.card h.D * Nat.card h.S * Nat.card h.Q1 := by
  have hQcard : Nat.card ↥h.Q = Nat.card h.S * Nat.card h.Q1 := by
    rw [← h.S_sup_Q1]
    exact card_sup_eq_card_mul_card_of_commute
      (fun a ha b hb => h.commute a ha b hb) h.S_inf_Q1
  have hHcard : Nat.card ↥h.H = Nat.card h.D * Nat.card ↥h.Q := by
    have h1 := Subgroup.card_mul_index (h.Q.subgroupOf h.H)
    have hc : Nat.card ↥(h.Q.subgroupOf h.H) = Nat.card ↥h.Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.Q_le_H).toEquiv
    rw [hc, index_subgroupOf_Q h] at h1
    exact h1.symm.trans (Nat.mul_comm _ _)
  rw [hHcard, hQcard]
  ring

/-- The index of a subgroup, as a real number: `[H : K] = |H| / |K|`. -/
theorem index_eq_div {H : Type} [Group H] [Fintype H] (K : Subgroup H) :
    (K.index : ℝ) = (Nat.card H : ℝ) / (Nat.card ↥K : ℝ) := by
  have hpos : (Nat.card ↥K : ℝ) ≠ 0 := by
    have h : Nat.card ↥K ≠ 0 := (Nat.card_pos (α := ↥K)).ne'
    exact_mod_cast h
  rw [eq_div_iff hpos]
  exact_mod_cast (Subgroup.index_mul_card K)

theorem sum_deg_sq_scriptSR_sup {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    (Q2 : Subgroup G) (hQ2 : Q2 ≤ h.Q1) (hQ2n : h.H ≤ Subgroup.normalizer (Q2 : Set G)) :
    ∑ χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h ⊔ Q2), ((Work.CharCore.irrDeg χ : ℝ))^2
      = (Nat.card h.D : ℝ) * ((Nat.card h.S : ℝ) / (Nat.card (FSScomm h) : ℝ)) *
        ((Nat.card h.Q1 : ℝ) / (Nat.card ↥Q2 : ℝ) - 1) := by
  classical
  set A : Subgroup G := FSScomm h with hA
  have hAleS : A ≤ h.S := by
    rw [hA]
    exact (Subgroup.commutator_le_sup h.S h.S).trans (le_of_eq (sup_idem h.S))
  have hAleQ : A ≤ h.Q := hAleS.trans h.S_le_Q
  have hAleH : A ≤ h.H := hAleQ.trans h.Q_le_H
  have hQ2leQ : Q2 ≤ h.Q := hQ2.trans h.Q1_le_Q
  have hQ2leH : Q2 ≤ h.H := hQ2leQ.trans h.Q_le_H
  have hRleQ : A ⊔ Q2 ≤ h.Q := sup_le hAleQ hQ2leQ
  have hRleH : A ⊔ Q2 ≤ h.H := hRleQ.trans h.Q_le_H
  have hA1leH : A ⊔ h.Q1 ≤ h.H := sup_le hAleH h.Q1_le_H
  have hAHn : h.H ≤ Subgroup.normalizer (A : Set G) := by
    rw [hA]; exact H_le_normalizer_FSScomm h
  have hRn : h.H ≤ Subgroup.normalizer ((A ⊔ Q2 : Subgroup G) : Set G) :=
    (le_inf hAHn hQ2n).trans (Subgroup.inf_normalizer_le_normalizer_sup A Q2)
  -- the join with `Q₁` collapses because `Q₂ ≤ Q₁`
  have hsupQ1 : (A ⊔ Q2) ⊔ h.Q1 = A ⊔ h.Q1 := by
    rw [sup_assoc, sup_eq_right.mpr hQ2]
  -- cardinalities of the two relevant subgroups of `H`
  have hcardSubR : Nat.card ↥((A ⊔ Q2).subgroupOf h.H) = Nat.card ↥(A ⊔ Q2) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRleH).toEquiv
  have hcardSubR1 : Nat.card ↥((A ⊔ h.Q1).subgroupOf h.H) = Nat.card ↥(A ⊔ h.Q1) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA1leH).toEquiv
  have hcardR : Nat.card ↥(A ⊔ Q2) = Nat.card ↥A * Nat.card ↥Q2 :=
    card_sup_eq_card_mul_card_of_commute
      (fun a ha b hb => h.commute a (hAleS ha) b (hQ2 hb))
      (by
        refine le_antisymm ?_ bot_le
        intro x hx
        obtain ⟨hxa, hxb⟩ := Subgroup.mem_inf.mp hx
        have hmem : x ∈ h.S ⊓ h.Q1 := Subgroup.mem_inf.mpr ⟨hAleS hxa, hQ2 hxb⟩
        rw [h.S_inf_Q1] at hmem
        simpa using hmem)
  have hcardR1 : Nat.card ↥(A ⊔ h.Q1) = Nat.card ↥A * Nat.card ↥h.Q1 :=
    card_sup_eq_card_mul_card_of_commute
      (fun a ha b hb => h.commute a (hAleS ha) b hb)
      (by
        refine le_antisymm ?_ bot_le
        intro x hx
        obtain ⟨hxa, hxb⟩ := Subgroup.mem_inf.mp hx
        have hmem : x ∈ h.S ⊓ h.Q1 := Subgroup.mem_inf.mpr ⟨hAleS hxa, hxb⟩
        rw [h.S_inf_Q1] at hmem
        simpa using hmem)
  rw [sum_deg_sq_scriptSR h (A ⊔ Q2) hRleQ hRn, hsupQ1]
  rw [index_eq_div (H := ↥h.H) ((A ⊔ Q2).subgroupOf h.H),
      index_eq_div (H := ↥h.H) ((A ⊔ h.Q1).subgroupOf h.H)]
  rw [hcardSubR, hcardSubR1, hcardR, hcardR1, card_H_eq h]
  have ha : (Nat.card ↥A : ℝ) ≠ 0 := by
    have h : Nat.card ↥A ≠ 0 := (Nat.card_pos (α := ↥A)).ne'
    exact_mod_cast h
  have hb : (Nat.card ↥Q2 : ℝ) ≠ 0 := by
    have h : Nat.card ↥Q2 ≠ 0 := (Nat.card_pos (α := ↥Q2)).ne'
    exact_mod_cast h
  have hq : (Nat.card ↥h.Q1 : ℝ) ≠ 0 := by
    have h : Nat.card ↥h.Q1 ≠ 0 := (Nat.card_pos (α := ↥h.Q1)).ne'
    exact_mod_cast h
  push_cast
  field_simp

end

end Work.FeitSibley.Coherence
