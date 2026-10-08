import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise

namespace Work.ThmF.Prove

/-- **Generalized Noether second isomorphism theorem, index form.**
If `H` normalizes `N`, then the relative index of `N` in `H` and in `H ⊔ N`
coincide: `[H ⊔ N : N] = [H : H ⊓ N]`, expressed as
`N.relIndex (H ⊔ N) = N.relIndex H`.

This is the general form of `Subgroup.relIndex_sup_right`, which only assumes
`N` normal in the whole group; here we only need `H ≤ N_G(N)` (and `N ≤ N_G(N)`
is automatic). -/
lemma relIndex_sup_eq_of_le_normalizer {G : Type*} [Group G] {H N : Subgroup G}
    (h : H ≤ Subgroup.normalizer (N : Set G)) :
    N.relIndex (H ⊔ N) = N.relIndex H := by
  letI := Subgroup.normal_subgroupOf_of_le_normalizer h
  letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H N h).toEquiv.symm

theorem step9SylowW {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {V W P : Subgroup G} (hWleV : W ≤ V) (hWV : V ≤ Subgroup.normalizer (W : Set G))
    (hVcard : Nat.card ↥V = Nat.card ↥W * p)
    (hPV : P ≤ V) (hPcard : Nat.card ↥P = p) (hPW : P ⊓ W = ⊥)
    (S : Sylow p G) (hPS : P ≤ (S : Subgroup G)) (hSV : (S : Subgroup G) ≤ V) :
    ((S : Subgroup G) ⊓ W).relIndex (S : Subgroup G) = p ∧
      (S : Subgroup G) = ((S : Subgroup G) ⊓ W) ⊔ P := by
  -- `W` is normalized by both `S` and `P`, since both live inside `V ≤ N_G(W)`.
  have hS_N : (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G) := hSV.trans hWV
  have hP_N : P ≤ Subgroup.normalizer (W : Set G) := hPV.trans hWV
  have hWpos : 0 < Nat.card ↥W := Nat.card_pos
  -- (B) `W` has relative index `p` in `P`, because `P ⊓ W = ⊥` and `|P| = p`.
  have hBP : W.relIndex P = p := by
    rw [← Subgroup.inf_relIndex_right W P, inf_comm, hPW, Subgroup.relIndex_bot_left, hPcard]
  -- (C) the same relative index is unchanged when passing from `P` to `W ⊔ P`.
  have hCP : W.relIndex (W ⊔ P) = p := by
    rw [sup_comm, relIndex_sup_eq_of_le_normalizer hP_N, hBP]
  -- hence `W.index = p * (W ⊔ P).index`.
  have hidxWP : W.index = p * (W ⊔ P).index := by
    have h3 := Subgroup.relIndex_mul_index (le_sup_left : W ≤ W ⊔ P)
    rw [hCP] at h3
    exact h3.symm
  -- consequently `|W ⊔ P| = |W| * p = |V|`.
  have hcardWP : Nat.card ↥(W ⊔ P) = Nat.card ↥V := by
    have h1 := Subgroup.card_mul_index W
    have h2 := Subgroup.card_mul_index (W ⊔ P)
    have hne : (W ⊔ P).index ≠ 0 := by
      intro h0; rw [h0, mul_zero] at h2; exact Nat.card_pos.ne' h2.symm
    have hkey : Nat.card ↥W * (p * (W ⊔ P).index) = Nat.card ↥(W ⊔ P) * (W ⊔ P).index := by
      rw [← hidxWP, h1, h2]
    rw [← mul_assoc] at hkey
    have := Nat.mul_right_cancel (Nat.pos_of_ne_zero hne) hkey
    rw [← this, hVcard]
  -- and with `W ⊔ P ≤ V` this gives `V = W ⊔ P`.
  have hWP_eq : W ⊔ P = V :=
    Subgroup.eq_of_le_of_card_ge (sup_le hWleV hPV) (le_of_eq hcardWP.symm)
  -- (A) `W` has relative index `p` in `V`, by index arithmetic against `|V| = |W| * p`.
  have hA : W.relIndex V = p := by
    have h3 := Subgroup.relIndex_mul_index hWleV
    have hidxV : W.index = p * V.index := by
      have h1 := Subgroup.card_mul_index W
      have h2 := Subgroup.card_mul_index V
      have hkey : Nat.card ↥W * W.index = Nat.card ↥W * (p * V.index) := by
        rw [h1, ← h2, hVcard, mul_assoc]
      exact Nat.mul_left_cancel hWpos hkey
    rw [hidxV] at h3
    have hVidx : V.index ≠ 0 := by
      intro h0
      have h2 := Subgroup.card_mul_index V
      rw [h0, mul_zero] at h2
      exact Nat.card_pos.ne' h2.symm
    exact Nat.mul_right_cancel (Nat.pos_of_ne_zero hVidx) h3
  -- `P ≤ S` forces `S ⊔ W = V` (the only intermediate subgroup between `W` and `V`).
  have hSW : (S : Subgroup G) ⊔ W = V :=
    le_antisymm (sup_le hSV hWleV)
      (by rw [← hWP_eq]; exact sup_le le_sup_right (hPS.trans le_sup_left))
  -- therefore `[S : S ⊓ W] = [V : W] = p`.
  have hrelS : W.relIndex (S : Subgroup G) = p := by
    rw [← relIndex_sup_eq_of_le_normalizer hS_N, hSW, hA]
  refine ⟨?_, ?_⟩
  · -- `(S ⊓ W).relIndex S = W.relIndex S = p`
    rw [Subgroup.inf_relIndex_left (S : Subgroup G) W, hrelS]
  · -- `S = (S ⊓ W) ⊔ P`: both inclusions, using that every element of `V = W * P`
    -- is a product `w * p` with `w ∈ W`, `p ∈ P`.
    apply le_antisymm
    · intro x hx
      obtain ⟨w, hw, pp, hpp, hwpp⟩ : ∃ w ∈ W, ∃ pp ∈ P, w * pp = x := by
        have hmem0 : x ∈ (W ⊔ P : Subgroup G) := by rw [hWP_eq]; exact hSV hx
        have hmem1 : x ∈ (↑W : Set G) * (↑P : Set G) :=
          Subgroup.coe_mul_of_right_le_normalizer_left W P hP_N ▸ hmem0
        rw [Set.mem_mul] at hmem1
        exact hmem1
      have hwS : w ∈ (S : Subgroup G) := by
        have hwx : w = x * pp⁻¹ := by rw [← hwpp]; group
        rw [hwx]
        exact mul_mem hx (inv_mem (hPS hpp))
      have hwSW : w ∈ (S : Subgroup G) ⊓ W := ⟨hwS, hw⟩
      rw [← hwpp]
      exact mul_mem (Subgroup.mem_sup_left hwSW) (Subgroup.mem_sup_right hpp)
    · exact sup_le inf_le_left hPS

end Work.ThmF.Prove
