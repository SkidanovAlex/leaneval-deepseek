import Mathlib
import Submission.Work.CORE3.Defs

/-!
# `Work.CORE3.conj_mul_sq_mem_centralizer`

Let `V` be a Klein four-group (`Work.GW2.IsFourGroup V`), and let `t, t1 ∈ V` with `t ≠ 1`,
`t1 ≠ t`.  Let `x, g` normalize `V`, with

* `x t x⁻¹ = t` and `x t1 x⁻¹ = t · t1`  (so `x` acts on `V = {1, t, t1, t·t1}` as the
  transposition `t1 ↔ t·t1`, fixing `t`), and
* `g t g⁻¹ ≠ t` and `g (g t g⁻¹) g⁻¹ ≠ t` (so `g` permutes the three nonidentity elements of
  `V` without fixed points, i.e. as a 3-cycle).

Then `(x·g)²` centralizes `V`: in `Aut(V) ≅ S₃` the product of a transposition and a
3-cycle is again a transposition, hence has order `2`.

The proof is completely explicit.  Write `u = x·g` and `a = g t g⁻¹`.  Then `a ∈ V` and
`a ∉ {1, t}`, so `a ∈ {t1, t·t1}` (it suffices to know `V = {1, t, t1, t·t1}`, which holds
because the four displayed elements are distinct and lie in the four-element group `V`).
In either case `g t1 g⁻¹ = t · a` (the second hypothesis on `g` rules out the alternative),
whence `u t u⁻¹ = x a x⁻¹ = t · a` and `u t1 u⁻¹ = x (g t1 g⁻¹) x⁻¹ = a`, and therefore
`u² t u⁻² = (t·a)·a = t` and `u² t1 u⁻² = t1`.  Hence `u²` commutes with both `t` and
`t1`, and then also with `t·t1`; as `V = {1, t, t1, t·t1}`, this says `u² ∈ C_G(V)`.
-/

namespace Work.CORE3

open Subgroup

theorem conj_mul_sq_mem_centralizer {G : Type*} [Group G]
    {V : Subgroup G} {t t1 x g : G}
    (hV : Work.GW2.IsFourGroup V) (htV : t ∈ V) (ht1V : t1 ∈ V)
    (ht : t ≠ 1) (hne : t1 ≠ t)
    (hx : x ∈ Subgroup.normalizer (V : Set G))
    (hxt : x * t * x⁻¹ = t) (hxt1 : x * t1 * x⁻¹ = t * t1)
    (hg : g ∈ Subgroup.normalizer (V : Set G))
    (h1 : g * t * g⁻¹ ≠ t) (h2 : g * (g * t * g⁻¹) * g⁻¹ ≠ t) :
    (x * g) * (x * g) ∈ Subgroup.centralizer (V : Set G) := by
  -- Elementary facts about `V` and its two involutions `t, t1`.
  have ht2 : t ^ 2 = 1 := hV.2 t htV
  have ht1_2 : t1 ^ 2 = 1 := hV.2 t1 ht1V
  have ht2' : t * t = 1 := by simpa [pow_two] using ht2
  have ht1_2' : t1 * t1 = 1 := by simpa [pow_two] using ht1_2
  have ht1ne : t1 ≠ 1 := by
    intro h
    rw [h] at hxt1
    simp at hxt1
    exact ht hxt1.symm
  -- Distinctness of the four elements `1, t, t1, t·t1` of `V`.
  have htt1ne1 : t * t1 ≠ 1 := by
    intro h
    apply hne
    have h' := congrArg (fun z => t * z) h
    rw [mul_one] at h'
    rw [show t * (t * t1) = t1 from by rw [← mul_assoc, ht2', one_mul]] at h'
    exact h'
  have ht_ne_tt1 : t ≠ t * t1 := by
    intro h
    apply ht1ne
    have h' : t * 1 = t * t1 := by rw [mul_one]; exact h
    exact (mul_left_cancel h').symm
  have ht1_ne_tt1 : t1 ≠ t * t1 := by
    intro h
    apply ht
    have h' : 1 * t1 = t * t1 := by rw [one_mul]; exact h
    exact (mul_right_cancel h').symm
  -- Hence `V = {1, t, t1, t·t1}` (both sets have exactly four elements).
  have h2s : ({t1, t * t1} : Set G).ncard = 2 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_singleton]
    simpa only [Set.mem_singleton_iff] using ht1_ne_tt1
  have h3s : ({t, t1, t * t1} : Set G).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem, h2s]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hne.symm, ht_ne_tt1⟩
  have h4s : ({1, t, t1, t * t1} : Set G).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem, h3s]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨ht.symm, ht1ne.symm, htt1ne1.symm⟩
  have hVcard : (V : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hV.1
  have hsub : ({1, t, t1, t * t1} : Set G) ⊆ (V : Set G) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact V.one_mem
    · exact htV
    · exact ht1V
    · exact V.mul_mem htV ht1V
  haveI hVfin : Finite V := by
    rw [← not_infinite_iff_finite]
    intro hinf
    have h0 : Nat.card (↥V) = 0 := Nat.card_eq_zero_of_infinite
    rw [hV.1] at h0
    exact absurd h0 (by norm_num)
  have hVset : (V : Set G) = {1, t, t1, t * t1} :=
    (Set.eq_of_subset_of_ncard_le hsub (by rw [hVcard, h4s])).symm
  have hmemV : ∀ v : G, v ∈ V ↔ v = 1 ∨ v = t ∨ v = t1 ∨ v = t * t1 := by
    intro v
    show v ∈ (V : Set G) ↔ _
    rw [hVset]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  -- Membership of the `g`-conjugates in `V`.
  have hgtV : g * t * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hg t).mp htV
  have hgt1V : g * t1 * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hg t1).mp ht1V
  have hgt_ne1 : g * t * g⁻¹ ≠ 1 := by
    intro h
    apply ht
    have h' := congrArg (fun z => g⁻¹ * z * g) h
    have e1 : g⁻¹ * (g * t * g⁻¹) * g = t := by group
    have e0 : g⁻¹ * (1 : G) * g = 1 := by group
    rw [e1, e0] at h'
    exact h'
  have hgt1_ne1 : g * t1 * g⁻¹ ≠ 1 := by
    intro h
    apply ht1ne
    have h' := congrArg (fun z => g⁻¹ * z * g) h
    have e1 : g⁻¹ * (g * t1 * g⁻¹) * g = t1 := by group
    have e0 : g⁻¹ * (1 : G) * g = 1 := by group
    rw [e1, e0] at h'
    exact h'
  have hconj_inj : ∀ {a b : G}, g * a * g⁻¹ = g * b * g⁻¹ → a = b := by
    intro a b h
    exact mul_left_cancel (mul_right_cancel h)
  -- `a = g t g⁻¹` lies in `{t1, t·t1}`.
  have ha : g * t * g⁻¹ = t1 ∨ g * t * g⁻¹ = t * t1 := by
    rcases (hmemV (g * t * g⁻¹)).mp hgtV with h | h | h | h
    · exact absurd h hgt_ne1
    · exact absurd h h1
    · exact Or.inl h
    · exact Or.inr h
  have hx_tt1 : x * (t * t1) * x⁻¹ = t1 := by
    rw [show x * (t * t1) * x⁻¹ = (x * t * x⁻¹) * (x * t1 * x⁻¹) from by group,
      hxt, hxt1, ← mul_assoc, ht2', one_mul]
  set u : G := x * g with hu_def
  change u * u ∈ Subgroup.centralizer (V : Set G)
  -- The two cases for `a = g t g⁻¹`.
  have key : (u * u * t * (u * u)⁻¹ = t) ∧ (u * u * t1 * (u * u)⁻¹ = t1) := by
    rcases ha with ha | ha
    · -- Case `g t g⁻¹ = t1`.
      have hb : g * t1 * g⁻¹ = t * t1 := by
        rcases (hmemV (g * t1 * g⁻¹)).mp hgt1V with h | h | h | h
        · exact absurd h hgt1_ne1
        · exact (h2 (by rw [ha, h])).elim
        · exact absurd (hconj_inj (h.trans ha.symm)) hne
        · exact h
      have hu_t : u * t * u⁻¹ = t * t1 := by
        rw [show u * t * u⁻¹ = x * (g * t * g⁻¹) * x⁻¹ from by rw [hu_def]; group,
          ha, hxt1]
      have hu_t1 : u * t1 * u⁻¹ = t1 := by
        rw [show u * t1 * u⁻¹ = x * (g * t1 * g⁻¹) * x⁻¹ from by rw [hu_def]; group,
          hb, hx_tt1]
      exact ⟨by
          calc u * u * t * (u * u)⁻¹
              = u * (u * t * u⁻¹) * u⁻¹ := by group
            _ = u * (t * t1) * u⁻¹ := by rw [hu_t]
            _ = (u * t * u⁻¹) * (u * t1 * u⁻¹) := by group
            _ = (t * t1) * t1 := by rw [hu_t, hu_t1]
            _ = t := by rw [mul_assoc, ht1_2', mul_one], by
          have hcu : Commute u t1 := mul_inv_eq_iff_eq_mul.mp hu_t1
          have hc1 : (u * u) * t1 = t1 * (u * u) := hcu.mul_left hcu
          calc u * u * t1 * (u * u)⁻¹ = ((u * u) * t1) * (u * u)⁻¹ := by group
            _ = (t1 * (u * u)) * (u * u)⁻¹ := by rw [hc1]
            _ = t1 := by group⟩
    · -- Case `g t g⁻¹ = t · t1`.
      have hb : g * t1 * g⁻¹ = t := by
        rcases (hmemV (g * t1 * g⁻¹)).mp hgt1V with h | h | h | h
        · exact absurd h hgt1_ne1
        · exact h
        · exact (h2 (by
            rw [ha]
            rw [show g * (t * t1) * g⁻¹ = (g * t * g⁻¹) * (g * t1 * g⁻¹)
                  from by group, ha, h, mul_assoc, ht1_2', mul_one])).elim
        · exact absurd (hconj_inj (h.trans ha.symm)) hne
      have hu_t : u * t * u⁻¹ = t1 := by
        rw [show u * t * u⁻¹ = x * (g * t * g⁻¹) * x⁻¹ from by rw [hu_def]; group,
          ha, hx_tt1]
      have hu_t1 : u * t1 * u⁻¹ = t := by
        rw [show u * t1 * u⁻¹ = x * (g * t1 * g⁻¹) * x⁻¹ from by rw [hu_def]; group,
          hb, hxt]
      exact ⟨by
          calc u * u * t * (u * u)⁻¹
              = u * (u * t * u⁻¹) * u⁻¹ := by group
            _ = u * t1 * u⁻¹ := by rw [hu_t]
            _ = t := hu_t1, by
          calc u * u * t1 * (u * u)⁻¹
              = u * (u * t1 * u⁻¹) * u⁻¹ := by group
            _ = u * t * u⁻¹ := by rw [hu_t1]
            _ = t1 := hu_t⟩
  obtain ⟨h2t, h2t1⟩ := key
  -- Convert the conjugation identities into commutation with `u * u`.
  have hcomm_t : t * (u * u) = (u * u) * t := by
    have h := h2t
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hcomm_t1 : t1 * (u * u) = (u * u) * t1 := by
    have h := h2t1
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rcases (hmemV y).mp hy with rfl | rfl | rfl | rfl
  · rw [one_mul, mul_one]
  · exact hcomm_t
  · exact hcomm_t1
  · calc (t * t1) * (u * u) = t * (t1 * (u * u)) := by rw [mul_assoc]
      _ = t * ((u * u) * t1) := by rw [hcomm_t1]
      _ = (u * u) * (t * t1) := by
            rw [← mul_assoc t (u * u) t1, hcomm_t, mul_assoc]

end Work.CORE3
