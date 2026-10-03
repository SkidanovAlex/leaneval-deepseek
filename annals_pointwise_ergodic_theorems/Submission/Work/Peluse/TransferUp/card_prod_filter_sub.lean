import Mathlib

namespace Work.Peluse.TransferUp

/-- Cardinality of `Icc 1 n` inside `ℤ`, with `n : ℕ`. -/
private lemma card_Icc_one_int (n : ℕ) : (Finset.Icc (1 : ℤ) (n : ℤ)).card = n := by
  rw [Int.card_Icc]; simp

theorem card_prod_filter_sub {H : ℕ} {m : ℤ}
    (hm : m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1)) :
    (((Finset.Icc (1 : ℤ) (H : ℤ)).product (Finset.Icc (1 : ℤ) (H : ℤ))).filter
        (fun p : ℤ × ℤ => p.2 - p.1 = m)).card = H - m.natAbs := by
  obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
  by_cases hm0 : (0 : ℤ) ≤ m
  · -- case `m ≥ 0`: the pairs are the graph of `a ↦ a + m` over `a ∈ Icc 1 (H - m)`
    have hle : m.natAbs ≤ H := by omega
    have hcast : (H : ℤ) - m = ((H - m.natAbs : ℕ) : ℤ) := by
      have hk : m = (m.natAbs : ℤ) := (Int.natAbs_of_nonneg hm0).symm
      conv_lhs => rw [hk]
      exact (Nat.cast_sub hle).symm
    have hset : (((Finset.Icc (1 : ℤ) (H : ℤ)).product (Finset.Icc (1 : ℤ) (H : ℤ))).filter
          (fun p : ℤ × ℤ => p.2 - p.1 = m))
        = (Finset.Icc (1 : ℤ) ((H : ℤ) - m)).image (fun a => (a, a + m)) := by
      ext p
      obtain ⟨a, b⟩ := p
      constructor
      · intro h
        rw [Finset.mem_filter] at h
        obtain ⟨hp, hsub⟩ := h
        rw [Finset.product_eq_sprod, Finset.mem_product] at hp
        obtain ⟨ha, hb⟩ := hp
        rw [Finset.mem_Icc] at ha hb
        rw [Finset.mem_image]
        refine ⟨a, ?_, ?_⟩
        · rw [Finset.mem_Icc]; exact ⟨ha.1, by omega⟩
        · rw [Prod.mk.injEq]; exact ⟨rfl, by omega⟩
      · intro h
        rw [Finset.mem_image] at h
        obtain ⟨x, hx, hxy⟩ := h
        rw [Finset.mem_Icc] at hx
        rw [Prod.mk.injEq] at hxy
        obtain ⟨rfl, rfl⟩ := hxy
        have h1 : x ∈ Finset.Icc (1 : ℤ) (H : ℤ) := by
          rw [Finset.mem_Icc]; exact ⟨hx.1, by omega⟩
        have h2 : x + m ∈ Finset.Icc (1 : ℤ) (H : ℤ) := by
          rw [Finset.mem_Icc]; exact ⟨by omega, by omega⟩
        have h3 : (x, x + m) ∈
            (Finset.Icc (1 : ℤ) (H : ℤ)).product (Finset.Icc (1 : ℤ) (H : ℤ)) := by
          rw [Finset.product_eq_sprod, Finset.mem_product]; exact ⟨h1, h2⟩
        rw [Finset.mem_filter]
        exact ⟨h3, by omega⟩
    have hcard : ((Finset.Icc (1 : ℤ) ((H : ℤ) - m)).image (fun a => (a, a + m))).card
        = (Finset.Icc (1 : ℤ) ((H : ℤ) - m)).card :=
      Finset.card_image_of_injective _ (fun a b h => congr_arg Prod.fst h)
    rw [hset, hcard, hcast, card_Icc_one_int]
  · -- case `m < 0`: the pairs are the graph of `b ↦ b - m` over `b ∈ Icc 1 (H + m)`
    have hm0' : m < 0 := not_le.mp hm0
    have hle : m.natAbs ≤ H := by omega
    have hcast : (H : ℤ) + m = ((H - m.natAbs : ℕ) : ℤ) := by
      have hk : m = -((m.natAbs : ℤ)) := by
        have h : (m.natAbs : ℤ) = -m := by rw [Int.natCast_natAbs, abs_of_neg hm0']
        omega
      conv_lhs => rw [hk]
      rw [Nat.cast_sub hle]; ring
    have hset : (((Finset.Icc (1 : ℤ) (H : ℤ)).product (Finset.Icc (1 : ℤ) (H : ℤ))).filter
          (fun p : ℤ × ℤ => p.2 - p.1 = m))
        = (Finset.Icc (1 : ℤ) ((H : ℤ) + m)).image (fun b => (b - m, b)) := by
      ext p
      obtain ⟨a, b⟩ := p
      constructor
      · intro h
        rw [Finset.mem_filter] at h
        obtain ⟨hp, hsub⟩ := h
        rw [Finset.product_eq_sprod, Finset.mem_product] at hp
        obtain ⟨ha, hb⟩ := hp
        rw [Finset.mem_Icc] at ha hb
        rw [Finset.mem_image]
        refine ⟨b, ?_, ?_⟩
        · rw [Finset.mem_Icc]; exact ⟨hb.1, by omega⟩
        · rw [Prod.mk.injEq]; exact ⟨by omega, rfl⟩
      · intro h
        rw [Finset.mem_image] at h
        obtain ⟨x, hx, hxy⟩ := h
        rw [Finset.mem_Icc] at hx
        rw [Prod.mk.injEq] at hxy
        obtain ⟨rfl, rfl⟩ := hxy
        have h1 : x - m ∈ Finset.Icc (1 : ℤ) (H : ℤ) := by
          rw [Finset.mem_Icc]; exact ⟨by omega, by omega⟩
        have h2 : x ∈ Finset.Icc (1 : ℤ) (H : ℤ) := by
          rw [Finset.mem_Icc]; exact ⟨hx.1, by omega⟩
        have h3 : (x - m, x) ∈
            (Finset.Icc (1 : ℤ) (H : ℤ)).product (Finset.Icc (1 : ℤ) (H : ℤ)) := by
          rw [Finset.product_eq_sprod, Finset.mem_product]; exact ⟨h1, h2⟩
        rw [Finset.mem_filter]
        exact ⟨h3, by omega⟩
    have hcard : ((Finset.Icc (1 : ℤ) ((H : ℤ) + m)).image (fun b => (b - m, b))).card
        = (Finset.Icc (1 : ℤ) ((H : ℤ) + m)).card :=
      Finset.card_image_of_injective _ (fun a b h => congr_arg Prod.snd h)
    rw [hset, hcard, hcast, card_Icc_one_int]

end Work.Peluse.TransferUp
