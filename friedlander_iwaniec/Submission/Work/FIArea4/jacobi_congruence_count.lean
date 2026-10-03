import Mathlib

namespace Work.FIArea4

/-- The number of integers `≤ m` lying in a fixed residue class modulo `d` is at most `m / d + 1`. -/
lemma card_filter_mod_le (d m c : ℕ) (_hd : 0 < d) :
    ((Finset.Icc 1 m).filter (fun r => r % d = c)).card ≤ m / d + 1 := by
  have hinj : Set.InjOn (fun r => r / d)
      (↑((Finset.Icc 1 m).filter (fun r => r % d = c)) : Set ℕ) := by
    intro x hx y hy hxy
    have hxy' : x / d = y / d := hxy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hx hy
    calc x = d * (x / d) + x % d := (Nat.div_add_mod x d).symm
      _ = d * (y / d) + y % d := by rw [hxy', hx.2, hy.2]
      _ = y := Nat.div_add_mod y d
  have hcard := Finset.card_image_of_injOn hinj
  have hsub : (((Finset.Icc 1 m).filter (fun r => r % d = c)).image (fun r => r / d))
      ⊆ Finset.Icc 0 (m / d) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨r, hr, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_Icc] at hr
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.div_le_div_right hr.1.2⟩
  calc ((Finset.Icc 1 m).filter (fun r => r % d = c)).card
      = (((Finset.Icc 1 m).filter (fun r => r % d = c)).image (fun r => r / d)).card :=
        hcard.symm
    _ ≤ (Finset.Icc 0 (m / d)).card := Finset.card_le_card hsub
    _ = m / d + 1 := by simp [Nat.card_Icc]

/-- Decompose a filtered product by its second coordinate. -/
lemma card_filter_product_eq_sum_snd {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (P : α × β → Prop) [DecidablePred P] :
    ((A.product B).filter P).card
      = ∑ s ∈ B, (A.filter (fun r => P (r, s))).card := by
  rw [Finset.product_eq_sprod]
  have hmap : Set.MapsTo Prod.snd
      (↑((A ×ˢ B).filter P) : Set (α × β)) (↑B : Set β) := by
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
    exact hp.1.2
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  refine Finset.sum_congr rfl ?_
  intro s hs
  have hinj : Set.InjOn Prod.fst
      (↑(((A ×ˢ B).filter P).filter (fun p => p.2 = s)) : Set (α × β)) := by
    intro p hp q hq hpq
    simp only [Finset.mem_coe, Finset.mem_filter] at hp hq
    exact Prod.ext hpq (by rw [hp.2, hq.2])
  have himg : (((A ×ˢ B).filter P).filter (fun p => p.2 = s)).image Prod.fst
      = A.filter (fun r => P (r, s)) := by
    ext r
    constructor
    · intro hr
      rcases Finset.mem_image.mp hr with ⟨p, hp, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      exact Finset.mem_filter.mpr ⟨hp.1.1.1, by rw [← hp.2]; exact hp.1.2⟩
    · intro hr
      rw [Finset.mem_filter] at hr
      exact Finset.mem_image.mpr ⟨(r, s),
        Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hr.1, hs⟩, hr.2⟩, rfl⟩, rfl⟩
  rw [← himg, Finset.card_image_of_injOn hinj]

/-- Decompose a filtered product by its first coordinate. -/
lemma card_filter_product_eq_sum_fst {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (P : α × β → Prop) [DecidablePred P] :
    ((A.product B).filter P).card
      = ∑ r ∈ A, (B.filter (fun s => P (r, s))).card := by
  rw [Finset.product_eq_sprod]
  have hmap : Set.MapsTo Prod.fst
      (↑((A ×ˢ B).filter P) : Set (α × β)) (↑A : Set α) := by
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
    exact hp.1.1
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  refine Finset.sum_congr rfl ?_
  intro r hr
  have hinj : Set.InjOn Prod.snd
      (↑(((A ×ˢ B).filter P).filter (fun p => p.1 = r)) : Set (α × β)) := by
    intro p hp q hq hpq
    simp only [Finset.mem_coe, Finset.mem_filter] at hp hq
    exact Prod.ext (by rw [hp.2, hq.2]) hpq
  have himg : (((A ×ˢ B).filter P).filter (fun p => p.1 = r)).image Prod.snd
      = B.filter (fun s => P (r, s)) := by
    ext s
    constructor
    · intro hs'
      rcases Finset.mem_image.mp hs' with ⟨p, hp, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      exact Finset.mem_filter.mpr ⟨hp.1.1.2, by rw [← hp.2]; exact hp.1.2⟩
    · intro hs'
      rw [Finset.mem_filter] at hs'
      exact Finset.mem_image.mpr ⟨(r, s),
        Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hr, hs'.1⟩, hs'.2⟩, rfl⟩, rfl⟩
  rw [← himg, Finset.card_image_of_injOn hinj]

/-- **Lemma 11.2 of Friedlander–Iwaniec** (the elementary count used for the local variance
`E(d)`: "For `(a,b,d) = 1` the number `N_d(R,S)` of solutions to `a r ≡ b s (mod d)` in positive
integers `r ≤ R`, `s ≤ S` satisfies `N_d(R,S) ≤ d^{-1}RS + √(RS)`").  We state it with the two
extra summands `Nat.sqrt (R*S) + 2` and in `ℕ`-arithmetic, which is all the applications need. -/
theorem jacobi_congruence_count (d R S a b : ℕ) (hd : 0 < d)
    (hab : Nat.Coprime a b) (had : Nat.Coprime a d) (hbd : Nat.Coprime b d) :
    (((Finset.Icc 1 R).product (Finset.Icc 1 S)).filter
        (fun p : ℕ × ℕ => (a * p.1) % d = (b * p.2) % d)).card
      ≤ (R * S) / d + Nat.sqrt (R * S) + 2 := by
  set N : ℕ := (((Finset.Icc 1 R).product (Finset.Icc 1 S)).filter
        (fun p : ℕ × ℕ => (a * p.1) % d = (b * p.2) % d)).card with hN
  -- Per-`s` bound: the `r ≤ R` satisfying `a r ≡ b s (mod d)` all lie in one residue class.
  have hA : ∀ s ∈ Finset.Icc 1 S,
      ((Finset.Icc 1 R).filter (fun r => (a * r) % d = (b * s) % d)).card ≤ R / d + 1 := by
    intro s _
    by_cases hne : ((Finset.Icc 1 R).filter (fun r => (a * r) % d = (b * s) % d)).Nonempty
    · obtain ⟨r0, hr0⟩ := hne
      have hsub : (Finset.Icc 1 R).filter (fun r => (a * r) % d = (b * s) % d) ⊆
          (Finset.Icc 1 R).filter (fun r => r % d = r0 % d) := by
        intro r hr
        simp only [Finset.mem_filter, Finset.mem_Icc] at hr hr0 ⊢
        refine ⟨hr.1, ?_⟩
        have hmod : (a * r) ≡ (a * r0) [MOD d] := by
          simp only [Nat.ModEq]; exact hr.2.trans hr0.2.symm
        have hcancel : r ≡ r0 [MOD d] :=
          Nat.ModEq.cancel_left_of_coprime (m := d) (c := a)
            (by simpa only [Nat.Coprime] using had.symm) hmod
        simpa only [Nat.ModEq] using hcancel
      calc ((Finset.Icc 1 R).filter (fun r => (a * r) % d = (b * s) % d)).card
          ≤ ((Finset.Icc 1 R).filter (fun r => r % d = r0 % d)).card := Finset.card_le_card hsub
        _ ≤ R / d + 1 := card_filter_mod_le d R (r0 % d) hd
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      exact Nat.zero_le _
  -- Symmetric per-`r` bound, using `(b,d) = 1`.
  have hB : ∀ r ∈ Finset.Icc 1 R,
      ((Finset.Icc 1 S).filter (fun s => (a * r) % d = (b * s) % d)).card ≤ S / d + 1 := by
    intro r _
    by_cases hne : ((Finset.Icc 1 S).filter (fun s => (a * r) % d = (b * s) % d)).Nonempty
    · obtain ⟨s0, hs0⟩ := hne
      have hsub : (Finset.Icc 1 S).filter (fun s => (a * r) % d = (b * s) % d) ⊆
          (Finset.Icc 1 S).filter (fun s => s % d = s0 % d) := by
        intro s hs
        simp only [Finset.mem_filter, Finset.mem_Icc] at hs hs0 ⊢
        refine ⟨hs.1, ?_⟩
        have hmod : (b * s) ≡ (b * s0) [MOD d] := by
          simp only [Nat.ModEq]; rw [← hs.2, hs0.2]
        have hcancel : s ≡ s0 [MOD d] :=
          Nat.ModEq.cancel_left_of_coprime (m := d) (c := b)
            (by simpa only [Nat.Coprime] using hbd.symm) hmod
        simpa only [Nat.ModEq] using hcancel
      calc ((Finset.Icc 1 S).filter (fun s => (a * r) % d = (b * s) % d)).card
          ≤ ((Finset.Icc 1 S).filter (fun s => s % d = s0 % d)).card := Finset.card_le_card hsub
        _ ≤ S / d + 1 := card_filter_mod_le d S (s0 % d) hd
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      exact Nat.zero_le _
  have h1 : N ≤ (R * S) / d + S := by
    rw [hN, card_filter_product_eq_sum_snd]
    have hSR : S * (R / d) ≤ (R * S) / d := by
      calc S * (R / d) ≤ S * R / d := Nat.mul_div_le_mul_div_assoc S R d
        _ = R * S / d := by rw [Nat.mul_comm S R]
    calc ∑ s ∈ Finset.Icc 1 S, ((Finset.Icc 1 R).filter (fun r => (a * r) % d = (b * s) % d)).card
        ≤ ∑ _s ∈ Finset.Icc 1 S, (R / d + 1) := Finset.sum_le_sum hA
      _ = S * (R / d + 1) := by rw [Finset.sum_const, Nat.card_Icc]; simp
      _ = S * (R / d) + S := by ring
      _ ≤ (R * S) / d + S := add_le_add_left hSR S
  have h2 : N ≤ (R * S) / d + R := by
    rw [hN, card_filter_product_eq_sum_fst]
    have hRS : R * (S / d) ≤ (R * S) / d := Nat.mul_div_le_mul_div_assoc R S d
    calc ∑ r ∈ Finset.Icc 1 R, ((Finset.Icc 1 S).filter (fun s => (a * r) % d = (b * s) % d)).card
        ≤ ∑ _r ∈ Finset.Icc 1 R, (S / d + 1) := Finset.sum_le_sum hB
      _ = R * (S / d + 1) := by rw [Finset.sum_const, Nat.card_Icc]; simp
      _ = R * (S / d) + R := by ring
      _ ≤ (R * S) / d + R := add_le_add_left hRS R
  rcases le_total R S with hRS' | hSR'
  · have hR : R ≤ Nat.sqrt (R * S) := Nat.le_sqrt.mpr (Nat.mul_le_mul_left R hRS')
    calc N ≤ (R * S) / d + R := h2
      _ ≤ (R * S) / d + Nat.sqrt (R * S) := add_le_add_right hR _
      _ ≤ (R * S) / d + Nat.sqrt (R * S) + 2 := Nat.le_add_right _ _
  · have hS : S ≤ Nat.sqrt (R * S) := Nat.le_sqrt.mpr (Nat.mul_le_mul_right S hSR')
    calc N ≤ (R * S) / d + S := h1
      _ ≤ (R * S) / d + Nat.sqrt (R * S) := add_le_add_right hS _
      _ ≤ (R * S) / d + Nat.sqrt (R * S) + 2 := Nat.le_add_right _ _

end Work.FIArea4
