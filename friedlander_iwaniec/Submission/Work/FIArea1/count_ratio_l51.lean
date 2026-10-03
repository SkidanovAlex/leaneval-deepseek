import Mathlib
import Submission.Work.FIArea1.l51_fibre_le
import Submission.Work.FIArea1.l51_sign_sum_le
import Submission.Work.FIArea1.l51_ratio_sum_pos

namespace Work.FIArea1

open Finset
open scoped BigOperators

/-- The `M` of the ratio parametrisation of `c₁²S₂ = c₂²S₁`: with `g = gcd(|c₁|,|c₂|)` the
solutions are `(t·(|c₁|/g)², t·(|c₂|/g)²)`, so the number of admissible `t` is `≍ K/M²`. -/
def ratioM (c₁ c₂ : ℤ) : ℕ :=
  max (c₁.natAbs / c₁.natAbs.gcd c₂.natAbs) (c₂.natAbs / c₁.natAbs.gcd c₂.natAbs)

/-- Membership in `s.product t`, in the `Finset.product` spelling: `Finset.mem_product` only
fires as a rewrite rule for the `×ˢ` spelling. -/
lemma mem_product_gen {α β : Type*} (s : Finset α) (t : Finset β) (p : α × β) :
    (p ∈ s.product t) ↔ (p.1 ∈ s ∧ p.2 ∈ t) :=
  Finset.mem_product

/-- `Finset.card_product` in the `Finset.product` spelling. -/
lemma card_product_gen {α β : Type*} (s : Finset α) (t : Finset β) :
    (s.product t).card = s.card * t.card :=
  Finset.card_product s t

/-- Membership in `s.filter p` with all arguments explicit. -/
lemma mem_filter_gen {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] (a : α) :
    (a ∈ s.filter p) ↔ (a ∈ s ∧ p a) :=
  Finset.mem_filter

/-- Membership in `(A × A) × (B × B)`, unfolded. -/
lemma mem_box4 (A B : Finset ℤ) (q : (ℤ × ℤ) × (ℤ × ℤ)) :
    (q ∈ (A.product A).product (B.product B)) ↔
      (q.1.1 ∈ A ∧ q.1.2 ∈ A ∧ q.2.1 ∈ B ∧ q.2.2 ∈ B) := by
  rw [mem_product_gen (A.product A) (B.product B) q, mem_product_gen A A q.1,
    mem_product_gen B B q.2]
  tauto

/-- **The degenerate `n* = 0` count for the off-diagonal of `FI` Lemma 5.1.** The number of
quadruples `(S₁,S₂,c₁,c₂)` with `S₁,S₂ ∈ [-K,K] ∖ {0}`, `|c₁|,|c₂| ≤ L` and
`c₁²·S₂ = c₂²·S₁` is at most `C·(K+1)·(K+1+L+1)`.

*Route.* For `(c₁,c₂) = (0,0)` all `(2K)²` pairs qualify. If exactly one of `c₁, c₂` is zero the
equation forces the corresponding `Sᵢ = 0`, which is erased, so there are no solutions. For
`c₁,c₂ ≠ 0` the solutions are `(S₁,S₂) = t·(c₁²/g, c₂²/g)` with `g = gcd(c₁,c₂)²` and
`|t| ≤ K·g/max(c₁²,c₂²)`, so at most `2K·g/max(c₁²,c₂²)` of them; here
`Σ_{|cᵢ| ≤ L} gcd(c₁,c₂)²/max(c₁²,c₂²) ≪ L` (group by `d = gcd(c₁,c₂)`, each `d` contributing
`≪ (L/d)·(L/d)/d²` summed as `Σ_d L²/d³·…`; numerically the sum is `≈ 1.73·L`). -/
theorem count_ratio_l51 : ∃ C : ℝ, 0 < C ∧ ∀ K L : ℕ,
    ((((((Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0).product
         ((Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0)).product
        (((Finset.Icc (-(L : ℤ)) (L : ℤ)).product (Finset.Icc (-(L : ℤ)) (L : ℤ)))))).filter
      (fun q : (ℤ × ℤ) × (ℤ × ℤ) => q.2.1 ^ 2 * q.1.2 = q.2.2 ^ 2 * q.1.1)).card
      ≤ C * ((K : ℝ) + 1) * ((K : ℝ) + 1 + ((L : ℝ) + 1)) := by
  refine ⟨100, by norm_num, fun K L => ?_⟩
  classical
  set A : Finset ℤ := (Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0 with hAdef
  set B : Finset ℤ := Finset.Icc (-(L : ℤ)) (L : ℤ) with hBdef
  set T : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
    ((A.product A).product (B.product B)).filter
      (fun q : (ℤ × ℤ) × (ℤ × ℤ) => q.2.1 ^ 2 * q.1.2 = q.2.2 ^ 2 * q.1.1) with hTdef
  set Fib : ℤ × ℤ → ℕ := fun cc =>
    ((A.product A).filter (fun ss : ℤ × ℤ => cc.1 ^ 2 * ss.2 = cc.2 ^ 2 * ss.1)).card
    with hFibdef
  -- ## Step 1: split `T` into the fibres over the pair `(c₁,c₂)`
  have hfiber : ∀ cc ∈ B.product B,
      (T.filter (fun q : (ℤ × ℤ) × (ℤ × ℤ) => q.2 = cc)).card = Fib cc := by
    intro cc hcc
    have hset : T.filter (fun q : (ℤ × ℤ) × (ℤ × ℤ) => q.2 = cc)
        = ((A.product A).filter
            (fun ss : ℤ × ℤ => cc.1 ^ 2 * ss.2 = cc.2 ^ 2 * ss.1)).image
              (fun ss => (ss, cc)) := by
      ext q
      rw [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hqT, hq2⟩
        obtain ⟨hqbox, hqcond⟩ := Finset.mem_filter.mp hqT
        obtain ⟨hqA1, hqA2, hqB1, hqB2⟩ := (mem_box4 A B q).mp hqbox
        refine ⟨q.1, ?_, Prod.ext rfl hq2.symm⟩
        exact (mem_filter_gen (A.product A)
          (fun ss : ℤ × ℤ => cc.1 ^ 2 * ss.2 = cc.2 ^ 2 * ss.1) q.1).mpr
          ⟨(mem_product_gen A A q.1).mpr ⟨hqA1, hqA2⟩, by rw [← hq2]; exact hqcond⟩
      · rintro ⟨ss, hss, hq⟩
        obtain ⟨hssBox, hssCond⟩ := Finset.mem_filter.mp hss
        obtain ⟨hss1, hss2⟩ := (mem_product_gen A A ss).mp hssBox
        obtain ⟨hcc1, hcc2⟩ := (mem_product_gen B B cc).mp hcc
        rw [← hq]
        exact ⟨(mem_filter_gen ((A.product A).product (B.product B))
              (fun q : (ℤ × ℤ) × (ℤ × ℤ) =>
                q.2.1 ^ 2 * q.1.2 = q.2.2 ^ 2 * q.1.1) (ss, cc)).mpr
              ⟨(mem_box4 A B (ss, cc)).mpr ⟨hss1, hss2, hcc1, hcc2⟩, hssCond⟩, rfl⟩
    have hinj : Function.Injective (fun ss : ℤ × ℤ => (ss, cc)) :=
      fun a b hab => (Prod.ext_iff.mp hab).1
    rw [hset, hFibdef]
    exact Finset.card_image_of_injective _ hinj
  have hdecomp : (T.card : ℝ) = ∑ cc ∈ B.product B, (Fib cc : ℝ) := by
    have hmaps : Set.MapsTo Prod.snd (↑T : Set ((ℤ × ℤ) × (ℤ × ℤ)))
        (↑(B.product B) : Set (ℤ × ℤ)) := by
      intro q hq
      obtain ⟨hqbox, hqcond⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqA1, hqA2, hqB1, hqB2⟩ := (mem_box4 A B q).mp hqbox
      exact (mem_product_gen B B q.2).mpr ⟨hqB1, hqB2⟩
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) hmaps, Nat.cast_sum]
    exact Finset.sum_congr rfl (fun cc hcc => by rw [hfiber cc hcc])
  -- ## Step 2: the `c₁c₂ = 0` part contributes exactly `Fib (0,0) = (#A)²`
  have hsplit : (∑ cc ∈ B.product B, (Fib cc : ℝ))
      = (∑ cc ∈ (B.product B).filter (fun cc : ℤ × ℤ => cc.1 ≠ 0 ∧ cc.2 ≠ 0), (Fib cc : ℝ))
        + (∑ cc ∈ (B.product B).filter (fun cc : ℤ × ℤ => ¬(cc.1 ≠ 0 ∧ cc.2 ≠ 0)),
            (Fib cc : ℝ)) :=
    (Finset.sum_filter_add_sum_filter_not (B.product B)
      (fun cc : ℤ × ℤ => cc.1 ≠ 0 ∧ cc.2 ≠ 0) (fun cc => (Fib cc : ℝ))).symm
  have hpos : (B.product B).filter (fun cc : ℤ × ℤ => cc.1 ≠ 0 ∧ cc.2 ≠ 0)
      = (B.erase 0).product (B.erase 0) := by
    ext cc
    rw [Finset.mem_filter, mem_product_gen B B cc, mem_product_gen (B.erase 0) (B.erase 0) cc,
      Finset.mem_erase, Finset.mem_erase]
    tauto
  have hFib0 : Fib (0, 0) = A.card * A.card := by
    have hkey : Fib (0, 0)
        = ((A.product A).filter
            (fun ss : ℤ × ℤ => (0 : ℤ) ^ 2 * ss.2 = (0 : ℤ) ^ 2 * ss.1)).card := rfl
    rw [hkey]
    have h1 : (A.product A).filter
        (fun ss : ℤ × ℤ => (0 : ℤ) ^ 2 * ss.2 = (0 : ℤ) ^ 2 * ss.1) = A.product A := by
      apply Finset.filter_true_of_mem
      intro ss hss
      simp
    rw [h1, card_product_gen A A]
  have hnotboth :
      (∑ cc ∈ (B.product B).filter (fun cc : ℤ × ℤ => ¬(cc.1 ≠ 0 ∧ cc.2 ≠ 0)),
        (Fib cc : ℝ)) ≤ (A.card : ℝ) ^ 2 := by
    have hmem : (0, 0) ∈ (B.product B).filter (fun cc : ℤ × ℤ => ¬(cc.1 ≠ 0 ∧ cc.2 ≠ 0)) := by
      rw [Finset.mem_filter]
      refine ⟨?_, by simp⟩
      rw [mem_product_gen B B (0, 0), hBdef]
      constructor <;> simp
    rw [Finset.sum_eq_single_of_mem (0, 0) hmem]
    · rw [hFib0, Nat.cast_mul, sq]
    · intro b hb hbne
      obtain ⟨hbB, hbnb⟩ := Finset.mem_filter.mp hb
      obtain ⟨hb1, hb2⟩ := (mem_product_gen B B b).mp hbB
      have hzero : Fib b = 0 := by
        have hcase : b.1 = 0 ∨ b.2 = 0 := by
          by_contra h
          push Not at h
          exact hbnb ⟨h.1, h.2⟩
        rcases hcase with h1 | h2
        · have hb2ne : b.2 ≠ 0 := fun h => hbne (Prod.ext h1 h)
          rw [hFibdef, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro ss hss
          have hss1 : ss.1 ≠ 0 := (Finset.mem_erase.mp ((mem_product_gen A A ss).mp hss).1).1
          rw [h1]
          intro hcon
          have h0 : b.2 ^ 2 * ss.1 = 0 := by rw [← hcon]; ring
          exact (mul_ne_zero (pow_ne_zero 2 hb2ne) hss1) h0
        · have hb1ne : b.1 ≠ 0 := fun h => hbne (Prod.ext h h2)
          rw [hFibdef, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro ss hss
          have hss2 : ss.2 ≠ 0 := (Finset.mem_erase.mp ((mem_product_gen A A ss).mp hss).2).1
          rw [h2]
          intro hcon
          have h0 : b.1 ^ 2 * ss.2 = 0 := by rw [hcon]; ring
          exact (mul_ne_zero (pow_ne_zero 2 hb1ne) hss2) h0
      rw [hzero, Nat.cast_zero]
  -- ## Step 3: on the both-nonzero part, use the fibre bound `Fib cc ≤ 3K/M²`
  have hbound1 : (∑ cc ∈ (B.erase 0).product (B.erase 0), (Fib cc : ℝ))
      ≤ ∑ cc ∈ (B.erase 0).product (B.erase 0),
          3 * (K : ℝ) / (ratioM cc.1 cc.2 : ℝ) ^ 2 := by
    apply Finset.sum_le_sum
    intro cc hcc
    obtain ⟨hc1, hc2⟩ := (mem_product_gen (B.erase 0) (B.erase 0) cc).mp hcc
    have hc1' : cc.1 ≠ 0 := (Finset.mem_erase.mp hc1).1
    have hc2' : cc.2 ≠ 0 := (Finset.mem_erase.mp hc2).1
    have h := l51_fibre_le K cc.1 cc.2 hc1' hc2'
    simpa only [hFibdef, ratioM, hAdef] using h
  have hbound2 : (∑ cc ∈ (B.erase 0).product (B.erase 0),
        3 * (K : ℝ) / (ratioM cc.1 cc.2 : ℝ) ^ 2)
      = 3 * (K : ℝ) * ∑ cc ∈ (B.erase 0).product (B.erase 0),
          1 / (ratioM cc.1 cc.2 : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro cc hcc
    rw [div_eq_mul_inv, one_div]
  have hbound3 : (∑ cc ∈ (B.erase 0).product (B.erase 0), 1 / (ratioM cc.1 cc.2 : ℝ) ^ 2)
      ≤ 32 * (L : ℝ) := by
    have hFnn : ∀ p ∈ (Finset.Icc 1 L).product (Finset.Icc 1 L),
        0 ≤ (1 : ℝ) / ((max (p.1 / p.1.gcd p.2) (p.2 / p.1.gcd p.2) : ℕ) : ℝ) ^ 2 := by
      intro p hp; positivity
    have hsign := l51_sign_sum_le L
      (fun p : ℕ × ℕ => (1 : ℝ) /
        ((max (p.1 / p.1.gcd p.2) (p.2 / p.1.gcd p.2) : ℕ) : ℝ) ^ 2) hFnn
    have hratio := l51_ratio_sum_pos L
    have hstep : (∑ cc ∈ (B.erase 0).product (B.erase 0), 1 / (ratioM cc.1 cc.2 : ℝ) ^ 2)
        ≤ 4 * ∑ p ∈ (Finset.Icc 1 L).product (Finset.Icc 1 L),
              (1 : ℝ) / ((max (p.1 / p.1.gcd p.2) (p.2 / p.1.gcd p.2) : ℕ) : ℝ) ^ 2 := by
      simpa only [hBdef, ratioM] using hsign
    linarith
  -- ## Step 4: assemble
  have hsum_le : (∑ cc ∈ B.product B, (Fib cc : ℝ))
      ≤ (A.card : ℝ) ^ 2 + 3 * (K : ℝ) * (32 * (L : ℝ)) := by
    have h1 : (∑ cc ∈ B.product B, (Fib cc : ℝ))
        = (∑ cc ∈ (B.erase 0).product (B.erase 0), (Fib cc : ℝ))
          + (∑ cc ∈ (B.product B).filter (fun cc : ℤ × ℤ => ¬(cc.1 ≠ 0 ∧ cc.2 ≠ 0)),
              (Fib cc : ℝ)) := by
      rw [hsplit, hpos]
    rw [h1]
    have h2 : (∑ cc ∈ (B.erase 0).product (B.erase 0), (Fib cc : ℝ))
        ≤ 3 * (K : ℝ) * (32 * (L : ℝ)) := by
      calc (∑ cc ∈ (B.erase 0).product (B.erase 0), (Fib cc : ℝ))
          ≤ ∑ cc ∈ (B.erase 0).product (B.erase 0),
              3 * (K : ℝ) / (ratioM cc.1 cc.2 : ℝ) ^ 2 := hbound1
        _ = 3 * (K : ℝ) * ∑ cc ∈ (B.erase 0).product (B.erase 0),
              1 / (ratioM cc.1 cc.2 : ℝ) ^ 2 := hbound2
        _ ≤ 3 * (K : ℝ) * (32 * (L : ℝ)) := by
              apply mul_le_mul_of_nonneg_left hbound3
              positivity
    linarith [h2, hnotboth]
  have hAcard : (A.card : ℝ) ≤ 2 * (K : ℝ) + 1 := by
    have h1 : (A.card : ℕ) ≤ 2 * K + 1 := by
      rw [hAdef]
      calc ((Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0).card
          ≤ (Finset.Icc (-(K : ℤ)) (K : ℤ)).card := Finset.card_erase_le
        _ = 2 * K + 1 := by
            rw [Int.card_Icc]
            have h2 : (K : ℤ) + 1 - (-(K : ℤ)) = ((2 * K + 1 : ℕ) : ℤ) := by push_cast; ring
            rw [h2, Int.toNat_natCast]
    exact_mod_cast h1
  have hfinal : (T.card : ℝ) ≤ 100 * ((K : ℝ) + 1) * ((K : ℝ) + 1 + ((L : ℝ) + 1)) := by
    have hA2 : (A.card : ℝ) ^ 2 ≤ (2 * (K : ℝ) + 1) ^ 2 := by
      have h0 : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
      nlinarith [hAcard, h0]
    have hbig : (2 * (K : ℝ) + 1) ^ 2 + 3 * (K : ℝ) * (32 * (L : ℝ))
        ≤ 100 * ((K : ℝ) + 1) * ((K : ℝ) + 1 + ((L : ℝ) + 1)) := by
      have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
      have hL : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
      nlinarith [hK, hL]
    linarith [hdecomp, hsum_le, hA2, hbig]
  exact hfinal

end Work.FIArea1
