import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.Basic

open Finset
open scoped BigOperators

namespace Work.NumberTheory.Chen.BTermCount

attribute [local instance] Classical.propDecidable

/-- Refined fibre bound: the number of `B`-term triples is at most the double sum over `(q, q₂)` of the number of primes `≤ (x+2)/(q q₂)`, where now `q₂ ≤ √((x+2)/q)` (because `q₂ ≤ q₃` and `q q₂ q₃ ≤ x+2` force `q₂² ≤ (x+2)/q`). -/
theorem bTripleCount_le_sum_pi_div (x M Y : ℕ) :
    bTripleCount x M Y ≤
      ∑ q ∈ (Finset.Icc M (Y - 1)).filter Nat.Prime,
        ∑ q₂ ∈ (Finset.Icc Y ((x + 2) / q).sqrt).filter Nat.Prime,
          (Nat.primesLE ((x + 2) / (q * q₂))).card := by
  rw [bTripleCount_eq_card]
  set S := bTripleSet x M Y with hS
  set T := (Finset.Icc M (Y - 1)).filter Nat.Prime with hT
  -- The number of triples with fixed first two components is at most the number of
  -- primes `≤ (x+2)/(q q₂)` (the third component injects into them).
  have hfiber : ∀ q q₂ : ℕ,
      (S.filter (fun t : ℕ × ℕ × ℕ => t.1 = q ∧ t.2.1 = q₂)).card
        ≤ (Nat.primesLE ((x + 2) / (q * q₂))).card := by
    intro q q₂
    refine Finset.card_le_card_of_injOn (fun t : ℕ × ℕ × ℕ => t.2.2) ?_ ?_
    · intro t ht
      simp only [Finset.mem_coe, Finset.mem_filter] at ht
      obtain ⟨htS, hq1, hq2⟩ := ht
      obtain ⟨hqp, hq₂p, hq₃p, -, -, -, hq₂q₃, hle⟩ := mem_bTripleSet.mp htS
      simp only [Finset.mem_coe, Nat.mem_primesLE]
      refine ⟨?_, hq₃p⟩
      have hpos : 0 < q * q₂ := by
        rw [← hq1, ← hq2]
        exact Nat.mul_pos hqp.pos hq₂p.pos
      rw [Nat.le_div_iff_mul_le hpos]
      calc t.2.2 * (q * q₂) = t.1 * t.2.1 * t.2.2 := by rw [hq1, hq2]; ring
        _ ≤ x + 2 := hle
    · intro t ht t' ht' h
      simp only [Finset.mem_coe, Finset.mem_filter] at ht ht'
      obtain ⟨-, h1, h2⟩ := ht
      obtain ⟨-, h1', h2'⟩ := ht'
      exact Prod.ext (h1.trans h1'.symm) (Prod.ext (h2.trans h2'.symm) h)
  -- For a fixed first component `q`, the second components lie in the shrunken range.
  have hinner : ∀ q : ℕ,
      (S.filter (fun t : ℕ × ℕ × ℕ => t.1 = q)).card
        ≤ ∑ q₂ ∈ (Finset.Icc Y ((x + 2) / q).sqrt).filter Nat.Prime,
            (Nat.primesLE ((x + 2) / (q * q₂))).card := by
    intro q
    set Sq := S.filter (fun t : ℕ × ℕ × ℕ => t.1 = q) with hSq
    have hdec : Sq.card = ∑ q₂ ∈ Sq.image (fun t : ℕ × ℕ × ℕ => t.2.1),
        (Sq.filter (fun t => t.2.1 = q₂)).card :=
      Finset.card_eq_sum_card_fiberwise (fun b hb => Finset.mem_image_of_mem _ hb)
    rw [hdec]
    have hsub : Sq.image (fun t : ℕ × ℕ × ℕ => t.2.1) ⊆
        (Finset.Icc Y ((x + 2) / q).sqrt).filter Nat.Prime := by
      intro q₂ hq₂
      rw [Finset.mem_image] at hq₂
      obtain ⟨t, ht, rfl⟩ := hq₂
      rw [hSq, Finset.mem_filter] at ht
      obtain ⟨htS, ht1⟩ := ht
      obtain ⟨hqp, hq₂p, -, -, -, hYq₂, hq₂q₃, hle⟩ := mem_bTripleSet.mp htS
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hYq₂, ?_⟩, hq₂p⟩
      have hqpos : 0 < q := by rw [← ht1]; exact hqp.pos
      rw [Nat.le_sqrt', Nat.le_div_iff_mul_le hqpos]
      calc t.2.1 ^ 2 * q = q * t.2.1 * t.2.1 := by ring
        _ ≤ q * t.2.1 * t.2.2 := Nat.mul_le_mul_left (q * t.2.1) hq₂q₃
        _ = t.1 * t.2.1 * t.2.2 := by rw [ht1]
        _ ≤ x + 2 := hle
    calc ∑ q₂ ∈ Sq.image (fun t : ℕ × ℕ × ℕ => t.2.1),
            (Sq.filter (fun t => t.2.1 = q₂)).card
        ≤ ∑ q₂ ∈ Sq.image (fun t : ℕ × ℕ × ℕ => t.2.1),
            (Nat.primesLE ((x + 2) / (q * q₂))).card := by
          apply Finset.sum_le_sum
          intro q₂ _
          have hfib : Sq.filter (fun t : ℕ × ℕ × ℕ => t.2.1 = q₂) =
              S.filter (fun t : ℕ × ℕ × ℕ => t.1 = q ∧ t.2.1 = q₂) := by
            rw [hSq, Finset.filter_filter]
          rw [hfib]
          exact hfiber q q₂
      _ ≤ ∑ q₂ ∈ (Finset.Icc Y ((x + 2) / q).sqrt).filter Nat.Prime,
            (Nat.primesLE ((x + 2) / (q * q₂))).card :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  have hdecomp : S.card =
      ∑ q ∈ S.image (fun t : ℕ × ℕ × ℕ => t.1), (S.filter (fun t => t.1 = q)).card :=
    Finset.card_eq_sum_card_fiberwise (fun b hb => Finset.mem_image_of_mem _ hb)
  rw [hdecomp]
  have hsub2 : S.image (fun t : ℕ × ℕ × ℕ => t.1) ⊆ T := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨t, ht, rfl⟩ := hq
    obtain ⟨hqp, -, -, hMq, hqY, -, -, -⟩ := mem_bTripleSet.mp ht
    rw [hT, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hMq, by omega⟩, hqp⟩
  calc ∑ q ∈ S.image (fun t : ℕ × ℕ × ℕ => t.1), (S.filter (fun t => t.1 = q)).card
      ≤ ∑ q ∈ S.image (fun t : ℕ × ℕ × ℕ => t.1),
          ∑ q₂ ∈ (Finset.Icc Y ((x + 2) / q).sqrt).filter Nat.Prime,
            (Nat.primesLE ((x + 2) / (q * q₂))).card :=
        Finset.sum_le_sum (fun q _ => hinner q)
    _ ≤ ∑ q ∈ T, ∑ q₂ ∈ (Finset.Icc Y ((x + 2) / q).sqrt).filter Nat.Prime,
            (Nat.primesLE ((x + 2) / (q * q₂))).card :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun _ _ _ => Nat.zero_le _)
    _ = ∑ q ∈ (Finset.Icc M (Y - 1)).filter Nat.Prime,
          ∑ q₂ ∈ (Finset.Icc Y ((x + 2) / q).sqrt).filter Nat.Prime,
            (Nat.primesLE ((x + 2) / (q * q₂))).card := by rw [hT]

end Work.NumberTheory.Chen.BTermCount
