import Mathlib
import Submission.Work.FIArea1.boxZ_dvd_count_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea1

open Finset

/-- The symmetric interval `[-N,N] ⊆ ℤ` meets a fixed residue class modulo `m > 0` in at most
`2N/m + 1` points.  (This is the sharp form of `int_card_mod_le`, whose bound is `2N/m + 2`; the
extra unit matters for the fibre count of *FI* Lemma 5.1.) -/
lemma int_card_zmod_le (N m : ℕ) (hm : 0 < m) (c : ZMod m) :
    ((Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun x : ℤ => (x : ZMod m) = c)).card
      ≤ 2 * N / m + 1 := by
  set t : ℕ := (c + (N : ZMod m)).val with ht
  have hmain : ((Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun x : ℤ => (x : ZMod m) = c)).card
      ≤ ((Finset.Icc 0 (2 * N)).filter (fun y => y % m = t)).card := by
    apply Finset.card_le_card_of_injOn (fun x : ℤ => (x + (N : ℤ)).toNat)
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hx ⊢
      obtain ⟨⟨hlo, hhi⟩, hc⟩ := hx
      have h0 : (0 : ℤ) ≤ x + (N : ℤ) := by omega
      refine ⟨⟨Nat.zero_le _, ?_⟩, ?_⟩
      · rw [Int.toNat_le]
        push_cast
        omega
      · have hzm : (((x + (N : ℤ)).toNat : ℕ) : ZMod m) = c + (N : ZMod m) := by
          rw [show ((((x + (N : ℤ)).toNat : ℕ)) : ZMod m) = ((x + (N : ℤ) : ℤ) : ZMod m) from by
                rw [← Int.toNat_of_nonneg h0]; norm_cast]
          push_cast [hc]; ring
        rw [ht, ← ZMod.val_natCast m ((x + (N : ℤ)).toNat)]
        exact congrArg ZMod.val hzm
    · intro x1 hx1 x2 hx2 h
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hx1 hx2
      dsimp only at h
      have h0a : (0 : ℤ) ≤ x1 + (N : ℤ) := by omega
      have h0b : (0 : ℤ) ≤ x2 + (N : ℤ) := by omega
      have e1 : ((x1 + (N : ℤ)).toNat : ℤ) = x1 + (N : ℤ) := Int.toNat_of_nonneg h0a
      have e2 : ((x2 + (N : ℤ)).toNat : ℤ) = x2 + (N : ℤ) := Int.toNat_of_nonneg h0b
      have hh : ((x1 + (N : ℤ)).toNat : ℤ) = ((x2 + (N : ℤ)).toNat : ℤ) := by rw [h]
      omega
  exact hmain.trans (nat_card_mod_le (2 * N) m t hm)

/-- Two solutions `(r₁,r₂)`, `(r₁',r₂')` of the same equation `r₁S₂ - r₂S₁ = d` have their first
coordinates congruent modulo `S₁.natAbs`.  This is where coprimality of `S₁, S₂` is used: the
difference of two solutions is a multiple of `(S₁, S₂)`, so its first coordinate is a multiple of
`S₁`. -/
lemma fibre_residue_eq {S₁ S₂ : ℤ} (hcop : IsCoprime S₁ S₂) {d : ℤ} {p q : ℤ × ℤ}
    (hp : p.1 * S₂ - p.2 * S₁ = d) (hq : q.1 * S₂ - q.2 * S₁ = d) :
    (p.1 : ZMod S₁.natAbs) = (q.1 : ZMod S₁.natAbs) := by
  have hkey : (p.1 - q.1) * S₂ = (p.2 - q.2) * S₁ := by linarith
  have hdvd : S₁ ∣ (p.1 - q.1) * S₂ := ⟨p.2 - q.2, by rw [hkey]; ring⟩
  have hdvd2 : S₁ ∣ (p.1 - q.1) := IsCoprime.dvd_of_dvd_mul_right hcop hdvd
  have hdvd3 : (S₁.natAbs : ℤ) ∣ (p.1 - q.1) :=
    (Int.natAbs_dvd (a := S₁) (b := p.1 - q.1)).mpr hdvd2
  have hzero : ((p.1 - q.1 : ℤ) : ZMod S₁.natAbs) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (p.1 - q.1) S₁.natAbs).mpr hdvd3
  push_cast at hzero
  exact sub_eq_zero.mp hzero

/-- **Fibre count for the off-diagonal of FI Lemma 5.1.** For coprime `S₁, S₂` with `S₁ ≠ 0`, the
integer pairs `(r₁,r₂)` in the box `|rᵢ| ≤ K` with `r₁S₂ - r₂S₁ = Δ̃ ≠ 0`, summed over the
divisors `Δ̃` of a fixed nonzero `N₀`, number at most `2·τ(|N₀|)·(2K/|S₁|+1)`; here `τ(m) = m.divisors.card`.

*Route:* for each admissible `Δ̃` the solutions of `r₁S₂ - r₂S₁ = Δ̃` form a coset of `ℤ(S₁,S₂)`
(the coprimality makes `(S₁,S₂)` generate the kernel), so at most `⌊2K/|S₁|⌋+1` of them have
`|r₁| ≤ K`; the number of nonzero divisors `Δ̃` of `N₀` is at most `2·τ(|N₀|)`. -/
theorem fibre_count_l51 (K : ℕ) (S₁ S₂ : ℤ) (hS₁ : S₁ ≠ 0)
    (hcop : Nat.Coprime S₁.natAbs S₂.natAbs) (N₀ : ℤ) (hN₀ : N₀ ≠ 0) :
    ((((Finset.Icc (-(K : ℤ)) (K : ℤ)).product (Finset.Icc (-(K : ℤ)) (K : ℤ))).filter
        (fun p : ℤ × ℤ => p.1 * S₂ - p.2 * S₁ ≠ 0 ∧ (p.1 * S₂ - p.2 * S₁) ∣ N₀)).card)
      ≤ 2 * N₀.natAbs.divisors.card * (2 * K / S₁.natAbs + 1) := by
  classical
  have hm : 0 < S₁.natAbs := Int.natAbs_pos.mpr hS₁
  have hcop' : IsCoprime S₁ S₂ := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs]; exact hcop
  set B : Finset (ℤ × ℤ) :=
    (Finset.Icc (-(K : ℤ)) (K : ℤ)).product (Finset.Icc (-(K : ℤ)) (K : ℤ)) with hBdef
  have hfiber : ∀ d : ℤ,
      (B.filter (fun p : ℤ × ℤ => p.1 * S₂ - p.2 * S₁ = d)).card ≤ 2 * K / S₁.natAbs + 1 := by
    intro d
    by_cases hem : (B.filter (fun p : ℤ × ℤ => p.1 * S₂ - p.2 * S₁ = d)) = ∅
    · rw [hem]; simp
    · obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr hem
      rw [hBdef] at hp₀
      simp only [Finset.mem_filter, Finset.mem_product, Finset.product_eq_sprod,
        Finset.mem_Icc] at hp₀
      obtain ⟨⟨hp₀1, hp₀2⟩, hp₀d⟩ := hp₀
      have hle : (B.filter (fun p : ℤ × ℤ => p.1 * S₂ - p.2 * S₁ = d)).card
          ≤ ((Finset.Icc (-(K : ℤ)) (K : ℤ)).filter
              (fun x : ℤ => (x : ZMod S₁.natAbs) = (p₀.1 : ZMod S₁.natAbs))).card := by
        apply Finset.card_le_card_of_injOn (fun p : ℤ × ℤ => p.1)
        · intro p hp
          simp only [Finset.mem_coe, Finset.mem_filter, hBdef, Finset.mem_product,
            Finset.product_eq_sprod, Finset.mem_Icc] at hp ⊢
          obtain ⟨⟨hp1, hp2⟩, hpd⟩ := hp
          exact ⟨⟨hp1.1, hp1.2⟩, fibre_residue_eq hcop' hpd hp₀d⟩
        · intro p hp q hq hpq
          simp only [Finset.mem_coe, Finset.mem_filter, hBdef, Finset.mem_product,
            Finset.product_eq_sprod, Finset.mem_Icc] at hp hq
          obtain ⟨⟨hp1, hp2⟩, hpd⟩ := hp
          obtain ⟨⟨hq1, hq2⟩, hqd⟩ := hq
          have h1 : p.1 = q.1 := hpq
          have h2 : p.2 = q.2 := by
            have hthis : p.2 * S₁ = q.2 * S₁ := by
              rw [h1] at hpd; linarith
            exact mul_right_cancel₀ hS₁ hthis
          exact Prod.ext h1 h2
      exact hle.trans (int_card_zmod_le K S₁.natAbs hm (p₀.1 : ZMod S₁.natAbs))
  set T : Finset (ℤ × ℤ) := B.filter (fun p : ℤ × ℤ =>
      p.1 * S₂ - p.2 * S₁ ≠ 0 ∧ (p.1 * S₂ - p.2 * S₁) ∣ N₀) with hTdef
  have hsub : T ⊆ N₀.divisors.biUnion
      (fun d : ℤ => B.filter (fun p : ℤ × ℤ => p.1 * S₂ - p.2 * S₁ = d)) := by
    intro p hp
    simp only [hTdef, Finset.mem_filter, Finset.mem_biUnion] at hp ⊢
    obtain ⟨hpB, hne, hdiv⟩ := hp
    exact ⟨p.1 * S₂ - p.2 * S₁, Int.mem_divisors.mpr ⟨hdiv, hN₀⟩, hpB, rfl⟩
  calc T.card ≤ (N₀.divisors.biUnion
          (fun d : ℤ => B.filter (fun p : ℤ × ℤ => p.1 * S₂ - p.2 * S₁ = d))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ d ∈ N₀.divisors,
          (B.filter (fun p : ℤ × ℤ => p.1 * S₂ - p.2 * S₁ = d)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ d ∈ N₀.divisors, (2 * K / S₁.natAbs + 1) :=
        Finset.sum_le_sum (fun d _ => hfiber d)
    _ = N₀.divisors.card * (2 * K / S₁.natAbs + 1) :=
        Finset.sum_const_nat (fun _ _ => rfl)
    _ = 2 * N₀.natAbs.divisors.card * (2 * K / S₁.natAbs + 1) := by
        rw [Int.divisors, Finset.card_disjUnion, Finset.card_map, Finset.card_map]; ring

end Work.FIArea1
