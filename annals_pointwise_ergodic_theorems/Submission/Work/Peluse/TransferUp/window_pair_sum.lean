import Mathlib

/-!
# The window pair sum

`∑_{n=1}^{H} ∑_{m=1}^{H} Ψ (m - n) = ∑_{e=-(H-1)}^{H-1} (H - |e|) Ψ e`

the elementary change of variables `e = m - n` in which the multiplicity of the shift `e`
is the number of pairs `(n,m) ∈ [1,H]²` with `m - n = e`, namely `H - |e|`.
-/

namespace Work.Peluse.TransferUp

open Finset

/-- The set of pairs `(n,m)` in `[1,H]²` whose difference `m - n` is `e`. -/
@[reducible] private def fibre (H : ℕ) (e : ℤ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 H) ×ˢ (Finset.Icc 1 H)).filter
    (fun p : ℕ × ℕ => (p.2 : ℤ) - (p.1 : ℤ) = e)

private lemma mem_fibre_iff {H : ℕ} {e : ℤ} {p : ℕ × ℕ} :
    p ∈ fibre H e ↔ (1 ≤ p.1 ∧ p.1 ≤ H) ∧ (1 ≤ p.2 ∧ p.2 ≤ H) ∧
      (p.2 : ℤ) - (p.1 : ℤ) = e := by
  simp only [fibre, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  tauto

/-- Swapping the coordinates of a pair changes the sign of its difference. -/
private lemma swap_mem_fibre {H : ℕ} {a b : ℤ} (hab : a + b = 0) {p : ℕ × ℕ}
    (hp : p ∈ fibre H a) : Prod.swap p ∈ fibre H b := by
  obtain ⟨n, m⟩ := p
  rw [mem_fibre_iff] at hp ⊢
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · show (1 : ℕ) ≤ m; exact hp.2.1.1
  · show m ≤ H; exact hp.2.1.2
  · show (1 : ℕ) ≤ n; exact hp.1.1
  · show n ≤ H; exact hp.1.2
  · show ((n : ℤ) - (m : ℤ)) = b; omega

/-- For `e ≥ 0` the pairs of `[1,H]²` with `m - n = e` are in bijection with `[1, H-e]`
(through `n ↦ (n, n+e)`). -/
private lemma card_fiber_nonneg (H : ℕ) (e : ℤ) (he : 0 ≤ e) :
    (fibre H e).card = H - e.toNat := by
  have hme_of : ∀ n m : ℕ, (m : ℤ) - (n : ℤ) = e → m = n + e.toNat := by
    intro n m hd
    have h2 : (m : ℤ) = ((n + e.toNat : ℕ) : ℤ) := by
      push_cast; rw [Int.toNat_of_nonneg he]; omega
    exact_mod_cast h2
  have hcard : (fibre H e).card = (Finset.Icc 1 (H - e.toNat)).card := by
    apply Finset.card_bij (fun (p : ℕ × ℕ) (_ : p ∈ fibre H e) => p.1)
    · intro p hp
      rw [mem_fibre_iff] at hp
      rw [Finset.mem_Icc]
      exact ⟨hp.1.1, by have := hme_of p.1 p.2 hp.2.2; omega⟩
    · intro p hp q hq heq
      rw [mem_fibre_iff] at hp hq
      have h1 := hme_of p.1 p.2 hp.2.2
      have h2 := hme_of q.1 q.2 hq.2.2
      have heq' : p.1 = q.1 := heq
      ext <;> omega
    · intro n hn
      rw [Finset.mem_Icc] at hn
      refine ⟨(n, n + e.toNat), ?_, rfl⟩
      rw [mem_fibre_iff]
      refine ⟨⟨hn.1, by omega⟩, ⟨by omega, by omega⟩, ?_⟩
      push_cast; rw [Int.toNat_of_nonneg he]; ring
  rw [hcard, Nat.card_Icc]
  omega

/-- The number of pairs `(n,m) ∈ [1,H]²` with `m - n = e` is `H - |e|`, for every `e : ℤ`. -/
private lemma card_fiber (H : ℕ) (e : ℤ) : (fibre H e).card = H - e.natAbs := by
  by_cases he : 0 ≤ e
  · rw [card_fiber_nonneg H e he]
    have h1 : ((e.natAbs : ℤ)) = ((e.toNat : ℤ)) := by
      rw [Int.natAbs_of_nonneg he, Int.toNat_of_nonneg he]
    omega
  · have hlt : e < 0 := lt_of_not_ge he
    have hne : 0 ≤ -e := by omega
    have hcards : (fibre H e).card = (fibre H (-e)).card := by
      apply Finset.card_bij (fun (p : ℕ × ℕ) (_ : p ∈ fibre H e) => Prod.swap p)
      · intro p hp
        exact swap_mem_fibre (by ring) hp
      · intro p hp q hq heq
        rw [← Prod.swap_swap p, heq, Prod.swap_swap q]
      · intro q hq
        refine ⟨Prod.swap q, swap_mem_fibre (a := -e) (b := e) (by ring) hq, ?_⟩
        exact Prod.swap_swap q
    have ha : ((((-e).toNat : ℕ)) : ℤ) = -e := Int.toNat_of_nonneg hne
    have hb : ((((-e).natAbs : ℕ)) : ℤ) = -e := Int.natAbs_of_nonneg hne
    have hc : (-e).natAbs = e.natAbs := Int.natAbs_neg e
    rw [hcards, card_fiber_nonneg H (-e) hne]
    omega

/-- `∑_{n=1}^{H} ∑_{m=1}^{H} Ψ (m - n) = ∑_{e=-(H-1)}^{H-1} (H - |e|) Ψ e`. -/
theorem window_pair_sum (H : ℕ) (Ψ : ℤ → ℂ) :
    (Finset.Icc 1 H).sum (fun n => (Finset.Icc 1 H).sum (fun m => Ψ ((m : ℤ) - (n : ℤ))))
      = (Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1)).sum
          (fun e => (((H - e.natAbs : ℕ)) : ℂ) * Ψ e) := by
  have hmaps : ∀ p ∈ (Finset.Icc 1 H) ×ˢ (Finset.Icc 1 H),
      (p.2 : ℤ) - (p.1 : ℤ) ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1) := by
    intro p hp
    obtain ⟨n, m⟩ := p
    simp only [Finset.mem_product, Finset.mem_Icc] at hp ⊢
    obtain ⟨⟨hn1, hn2⟩, ⟨hm1, hm2⟩⟩ := hp
    constructor <;> omega
  rw [← Finset.sum_product (Finset.Icc 1 H) (Finset.Icc 1 H)
      (fun p : ℕ × ℕ => Ψ ((p.2 : ℤ) - (p.1 : ℤ)))]
  refine (Finset.sum_fiberwise_of_maps_to (s := (Finset.Icc 1 H) ×ˢ (Finset.Icc 1 H))
      (t := Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1))
      (g := fun p : ℕ × ℕ => (p.2 : ℤ) - (p.1 : ℤ)) hmaps
      (fun p : ℕ × ℕ => Ψ ((p.2 : ℤ) - (p.1 : ℤ)))).symm.trans ?_
  refine Finset.sum_congr rfl (fun e he => ?_)
  have hsum : (∑ p ∈ (Finset.Icc 1 H) ×ˢ (Finset.Icc 1 H) with
        (p.2 : ℤ) - (p.1 : ℤ) = e, Ψ ((p.2 : ℤ) - (p.1 : ℤ)))
      = (∑ p ∈ (Finset.Icc 1 H) ×ˢ (Finset.Icc 1 H) with
        (p.2 : ℤ) - (p.1 : ℤ) = e, Ψ e) := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.mem_filter] at hp
    rw [hp.2]
  have hconst : (∑ p ∈ (Finset.Icc 1 H) ×ˢ (Finset.Icc 1 H) with
        (p.2 : ℤ) - (p.1 : ℤ) = e, Ψ e)
      = (((fibre H e).card : ℕ) : ℂ) * Ψ e := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hsum, hconst, card_fiber H e]

end Work.Peluse.TransferUp
