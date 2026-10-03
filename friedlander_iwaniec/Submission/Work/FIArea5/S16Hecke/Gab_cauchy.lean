import Mathlib

/-!
# `Work.FIArea5.S16Hecke.Gab_cauchy`

The sequence `Gab a b` is the coefficient sequence of the four-fold product of geometric series
`1/((1-X)(1-aX)(1-bX)(1-abX))`; `Gab_cauchy` states this explicitly as the unrolled
coefficient sum.

The definitions `S` and `Gab` reproduced below are the ones of the shared local-factor module
`Submission.Work.FIArea5.S16Hecke.hecke_prod_local` (same names, same namespace, same bodies).
That module is currently not compilable -- an unrelated later lemma in it fails -- so it cannot be
imported; the definitions needed here are therefore carried locally, with identical bodies, so
that the names `Work.FIArea5.S16Hecke.S` and `Work.FIArea5.S16Hecke.Gab` resolve to exactly the
requested definitions.
-/

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators

noncomputable section

/-- `S a n = 1 + a + … + a^n`. -/
def S (a : ℝ) (n : ℕ) : ℝ := ∑ t ∈ Finset.range (n+1), a^t

/-- The coefficient sequence of `1/((1-X)(1-aX)(1-bX)(1-abX))`. -/
def Gab (a b : ℝ) (k : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (k/2+1), (a*b)^m * S a (k-2*m) * S b (k-2*m)

/-- The unrolled coefficient sequence of `1/((1-X)(1-aX)(1-bX)(1-abX))`: the sum over all
triples (n2,n3,n4) with n2+n3+n4 <= k of a^(n2+n4) * b^(n3+n4). -/
def L (a b : ℝ) (k : ℕ) : ℝ :=
  ∑ n2 ∈ Finset.range (k+1), ∑ n3 ∈ Finset.range (k+1), ∑ n4 ∈ Finset.range (k+1),
    (if n2 + n3 + n4 ≤ k then a^(n2+n4) * b^(n3+n4) else 0)

/-- S a t is the sum of a^i for i in range (t+1). -/
lemma Sshow (a : ℝ) (t : ℕ) : S a t = ∑ j ∈ Finset.range (t+1), a^j := rfl

/-- Regrouping a sum over the simplex n3 + n4 <= k by the value t = n3 + n4. -/
lemma simplex_reindex (k : ℕ) (H : ℕ → ℕ → ℝ) :
    (∑ n3 ∈ Finset.range (k+1), ∑ n4 ∈ Finset.range (k+1),
        (if n3 + n4 ≤ k then H n3 n4 else 0))
      = ∑ t ∈ Finset.range (k+1), ∑ n4 ∈ Finset.range (t+1), H (t - n4) n4 := by
  have hL1 : (∑ n3 ∈ Finset.range (k+1), ∑ n4 ∈ Finset.range (k+1),
        (if n3 + n4 ≤ k then H n3 n4 else 0))
      = ∑ p ∈ (Finset.range (k+1) ×ˢ Finset.range (k+1)),
          (if p.1 + p.2 ≤ k then H p.1 p.2 else 0) := by
    rw [Finset.sum_product]
  have hL2 : (∑ p ∈ (Finset.range (k+1) ×ˢ Finset.range (k+1)),
        (if p.1 + p.2 ≤ k then H p.1 p.2 else 0))
      = ∑ p ∈ (Finset.range (k+1) ×ˢ Finset.range (k+1)).filter (fun p => p.1 + p.2 ≤ k),
          H p.1 p.2 := by
    rw [Finset.sum_filter]
  have hR : (∑ t ∈ Finset.range (k+1), ∑ n4 ∈ Finset.range (t+1), H (t - n4) n4)
      = ∑ x ∈ (Finset.range (k+1)).sigma (fun tt => Finset.range (tt+1)), H (x.1 - x.2) x.2 := by
    rw [Finset.sum_sigma']
  rw [hL1, hL2, hR]
  refine Finset.sum_bij' (fun p _ => (⟨p.1 + p.2, p.2⟩ : Sigma (fun _ : ℕ => ℕ)))
      (fun x _ => (x.1 - x.2, x.2)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    simp only [Finset.mem_sigma, Finset.mem_range]
    exact ⟨by omega, by omega⟩
  · intro x hx
    have hx2 := Finset.mem_sigma.mp hx
    simp only [Finset.mem_range] at hx2
    obtain ⟨h1, h2⟩ := hx2
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨by omega, by omega⟩, by omega⟩
  · intro p hp
    simp only [Nat.add_sub_cancel]
  · intro x hx
    have hx2 := Finset.mem_sigma.mp hx
    simp only [Finset.mem_range] at hx2
    obtain ⟨h1, h2⟩ := hx2
    rw [Nat.sub_add_cancel (by omega : x.2 ≤ x.1)]
  · intro p hp
    simp only
    rw [Nat.add_sub_cancel]

/-- The n2 = 0 part of L: it equals sum_t b^t * S a t. -/
lemma Gzero (a b : ℝ) (k : ℕ) :
    (∑ n3 ∈ Finset.range (k+1), ∑ n4 ∈ Finset.range (k+1),
        (if n3 + n4 ≤ k then a^(n4)*b^(n3+n4) else 0))
      = ∑ t ∈ Finset.range (k+1), b^t * S a t := by
  rw [simplex_reindex k (fun n3 n4 => a^(n4)*b^(n3+n4))]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  rw [Sshow]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n4 hn4 => ?_)
  rw [Finset.mem_range] at hn4
  rw [Nat.sub_add_cancel (by omega : n4 ≤ t)]
  ring

/-- Pointwise form of the shift n2 -> n2 + 1 in the sum defining L. -/
lemma hpt (a b : ℝ) (k m n3 n4 : ℕ) (hm : m < k) :
    (if m + 1 + n3 + n4 ≤ k then a^(m+1+n4)*b^(n3+n4) else 0)
      = a * (if m + n3 + n4 ≤ k-1 then a^(m+n4)*b^(n3+n4) else 0) := by
  by_cases h : m + n3 + n4 ≤ k - 1
  · rw [if_pos h, if_pos (by omega : m+1+n3+n4 ≤ k)]
    have : m + 1 + n4 = (m+n4)+1 := by omega
    rw [this, pow_succ]
    ring
  · rw [if_neg h, if_neg (by omega : ¬ (m+1+n3+n4 ≤ k)), mul_zero]

/-- The n2 >= 1 part of L is a times L with k lowered by one. -/
lemma shift_lemma (a b : ℝ) (k : ℕ) :
    (∑ n2 ∈ Finset.range k, ∑ n3 ∈ Finset.range (k+1), ∑ n4 ∈ Finset.range (k+1),
        (if n2 + 1 + n3 + n4 ≤ k then a^(n2+1+n4)*b^(n3+n4) else 0))
      = a * (∑ n2 ∈ Finset.range k, ∑ n3 ∈ Finset.range k, ∑ n4 ∈ Finset.range k,
        (if n2 + n3 + n4 ≤ k-1 then a^(n2+n4)*b^(n3+n4) else 0)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n2 hn2 => ?_)
  rw [Finset.mem_range] at hn2
  rw [Finset.sum_range_succ]
  have hT : (∑ n4 ∈ Finset.range (k+1),
      (if n2 + 1 + k + n4 ≤ k then a^(n2+1+n4)*b^(k+n4) else 0)) = 0 := by
    apply Finset.sum_eq_zero; intro n4 hn4
    rw [if_neg (by omega : ¬ (n2 + 1 + k + n4 ≤ k))]
  rw [hT, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n3 hn3 => ?_)
  rw [Finset.mem_range] at hn3
  rw [Finset.sum_range_succ]
  have hT2 : (if n2 + 1 + n3 + k ≤ k then a^(n2+1+k)*b^(n3+k) else 0) = 0 := by
    rw [if_neg (by omega : ¬ (n2 + 1 + n3 + k ≤ k))]
  rw [hT2, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n4 hn4 => ?_)
  exact hpt a b k n2 n3 n4 hn2

/-- The key algebraic identity behind the telescoping. -/
lemma GsubE (a b : ℝ) (t : ℕ) :
    S a t * S b t - (∑ i ∈ Finset.range t, a^i)*(∑ j ∈ Finset.range t, b^j)
      = b^t*S a t + a^t*(∑ j ∈ Finset.range t, b^j) := by
  have ha : S a t = (∑ i ∈ Finset.range t, a^i) + a^t := by rw [S, Finset.sum_range_succ]
  have hb : S b t = (∑ j ∈ Finset.range t, b^j) + b^t := by rw [S, Finset.sum_range_succ]
  rw [ha, hb]
  ring

/-- Telescoping. -/
lemma telescope (a b : ℝ) (k : ℕ) :
    ∑ t ∈ Finset.range (k+1),
        (S a t * S b t - (∑ i ∈ Finset.range t, a^i)*(∑ j ∈ Finset.range t, b^j))
      = S a k * S b k := by
  set F : ℕ → ℝ := fun s => (∑ i ∈ Finset.range s, a^i)*(∑ j ∈ Finset.range s, b^j)
  have hFeval : ∀ s, F s = (∑ i ∈ Finset.range s, a^i)*(∑ j ∈ Finset.range s, b^j) :=
    fun s => rfl
  have hstep : ∀ t, S a t * S b t - (∑ i ∈ Finset.range t, a^i)*(∑ j ∈ Finset.range t, b^j)
      = F (t+1) - F t := by
    intro t
    rw [hFeval, hFeval, Sshow a t, Sshow b t]
  rw [Finset.sum_congr rfl (fun t _ => hstep t), Finset.sum_range_sub F (k+1)]
  rw [hFeval, hFeval]
  simp only [Finset.sum_range_zero, mul_zero, sub_zero]
  rw [Sshow a k, Sshow b k]

/-- Reindexing. -/
lemma reindex_Sb (a b : ℝ) (k : ℕ) :
    ∑ t ∈ Finset.range (k+1), a^t * (∑ j ∈ Finset.range t, b^j)
      = a * ∑ t ∈ Finset.range k, a^t * S b t := by
  rw [Finset.sum_range_succ']
  rw [Finset.sum_range_zero, mul_zero, add_zero]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  rw [Sshow]
  rw [pow_succ]
  ring

/-- Combining the telescoping with the n2 = 0 part. -/
lemma telescoping_final (a b : ℝ) (k : ℕ) :
    (∑ t ∈ Finset.range (k+1), b^t * S a t) + a * (∑ t ∈ Finset.range k, a^t * S b t)
      = S a k * S b k := by
  rw [← telescope a b k, ← reindex_Sb a b k, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  exact (GsubE a b t).symm

/-- The symmetry L a b k = L b a k. -/
lemma Lsym (a b : ℝ) (k : ℕ) : L a b k = L b a k := by
  unfold L
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  refine Finset.sum_congr rfl (fun y _ => ?_)
  refine Finset.sum_congr rfl (fun z _ => ?_)
  by_cases h : x + y + z ≤ k
  · rw [if_pos h, if_pos (by omega : y + x + z ≤ k), mul_comm]
  · rw [if_neg h, if_neg (by omega : ¬ (y + x + z ≤ k))]

/-- The two-step recurrence for the coefficient sequence of the product of geometric series. -/
lemma Gab_rec (a b : ℝ) (k : ℕ) (hk : 2 ≤ k) :
    Gab a b k = S a k * S b k + a * b * Gab a b (k - 2) := by
  have hdiv : (k - 2) / 2 + 1 = k / 2 := by omega
  have key : ∀ m : ℕ,
      (a*b)^(m+1) * S a (k - 2*(m+1)) * S b (k - 2*(m+1))
        = a*b*((a*b)^m * S a ((k-2) - 2*m) * S b ((k-2) - 2*m)) := by
    intro m
    rw [pow_succ']
    have h1 : k - 2*(m+1) = (k-2) - 2*m := by omega
    rw [h1]
    ring
  unfold Gab
  rw [Finset.sum_range_succ', hdiv]
  rw [Finset.sum_congr rfl (fun m hm => key m)]
  rw [← Finset.mul_sum]
  have : k - 0 = k := Nat.sub_zero k
  rw [this]
  ring

/-- Split of L according to n2 = 0 versus n2 >= 1. -/
lemma split1 (a b : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    L a b k = (∑ t ∈ Finset.range (k+1), b^t * S a t) + a * L a b (k-1) := by
  have hLHS : L a b k = (∑ n2 ∈ Finset.range k, ∑ n3 ∈ Finset.range (k+1),
        ∑ n4 ∈ Finset.range (k+1),
        (if n2 + 1 + n3 + n4 ≤ k then a^(n2+1+n4)*b^(n3+n4) else 0))
      + (∑ n3 ∈ Finset.range (k+1), ∑ n4 ∈ Finset.range (k+1),
        (if n3+n4 ≤ k then a^(n4)*b^(n3+n4) else 0)) := by
    unfold L
    rw [Finset.sum_range_succ' (fun n2 => ∑ n3 ∈ Finset.range (k+1),
        ∑ n4 ∈ Finset.range (k+1),
        (if n2+n3+n4≤k then a^(n2+n4)*b^(n3+n4) else 0)) k]
    simp only [Nat.zero_add]
  have hk1 : (∑ n2 ∈ Finset.range k, ∑ n3 ∈ Finset.range k, ∑ n4 ∈ Finset.range k,
        (if n2+n3+n4 ≤ k-1 then a^(n2+n4)*b^(n3+n4) else 0)) = L a b (k-1) := by
    unfold L
    rw [show (k-1)+1 = k from by omega]
  rw [hLHS, shift_lemma a b k, Gzero a b k, hk1]
  ring

/-- Split of L according to n3 = 0 versus n3 >= 1 (the mirror of split1). -/
lemma split1' (a b : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    L a b k = (∑ t ∈ Finset.range (k+1), a^t * S b t) + b * L a b (k-1) := by
  rw [Lsym a b k, split1 b a k hk, ← Lsym a b (k-1)]

/-- The two-step recurrence for L. -/
lemma L_rec (a b : ℝ) (k : ℕ) (hk : 2 ≤ k) :
    L a b k = S a k * S b k + a*b*L a b (k-2) := by
  have h1 := split1 a b k (by omega)
  have h2 := split1' a b (k-1) (by omega)
  rw [h1, h2]
  have hk2 : k - 1 - 1 = k - 2 := by omega
  have hk3 : k - 1 + 1 = k := by omega
  rw [hk2, hk3, mul_add, ← add_assoc, telescoping_final a b k]
  ring

theorem Gab_cauchy (a b : ℝ) (k : ℕ) :
    Gab a b k = ∑ n2 ∈ Finset.range (k+1), ∑ n3 ∈ Finset.range (k+1), ∑ n4 ∈ Finset.range (k+1),
      (if n2 + n3 + n4 ≤ k then a^(n2+n4) * b^(n3+n4) else 0) := by
  show Gab a b k = L a b k
  have key : ∀ k, Gab a b k = L a b k := fun k =>
    Nat.strongRecOn k (fun k ih => by
      match k with
      | 0 => simp [Gab, L, S]
      | 1 =>
        simp only [Gab, L, S, Finset.sum_range_succ, Finset.sum_range_zero]
        norm_num
        ring
      | n+2 =>
        rw [Gab_rec a b (n+2) (by omega), L_rec a b (n+2) (by omega)]
        rw [show n + 2 - 2 = n from by omega, ih n (by omega)])
  exact key k

end

end Work.FIArea5.S16Hecke
