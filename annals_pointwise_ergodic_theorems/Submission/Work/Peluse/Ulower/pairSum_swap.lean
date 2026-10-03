import Mathlib
import Submission.Work.Peluse.Ulower.dense_le_defs

namespace Work.Peluse.Ulower

open scoped BigOperators

noncomputable section

/-!
# The swap `pairSum f A C = pairSum f C A` of the two index ranges

`pairSum f A C = ∑_{a,b ∈ A} ∑_x ‖∑_{k ∈ C} f (x+a+k)·conj (f (x+b+k))‖²` is the `x`-sum of
Peluse's level-two box sum with the outer index range `A` (used twice) and the inner index range
`C`.  Expanding the squared modulus of the inner sum and reordering the resulting *quadruple* sum
over `(a,b,k,l,x)` — the point of the box norm — shows that the roles of the two index ranges may
be interchanged:

`pairSum f A C = pairSum f C A`.

The only care needed is the `x`-sum: `f` is finitely supported, so every `x`-sum below is in fact
a finite sum over a fixed window `[-n,n]`, and the reordering of the quadruple sum is then an
elementary `Finset` manipulation (the `tsum` is replaced by the window sum once and for all).

The reordering is the same one as in `Work.Peluse.Concat.pair_sum_mono_mixed`: with
`Tf f a b k l x = f (x+a+k)·conj (f (x+b+k))·conj (f (x+a+l))·f (x+b+l)`, the expansion of the
square gives

`pairSum f A C = ∑_{a,b ∈ A} ∑_{k,l ∈ C} ∑_x Tf f a b k l x`,

and `Tf` is symmetric under the interchange of the two pairs `(a,b) ↔ (k,l)`.
-/

/-- `‖∑ g‖²`, as a complex number, is the double sum `∑_{i,j} g_i · conj(g_j)`. -/
private lemma ofReal_norm_sq_finset_sum {ι : Type*} (s : Finset ι) (g : ι → ℂ) :
    ((‖∑ i ∈ s, g i‖ ^ 2 : ℝ) : ℂ) = ∑ i ∈ s, ∑ j ∈ s, g i * star (g j) := by
  have hz : ((‖∑ i ∈ s, g i‖ ^ 2 : ℝ) : ℂ) =
      (∑ i ∈ s, g i) * star (∑ i ∈ s, g i) := by
    have h := Complex.mul_conj (∑ i ∈ s, g i)
    rw [Complex.normSq_eq_norm_sq] at h
    exact h.symm
  rw [hz, star_sum, Finset.sum_mul_sum]

/-- Pushing the cast `ℝ → ℂ` through a finite sum (one level). -/
private lemma ofReal_finset_sum {ι : Type*} (s : Finset ι) (F : ι → ℝ) :
    ((∑ i ∈ s, F i : ℝ) : ℂ) = ∑ i ∈ s, ((F i : ℝ) : ℂ) := by
  push_cast
  ring

/-- The summation window `[-n,n]`.  Every `x`-sum below is supported in it. -/
private def win (n : ℕ) : Finset ℤ := Finset.Icc (-(n : ℤ)) (n : ℤ)

/-- The fourfold product whose sums give both sides of the identity. -/
private def Tf (f : ℤ → ℂ) (a b k l x : ℤ) : ℂ :=
  f (x + a + k) * star (f (x + b + k)) * star (f (x + a + l)) * f (x + b + l)

/-- `f` vanishes on every shifted argument `x + a + k` with `a ∈ Q`, `k ∈ C` and `x` outside the
window `win n`, provided `n ≥ N + |a| + |k|` for all such `a, k`. -/
private lemma win_van (Q C : Finset ℤ) (f : ℤ → ℂ) (N : ℕ)
    (hN : ∀ x : ℤ, N < x.natAbs → f x = 0)
    {n : ℕ} (hn : ∀ a ∈ Q, ∀ k ∈ C, N + a.natAbs + k.natAbs ≤ n) :
    ∀ (a k x : ℤ), a ∈ Q → k ∈ C → x ∉ win n → f (x + a + k) = 0 := by
  intro a k x ha hk hx
  apply hN
  have hx' : x < -(n : ℤ) ∨ (n : ℤ) < x := by
    by_cases h : -(n : ℤ) ≤ x
    · right
      exact not_le.mp (not_and.mp (fun hh => hx (Finset.mem_Icc.mpr hh)) h)
    · left
      exact not_le.mp h
  have hnx : (n : ℤ) < (x.natAbs : ℤ) := by
    rcases hx' with h | h
    · have h2 : -x ≤ ((-x).natAbs : ℤ) := Int.le_natAbs
      rw [Int.natAbs_neg] at h2
      omega
    · have h2 : x ≤ (x.natAbs : ℤ) := Int.le_natAbs
      omega
  have htri : (x.natAbs : ℤ) ≤ ((x + a + k).natAbs : ℤ) + (a.natAbs : ℤ) + (k.natAbs : ℤ) := by
    have h1 := Int.natAbs_add_le (x + a + k) (-(a + k))
    rw [show x + a + k + -(a + k) = x by ring, Int.natAbs_neg] at h1
    have h2 := Int.natAbs_add_le a k
    omega
  have := hn a ha k hk
  omega

/-- **The reordering of the quadruple sum.**  Re-expanding the squared modulus in the other order
shows that the `x`-sum of squared moduli does not change when the roles of the two index ranges
`A` (outer pair) and `C` (inner index) are interchanged. -/
private lemma pair_swap_aux (f : ℤ → ℂ) (N : ℕ) (hN : Work.Peluse.SupportIn f N)
    (A C : Finset ℤ) :
    (∑ a ∈ A, ∑ b ∈ A, ∑' x : ℤ, ‖∑ k ∈ C, f (x + a + k) * star (f (x + b + k))‖ ^ 2)
      = ∑ k ∈ C, ∑ l ∈ C, ∑' x : ℤ,
          ‖∑ a ∈ A, f (x + k + a) * star (f (x + l + a))‖ ^ 2 := by
  classical
  -- the summation window
  set n : ℕ := N + (∑ a ∈ A, a.natAbs) + (∑ k ∈ C, k.natAbs) with hn
  have hnA : ∀ a ∈ A, ∀ k ∈ C, N + a.natAbs + k.natAbs ≤ n := by
    intro a ha k hk
    rw [hn]
    have h1 : a.natAbs ≤ ∑ a ∈ A, a.natAbs :=
      Finset.single_le_sum (fun i _ => Nat.zero_le _) ha
    have h2 : k.natAbs ≤ ∑ k ∈ C, k.natAbs :=
      Finset.single_le_sum (fun i _ => Nat.zero_le _) hk
    omega
  have hvan : ∀ (a k x : ℤ), a ∈ A → k ∈ C → x ∉ win n → f (x + a + k) = 0 :=
    win_van A C f N (fun x hx => hN x hx) hnA
  -- replace the two `tsum`s by finite sums over the window
  have hL : (∑ a ∈ A, ∑ b ∈ A, ∑' x : ℤ,
        ‖∑ k ∈ C, f (x + a + k) * star (f (x + b + k))‖ ^ 2)
      = ∑ a ∈ A, ∑ b ∈ A, ∑ x ∈ win n,
          ‖∑ k ∈ C, f (x + a + k) * star (f (x + b + k))‖ ^ 2 := by
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    exact tsum_eq_sum (s := win n) fun x hx => by
      have hz : (∑ k ∈ C, f (x + a + k) * star (f (x + b + k))) = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        rw [hvan a k x ha hk hx, zero_mul]
      rw [hz]
      simp
  have hR : (∑ k ∈ C, ∑ l ∈ C, ∑' x : ℤ,
        ‖∑ a ∈ A, f (x + k + a) * star (f (x + l + a))‖ ^ 2)
      = ∑ k ∈ C, ∑ l ∈ C, ∑ x ∈ win n,
          ‖∑ a ∈ A, f (x + a + k) * star (f (x + a + l))‖ ^ 2 := by
    refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl => ?_
    have hpt : ∀ x : ℤ, ‖∑ a ∈ A, f (x + k + a) * star (f (x + l + a))‖ ^ 2
        = ‖∑ a ∈ A, f (x + a + k) * star (f (x + a + l))‖ ^ 2 := by
      intro x
      have hs : (∑ a ∈ A, f (x + k + a) * star (f (x + l + a)))
          = ∑ a ∈ A, f (x + a + k) * star (f (x + a + l)) := by
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [show x + k + a = x + a + k by ring, show x + l + a = x + a + l by ring]
      rw [hs]
    rw [tsum_congr hpt]
    exact tsum_eq_sum (s := win n) fun x hx => by
      have hz : (∑ a ∈ A, f (x + a + k) * star (f (x + a + l))) = 0 := by
        refine Finset.sum_eq_zero fun a ha => ?_
        rw [hvan a k x ha hk hx, zero_mul]
      rw [hz]
      simp
  rw [hL, hR]
  apply Complex.ofReal_injective
  simp only [ofReal_finset_sum]
  -- expand each squared modulus
  have hLc : (∑ a ∈ A, ∑ b ∈ A, ∑ x ∈ win n,
        ((‖∑ k ∈ C, f (x + a + k) * star (f (x + b + k))‖ ^ 2 : ℝ) : ℂ))
      = ∑ a ∈ A, ∑ b ∈ A, ∑ x ∈ win n, ∑ k ∈ C, ∑ l ∈ C, Tf f a b k l x := by
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb =>
      Finset.sum_congr rfl fun x hx => ?_
    rw [ofReal_norm_sq_finset_sum C (fun k => f (x + a + k) * star (f (x + b + k)))]
    refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl => ?_
    simp only [Tf]
    rw [star_mul, star_star]
    ring
  have hRc : (∑ k ∈ C, ∑ l ∈ C, ∑ x ∈ win n,
        ((‖∑ a ∈ A, f (x + a + k) * star (f (x + a + l))‖ ^ 2 : ℝ) : ℂ))
      = ∑ k ∈ C, ∑ l ∈ C, ∑ x ∈ win n, ∑ a ∈ A, ∑ b ∈ A, Tf f a b k l x := by
    refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl =>
      Finset.sum_congr rfl fun x hx => ?_
    rw [ofReal_norm_sq_finset_sum A (fun a => f (x + a + k) * star (f (x + a + l)))]
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    simp only [Tf]
    rw [star_mul, star_star]
    ring
  -- group the two index pairs into product Finsets
  have hprodL : (∑ p ∈ A ×ˢ A, ∑ x ∈ win n, ∑ q ∈ C ×ˢ C, Tf f p.1 p.2 q.1 q.2 x)
      = ∑ a ∈ A, ∑ b ∈ A, ∑ x ∈ win n, ∑ k ∈ C, ∑ l ∈ C, Tf f a b k l x := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb =>
      Finset.sum_congr rfl fun x hx => ?_
    exact Finset.sum_product C C (fun q : ℤ × ℤ => Tf f a b q.1 q.2 x)
  have hprodR : (∑ q ∈ C ×ˢ C, ∑ x ∈ win n, ∑ p ∈ A ×ˢ A, Tf f p.1 p.2 q.1 q.2 x)
      = ∑ k ∈ C, ∑ l ∈ C, ∑ x ∈ win n, ∑ a ∈ A, ∑ b ∈ A, Tf f a b k l x := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl =>
      Finset.sum_congr rfl fun x hx => ?_
    exact Finset.sum_product A A (fun p : ℤ × ℤ => Tf f p.1 p.2 k l x)
  have hP : (∑ p ∈ A ×ˢ A, ∑ x ∈ win n, ∑ q ∈ C ×ˢ C, Tf f p.1 p.2 q.1 q.2 x)
      = ∑ q ∈ C ×ˢ C, ∑ x ∈ win n, ∑ p ∈ A ×ˢ A, Tf f p.1 p.2 q.1 q.2 x := by
    calc (∑ p ∈ A ×ˢ A, ∑ x ∈ win n, ∑ q ∈ C ×ˢ C, Tf f p.1 p.2 q.1 q.2 x)
        = ∑ p ∈ A ×ˢ A, ∑ q ∈ C ×ˢ C, ∑ x ∈ win n, Tf f p.1 p.2 q.1 q.2 x := by
          refine Finset.sum_congr rfl fun p hp => ?_
          exact Finset.sum_comm
      _ = ∑ q ∈ C ×ˢ C, ∑ p ∈ A ×ˢ A, ∑ x ∈ win n, Tf f p.1 p.2 q.1 q.2 x :=
          Finset.sum_comm
      _ = ∑ q ∈ C ×ˢ C, ∑ x ∈ win n, ∑ p ∈ A ×ˢ A, Tf f p.1 p.2 q.1 q.2 x := by
          refine Finset.sum_congr rfl fun q hq => ?_
          exact Finset.sum_comm
  calc (∑ a ∈ A, ∑ b ∈ A, ∑ x ∈ win n,
        ((‖∑ k ∈ C, f (x + a + k) * star (f (x + b + k))‖ ^ 2 : ℝ) : ℂ))
      = ∑ a ∈ A, ∑ b ∈ A, ∑ x ∈ win n, ∑ k ∈ C, ∑ l ∈ C, Tf f a b k l x := hLc
    _ = ∑ p ∈ A ×ˢ A, ∑ x ∈ win n, ∑ q ∈ C ×ˢ C, Tf f p.1 p.2 q.1 q.2 x := hprodL.symm
    _ = ∑ q ∈ C ×ˢ C, ∑ x ∈ win n, ∑ p ∈ A ×ˢ A, Tf f p.1 p.2 q.1 q.2 x := hP
    _ = ∑ k ∈ C, ∑ l ∈ C, ∑ x ∈ win n, ∑ a ∈ A, ∑ b ∈ A, Tf f a b k l x := hprodR
    _ = (∑ k ∈ C, ∑ l ∈ C, ∑ x ∈ win n,
        ((‖∑ a ∈ A, f (x + a + k) * star (f (x + a + l))‖ ^ 2 : ℝ) : ℂ)) := hRc.symm

theorem pairSum_swap {f : ℤ → ℂ} (hf : Work.Peluse.FinSuppZ f) (A C : Finset ℤ) :
    Work.Peluse.Ulower.pairSum f A C = Work.Peluse.Ulower.pairSum f C A := by
  obtain ⟨N, hN⟩ := hf
  rw [pairSum, pairSum]
  exact pair_swap_aux f N hN A C

end

end Work.Peluse.Ulower
