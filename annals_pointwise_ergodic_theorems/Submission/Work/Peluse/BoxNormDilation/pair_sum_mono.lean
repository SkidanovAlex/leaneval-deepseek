/-
# Monotonicity of the pair sum in the dilation comparison for Peluse's box norms

This file proves `Work.Peluse.BoxNormDilation.pair_sum_mono`, the comparison step used in
`Submission/Work/Peluse/BoxNormDilation/dilated_directions_ge.lean`.

## The mathematics

The quantity

`P(Q, C) = ∑_{a,b ∈ Q} ∑_{x ∈ ℤ} ‖∑_{k ∈ C} f(x+a+k)·conj(f(x+b+k))‖²`

is *monotone* in the second argument `C` (and, as it happens, is also symmetric in the sense
described below).  The point is that the *inner* index range `C` and the *outer* index range `Q`
play symmetric roles after re-expanding the square: writing

`T(a,b,k,l,x) = f(x+a+k)·conj(f(x+b+k))·conj(f(x+a+l))·f(x+b+l)`,

one has

`‖∑_{k ∈ C} f(x+a+k)·conj(f(x+b+k))‖² = ∑_{k,l ∈ C} T(a,b,k,l,x)`

(expand `z·conj z` and use `Finset.sum_mul_sum`), and equally

`‖∑_{a ∈ Q} f(x+a+k)·conj(f(x+a+l))‖² = ∑_{a,b ∈ Q} T(a,b,k,l,x)`

— the very same `T`, by commutativity of `ℂ`.  Consequently `P(Q,C)` does not change when the
roles of `Q` and `C` are interchanged:

`P(Q, C) = ∑_{k,l ∈ C} ∑_{x} ‖∑_{a ∈ Q} f(x+a+k)·conj(f(x+a+l))‖²`,

and in this form the monotonicity in `C` is immediate: all the summands are nonnegative and the
index range grows from `Q×Q` to `C×C`.

Everything is a finite sum: `f` is finitely supported (`FinSuppZ`), so each `x`-sum is supported
in the window `win n` with `n = N + ∑_{a∈Q} |a| + ∑_{k∈C} |k|`, where `f` vanishes off `[-N,N]`.

## Formalisation notes

The reindexing `∑_{a,b} ∑_x ∑_{k,l} T = ∑_{k,l} ∑_x ∑_{a,b} T` is performed by first grouping the
index pairs `(a,b)` and `(k,l)` into product Finsets (`Finset.sum_product`, which is applied in the
direction *from* the product sum so that the `rw` pattern is a genuine single sum).  The `ℂ`-level
identity is transferred to `ℝ` with `Complex.ofReal_injective`.
-/
import Mathlib
import Submission.Work.Peluse.Basic

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.BoxNormDilation

noncomputable section

/-! ## Elementary expansions and the summation window -/

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

/-! ## The interchange of the two index ranges -/

/-- Re-expanding in the other order shows that the `x`-sum of the squared norms does not change
when the roles of the two index ranges `Q` (outer pair) and `C` (inner index) are interchanged. -/
private lemma pair_swap (Q C : Finset ℤ) (f : ℤ → ℂ) (N : ℕ)
    (hN : Work.Peluse.SupportIn f N) :
    (∑ a ∈ Q, ∑ b ∈ Q, ∑' x : ℤ, ‖∑ k ∈ C, f (x + a + k) * star (f (x + b + k))‖ ^ 2)
      = ∑ k ∈ C, ∑ l ∈ C, ∑' x : ℤ,
          ‖∑ a ∈ Q, f (x + a + k) * star (f (x + a + l))‖ ^ 2 := by
  classical
  -- the summation window
  set n : ℕ := N + (∑ a ∈ Q, a.natAbs) + (∑ k ∈ C, k.natAbs) with hn
  have hn' : ∀ a ∈ Q, ∀ k ∈ C, N + a.natAbs + k.natAbs ≤ n := by
    intro a ha k hk
    rw [hn]
    have h1 : a.natAbs ≤ ∑ a ∈ Q, a.natAbs :=
      Finset.single_le_sum (fun i _ => Nat.zero_le _) ha
    have h2 : k.natAbs ≤ ∑ k ∈ C, k.natAbs :=
      Finset.single_le_sum (fun i _ => Nat.zero_le _) hk
    omega
  have hvan : ∀ (a k x : ℤ), a ∈ Q → k ∈ C → x ∉ win n → f (x + a + k) = 0 :=
    win_van Q C f N (fun x hx => hN x hx) hn'
  -- replace the two `tsum`s by finite sums over the window
  have hL : (∑ a ∈ Q, ∑ b ∈ Q, ∑' x : ℤ,
        ‖∑ k ∈ C, f (x + a + k) * star (f (x + b + k))‖ ^ 2)
      = ∑ a ∈ Q, ∑ b ∈ Q, ∑ x ∈ win n,
          ‖∑ k ∈ C, f (x + a + k) * star (f (x + b + k))‖ ^ 2 := by
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    exact tsum_eq_sum (s := win n) fun x hx => by
      have hz : (∑ k ∈ C, f (x + a + k) * star (f (x + b + k))) = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        rw [hvan a k x ha hk hx, zero_mul]
      rw [hz]
      simp
  have hR : (∑ k ∈ C, ∑ l ∈ C, ∑' x : ℤ,
        ‖∑ a ∈ Q, f (x + a + k) * star (f (x + a + l))‖ ^ 2)
      = ∑ k ∈ C, ∑ l ∈ C, ∑ x ∈ win n,
          ‖∑ a ∈ Q, f (x + a + k) * star (f (x + a + l))‖ ^ 2 := by
    refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl => ?_
    exact tsum_eq_sum (s := win n) fun x hx => by
      have hz : (∑ a ∈ Q, f (x + a + k) * star (f (x + a + l))) = 0 := by
        refine Finset.sum_eq_zero fun a ha => ?_
        rw [hvan a k x ha hk hx, zero_mul]
      rw [hz]
      simp
  rw [hL, hR]
  apply Complex.ofReal_injective
  simp only [ofReal_finset_sum]
  -- expand each squared norm
  have hLc : (∑ a ∈ Q, ∑ b ∈ Q, ∑ x ∈ win n,
        ((‖∑ k ∈ C, f (x + a + k) * star (f (x + b + k))‖ ^ 2 : ℝ) : ℂ))
      = ∑ a ∈ Q, ∑ b ∈ Q, ∑ x ∈ win n, ∑ k ∈ C, ∑ l ∈ C, Tf f a b k l x := by
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb =>
      Finset.sum_congr rfl fun x hx => ?_
    rw [ofReal_norm_sq_finset_sum C (fun k => f (x + a + k) * star (f (x + b + k)))]
    refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl => ?_
    simp only [Tf]
    rw [star_mul, star_star]
    ring
  have hRc : (∑ k ∈ C, ∑ l ∈ C, ∑ x ∈ win n,
        ((‖∑ a ∈ Q, f (x + a + k) * star (f (x + a + l))‖ ^ 2 : ℝ) : ℂ))
      = ∑ k ∈ C, ∑ l ∈ C, ∑ x ∈ win n, ∑ a ∈ Q, ∑ b ∈ Q, Tf f a b k l x := by
    refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl =>
      Finset.sum_congr rfl fun x hx => ?_
    rw [ofReal_norm_sq_finset_sum Q (fun a => f (x + a + k) * star (f (x + a + l)))]
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    simp only [Tf]
    rw [star_mul, star_star]
    ring
  -- group the two index pairs into product Finsets
  have hprodL : (∑ p ∈ Q ×ˢ Q, ∑ x ∈ win n, ∑ q ∈ C ×ˢ C, Tf f p.1 p.2 q.1 q.2 x)
      = ∑ a ∈ Q, ∑ b ∈ Q, ∑ x ∈ win n, ∑ k ∈ C, ∑ l ∈ C, Tf f a b k l x := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb =>
      Finset.sum_congr rfl fun x hx => ?_
    exact Finset.sum_product C C (fun q : ℤ × ℤ => Tf f a b q.1 q.2 x)
  have hprodR : (∑ q ∈ C ×ˢ C, ∑ x ∈ win n, ∑ p ∈ Q ×ˢ Q, Tf f p.1 p.2 q.1 q.2 x)
      = ∑ k ∈ C, ∑ l ∈ C, ∑ x ∈ win n, ∑ a ∈ Q, ∑ b ∈ Q, Tf f a b k l x := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl =>
      Finset.sum_congr rfl fun x hx => ?_
    exact Finset.sum_product Q Q (fun p : ℤ × ℤ => Tf f p.1 p.2 k l x)
  have hP : (∑ p ∈ Q ×ˢ Q, ∑ x ∈ win n, ∑ q ∈ C ×ˢ C, Tf f p.1 p.2 q.1 q.2 x)
      = ∑ q ∈ C ×ˢ C, ∑ x ∈ win n, ∑ p ∈ Q ×ˢ Q, Tf f p.1 p.2 q.1 q.2 x := by
    calc (∑ p ∈ Q ×ˢ Q, ∑ x ∈ win n, ∑ q ∈ C ×ˢ C, Tf f p.1 p.2 q.1 q.2 x)
        = ∑ p ∈ Q ×ˢ Q, ∑ q ∈ C ×ˢ C, ∑ x ∈ win n, Tf f p.1 p.2 q.1 q.2 x := by
          refine Finset.sum_congr rfl fun p hp => ?_
          exact Finset.sum_comm
      _ = ∑ q ∈ C ×ˢ C, ∑ p ∈ Q ×ˢ Q, ∑ x ∈ win n, Tf f p.1 p.2 q.1 q.2 x :=
          Finset.sum_comm
      _ = ∑ q ∈ C ×ˢ C, ∑ x ∈ win n, ∑ p ∈ Q ×ˢ Q, Tf f p.1 p.2 q.1 q.2 x := by
          refine Finset.sum_congr rfl fun q hq => ?_
          exact Finset.sum_comm
  calc (∑ a ∈ Q, ∑ b ∈ Q, ∑ x ∈ win n,
        ((‖∑ k ∈ C, f (x + a + k) * star (f (x + b + k))‖ ^ 2 : ℝ) : ℂ))
      = ∑ a ∈ Q, ∑ b ∈ Q, ∑ x ∈ win n, ∑ k ∈ C, ∑ l ∈ C, Tf f a b k l x := hLc
    _ = ∑ p ∈ Q ×ˢ Q, ∑ x ∈ win n, ∑ q ∈ C ×ˢ C, Tf f p.1 p.2 q.1 q.2 x := hprodL.symm
    _ = ∑ q ∈ C ×ˢ C, ∑ x ∈ win n, ∑ p ∈ Q ×ˢ Q, Tf f p.1 p.2 q.1 q.2 x := hP
    _ = ∑ k ∈ C, ∑ l ∈ C, ∑ x ∈ win n, ∑ a ∈ Q, ∑ b ∈ Q, Tf f a b k l x := hprodR
    _ = (∑ k ∈ C, ∑ l ∈ C, ∑ x ∈ win n,
        ((‖∑ a ∈ Q, f (x + a + k) * star (f (x + a + l))‖ ^ 2 : ℝ) : ℂ)) := hRc.symm

/-! ## The monotonicity -/

theorem pair_sum_mono {A B : Finset ℤ} (hAB : A ⊆ B) {f : ℤ → ℂ} (hf : Work.Peluse.FinSuppZ f) :
    ∑ a ∈ A, ∑ b ∈ A, ∑' x : ℤ, ‖∑ k ∈ A, f (x + a + k) * star (f (x + b + k))‖ ^ 2
      ≤ ∑ a ∈ A, ∑ b ∈ A, ∑' x : ℤ, ‖∑ k ∈ B, f (x + a + k) * star (f (x + b + k))‖ ^ 2 := by
  obtain ⟨N, hN⟩ := hf
  rw [pair_swap A A f N hN, pair_swap A B f N hN]
  have hnonneg : ∀ k l : ℤ,
      0 ≤ ∑' x : ℤ, ‖∑ a ∈ A, f (x + a + k) * star (f (x + a + l))‖ ^ 2 :=
    fun k l => tsum_nonneg fun x => by positivity
  have h1 : (∑ k ∈ A, ∑ l ∈ A,
        ∑' x : ℤ, ‖∑ a ∈ A, f (x + a + k) * star (f (x + a + l))‖ ^ 2)
      ≤ ∑ k ∈ B, ∑ l ∈ A,
        ∑' x : ℤ, ‖∑ a ∈ A, f (x + a + k) * star (f (x + a + l))‖ ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hAB fun k hk hkA => ?_
    exact Finset.sum_nonneg fun l hl => hnonneg k l
  have h2 : (∑ k ∈ B, ∑ l ∈ A,
        ∑' x : ℤ, ‖∑ a ∈ A, f (x + a + k) * star (f (x + a + l))‖ ^ 2)
      ≤ ∑ k ∈ B, ∑ l ∈ B,
        ∑' x : ℤ, ‖∑ a ∈ A, f (x + a + k) * star (f (x + a + l))‖ ^ 2 := by
    refine Finset.sum_le_sum fun k hk => ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg hAB fun l hl hlA => hnonneg k l
  exact le_trans h1 h2

end

end Work.Peluse.BoxNormDilation
