/-
# The mixed monotonicity of the pair sum (both index ranges grow)

`Submission/Work/Peluse/BoxNormDilation/pair_sum_mono.lean` proves that

`P(Q, C) = ∑_{a,b ∈ Q} ∑_x ‖∑_{k ∈ C} f(x+a+k)·conj(f(x+b+k))‖²`

is monotone in `C` **while the outer range `Q` is kept fixed** (there the two ranges are forced to
coincide on the left).  The present file proves the *mixed* statement needed by
`Submission/Work/Peluse/Concat/`: both the outer range `A` and the inner range `B` may grow,
`P(A, B) ≤ P(A', B')` for `A ⊆ A'` and `B ⊆ B'`.

The mathematics is the same "two-dimensional" symmetry as in `pair_sum_mono`: writing
`T(a,b,k,l,x) = f(x+a+k)·conj(f(x+b+k))·conj(f(x+a+l))·f(x+b+l)`, the expansion of the square gives

`P(Q,C) = ∑_{a,b ∈ Q} ∑_{k,l ∈ C} ∑_x T(a,b,k,l,x)`,

and `T` is invariant under the interchange of the pairs `(a,b) ↔ (k,l)`.  Hence

`P(Q, C) = ∑_{k,l ∈ C} ∑_x ‖∑_{a ∈ Q} f(x+a+k)·conj(f(x+a+l))‖²` .

In this presentation `P` is visibly monotone in the *outer* range `C` with the norm set `Q` fixed,
and monotone in the norm set `Q` — wait, it is *not* monotone in `Q` pointwise; but that step is not
needed: the chain used below is

`P(A,B) ≤ P(A,B') ≤ P(A',B')`,

where the first inequality is the monotonicity in the outer range in the swapped presentation
(both sides having the same norm set `A`), and the second is the trivial enlargement of the double
range `A × A ⊆ A' × A'` of a *nonnegative* summand.
-/
import Mathlib
import Submission.Work.Peluse.Basic

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Concat

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

/-! ## The two monotonicities -/

/-- Enlarging a doubly-indexed range of a nonnegative sum. -/
private lemma double_sum_le_of_subset {s t : Finset ℤ} (h : s ⊆ t) (F : ℤ → ℤ → ℝ)
    (hF : ∀ k l, 0 ≤ F k l) :
    (∑ k ∈ s, ∑ l ∈ s, F k l) ≤ ∑ k ∈ t, ∑ l ∈ t, F k l := by
  have h1 : (∑ k ∈ s, ∑ l ∈ s, F k l) ≤ ∑ k ∈ s, ∑ l ∈ t, F k l :=
    Finset.sum_le_sum fun k _ => Finset.sum_le_sum_of_subset_of_nonneg h
      (fun l _ _ => hF k l)
  have h2 : (∑ k ∈ s, ∑ l ∈ t, F k l) ≤ ∑ k ∈ t, ∑ l ∈ t, F k l :=
    Finset.sum_le_sum_of_subset_of_nonneg h
      (fun k _ _ => Finset.sum_nonneg fun l _ => hF k l)
  exact le_trans h1 h2

/-- **Monotonicity of the pair sum in the inner index range**, with the outer range fixed. -/
private lemma pair_sum_mono_inner {Q C C' : Finset ℤ} (h : C ⊆ C') {f : ℤ → ℂ}
    (hf : Work.Peluse.FinSuppZ f) :
    (∑ a ∈ Q, ∑ b ∈ Q, ∑' x : ℤ, ‖∑ k ∈ C, f (x + a + k) * star (f (x + b + k))‖ ^ 2)
      ≤ ∑ a ∈ Q, ∑ b ∈ Q, ∑' x : ℤ,
          ‖∑ k ∈ C', f (x + a + k) * star (f (x + b + k))‖ ^ 2 := by
  obtain ⟨N, hN⟩ := hf
  rw [pair_swap Q C f N hN, pair_swap Q C' f N hN]
  exact double_sum_le_of_subset h
    (fun k l => ∑' x : ℤ, ‖∑ a ∈ Q, f (x + a + k) * star (f (x + a + l))‖ ^ 2)
    (fun k l => tsum_nonneg fun x => by positivity)

/-- **Mixed monotonicity of the pair sum**: both index ranges may grow. -/
theorem pair_sum_mono_mixed {A A' B B' : Finset ℤ} (hA : A ⊆ A') (hB : B ⊆ B') {f : ℤ → ℂ}
    (hf : Work.Peluse.FinSuppZ f) :
    (∑ a ∈ A, ∑ b ∈ A, ∑' x : ℤ, ‖∑ k ∈ B, f (x + a + k) * star (f (x + b + k))‖ ^ 2)
      ≤ ∑ a ∈ A', ∑ b ∈ A', ∑' x : ℤ,
          ‖∑ k ∈ B', f (x + a + k) * star (f (x + b + k))‖ ^ 2 := by
  -- step 1: the inner range grows, the outer one is kept at `A`
  have h1 : (∑ a ∈ A, ∑ b ∈ A, ∑' x : ℤ,
        ‖∑ k ∈ B, f (x + a + k) * star (f (x + b + k))‖ ^ 2)
      ≤ ∑ a ∈ A, ∑ b ∈ A, ∑' x : ℤ,
          ‖∑ k ∈ B', f (x + a + k) * star (f (x + b + k))‖ ^ 2 :=
    pair_sum_mono_inner hB hf
  -- step 2: the doubly-indexed outer range grows, the inner one is kept at `B'`
  have h2 : (∑ a ∈ A, ∑ b ∈ A, ∑' x : ℤ,
        ‖∑ k ∈ B', f (x + a + k) * star (f (x + b + k))‖ ^ 2)
      ≤ ∑ a ∈ A', ∑ b ∈ A', ∑' x : ℤ,
          ‖∑ k ∈ B', f (x + a + k) * star (f (x + b + k))‖ ^ 2 :=
    double_sum_le_of_subset hA
      (fun a b => ∑' x : ℤ, ‖∑ k ∈ B', f (x + a + k) * star (f (x + b + k))‖ ^ 2)
      (fun a b => tsum_nonneg fun x => by positivity)
  exact le_trans h1 h2

end

end Work.Peluse.Concat
