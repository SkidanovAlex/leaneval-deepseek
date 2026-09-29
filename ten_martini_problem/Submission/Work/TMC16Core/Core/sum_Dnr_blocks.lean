import Mathlib
import Submission.Work.TMC16Core.Defs

namespace Work.TMC16Core.Core

/-- Two adjacent integer intervals join into one: `[a,b] ∪ [b+1,c] = [a,c]`
(from `a ≤ b+1` and `b+1 ≤ c`).  The point `b+1` is the common (complementary)
endpoint. -/
lemma Icc_union_Icc_succ {a b c : ℤ} (h1 : a ≤ b + 1) (h2 : b + 1 ≤ c) :
    Finset.Icc a b ∪ Finset.Icc (b + 1) c = Finset.Icc a c := by
  ext x
  simp only [Finset.mem_union, Finset.mem_Icc]
  constructor
  · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
    · exact ⟨h, by linarith⟩
    · exact ⟨by linarith, h'⟩
  · rintro ⟨h, h'⟩
    rcases le_or_gt x b with hb | hb
    · exact Or.inl ⟨h, hb⟩
    · exact Or.inr ⟨by linarith, h'⟩

/-- `erase` distributes over union. -/
lemma erase_union (A B : Finset ℤ) (d : ℤ) :
    (A ∪ B).erase d = A.erase d ∪ B.erase d := by
  ext x
  simp only [Finset.mem_erase, Finset.mem_union]
  tauto

/-- **Block decomposition of an integer sum.**  If `1 ≤ m`, the sum of `g` over
`[a, a+N*m-1]` (with one point `d` removed) splits as the sum over the `N`
consecutive blocks `[a+t*m, a+t*m+m-1]` (`t = 0,…,N-1`), each with `d` removed. -/
lemma sum_blocks (a m : ℤ) (hm : 1 ≤ m) (N : ℕ) (d : ℤ) (g : ℤ → ℝ) :
    (∑ k ∈ (Finset.Icc a (a + (N:ℤ)*m - 1)).erase d, g k)
      = ∑ t ∈ Finset.range N,
          ∑ k ∈ (Finset.Icc (a + (t:ℤ)*m) (a + (t:ℤ)*m + m - 1)).erase d, g k := by
  induction N with
  | zero =>
    have hlt : a + ((0:ℕ):ℤ)*m - 1 < a := by push_cast; omega
    rw [Finset.Icc_eq_empty_of_lt hlt, Finset.range_zero]
    simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ← ih]
    have hN0 : (0:ℤ) ≤ (N:ℤ) := by exact_mod_cast Nat.zero_le N
    have hsplit : Finset.Icc a (a + ((N+1:ℕ):ℤ)*m - 1)
        = Finset.Icc a (a + (N:ℤ)*m - 1) ∪ Finset.Icc (a + (N:ℤ)*m) (a + (N:ℤ)*m + m - 1) := by
      have h1 : a ≤ (a + (N:ℤ)*m - 1) + 1 := by
        have : (0:ℤ) ≤ (N:ℤ)*m := mul_nonneg hN0 (by linarith)
        linarith
      have h2 : (a + (N:ℤ)*m - 1) + 1 ≤ a + (N:ℤ)*m + m - 1 := by linarith
      have h := Icc_union_Icc_succ (a := a) (b := a + (N:ℤ)*m - 1)
        (c := a + (N:ℤ)*m + m - 1) h1 h2
      rw [show (a + (N:ℤ)*m - 1) + 1 = a + (N:ℤ)*m by ring] at h
      rw [h]
      congr 1
      push_cast
      ring
    rw [hsplit, erase_union]
    have hdAB : Disjoint ((Finset.Icc a (a + (N:ℤ)*m - 1)).erase d)
        (((Finset.Icc (a + (N:ℤ)*m) (a + (N:ℤ)*m + m - 1))).erase d) := by
      rw [Finset.disjoint_left]
      intro x hx hy
      rw [Finset.mem_erase] at hx hy
      rw [Finset.mem_Icc] at hx hy
      obtain ⟨-, hxa, hxb⟩ := hx
      obtain ⟨-, hya, hyb⟩ := hy
      linarith
    rw [Finset.sum_union hdAB]

/-- The `∑_{t<2A}` block decomposition of the *left* (negative-anchored) interval
`[-A*m, A*m-1]`. -/
lemma sum_blocks_left (m : ℤ) (hm : 1 ≤ m) (A : ℕ) (d : ℤ) (g : ℤ → ℝ) :
    (∑ k ∈ (Finset.Icc (-((A:ℤ)*m)) ((A:ℤ)*m - 1)).erase d, g k)
      = ∑ t ∈ Finset.range (2*A),
          ∑ k ∈ (Finset.Icc (-((A:ℤ)*m) + (t:ℤ)*m)
              (-((A:ℤ)*m) + (t:ℤ)*m + m - 1)).erase d, g k := by
  have h := sum_blocks (-((A:ℤ)*m)) m hm (2*A) d g
  have h1 : -((A:ℤ)*m) + ((2*A:ℕ):ℤ)*m - 1 = (A:ℤ)*m - 1 := by push_cast; ring
  rw [h1] at h
  exact h

/-- The `∑_{t<2B}` block decomposition of the *right* interval
`[y-B*m, y+B*m-1]`. -/
lemma sum_blocks_right (m : ℤ) (hm : 1 ≤ m) (y : ℤ) (B : ℕ) (d : ℤ) (g : ℤ → ℝ) :
    (∑ k ∈ (Finset.Icc (y - (B:ℤ)*m) (y + (B:ℤ)*m - 1)).erase d, g k)
      = ∑ t ∈ Finset.range (2*B),
          ∑ k ∈ (Finset.Icc (y - (B:ℤ)*m + (t:ℤ)*m)
              (y - (B:ℤ)*m + (t:ℤ)*m + m - 1)).erase d, g k := by
  have h := sum_blocks (y - (B:ℤ)*m) m hm (2*B) d g
  have h1 : y - (B:ℤ)*m + ((2*B:ℕ):ℤ)*m - 1 = y + (B:ℤ)*m - 1 := by push_cast; ring
  rw [h1] at h
  exact h

theorem sum_Dnr_blocks {q : ℕ → ℕ} {n s a' b' : ℕ} {y d : ℤ}
    (hab : a' + b' = s) (hL : 1 ≤ q (n - 1)) (hdisj : (s : ℤ) * (q (n - 1) : ℤ) ≤ y)
    (g : ℤ → ℝ) :
    ∑ k ∈ ((Finset.Icc (-((a' : ℤ) * (q (n - 1) : ℤ))) ((a' : ℤ) * (q (n - 1) : ℤ) - 1)) ∪
        (Finset.Icc (y - (b' : ℤ) * (q (n - 1) : ℤ)) (y + (b' : ℤ) * (q (n - 1) : ℤ) - 1))).erase d, g k
      = (∑ t ∈ Finset.range (2 * a'),
          ∑ k ∈ (Finset.Icc (-((a' : ℤ) * (q (n - 1) : ℤ)) + (t : ℤ) * (q (n - 1) : ℤ))
              (-((a' : ℤ) * (q (n - 1) : ℤ)) + (t : ℤ) * (q (n - 1) : ℤ) + (q (n - 1) : ℤ) - 1)).erase d, g k)
        + (∑ t ∈ Finset.range (2 * b'),
          ∑ k ∈ (Finset.Icc (y - (b' : ℤ) * (q (n - 1) : ℤ) + (t : ℤ) * (q (n - 1) : ℤ))
              (y - (b' : ℤ) * (q (n - 1) : ℤ) + (t : ℤ) * (q (n - 1) : ℤ) + (q (n - 1) : ℤ) - 1)).erase d, g k) := by
  have hm : (1:ℤ) ≤ (q (n - 1) : ℤ) := by exact_mod_cast hL
  have hleft := sum_blocks_left (q (n - 1) : ℤ) hm a' d g
  have hright := sum_blocks_right (q (n - 1) : ℤ) hm y b' d g
  -- the two intervals are disjoint: the right one starts at `y - b'*m ≥ a'*m`.
  have hdisj' : ((a':ℤ) + (b':ℤ)) * (q (n - 1) : ℤ) ≤ y := by
    have hs : ((s : ℤ)) = (a' : ℤ) + (b' : ℤ) := by rw [← hab]; push_cast; ring
    rw [← hs]; exact hdisj
  have hdisjS : Disjoint (Finset.Icc (-((a':ℤ)*(q (n - 1):ℤ))) ((a':ℤ)*(q (n - 1):ℤ) - 1))
      (Finset.Icc (y - (b':ℤ)*(q (n - 1):ℤ)) (y + (b':ℤ)*(q (n - 1):ℤ) - 1)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_Icc] at hx1 hx2
    obtain ⟨hx1a, hx1b⟩ := hx1
    obtain ⟨hx2a, hx2b⟩ := hx2
    have key : y ≤ ((a':ℤ) + (b':ℤ)) * (q (n - 1):ℤ) - 1 := by
      have e : ((a':ℤ) + (b':ℤ)) * (q (n - 1):ℤ)
          = (a':ℤ)*(q (n - 1):ℤ) + (b':ℤ)*(q (n - 1):ℤ) := by ring
      rw [e]; linarith
    linarith
  have hdisjE : Disjoint ((Finset.Icc (-((a':ℤ)*(q (n - 1):ℤ))) ((a':ℤ)*(q (n - 1):ℤ) - 1)).erase d)
      ((Finset.Icc (y - (b':ℤ)*(q (n - 1):ℤ)) (y + (b':ℤ)*(q (n - 1):ℤ) - 1)).erase d) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    rw [Finset.mem_erase] at hx hy
    exact (Finset.disjoint_left.mp hdisjS) hx.2 hy.2
  rw [erase_union, Finset.sum_union hdisjE, hleft, hright]

end Work.TMC16Core.Core
