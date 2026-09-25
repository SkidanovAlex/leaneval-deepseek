import Mathlib

/-!
# Region II: the "net-loss sum bound"

For `a = m - 3 ≥ 1`, `B > 0`, `c ≥ 0` we prove

`Σ_{n=m-2}^{Pf} max (B/(n(n-1)) - c) 0 ≤ (√(B/(m-3)) - √(c(m-3)))²`.

The proof is a discrete telescoping estimate.  Writing
`f k = B/k + c*k - 2√(B c)` (so that `f k = (√(B/k) - √(c k))² ≥ 0`), the summand at
index `n` is the backward difference `f (n-1) - f n`.  The sequence `f` is discretely
convex on the relevant range: its forward differences `f k - f (k-1)` are nondecreasing,
because they equal `c - B/(k(k-1))`.  A general combinatorial lemma
(`netLoss_sum_max_sub_le_of_convex`, proved by induction using the fact that the
"positive drops" of a discretely convex nonnegative sequence form an initial segment)
then gives `Σ max (f(n-1) - f n) 0 ≤ f a`, and `f a` is exactly the right-hand side.
-/

namespace Work.RHContract.A.regionII

/-- Telescoping of backward differences over `Icc (a+1) k`, for `a ≤ k`. -/
private lemma netLoss_telesc (f : ℕ → ℝ) (a k : ℕ) (hak : a ≤ k) :
    ∑ n ∈ Finset.Icc (a+1) k, (f (n-1) - f n) = f a - f k := by
  induction k, hak using Nat.le_induction with
  | base => simp
  | succ k hak ih =>
      rw [Finset.sum_Icc_succ_top (f := fun n => f (n-1) - f n) (by omega : a+1 ≤ k+1)]
      rw [ih]
      have : k + 1 - 1 = k := by omega
      simp only [this]
      ring

/-- **Discrete convexity/combinatorial key lemma.**
If `f` is nonnegative on `[a,P]` and its forward differences are nondecreasing on
`[a+1,P]` (i.e. `f` is discretely convex there), then the sum of the positive backward
drops is at most `f a`. -/
private theorem netLoss_sum_max_sub_le_of_convex (f : ℕ → ℝ) (a P : ℕ) (haP : a ≤ P)
    (hnn : ∀ n, a ≤ n → n ≤ P → 0 ≤ f n)
    (hconv : ∀ n, a + 1 ≤ n → n < P → f n - f (n-1) ≤ f (n+1) - f n) :
    ∑ n ∈ Finset.Icc (a+1) P, max (f (n-1) - f n) 0 ≤ f a := by
  -- the backward drop `f n - f (n+1)` is antitone (adjacent form of convexity)
  have hanti : ∀ n, a+1 ≤ n → n+1 ≤ P → f n - f (n+1) ≤ f (n-1) - f n := by
    intro n hn hnP
    have h := hconv n hn (by omega)
    linarith
  -- chained form: for `a+1 ≤ n ≤ m ≤ P`, `f m - f (m+1) ≤ f (n-1) - f n`
  have chain : ∀ n m, a+1 ≤ n → n ≤ m → m ≤ P → f (m-1) - f m ≤ f (n-1) - f n := by
    intro n m hn hnm
    induction m, hnm using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ m hnm ih =>
        intro hmP
        have e : m + 1 - 1 = m := by omega
        rw [e]
        have h1 : f m - f (m+1) ≤ f (m-1) - f m := hanti m (by omega) hmP
        have h2 : f (m-1) - f m ≤ f (n-1) - f n := ih (by omega)
        linarith
  -- `max (·) 0` is the positive part, i.e. the sum over the (initial-segment) filter
  have hsum_eq : ∑ n ∈ Finset.Icc (a+1) P, max (f (n-1) - f n) 0
      = ∑ n ∈ (Finset.Icc (a+1) P).filter (fun n => 0 ≤ f (n-1) - f n), (f (n-1) - f n) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : 0 ≤ f (n-1) - f n
    · rw [if_pos hn, max_eq_left hn]
    · rw [if_neg hn, max_eq_right (le_of_lt (not_le.mp hn))]
  rw [hsum_eq]
  by_cases hne : ((Finset.Icc (a+1) P).filter (fun n => 0 ≤ f (n-1) - f n)).Nonempty
  · -- the positive drops form the initial segment `Icc (a+1) k`
    set k : ℕ := ((Finset.Icc (a+1) P).filter (fun n => 0 ≤ f (n-1) - f n)).max' hne with hk
    have hkT : k ∈ (Finset.Icc (a+1) P).filter (fun n => 0 ≤ f (n-1) - f n) := by
      rw [hk]; exact Finset.max'_mem _ hne
    have hkIcc : a+1 ≤ k ∧ k ≤ P := Finset.mem_Icc.mp (Finset.mem_filter.mp hkT).1
    have hkpos : 0 ≤ f (k-1) - f k := (Finset.mem_filter.mp hkT).2
    have hT_eq :
        (Finset.Icc (a+1) P).filter (fun n => 0 ≤ f (n-1) - f n) = Finset.Icc (a+1) k := by
      apply Finset.ext
      intro n
      rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hnlo, hnP⟩, hpos⟩
        refine ⟨hnlo, ?_⟩
        have hle : n ≤ ((Finset.Icc (a+1) P).filter (fun n => 0 ≤ f (n-1) - f n)).max' hne :=
          Finset.le_max' _ n (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hnlo, hnP⟩, hpos⟩)
        rw [← hk] at hle
        exact hle
      · rintro ⟨hnlo, hnhi⟩
        refine ⟨⟨hnlo, by omega⟩, ?_⟩
        exact le_trans hkpos (chain n k (by omega) hnhi hkIcc.2)
    rw [hT_eq]
    have htel : ∑ n ∈ Finset.Icc (a+1) k, (f (n-1) - f n) = f a - f k :=
      netLoss_telesc f a k (by omega)
    rw [htel]
    have hfk : 0 ≤ f k := hnn k (by omega) hkIcc.2
    linarith
  · -- no positive drop at all
    rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
    exact hnn a le_rfl haP

/-- Backward difference of `k ↦ B/k + c*k` equals `B/(n(n-1)) - c`. -/
private lemma netLoss_summand_eq (n : ℕ) (B c : ℝ) (hn : 2 ≤ n) :
    B / ((n : ℝ) * ((n : ℝ) - 1)) - c
      = (B / ((n-1 : ℕ) : ℝ) + c * ((n-1 : ℕ) : ℝ))
          - (B / (n : ℝ) + c * (n : ℝ)) := by
  have hn10 : ((n:ℝ) - 1) ≠ 0 := by
    have : (1:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  have hn1' : ((n-1 : ℕ) : ℝ) = (n:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  rw [hn1']
  field_simp
  ring

/-- `f k = B/k + c*k - 2√(B c) ≥ 0`. -/
private lemma netLoss_f_nonneg (n : ℕ) (B c : ℝ) (hn : 1 ≤ n) (hB : 0 ≤ B) (hc : 0 ≤ c) :
    0 ≤ B / (n:ℝ) + c*(n:ℝ) - 2*Real.sqrt (B*c) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h1 : (0:ℝ) ≤ B / (n:ℝ) := by positivity
  have h2 : (0:ℝ) ≤ c * (n:ℝ) := by positivity
  have hsq : Real.sqrt (B/(n:ℝ)) * Real.sqrt (c*(n:ℝ)) = Real.sqrt (B*c) := by
    rw [← Real.sqrt_mul h1 (c*(n:ℝ))]
    congr 1
    field_simp
  have hsub := sq_nonneg (Real.sqrt (B/(n:ℝ)) - Real.sqrt (c*(n:ℝ)))
  rw [sub_sq, Real.sq_sqrt h1, Real.sq_sqrt h2] at hsub
  nlinarith [hsub, hsq]

/-- Discrete convexity of `k ↦ B/k + c*k` (for `B ≥ 0`). -/
private lemma netLoss_d_mono (n : ℕ) (B c : ℝ) (hn : 2 ≤ n) (hB : 0 ≤ B) :
    (B/(n:ℝ) + c*(n:ℝ)) - (B/((n-1:ℕ):ℝ) + c*((n-1:ℕ):ℝ))
      ≤ (B/((n+1:ℕ):ℝ) + c*((n+1:ℕ):ℝ)) - (B/(n:ℝ) + c*(n:ℝ)) := by
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hcast1 : ((n-1:ℕ):ℝ) = (n:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega: 1 ≤ n), Nat.cast_one]
  have hcast2 : ((n+1:ℕ):ℝ) = (n:ℝ) + 1 := by rw [Nat.cast_add, Nat.cast_one]
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith
  have hnm : (0:ℝ) < (n:ℝ) - 1 := by
    have : (1:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  have hnp : (0:ℝ) < (n:ℝ) + 1 := by linarith
  have hden1 : (0:ℝ) < (n:ℝ) * ((n:ℝ) - 1) := mul_pos hnpos hnm
  have hn0 : (n:ℝ) ≠ 0 := ne_of_gt hnpos
  have hnm0 : ((n:ℝ) - 1) ≠ 0 := ne_of_gt hnm
  have hnp0 : ((n:ℝ) + 1) ≠ 0 := ne_of_gt hnp
  have hlhs : (B/(n:ℝ) + c*(n:ℝ)) - (B/((n-1:ℕ):ℝ) + c*((n-1:ℕ):ℝ))
      = c - B/((n:ℝ) * ((n:ℝ) - 1)) := by
    rw [hcast1]; field_simp; ring
  have hrhs : (B/((n+1:ℕ):ℝ) + c*((n+1:ℕ):ℝ)) - (B/(n:ℝ) + c*(n:ℝ))
      = c - B/((n:ℝ) * ((n:ℝ) + 1)) := by
    rw [hcast2]; field_simp; ring
  rw [hlhs, hrhs]
  have hle : B/((n:ℝ) * ((n:ℝ) + 1)) ≤ B/((n:ℝ) * ((n:ℝ) - 1)) :=
    div_le_div_of_nonneg_left hB hden1 (by nlinarith)
  linarith

/-- The right-hand side `(√(B/(m-3)) - √(c(m-3)))²` in the form of `f (m-3)`. -/
private lemma netLoss_rhs_eq (m : ℕ) (B c : ℝ) (hm : 4 ≤ m) (hB : 0 ≤ B) (hc : 0 ≤ c) :
    (Real.sqrt (B / ((m : ℝ) - 3)) - Real.sqrt (c * ((m : ℝ) - 3))) ^ 2
      = B / ((m - 3 : ℕ) : ℝ) + c * ((m - 3 : ℕ) : ℝ) - 2 * Real.sqrt (B * c) := by
  have hcast : ((m - 3 : ℕ) : ℝ) = (m : ℝ) - 3 := by
    rw [Nat.cast_sub (by omega : 3 ≤ m), Nat.cast_ofNat]
  rw [hcast]
  have hm3 : (0:ℝ) < (m:ℝ) - 3 := by
    have h3 : (3:ℝ) < (m:ℝ) := by exact_mod_cast (show 3 < m by omega)
    linarith
  have h1 : (0:ℝ) ≤ B / ((m:ℝ) - 3) := by positivity
  have h2 : (0:ℝ) ≤ c * ((m:ℝ) - 3) := by positivity
  have hsq : Real.sqrt (B / ((m:ℝ) - 3)) * Real.sqrt (c * ((m:ℝ) - 3)) = Real.sqrt (B*c) := by
    rw [← Real.sqrt_mul h1 (c * ((m:ℝ) - 3))]
    congr 1
    field_simp
  rw [sub_sq, Real.sq_sqrt h1, Real.sq_sqrt h2]
  nlinarith [hsq]

theorem netLossSumBound (m Pf : ℕ) (B c : ℝ) (hB : 0 < B) (hc : 0 ≤ c)
    (hm : 4 ≤ m) (hmPf : m - 2 ≤ Pf) :
    ∑ n ∈ Finset.Icc (m - 2) Pf, max (B / ((n : ℝ) * ((n : ℝ) - 1)) - c) 0
      ≤ (Real.sqrt (B / ((m : ℝ) - 3)) - Real.sqrt (c * ((m : ℝ) - 3))) ^ 2 := by
  have hBnn : (0:ℝ) ≤ B := le_of_lt hB
  set a : ℕ := m - 3 with ha
  set f : ℕ → ℝ := fun k => B/(k:ℝ) + c*(k:ℝ) - 2*Real.sqrt (B*c) with hf
  have haP : a ≤ Pf := by omega
  have hIcc : Finset.Icc (m-2) Pf = Finset.Icc (a+1) Pf := by
    have h1 : a + 1 = m - 2 := by omega
    rw [h1]
  have hnn : ∀ n, a ≤ n → n ≤ Pf → 0 ≤ f n := by
    intro n han _
    rw [hf]
    exact netLoss_f_nonneg n B c (by omega) hBnn hc
  have hconv : ∀ n, a + 1 ≤ n → n < Pf → f n - f (n-1) ≤ f (n+1) - f n := by
    intro n hn _
    have hn2 : 2 ≤ n := by omega
    rw [hf]
    have := netLoss_d_mono n B c hn2 hBnn
    linarith
  have hkey := netLoss_sum_max_sub_le_of_convex f a Pf haP hnn hconv
  have hgoal_sum_eq :
      (∑ n ∈ Finset.Icc (m - 2) Pf, max (B / ((n : ℝ) * ((n : ℝ) - 1)) - c) 0)
        = ∑ n ∈ Finset.Icc (a+1) Pf, max (f (n-1) - f n) 0 := by
    rw [hIcc]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn2 : 2 ≤ n := by omega
    apply congrArg (fun x => max x 0)
    rw [hf]
    have hse := netLoss_summand_eq n B c hn2
    linarith [hse]
  rw [hgoal_sum_eq]
  have hfa : f a = (Real.sqrt (B / ((m : ℝ) - 3)) - Real.sqrt (c * ((m : ℝ) - 3))) ^ 2 := by
    rw [netLoss_rhs_eq m B c hm hBnn hc, hf, ha]
  rw [← hfa]
  exact hkey

end Work.RHContract.A.regionII
