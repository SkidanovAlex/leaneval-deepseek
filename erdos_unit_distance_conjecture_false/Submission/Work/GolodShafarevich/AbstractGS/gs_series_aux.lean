import Mathlib

namespace Work.GolodShafarevich.AbstractGS

/-- The numerical Golod–Shafarevich series argument: a monotone, eventually constant sequence
satisfying `d * a n + 1 ≤ a (n+1) + r * a (n-1)` forces `4 r > d ^ 2`. -/
theorem gs_series_aux {a : ℕ → ℕ} {d r : ℕ} (hd : 1 ≤ d)
    (ha0 : a 0 = 0) (ha1 : a 1 = 1)
    (hmono : Monotone a) (hstab : ∃ N, ∀ n ≥ N, a n = a N)
    (hineq : ∀ n : ℕ, 1 ≤ n → d * a n + 1 ≤ a (n + 1) + r * a (n - 1)) :
    4 * r > d ^ 2 := by
  by_contra hcon
  push Not at hcon
  have h4r : (4 : ℝ) * (r : ℝ) ≤ (d : ℝ) ^ 2 := by
    have h : ((4 * r : ℕ) : ℝ) ≤ ((d ^ 2 : ℕ) : ℝ) := by exact_mod_cast hcon
    push_cast at h
    linarith
  have hD : (0 : ℝ) ≤ (d : ℝ) ^ 2 - 4 * (r : ℝ) := by linarith
  set s : ℝ := Real.sqrt ((d : ℝ) ^ 2 - 4 * (r : ℝ)) with hs
  have hs2 : s ^ 2 = (d : ℝ) ^ 2 - 4 * (r : ℝ) := by
    rw [hs]
    exact Real.sq_sqrt hD
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsd : s ≤ (d : ℝ) := by
    have h1 : s ^ 2 ≤ (d : ℝ) ^ 2 := by rw [hs2]; nlinarith [Nat.cast_nonneg (α := ℝ) r]
    nlinarith [hs0, Nat.cast_nonneg (α := ℝ) d]
  set α : ℝ := ((d : ℝ) + s) / 2 with hα
  set β : ℝ := ((d : ℝ) - s) / 2 with hβ
  have hαd : α + β = (d : ℝ) := by rw [hα, hβ]; ring
  have hαβ : α * β = (r : ℝ) := by
    rw [hα, hβ]
    have h : ((d : ℝ) + s) * ((d : ℝ) - s) = 4 * (r : ℝ) := by nlinarith [hs2]
    linarith
  have hβ0 : 0 ≤ β := by rw [hβ]; linarith
  have hα1 : 1 ≤ α := by
    rw [hα]
    by_cases h2 : 2 ≤ d
    · have h2' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast h2
      linarith
    · have hdle : d ≤ 1 := by omega
      have hd1 : d = 1 := by omega
      have hd2 : d ^ 2 ≤ 1 := by
        rw [pow_two]
        calc d * d ≤ 1 * 1 := Nat.mul_le_mul hdle hdle
          _ = 1 := by norm_num
      have hr0 : r = 0 := by omega
      have hs1 : s = 1 := by
        rw [hs]
        have h2 : (d : ℝ) ^ 2 - 4 * (r : ℝ) = 1 := by rw [hd1, hr0]; norm_num
        rw [h2, Real.sqrt_one]
      have hd1R : (d : ℝ) = 1 := by rw [hd1]; norm_num
      rw [hs1, hd1R]
      norm_num
  set c : ℕ → ℝ := fun n => (a n : ℝ) - β * (a (n - 1) : ℝ) with hc
  have hc1 : c 1 = 1 := by
    simp only [hc, ha1, ha0, Nat.cast_one, Nat.cast_zero]
    ring
  have hrec : ∀ n : ℕ, 1 ≤ n → c (n + 1) ≥ α * c n + 1 := by
    intro n hn
    have h1 := hineq n hn
    have h1' : ((d * a n + 1 : ℕ) : ℝ) ≤ ((a (n + 1) + r * a (n - 1) : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h1'
    simp only [hc]
    push_cast
    nlinarith [hαd, hαβ, h1', Nat.cast_nonneg (α := ℝ) (a (n - 1))]
  have hcge : ∀ n : ℕ, 1 ≤ n → c n ≥ (n : ℝ) := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ n ih =>
      intro hn
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        rw [hc1]
        norm_num
      · have h1 := hrec n (by omega)
        have h2 := ih (by omega)
        push_cast
        nlinarith [h1, hα1, h2]
  have hage : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ (a n : ℝ) := by
    intro n hn
    have h1 := hcge n hn
    have h2 : c n ≤ (a n : ℝ) := by
      simp only [hc]
      nlinarith [hβ0, Nat.cast_nonneg (α := ℝ) (a (n - 1))]
    linarith
  obtain ⟨N, hN⟩ := hstab
  have hbdd : ∀ n : ℕ, (a n : ℝ) ≤ (a N : ℝ) := by
    intro n
    rcases lt_or_ge n N with h | h
    · exact_mod_cast hmono (le_of_lt h)
    · have : a n = a N := hN n h
      rw [this]
  have hbig := hage (a N + N + 2) (by omega)
  have hsmall := hbdd (a N + N + 2)
  push_cast at hbig
  linarith [Nat.cast_nonneg (α := ℝ) N]

end Work.GolodShafarevich.AbstractGS
