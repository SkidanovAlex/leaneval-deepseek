import Mathlib

namespace Work.BourgainPlan.IonescuWainger

/-- Sharp tail bound for the `1/m²` series: `∑_{m=N+1}^{K} 1/m² ≤ 1/(N+1/2) = 2/(2N+1)`.
The proof uses the midpoint telescoping inequality `1/m² ≤ 1/(m-1/2) - 1/(m+1/2)`. -/
lemma tail_inv_sq_le (N K : ℕ) :
    ∑ n ∈ Finset.Ico N K, (1 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤ 2 / (2 * (N : ℝ) + 1) := by
  rw [Finset.sum_Ico_eq_sum_range]
  set m : ℕ := K - N
  have hterm : ∀ k ∈ Finset.range m,
      (1:ℝ)/((((N + k : ℕ)) : ℝ) + 1)^2 ≤ (1/((N:ℝ)+k+1/2) - 1/((N:ℝ)+k+3/2)) := by
    intro k _
    have hcast : ((((N + k : ℕ)) : ℝ) + 1) = (N:ℝ)+k+1 := by push_cast; ring
    rw [hcast]
    have hx1 : (1:ℝ) ≤ (N:ℝ)+k+1 := by
      have : (1:ℕ) ≤ N+k+1 := by omega
      exact_mod_cast this
    have hpos : 0 < ((N:ℝ)+k+1)^2 - 1/4 := by nlinarith
    have hkey : (1:ℝ)/(((N:ℝ)+k+1)^2) ≤ 1/(((N:ℝ)+k+1)^2 - 1/4) :=
      one_div_le_one_div_of_le hpos (by linarith)
    have heq : (1:ℝ)/(((N:ℝ)+k+1)^2 - 1/4) = 1/((N:ℝ)+k+1/2) - 1/((N:ℝ)+k+3/2) := by
      have hfac : ((N:ℝ)+k+1)^2 - 1/4 = (((N:ℝ)+k+1) - 1/2)*(((N:ℝ)+k+1) + 1/2) := by ring
      rw [hfac, div_sub_div]
      · ring
      · linarith
      · linarith
    rwa [heq] at hkey
  have htel : ∀ m : ℕ, ∑ k ∈ Finset.range m, ((1:ℝ)/((N:ℝ)+k+1/2) - 1/((N:ℝ)+k+3/2))
      = 1/((N:ℝ)+1/2) - 1/((N:ℝ)+m+1/2) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring_nf
  calc ∑ k ∈ Finset.range m, (1:ℝ)/((((N + k : ℕ)) : ℝ)+1)^2
      ≤ ∑ k ∈ Finset.range m, ((1:ℝ)/((N:ℝ)+k+1/2) - 1/((N:ℝ)+k+3/2)) :=
        Finset.sum_le_sum hterm
    _ = 1/((N:ℝ)+1/2) - 1/((N:ℝ)+m+1/2) := htel m
    _ ≤ 1/((N:ℝ)+1/2) := by
        have : 0 ≤ 1/((N:ℝ)+m+1/2) := by positivity
        linarith
    _ = 2/(2*(N:ℝ)+1) := by field_simp

/-- **Two-scale sum bound.**  For `a > 0` and `b ≥ 0`,
`∑_{k ≥ 1} min(a, b/k²) ≤ 2√(a b)`.
This is the sharp form of the elementary integral comparison for `min(a, b/x²)`; the constant
`2` is optimal. -/
lemma tsum_min_div_sq_le (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    ∑' n : ℕ, min a (b / ((n : ℝ) + 1) ^ 2) ≤ 2 * Real.sqrt (a * b) := by
  have hbda : 0 ≤ b / a := div_nonneg hb ha.le
  set M : ℝ := Real.sqrt (b / a) with hM
  have hMnn : 0 ≤ M := by rw [hM]; positivity
  have hMsq : M^2 = b/a := by rw [hM]; exact Real.sq_sqrt hbda
  have hb_eq : b = a * M^2 := by rw [hMsq]; field_simp
  set N : ℕ := ⌊M⌋₊ with hN
  have hNle : (N:ℝ) ≤ M := by rw [hN]; exact Nat.floor_le hMnn
  have hNlt : M < (N:ℝ) + 1 := by rw [hN]; exact Nat.lt_floor_add_one M
  have hδ0 : 0 ≤ M - (N:ℝ) := by linarith
  have hδ1 : M - (N:ℝ) ≤ 1 := by linarith
  have hnn : ∀ n : ℕ, 0 ≤ min a (b / ((n:ℝ)+1)^2) := by
    intro n; exact le_min ha.le (by positivity)
  -- the partial sums of `min a (b/(n+1)^2)` are bounded by `a*N + b·2/(2N+1)`
  have hkey : ∀ K : ℕ, ∑ n ∈ Finset.range K, min a (b / ((n:ℝ)+1)^2)
      ≤ a * (N:ℝ) + b * (2/(2*(N:ℝ)+1)) := by
    intro K
    have hpt : ∀ n ∈ Finset.range K, min a (b/((n:ℝ)+1)^2)
        ≤ (if n < N then a else b/((n:ℝ)+1)^2) := by
      intro n _
      by_cases h : n < N
      · simp only [h, if_true]; exact min_le_left _ _
      · simp only [h, if_false]; exact min_le_right _ _
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [Finset.sum_ite]
    have hcard : ((Finset.range K).filter (fun n => n < N)).card ≤ N := by
      have hsub : (Finset.range K).filter (fun n => n < N) ⊆ Finset.range N := by
        intro n hn
        simp only [Finset.mem_filter, Finset.mem_range] at hn
        exact Finset.mem_range.mpr hn.2
      calc ((Finset.range K).filter (fun n => n < N)).card
            ≤ (Finset.range N).card := Finset.card_le_card hsub
        _ = N := Finset.card_range N
    have h1' : ∑ n ∈ (Finset.range K).filter (fun n => n < N), a ≤ a * (N:ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      calc ((Finset.range K).filter (fun n => n < N)).card * a
            ≤ (N:ℝ) * a := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) ha.le
        _ = a * (N:ℝ) := by ring
    have h2' : ∑ n ∈ (Finset.range K).filter (fun n => ¬ n < N), b/((n:ℝ)+1)^2
        ≤ b * (2/(2*(N:ℝ)+1)) := by
      have hsub : (Finset.range K).filter (fun n => ¬ n < N) ⊆ Finset.Ico N K := by
        intro n hn
        simp only [Finset.mem_filter, Finset.mem_range] at hn
        simp only [Finset.mem_Ico]
        omega
      have hstep : ∑ n ∈ (Finset.range K).filter (fun n => ¬ n < N), b/((n:ℝ)+1)^2
          ≤ ∑ n ∈ Finset.Ico N K, b/((n:ℝ)+1)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
      refine hstep.trans ?_
      have heq2 : ∑ n ∈ Finset.Ico N K, b/((n:ℝ)+1)^2
          = b * ∑ n ∈ Finset.Ico N K, (1:ℝ)/((n:ℝ)+1)^2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun n _ => by rw [mul_one_div]
      rw [heq2]
      exact mul_le_mul_of_nonneg_left (tail_inv_sq_le N K) hb
    linarith [h1', h2']
  -- the numerical core: `a*N + b·2/(2N+1) ≤ 2 a M`
  have hfac : 0 ≤ ((2*M - (N:ℝ)) * (2*(N:ℝ)+1) - 2*M^2) := by
    have h1 : (2*M - (N:ℝ)) * (2*(N:ℝ)+1) - 2*M^2
        = (N:ℝ) + 2*(M-(N:ℝ)) - 2*(M-(N:ℝ))^2 := by ring
    rw [h1]
    nlinarith [hδ0, hδ1, mul_nonneg hδ0 (by linarith : (0:ℝ) ≤ 1 - (M - (N:ℝ)))]
  have hfin : a * (N:ℝ) + b * (2/(2*(N:ℝ)+1)) ≤ 2 * a * M := by
    have hpos : 0 < 2*(N:ℝ) + 1 := by positivity
    have hgoal : 2 * a * M^2 / (2*(N:ℝ)+1) ≤ 2*a*M - a*(N:ℝ) := by
      rw [div_le_iff₀ hpos]
      nlinarith [hfac, ha]
    have heq : a * (N:ℝ) + b * (2/(2*(N:ℝ)+1)) = a*(N:ℝ) + 2*a*M^2/(2*(N:ℝ)+1) := by
      rw [hb_eq]; ring
    rw [heq]
    linarith [hgoal]
  have hsqrt : Real.sqrt (a*b) = a*M := by
    have h1 : a*b = (a*M)^2 := by rw [mul_pow, hMsq]; field_simp
    rw [h1, Real.sqrt_sq (by positivity)]
  calc ∑' n : ℕ, min a (b / ((n:ℝ)+1)^2)
      ≤ a * (N:ℝ) + b * (2/(2*(N:ℝ)+1)) := Real.tsum_le_of_sum_range_le hnn hkey
    _ ≤ 2 * a * M := hfin
    _ = 2 * Real.sqrt (a * b) := by rw [hsqrt]; ring

theorem tsum_two_scale_bound (ε B : ℝ) (f : ℤ → ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1/2) (hB : 0 ≤ B)
    (hf : ∀ n, 0 ≤ f n) (h1 : ∀ n, f n ≤ 2 * ε) (h2 : ∀ n, n ≠ 0 → f n ≤ B / (n : ℝ) ^ 2) :
    Summable f ∧ (∑' n : ℤ, f n) ≤ 5 + 2 * B * ε := by
  have ha : (0:ℝ) < 2 * ε := by linarith
  have h2ε : 2 * ε ≤ 1 := by linarith
  -- summable majorant `B/(n+1)^2` on ℕ
  have hmaj : Summable (fun n : ℕ => B / ((n:ℝ)+1)^2) := by
    have h1' : Summable (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)^2) := by
      have hs := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
      have := (summable_nat_add_iff (f := fun n : ℕ => (1:ℝ)/(n:ℝ)^2) 1).mpr hs
      simpa using this
    simpa [div_eq_mul_inv] using h1'.mul_left B
  -- summability of the two tails of `f`
  have hsum1 : Summable (fun n : ℕ => f ((n:ℤ) + 1)) := by
    refine Summable.of_nonneg_of_le (fun n => hf _) (fun n => ?_) hmaj
    have hne : ((n:ℤ) + 1) ≠ 0 := by omega
    have := h2 ((n:ℤ)+1) hne
    simpa using this
  have hsum2 : Summable (fun n : ℕ => f (-((n:ℤ)+1))) := by
    refine Summable.of_nonneg_of_le (fun n => hf _) (fun n => ?_) hmaj
    have hne : -((n:ℤ)+1) ≠ 0 := by omega
    have hb := h2 (-((n:ℤ)+1)) hne
    have hden : (((-((n:ℤ)+1) : ℤ)) : ℝ) ^ 2 = ((n:ℝ)+1)^2 := by push_cast; ring
    rw [hden] at hb
    exact hb
  have hfsum : Summable f := Summable.of_add_one_of_neg_add_one hsum1 hsum2
  -- the comparison function `g n = min (2ε) (B/(n+1)^2)`
  have hgsum : Summable (fun n : ℕ => min (2*ε) (B / ((n:ℝ)+1)^2)) :=
    Summable.of_nonneg_of_le (fun n => le_min ha.le (by positivity))
      (fun n => min_le_right _ _) hmaj
  have hg1 : ∀ n : ℕ, f ((n:ℤ)+1) ≤ min (2*ε) (B / ((n:ℝ)+1)^2) := by
    intro n
    refine le_min (h1 _) ?_
    have hne : ((n:ℤ) + 1) ≠ 0 := by omega
    have := h2 ((n:ℤ)+1) hne
    simpa using this
  have hg2 : ∀ n : ℕ, f (-((n:ℤ)+1)) ≤ min (2*ε) (B / ((n:ℝ)+1)^2) := by
    intro n
    refine le_min (h1 _) ?_
    have hne : -((n:ℤ)+1) ≠ 0 := by omega
    have hb := h2 (-((n:ℤ)+1)) hne
    have hden : (((-((n:ℤ)+1) : ℤ)) : ℝ) ^ 2 = ((n:ℝ)+1)^2 := by push_cast; ring
    rw [hden] at hb
    exact hb
  have hbound1 : (∑' n : ℕ, f ((n:ℤ)+1))
      ≤ ∑' n : ℕ, min (2*ε) (B / ((n:ℝ)+1)^2) :=
    Summable.tsum_le_tsum hg1 hsum1 hgsum
  have hbound2 : (∑' n : ℕ, f (-((n:ℤ)+1)))
      ≤ ∑' n : ℕ, min (2*ε) (B / ((n:ℝ)+1)^2) :=
    Summable.tsum_le_tsum hg2 hsum2 hgsum
  have hmin : (∑' n : ℕ, min (2*ε) (B / ((n:ℝ)+1)^2)) ≤ 2 * Real.sqrt ((2*ε)*B) :=
    tsum_min_div_sq_le (2*ε) B ha hB
  refine ⟨hfsum, ?_⟩
  rw [tsum_of_add_one_of_neg_add_one hsum1 hsum2]
  have hs : (0:ℝ) ≤ 2*B*ε := by positivity
  calc (∑' n : ℕ, f ((n:ℤ)+1)) + f 0 + (∑' n : ℕ, f (-((n:ℤ)+1)))
      ≤ (∑' n : ℕ, min (2*ε) (B / ((n:ℝ)+1)^2)) + 2*ε
          + (∑' n : ℕ, min (2*ε) (B / ((n:ℝ)+1)^2)) :=
        add_le_add (add_le_add hbound1 (h1 0)) hbound2
    _ = 2 * (∑' n : ℕ, min (2*ε) (B / ((n:ℝ)+1)^2)) + 2*ε := by ring
    _ ≤ 2 * (2 * Real.sqrt ((2*ε)*B)) + 2*ε := by linarith [hmin]
    _ ≤ 5 + 2 * B * ε := by
        rw [show (2:ℝ)*ε*B = 2*B*ε by ring]
        nlinarith [sq_nonneg (Real.sqrt (2*B*ε) - 2), Real.sq_sqrt hs, h2ε]

end Work.BourgainPlan.IonescuWainger
