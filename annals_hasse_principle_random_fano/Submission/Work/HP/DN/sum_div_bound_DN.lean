import Mathlib

/-!
# A quarter-bound for the `g`-adic union sum (helper for `Work.HP.DN.primCount_lower`)

`sum_div_bound_DN` is the numerical input of the box union bound in
`Work.HP.DN.primCount_lower`: the contribution of the `g`-divisible boxes, `g ≥ 2`, to
`#box(B)` is at most a quarter of the leading term `(2B)^N`.

The four private lemmas below are copied verbatim from the (inaccessible) private helpers of
`Submission.Work.HP.count_basic`, where the same bound is used for `count_basic`.
-/

namespace Work.HP.DN

/-- For `k ≥ 4`, `1/k^6` is at most half of the `5`-th power telescoping difference. -/
private lemma telescope_step (k : ℕ) (hk : 4 ≤ k) :
    (1 / (k:ℝ))^6 ≤ (1/2) * ((1 / ((k-1:ℕ):ℝ))^5 - (1 / (k:ℝ))^5) := by
  set u : ℝ := ((k-1:ℕ):ℝ) with hu
  have huk : (k:ℝ) = u + 1 := by
    have h1 : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
    rw [hu, ← h1]; push_cast; ring
  have hu0 : 0 < u := by
    rw [hu]; exact_mod_cast (by omega : 0 < k - 1)
  rw [huk]
  have hden : (0:ℝ) < 2 * u^5 * (u+1)^6 := by positivity
  rw [← sub_nonneg]
  have heq : (1/2) * ((1/u)^5 - (1/(u+1))^5) - (1/(u+1))^6
      = ((u+1)*((u+1)^5 - u^5) - 2*u^5) / (2*u^5*(u+1)^6) := by
    field_simp
  rw [heq]
  apply div_nonneg _ (le_of_lt hden)
  have h : (u+1)*((u+1)^5 - u^5) - 2*u^5 = 3*u^5+15*u^4+20*u^3+15*u^2+6*u+1 := by ring
  rw [h]
  positivity

/-- Tail bound for `Σ 1/k^6` by the `5`-th power telescoping. -/
private lemma sum_inv_pow6_le (B : ℕ) (hB : 5 ≤ B) :
    ∑ k ∈ Finset.Icc 4 B, (1/(k:ℝ))^6 ≤ 1/486 := by
  have hIcc : Finset.Icc 4 B = Finset.Ico 4 (B+1) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  have hB3 : B + 1 - 4 = B - 3 := by omega
  rw [hB3]
  have hstep : ∀ j : ℕ, (1/((4+j:ℕ):ℝ))^6
      ≤ (1/2)*((1/((3+j:ℕ):ℝ))^5 - (1/((4+j:ℕ):ℝ))^5) := by
    intro j
    have h := telescope_step (4+j) (by omega)
    have h1 : (4 + j - 1 : ℕ) = 3 + j := by omega
    simpa [h1] using h
  have hkey : ∑ j ∈ Finset.range (B-3), ((1/((3+j:ℕ):ℝ))^5 - (1/((4+j:ℕ):ℝ))^5)
      = (1/3:ℝ)^5 - (1/(B:ℝ))^5 := by
    have h : ∀ j : ℕ, (1/((4+j:ℕ):ℝ))^5
        = (fun t : ℕ => (1/((3+t:ℕ):ℝ))^5) (j+1) := by
      intro j
      show (1/((4+j:ℕ):ℝ))^5 = (1/((3+(j+1):ℕ):ℝ))^5
      have : (3 + (j+1) : ℕ) = 4 + j := by omega
      rw [this]
    rw [Finset.sum_congr rfl (fun j _ => by rw [h j]), Finset.sum_range_sub']
    have h1 : (3 + (B-3) : ℕ) = B := by omega
    have h2 : (3 + 0 : ℕ) = 3 := by omega
    rw [h1, h2]
    norm_num
  calc ∑ j ∈ Finset.range (B-3), (1/((4+j:ℕ):ℝ))^6
      ≤ ∑ j ∈ Finset.range (B-3), (1/2)*((1/((3+j:ℕ):ℝ))^5 - (1/((4+j:ℕ):ℝ))^5) :=
        Finset.sum_le_sum (fun j _ => hstep j)
    _ = (1/2) * ∑ j ∈ Finset.range (B-3), ((1/((3+j:ℕ):ℝ))^5 - (1/((4+j:ℕ):ℝ))^5) := by
        rw [Finset.mul_sum]
    _ = (1/2) * ((1/3:ℝ)^5 - (1/(B:ℝ))^5) := by rw [hkey]
    _ ≤ 1/486 := by
        have hp : (0:ℝ) < (1/(B:ℝ))^5 := by
          have : (0:ℝ) < (B:ℝ) := by exact_mod_cast (by omega : 0 < B)
          positivity
        have h3 : ((1:ℝ)/3)^5 = 1/243 := by norm_num
        rw [h3]; linarith

/-- The final numeric inequality for the box union bound. -/
private lemma numeric_final (N : ℕ) (hN : 6 ≤ N) (x : ℝ) (hx : 0 < x) :
    3^N * x^N * ((1/2:ℝ)^(N-6) * (1/64+1/729+1/486)) ≤ 2^N * x^N / 4 := by
  obtain ⟨k, rfl⟩ : ∃ k, N = 6 + k := ⟨N - 6, by omega⟩
  rw [show 6 + k - 6 = k by omega]
  have h4 : ((3:ℝ)/2)^k = ((3:ℝ)/4)^k * 2^k := by
    rw [div_pow, div_pow, show (4:ℝ)^k = 2^k * 2^k by rw [← mul_pow]; norm_num]
    field_simp
  have hkey : (729:ℝ) * (1/64+1/729+1/486) * ((3:ℝ)/2)^k ≤ 16 * 2^k := by
    rw [h4]
    have h1 : (729:ℝ) * (1/64+1/729+1/486) ≤ 16 := by norm_num
    have h2 : ((3:ℝ)/4)^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc 729 * (1/64+1/729+1/486) * (((3:ℝ)/4)^k * 2^k)
        = (729 * (1/64+1/729+1/486) * ((3:ℝ)/4)^k) * 2^k := by ring
      _ ≤ (16 * 1) * 2^k := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          calc 729 * (1/64+1/729+1/486) * ((3:ℝ)/4)^k ≤ 16 * ((3:ℝ)/4)^k :=
                mul_le_mul_of_nonneg_right h1 (by positivity)
            _ ≤ 16 * 1 := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = 16 * 2^k := by ring
  calc 3^(6+k) * x^(6+k) * ((1/2:ℝ)^k * (1/64+1/729+1/486))
      = (729 * (1/64+1/729+1/486) * ((3:ℝ)/2)^k) * x^(6+k) := by
        have h3 : (3:ℝ)^(6+k) = 729 * 3^k := by rw [pow_add]; norm_num
        have h2 : ((1:ℝ)/2)^k = 1/2^k := by rw [div_pow, one_pow]
        have h5 : ((3:ℝ)/2)^k = 3^k/2^k := by rw [div_pow]
        rw [h3, h2, h5]
        field_simp
    _ ≤ (16 * 2^k) * x^(6+k) := mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = 2^(6+k) * x^(6+k) / 4 := by
        rw [show (2:ℝ)^(6+k) = 64 * 2^k by rw [pow_add]; norm_num]
        ring



/-- Union-bound lower bound for the primitive vectors of a box: the sum of the `g`-divisible
terms is at most a quarter of the leading term `(2B)^N`. -/
private lemma sum_div_bound_aux (N B : ℕ) (hN : 6 ≤ N) (hB : 5 ≤ B) :
    (∑ g ∈ Finset.Icc 2 B, (2 * ((B / g : ℕ) : ℝ) + 1) ^ N) ≤ (2 * (B : ℝ)) ^ N / 4 := by
  have hBpos : (0:ℝ) < (B:ℝ) := by exact_mod_cast (by omega : 0 < B)
  have hterm : ∀ g ∈ Finset.Icc 2 B,
      (2 * ((B / g : ℕ) : ℝ) + 1) ^ N ≤ (3 * (B:ℝ) / g) ^ N := by
    intro g hg
    obtain ⟨hg2, hgB⟩ := Finset.mem_Icc.mp hg
    have hcast : ((B / g : ℕ) : ℝ) ≤ (B:ℝ)/(g:ℝ) := Nat.cast_div_le
    have hb1 : (1:ℝ) ≤ (B:ℝ)/(g:ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast (by omega : 0 < g))]
      have hBg : (g:ℝ) ≤ (B:ℝ) := by exact_mod_cast hgB
      linarith
    have hle : 2 * ((B / g : ℕ) : ℝ) + 1 ≤ 3 * (B:ℝ) / (g:ℝ) := by
      rw [mul_div_assoc]
      linarith
    exact pow_le_pow_left₀ (by positivity) hle N
  have hsum1 : ∑ g ∈ Finset.Icc 2 B, (2 * ((B / g : ℕ) : ℝ) + 1) ^ N
      ≤ ∑ g ∈ Finset.Icc 2 B, (3 * (B:ℝ) / g) ^ N := Finset.sum_le_sum hterm
  have hsum2 : ∑ g ∈ Finset.Icc 2 B, (3 * (B:ℝ) / g) ^ N
      ≤ (3*(B:ℝ))^N * ((1/2:ℝ)^(N-6) * (1/64+1/729+1/486)) := by
    have hfac : ∑ g ∈ Finset.Icc 2 B, (3 * (B:ℝ) / g) ^ N
        = (3*(B:ℝ))^N * ∑ g ∈ Finset.Icc 2 B, ((1:ℝ)/(g:ℝ))^N := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g hg
      rw [div_eq_mul_inv, mul_pow, one_div, inv_pow]
    rw [hfac]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc ∑ g ∈ Finset.Icc 2 B, ((1:ℝ)/(g:ℝ))^N
        ≤ ∑ g ∈ Finset.Icc 2 B, (1/2:ℝ)^(N-6) * ((1:ℝ)/(g:ℝ))^6 := by
          apply Finset.sum_le_sum
          intro g hg
          obtain ⟨hg2, hgB⟩ := Finset.mem_Icc.mp hg
          have hgpos : (0:ℝ) < (g:ℝ) := by exact_mod_cast (by omega : 0 < g)
          have hle : ((1:ℝ)/(g:ℝ)) ≤ 1/2 := by
            rw [div_le_iff₀ hgpos]
            have h2g : (2:ℝ) ≤ (g:ℝ) := by exact_mod_cast hg2
            linarith
          have hsplit : ((1:ℝ)/(g:ℝ))^N
              = ((1:ℝ)/(g:ℝ))^6 * ((1:ℝ)/(g:ℝ))^(N-6) := by
            conv_lhs => rw [show N = 6 + (N-6) by omega]
            rw [pow_add]
          rw [hsplit]
          have h1 : ((1:ℝ)/(g:ℝ))^(N-6) ≤ (1/2:ℝ)^(N-6) :=
            pow_le_pow_left₀ (by positivity) hle (N-6)
          calc ((1:ℝ)/(g:ℝ))^6 * ((1:ℝ)/(g:ℝ))^(N-6)
              ≤ ((1:ℝ)/(g:ℝ))^6 * (1/2:ℝ)^(N-6) := mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = (1/2:ℝ)^(N-6) * ((1:ℝ)/(g:ℝ))^6 := by ring
      _ = (1/2:ℝ)^(N-6) * ∑ g ∈ Finset.Icc 2 B, ((1:ℝ)/(g:ℝ))^6 := by rw [Finset.mul_sum]
      _ ≤ (1/2:ℝ)^(N-6) * (1/64+1/729+1/486) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hsub : Finset.Icc 2 B ⊆ insert 2 (insert 3 (Finset.Icc 4 B)) := by
            intro g hg
            simp only [Finset.mem_Icc] at hg
            simp only [Finset.mem_insert, Finset.mem_Icc]
            omega
          have h := Finset.sum_le_sum_of_subset_of_nonneg hsub
            (f := fun g : ℕ => ((1:ℝ)/(g:ℝ))^6) (by intro g _ _; positivity)
          have heval : ∑ g ∈ insert 2 (insert 3 (Finset.Icc 4 B)), ((1:ℝ)/(g:ℝ))^6
              = 1/64 + 1/729 + ∑ g ∈ Finset.Icc 4 B, ((1:ℝ)/(g:ℝ))^6 := by
            rw [Finset.sum_insert (by simp [Finset.mem_Icc] :
                  (2:ℕ) ∉ insert 3 (Finset.Icc 4 B)),
                Finset.sum_insert (by simp [Finset.mem_Icc] : (3:ℕ) ∉ Finset.Icc 4 B)]
            norm_num
            ring
          rw [heval] at h
          have htail := sum_inv_pow6_le B hB
          linarith
  have hfin := numeric_final N hN (B:ℝ) hBpos
  have h3 : (3*(B:ℝ))^N = 3^N * (B:ℝ)^N := by rw [mul_pow]
  have h2 : (2*(B:ℝ))^N / 4 = 2^N * (B:ℝ)^N / 4 := by rw [mul_pow]
  rw [h3] at hsum2
  linarith [hsum1, hsum2, hfin, h2]

/-- Union-bound lower bound for the primitive vectors of a box: the sum of the `g`-divisible
terms is at most a quarter of the leading term `(2B)^N`. -/
theorem sum_div_bound_DN (N B : ℕ) (hN : 6 ≤ N) (hB : 5 ≤ B) :
    ∑ g ∈ Finset.Icc 2 B, (2 * ((B / g : ℕ) : ℝ) + 1) ^ N ≤ (2 * (B : ℝ)) ^ N / 4 :=
  sum_div_bound_aux N B hN hB

end Work.HP.DN
