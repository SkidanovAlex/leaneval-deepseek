import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Work.Higman.Q3.L12

/-! ## Carries for integer relations between powers of two

If `∑ t < n, c t * 2 ^ t = 0` for `c : ℕ → ℤ`, the partial sums
`S t = ∑ s < t, c s * 2 ^ s` are divisible by `2 ^ t`, and `κ t = S t / 2 ^ t` is a
"carry" sequence with `κ 0 = κ n = 0`, `c t = 2 * κ (t+1) - κ t` and
`∑ t < n, κ t = ∑ t < n, c t`. -/

/-- The `t`-th partial sum of `c s * 2 ^ s`. -/
def csum (c : ℕ → ℤ) (t : ℕ) : ℤ := ∑ s ∈ Finset.range t, c s * (2 : ℤ) ^ s

/-- The `t`-th carry of the sequence `c`: the partial sum `csum c t` divided by `2 ^ t`. -/
def carry (c : ℕ → ℤ) (t : ℕ) : ℤ := csum c t / (2 : ℤ) ^ t

theorem carry_spec {n : ℕ} {c : ℕ → ℤ}
    (h : ∑ t ∈ Finset.range n, c t * (2 : ℤ) ^ t = 0) :
    carry c 0 = 0 ∧ carry c n = 0 ∧
      (∀ t < n, c t = 2 * carry c (t + 1) - carry c t) ∧
      (∑ t ∈ Finset.range n, carry c t) = ∑ t ∈ Finset.range n, c t := by
  have hcsumn : csum c n = 0 := h
  have hdiv : ∀ t ≤ n, (2 : ℤ) ^ t ∣ csum c t := by
    intro t ht
    have hsplit := Finset.sum_range_add (fun s => c s * (2 : ℤ) ^ s) t (n - t)
    rw [Nat.add_sub_of_le ht] at hsplit
    have hfac : (∑ x ∈ Finset.range (n - t), c (t + x) * (2 : ℤ) ^ (t + x))
        = (2 : ℤ) ^ t * ∑ x ∈ Finset.range (n - t), c (t + x) * (2 : ℤ) ^ x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by rw [pow_add]; ring
    rw [hfac, h] at hsplit
    have hcst : csum c t = ∑ x ∈ Finset.range t, c x * (2 : ℤ) ^ x := rfl
    have : csum c t
        = (2 : ℤ) ^ t * (-∑ x ∈ Finset.range (n - t), c (t + x) * (2 : ℤ) ^ x) := by
      rw [hcst]; linarith
    rw [this]
    exact dvd_mul_right _ _
  have hspec : ∀ t ≤ n, carry c t * (2 : ℤ) ^ t = csum c t := by
    intro t ht
    rw [carry]
    exact Int.ediv_mul_cancel (hdiv t ht)
  have hc0 : carry c 0 = 0 := by
    have h0 : csum c 0 = 0 := by simp [csum]
    rw [carry, h0]
    simp
  have hcn : carry c n = 0 := by
    have := hspec n le_rfl
    rw [hcsumn] at this
    exact (mul_eq_zero.mp this).resolve_right (by positivity)
  have hrec : ∀ t < n, c t = 2 * carry c (t + 1) - carry c t := by
    intro t ht
    have h1 := hspec t (le_of_lt ht)
    have h2 := hspec (t + 1) ht
    have h3 : csum c (t + 1) = csum c t + c t * (2 : ℤ) ^ t := by
      rw [csum, csum, Finset.sum_range_succ]
    rw [h3] at h2
    have h4 : (2 * carry c (t + 1)) * (2 : ℤ) ^ t = (carry c t + c t) * (2 : ℤ) ^ t := by
      rw [pow_succ] at h2
      nlinarith [h1, h2]
    have h5 := mul_right_cancel₀ (by positivity : (2 : ℤ) ^ t ≠ 0) h4
    linarith
  refine ⟨hc0, hcn, hrec, ?_⟩
  have hsumrec : (∑ t ∈ Finset.range n, c t)
      = ∑ t ∈ Finset.range n, (2 * carry c (t + 1) - carry c t) :=
    Finset.sum_congr rfl fun t ht => hrec t (Finset.mem_range.mp ht)
  rw [hsumrec, Finset.sum_sub_distrib]
  have h2 : (∑ t ∈ Finset.range n, 2 * carry c (t + 1))
      = 2 * ∑ t ∈ Finset.range n, carry c (t + 1) := by
    rw [Finset.mul_sum]
  have hA : (∑ t ∈ Finset.range n, carry c (t + 1))
      = (∑ t ∈ Finset.range (n + 1), carry c t) - carry c 0 := by
    have := Finset.sum_range_succ' (carry c) n
    linarith
  have hB : (∑ t ∈ Finset.range n, carry c t)
      = (∑ t ∈ Finset.range (n + 1), carry c t) - carry c n := by
    have := Finset.sum_range_succ (carry c) n
    linarith
  rw [h2, hA, hB, hc0, hcn]
  ring

/-- Classification of the carries when `-1 ≤ c t ≤ 2`: all carries lie in `{0,1}`. -/
theorem carry_mem_nonneg {n : ℕ} {c κ : ℕ → ℤ} (hκ0 : κ 0 = 0)
    (hrec : ∀ t < n, c t = 2 * κ (t + 1) - κ t)
    (hc : ∀ t < n, -1 ≤ c t ∧ c t ≤ 2) :
    ∀ t ≤ n, 0 ≤ κ t ∧ κ t ≤ 1 := by
  intro t
  induction t with
  | zero => intro _; rw [hκ0]; norm_num
  | succ t ih =>
      intro ht
      have ht' : t < n := by omega
      have ih' := ih (by omega)
      have hc' := hc t ht'
      have hr := hrec t ht'
      constructor <;> omega

/-- Classification of the carries when `-2 ≤ c t ≤ 1`: all carries lie in `{-1,0}`. -/
theorem carry_mem_nonpos {n : ℕ} {c κ : ℕ → ℤ} (hκ0 : κ 0 = 0)
    (hrec : ∀ t < n, c t = 2 * κ (t + 1) - κ t)
    (hc : ∀ t < n, -2 ≤ c t ∧ c t ≤ 1) :
    ∀ t ≤ n, -1 ≤ κ t ∧ κ t ≤ 0 := by
  intro t
  induction t with
  | zero => intro _; rw [hκ0]; norm_num
  | succ t ih =>
      intro ht
      have ht' : t < n := by omega
      have ih' := ih (by omega)
      have hc' := hc t ht'
      have hr := hrec t ht'
      constructor <;> omega

/-- `∑ t < n, 2 ^ t = 2 ^ n - 1` in `ℤ`. -/
theorem sum_pow_two (n : ℕ) : (∑ t ∈ Finset.range n, (2 : ℤ) ^ t) = (2 : ℤ) ^ n - 1 := by
  have := geom_sum_mul (2 : ℤ) n
  simpa using this

/-- Splitting `∑ t < n, (d t + a) * 2 ^ t`. -/
theorem sum_add_mul_pow (n : ℕ) (d : ℕ → ℤ) (a : ℤ) :
    (∑ t ∈ Finset.range n, (d t + a) * (2 : ℤ) ^ t)
      = (∑ t ∈ Finset.range n, d t * (2 : ℤ) ^ t) + a * ((2 : ℤ) ^ n - 1) := by
  have h1 : (∑ t ∈ Finset.range n, (d t + a) * (2 : ℤ) ^ t)
      = (∑ t ∈ Finset.range n, d t * (2 : ℤ) ^ t)
        + ∑ t ∈ Finset.range n, a * (2 : ℤ) ^ t := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [h1, ← Finset.mul_sum, sum_pow_two]

/-- If `∑ t < n, c t * 2 ^ t = 0` with `-1 ≤ c t ≤ 2` and `∑ t < n, c t = 0`, then `c = 0`. -/
theorem digit_zero {n : ℕ} {c : ℕ → ℤ}
    (hrel : ∑ t ∈ Finset.range n, c t * (2 : ℤ) ^ t = 0)
    (hc : ∀ t < n, -1 ≤ c t ∧ c t ≤ 2)
    (hsum : ∑ t ∈ Finset.range n, c t = 0) :
    ∀ t < n, c t = 0 := by
  obtain ⟨hc0, hcn, hrec, hsumκ⟩ := carry_spec hrel
  have hclass := carry_mem_nonneg hc0 hrec hc
  have hzero : ∀ t < n, carry c t = 0 := by
    have h1 : (∑ t ∈ Finset.range n, carry c t) = 0 := by rw [hsumκ, hsum]
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun t ht => (hclass t (le_of_lt (Finset.mem_range.mp ht))).1)).mp h1
    intro t ht
    exact h2 t (Finset.mem_range.mpr ht)
  intro t ht
  have h1 : c t = 2 * carry c (t + 1) - carry c t := hrec t ht
  have h2 : carry c t = 0 := hzero t ht
  have h3 : carry c (t + 1) = 0 := by
    by_cases h : t + 1 = n
    · rw [h, hcn]
    · exact hzero (t + 1) (by omega)
  rw [h1, h2, h3]
  ring

/-- If `∑ t < n, c t * 2 ^ t = 0` with `-2 ≤ c t ≤ 1` and `∑ t < n, c t = -n`, contradiction. -/
theorem digit_one {n : ℕ} (hn : 0 < n) {c : ℕ → ℤ}
    (hrel : ∑ t ∈ Finset.range n, c t * (2 : ℤ) ^ t = 0)
    (hc : ∀ t < n, -2 ≤ c t ∧ c t ≤ 1)
    (hsum : ∑ t ∈ Finset.range n, c t = -(n : ℤ)) : False := by
  obtain ⟨hc0, hcn, hrec, hsumκ⟩ := carry_spec hrel
  have hclass := carry_mem_nonpos hc0 hrec hc
  have hbound : -((n : ℤ) - 1) ≤ ∑ t ∈ Finset.range n, carry c t := by
    have hsplit : (∑ t ∈ Finset.range n, carry c t)
        = (∑ t ∈ Finset.range (n - 1), carry c (t + 1)) + carry c 0 := by
      have hsp := Finset.sum_range_succ' (carry c) (n - 1)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hsp
      linarith
    rw [hsplit, hc0, add_zero]
    calc (∑ t ∈ Finset.range (n - 1), carry c (t + 1))
        ≥ ∑ t ∈ Finset.range (n - 1), (-1 : ℤ) := by
          refine Finset.sum_le_sum fun t ht => ?_
          have htn : t + 1 ≤ n := by have := Finset.mem_range.mp ht; omega
          exact (hclass (t + 1) htn).1
      _ = -((n : ℤ) - 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            Nat.cast_sub (by omega : 1 ≤ n)]
          ring
  linarith [hsumκ, hsum]

/-- The digit analysis: an integer combination of powers of `2` with coefficients in
`[-1,2]` and sum of coefficients `0` which is a multiple of `2 ^ n - 1` must be `0`. -/
theorem digit_analysis {n : ℕ} (hn : 0 < n) {d : ℕ → ℤ} (K : ℤ)
    (hdlo : ∀ t < n, -1 ≤ d t) (hdhi : ∀ t < n, d t ≤ 2)
    (hsum : ∑ t ∈ Finset.range n, d t = 0)
    (hK : ∑ t ∈ Finset.range n, d t * (2 : ℤ) ^ t = K * ((2 : ℤ) ^ n - 1)) :
    ∀ t < n, d t = 0 := by
  have hMpos : 0 < (2 : ℤ) ^ n - 1 := by
    have h1 : (2 : ℤ) ^ 1 ≤ (2 : ℤ) ^ n := pow_le_pow_right₀ (by norm_num) (by omega : 1 ≤ n)
    have : (2 : ℤ) ≤ (2 : ℤ) ^ n := by simpa using h1
    linarith
  have hbound : |∑ t ∈ Finset.range n, d t * (2 : ℤ) ^ t| ≤ 2 * ((2 : ℤ) ^ n - 1) := by
    have h1 : |∑ t ∈ Finset.range n, d t * (2 : ℤ) ^ t|
        ≤ ∑ t ∈ Finset.range n, |d t * (2 : ℤ) ^ t| := Finset.abs_sum_le_sum_abs _ _
    have h2 : (∑ t ∈ Finset.range n, |d t * (2 : ℤ) ^ t|)
        ≤ ∑ t ∈ Finset.range n, 2 * (2 : ℤ) ^ t := by
      refine Finset.sum_le_sum fun t ht => ?_
      have hlt := Finset.mem_range.mp ht
      have hpt : (0 : ℤ) < (2 : ℤ) ^ t := by positivity
      have hdt : |d t| ≤ 2 := by
        rw [abs_le]; exact ⟨by linarith [hdlo t hlt], hdhi t hlt⟩
      rw [abs_mul, abs_of_nonneg (le_of_lt hpt)]
      nlinarith
    have h3 : (∑ t ∈ Finset.range n, 2 * (2 : ℤ) ^ t) = 2 * ((2 : ℤ) ^ n - 1) := by
      rw [← Finset.mul_sum, sum_pow_two]
    linarith
  have hKabs : |K| ≤ 2 := by
    have hmul : |K| * ((2 : ℤ) ^ n - 1) = |K * ((2 : ℤ) ^ n - 1)| := by
      rw [abs_mul, abs_of_nonneg (le_of_lt hMpos)]
    rw [hK] at hbound
    rw [← hmul] at hbound
    nlinarith [hbound, hMpos]
  have hcases : K = -2 ∨ K = -1 ∨ K = 0 ∨ K = 1 ∨ K = 2 := by
    have := abs_le.mp hKabs
    omega
  rcases hcases with hK2 | hK1 | hK0 | hKp1 | hKp2
  · -- `K = -2`
    exfalso
    have hpos : 0 < ∑ t ∈ Finset.range n, (d t + 2) * (2 : ℤ) ^ t := by
      refine Finset.sum_pos (fun t ht => ?_) ⟨0, Finset.mem_range.mpr hn⟩
      have hlt := Finset.mem_range.mp ht
      have hpt : (0 : ℤ) < (2 : ℤ) ^ t := by positivity
      have hp := hdlo t hlt
      nlinarith
    have hzero : (∑ t ∈ Finset.range n, (d t + 2) * (2 : ℤ) ^ t) = 0 := by
      rw [sum_add_mul_pow, hK, hK2]; ring
    linarith
  · -- `K = -1`
    exfalso
    have hzero : (∑ t ∈ Finset.range n, (d t + 1) * (2 : ℤ) ^ t) = 0 := by
      rw [sum_add_mul_pow, hK, hK1]; ring
    have hnn : ∀ t ∈ Finset.range n, 0 ≤ (d t + 1) * (2 : ℤ) ^ t := by
      intro t ht
      have hlt := Finset.mem_range.mp ht
      have hpt : (0 : ℤ) ≤ (2 : ℤ) ^ t := by positivity
      have hp := hdlo t hlt
      nlinarith
    have hz : ∀ t ∈ Finset.range n, (d t + 1) * (2 : ℤ) ^ t = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero
    have hd1 : ∀ t < n, d t = -1 := by
      intro t ht
      have hpt : (0 : ℤ) < (2 : ℤ) ^ t := by positivity
      have h1 := hz t (Finset.mem_range.mpr ht)
      rcases mul_eq_zero.mp h1 with h | h
      · omega
      · exact absurd h (ne_of_gt hpt)
    have hneg : (∑ t ∈ Finset.range n, d t) = -(n : ℤ) := by
      have : (∑ t ∈ Finset.range n, d t) = ∑ t ∈ Finset.range n, (-1 : ℤ) :=
        Finset.sum_congr rfl fun t ht => hd1 t (Finset.mem_range.mp ht)
      rw [this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    rw [hsum] at hneg
    have hn0 : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
    linarith
  · -- `K = 0`
    intro t ht
    have hrel0 : (∑ s ∈ Finset.range n, d s * (2 : ℤ) ^ s) = 0 := by
      rw [hK, hK0]; ring
    exact digit_zero hrel0 (fun s hs => ⟨hdlo s hs, hdhi s hs⟩) hsum t ht
  · -- `K = 1`
    exfalso
    have hrel : (∑ t ∈ Finset.range n, (d t - 1) * (2 : ℤ) ^ t) = 0 := by
      have h1 := sum_add_mul_pow n d (-1)
      have h2 : (∑ t ∈ Finset.range n, (d t - 1) * (2 : ℤ) ^ t)
          = (∑ t ∈ Finset.range n, d t * (2 : ℤ) ^ t) + (-1) * ((2 : ℤ) ^ n - 1) := by
        simpa [sub_eq_add_neg] using h1
      rw [h2, hK, hKp1]; ring
    have hc : ∀ t < n, -2 ≤ d t - 1 ∧ d t - 1 ≤ 1 :=
      fun t ht => ⟨by have := hdlo t ht; omega, by have := hdhi t ht; omega⟩
    have hsum' : (∑ t ∈ Finset.range n, (d t - 1)) = -(n : ℤ) := by
      rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    exact digit_one hn hrel hc hsum'
  · -- `K = 2`
    exfalso
    have hzero : (∑ t ∈ Finset.range n, (d t - 2) * (2 : ℤ) ^ t) = 0 := by
      have h1 := sum_add_mul_pow n d (-2)
      have h2 : (∑ t ∈ Finset.range n, (d t - 2) * (2 : ℤ) ^ t)
          = (∑ t ∈ Finset.range n, d t * (2 : ℤ) ^ t) + (-2) * ((2 : ℤ) ^ n - 1) := by
        simpa [sub_eq_add_neg] using h1
      rw [h2, hK, hKp2]; ring
    have hnp : ∀ t ∈ Finset.range n, (d t - 2) * (2 : ℤ) ^ t ≤ 0 := by
      intro t ht
      have hlt := Finset.mem_range.mp ht
      have hpt : (0 : ℤ) < (2 : ℤ) ^ t := by positivity
      have hp := hdhi t hlt
      nlinarith
    have hz : ∀ t ∈ Finset.range n, (d t - 2) * (2 : ℤ) ^ t = 0 :=
      (Finset.sum_eq_zero_iff_of_nonpos hnp).mp hzero
    have hd2 : ∀ t < n, d t = 2 := by
      intro t ht
      have hpt : (0 : ℤ) < (2 : ℤ) ^ t := by positivity
      have h1 := hz t (Finset.mem_range.mpr ht)
      rcases mul_eq_zero.mp h1 with h | h
      · omega
      · exact absurd h (ne_of_gt hpt)
    have htwo : (∑ t ∈ Finset.range n, d t) = 2 * (n : ℤ) := by
      have : (∑ t ∈ Finset.range n, d t) = ∑ t ∈ Finset.range n, (2 : ℤ) :=
        Finset.sum_congr rfl fun t ht => hd2 t (Finset.mem_range.mp ht)
      rw [this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    rw [hsum] at htwo
    have hn0 : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
    linarith

/-- **Sparse sums of powers of `2` modulo `2 ^ n - 1`.**

Let `n > 0` and let `A`, `B` be multisets of natural numbers, all of whose elements are
`< n`, with `A.card = B.card = 4`, every element of `A` of multiplicity at most `2`
(i.e. `A.count t ≤ 2` for all `t`) and all elements of `B` distinct (`B.count t ≤ 1`).
If `∑ a ∈ A, 2 ^ a ≡ ∑ b ∈ B, 2 ^ b (mod 2 ^ n - 1)` then `A = B`. -/
theorem sparse_matching {n : ℕ} (hn : 0 < n) {A B : Multiset ℕ}
    (hA : ∀ a ∈ A, a < n) (hB : ∀ b ∈ B, b < n)
    (hA4 : A.card = 4) (hB4 : B.card = 4)
    (hAm : ∀ t, A.count t ≤ 2) (hBm : ∀ t, B.count t ≤ 1)
    (h : (A.map (fun a => 2 ^ a)).sum ≡ (B.map (fun b => 2 ^ b)).sum [MOD 2 ^ n - 1]) :
    A = B := by
  -- the sums of the counts
  have hcA : (∑ t ∈ Finset.range n, (A.count t : ℤ) * (2 : ℤ) ^ t)
      = (A.map (fun a => (2 : ℤ) ^ a)).sum := by
    rw [Finset.sum_multiset_map_count A (fun t => (2 : ℤ) ^ t)]
    have hsub : A.toFinset ⊆ Finset.range n := fun x hx =>
      Finset.mem_range.mpr (hA x (Multiset.mem_toFinset.mp hx))
    have hz : ∀ x ∈ Finset.range n, x ∉ A.toFinset → A.count x • (2 : ℤ) ^ x = 0 := by
      intro x _ hx
      have h0 : A.count x = 0 := Multiset.count_eq_zero_of_notMem (by simpa using hx)
      simp [h0]
    rw [Finset.sum_subset hsub hz]
    simp only [nsmul_eq_mul]
  have hcB : (∑ t ∈ Finset.range n, (B.count t : ℤ) * (2 : ℤ) ^ t)
      = (B.map (fun b => (2 : ℤ) ^ b)).sum := by
    rw [Finset.sum_multiset_map_count B (fun t => (2 : ℤ) ^ t)]
    have hsub : B.toFinset ⊆ Finset.range n := fun x hx =>
      Finset.mem_range.mpr (hB x (Multiset.mem_toFinset.mp hx))
    have hz : ∀ x ∈ Finset.range n, x ∉ B.toFinset → B.count x • (2 : ℤ) ^ x = 0 := by
      intro x _ hx
      have h0 : B.count x = 0 := Multiset.count_eq_zero_of_notMem (by simpa using hx)
      simp [h0]
    rw [Finset.sum_subset hsub hz]
    simp only [nsmul_eq_mul]
  -- casts of the two sums
  have hAZ : (((A.map (fun a => 2 ^ a)).sum : ℕ) : ℤ) = (A.map (fun a => (2 : ℤ) ^ a)).sum := by
    rw [Nat.cast_multiset_sum, Multiset.map_map]
    congr 1
  have hBZ : (((B.map (fun b => 2 ^ b)).sum : ℕ) : ℤ) = (B.map (fun b => (2 : ℤ) ^ b)).sum := by
    rw [Nat.cast_multiset_sum, Multiset.map_map]
    congr 1
  -- divisibility
  obtain ⟨K, hKrel⟩ : ∃ K : ℤ, (((B.map (fun b => 2 ^ b)).sum : ℕ) : ℤ)
      - (((A.map (fun a => 2 ^ a)).sum : ℕ) : ℤ) = K * ((2 : ℤ) ^ n - 1) := by
    obtain ⟨k, hk⟩ := Nat.modEq_iff_dvd.mp h
    have hMZ : ((((2 : ℕ) ^ n - 1 : ℕ)) : ℤ) = (2 : ℤ) ^ n - 1 := by
      rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow]
      norm_num
    refine ⟨k, ?_⟩
    rw [hMZ] at hk
    rw [hk, mul_comm]
  have hsumd : (∑ t ∈ Finset.range n, ((A.count t : ℤ) - (B.count t : ℤ)) * (2 : ℤ) ^ t)
      = (((A.map (fun a => 2 ^ a)).sum : ℕ) : ℤ)
        - (((B.map (fun b => 2 ^ b)).sum : ℕ) : ℤ) := by
    rw [hAZ, hBZ, ← hcA, ← hcB, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  have hrel : (∑ t ∈ Finset.range n, ((A.count t : ℤ) - (B.count t : ℤ)) * (2 : ℤ) ^ t)
      = (-K) * ((2 : ℤ) ^ n - 1) := by
    rw [hsumd]
    linarith [hKrel]
  have hlo : ∀ t < n, -1 ≤ (A.count t : ℤ) - (B.count t : ℤ) := by
    intro t ht
    have h1 : (B.count t : ℤ) ≤ 1 := by exact_mod_cast hBm t
    have h2 : (0 : ℤ) ≤ (A.count t : ℤ) := by positivity
    linarith
  have hhi : ∀ t < n, (A.count t : ℤ) - (B.count t : ℤ) ≤ 2 := by
    intro t ht
    have h1 : (A.count t : ℤ) ≤ 2 := by exact_mod_cast hAm t
    have h2 : (0 : ℤ) ≤ (B.count t : ℤ) := by positivity
    linarith
  have hsum0 : (∑ t ∈ Finset.range n, ((A.count t : ℤ) - (B.count t : ℤ))) = 0 := by
    rw [Finset.sum_sub_distrib]
    have h1 : (∑ t ∈ Finset.range n, (A.count t : ℤ)) = 4 := by
      rw [← Nat.cast_sum,
        Multiset.sum_count_eq_card (fun a ha => Finset.mem_range.mpr (hA a ha)), hA4]
      norm_num
    have h2 : (∑ t ∈ Finset.range n, (B.count t : ℤ)) = 4 := by
      rw [← Nat.cast_sum,
        Multiset.sum_count_eq_card (fun b hb => Finset.mem_range.mpr (hB b hb)), hB4]
      norm_num
    rw [h1, h2]; norm_num
  have hd : ∀ t < n, (A.count t : ℤ) - (B.count t : ℤ) = 0 :=
    digit_analysis hn (-K) hlo hhi hsum0 hrel
  refine Multiset.ext.mpr fun t => ?_
  by_cases ht : t < n
  · have h1 := hd t ht
    have h2 : (A.count t : ℤ) = (B.count t : ℤ) := by linarith
    exact_mod_cast h2
  · push_neg at ht
    have hAc : A.count t = 0 :=
      Multiset.count_eq_zero_of_notMem fun hmem => absurd (hA t hmem) (by omega)
    have hBc : B.count t = 0 :=
      Multiset.count_eq_zero_of_notMem fun hmem => absurd (hB t hmem) (by omega)
    rw [hAc, hBc]

end Work.Higman.Q3.L12
