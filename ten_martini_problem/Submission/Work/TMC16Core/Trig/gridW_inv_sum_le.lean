import Mathlib
import Submission.Work.TMC16Core.Trig.gridW

/-!
# Reciprocal sums of `gridW` with the minimal term removed

`gridW q A j` is the distance from `j + A` to the nearest multiple of `q` (for `0 ≤ A < q`,
`j < q`).  Writing `A = ⌊A⌋₊ + f` with `f = A - ⌊A⌋₊ ∈ [0,1)` one has
`gridW q A j = min (f + r) (q - f - r)` where `r = (j + ⌊A⌋₊) % q`, and `j ↦ r` is a bijection
of `{0, …, q-1}`.

Hence the values `gridW q A j` (`j < q`) are the values `min (f+i) (q-f-i)` (`i < q`) in some
order.  The latter function is a concave "tent" whose minimum is attained only at `i = 0` or at
`i = q-1`.  Removing that single term, the two reciprocal ramps are bounded by harmonic sums,
giving `4 * (1 + log q)`.
-/

noncomputable section

namespace Work.TMC16Core.Trig

/-! ## Harmonic sums -/

/-- `∑_{i<n} 1/(i+1)` -/
private def harmR (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, ((i : ℝ) + 1)⁻¹

private lemma harmR_le_one_add_log (n : ℕ) : harmR n ≤ 1 + Real.log (n : ℝ) := by
  have h : harmR n = (harmonic n : ℝ) := by
    unfold harmR harmonic
    push_cast
    ring
  rw [h]
  exact harmonic_le_one_add_log n

private lemma harmR_mono {m n : ℕ} (h : m ≤ n) : harmR m ≤ harmR n := by
  rw [harmR, harmR]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le hx h))
  · intro x _ _
    positivity

/-- The reciprocal of a minimum of two nonnegative numbers is at most the sum of reciprocals. -/
private lemma inv_min_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (min a b)⁻¹ ≤ a⁻¹ + b⁻¹ := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    have : 0 ≤ b⁻¹ := inv_nonneg.mpr hb
    linarith
  · rw [min_eq_right h]
    have : 0 ≤ a⁻¹ := inv_nonneg.mpr ha
    linarith

private lemma sum_inv_add_one_le_harmR (n : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    ∑ i ∈ Finset.range n, (v + ((i : ℝ) + 1))⁻¹ ≤ harmR n := by
  rw [harmR]
  apply Finset.sum_le_sum
  intro i _
  rw [inv_le_inv₀ (by linarith : (0 : ℝ) < v + ((i : ℝ) + 1)) (by positivity : (0 : ℝ) < (i : ℝ) + 1)]
  linarith

private lemma sum_inv_le_inv_add_harmR (n : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    ∑ i ∈ Finset.range n, (v + (i : ℝ))⁻¹ ≤ v⁻¹ + harmR n := by
  rcases Nat.eq_zero_or_pos n with h | hn
  · subst h
    rw [Finset.range_zero, Finset.sum_empty, harmR, Finset.range_zero, Finset.sum_empty]
    exact add_nonneg (inv_nonneg.mpr hv) le_rfl
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one]
    have h1 : ∑ k ∈ Finset.range m, (v + ((k : ℝ) + 1))⁻¹ ≤ harmR m :=
      sum_inv_add_one_le_harmR m hv
    have h2 : harmR m ≤ harmR (m + 1) := harmR_mono (by omega)
    linarith

private lemma sum_inv_le_harmR_of_one_le (n : ℕ) {v : ℝ} (hv : 1 ≤ v) :
    ∑ i ∈ Finset.range n, (v + (i : ℝ))⁻¹ ≤ harmR n := by
  rw [harmR]
  apply Finset.sum_le_sum
  intro i _
  rw [inv_le_inv₀ (by linarith : (0 : ℝ) < v + (i : ℝ)) (by positivity : (0 : ℝ) < (i : ℝ) + 1)]
  linarith

/-! ## The analytic core: the reciprocal sum of the tent function with its minimum removed -/

/-- The tent function `i ↦ min (f+i) (q-f-i)` on the grid `{0, …, q-1}`. -/
private def cfun (q : ℕ) (f : ℝ) (i : ℕ) : ℝ :=
  min (f + (i : ℝ)) ((q : ℝ) - f - (i : ℝ))

private lemma sum_inv_min_shift_le {q : ℕ} (hq : 2 ≤ q) {f : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1)
    {i₁ : ℕ} (hi₁ : i₁ < q) (hmin : ∀ i < q, cfun q f i₁ ≤ cfun q f i) :
    ∑ i ∈ (Finset.range q).erase i₁, (cfun q f i)⁻¹ ≤ 4 * (1 + Real.log (q : ℝ)) := by
  have hq0 : 0 < q := by omega
  have hq1 : 1 ≤ q := by omega
  have hcast1 : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub hq1]; norm_num
  have hcast2 : ((q - 2 : ℕ) : ℝ) = (q : ℝ) - 2 := by
    rw [Nat.cast_sub (show 2 ≤ q from hq)]; norm_num
  -- values at the two endpoints
  have hc0 : cfun q f 0 = f := by
    have hle : f ≤ (q : ℝ) - f := by
      have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      linarith
    simp only [cfun, Nat.cast_zero, add_zero, sub_zero]
    exact min_eq_left hle
  have hcq1 : cfun q f (q - 1) = 1 - f := by
    have hle : (1 : ℝ) - f ≤ f + ((q : ℝ) - 1) := by
      have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      linarith
    have harg : (q : ℝ) - f - ((q : ℝ) - 1) = 1 - f := by ring
    simp only [cfun]
    rw [hcast1, harg]
    exact min_eq_right hle
  -- `cfun q f i₁` is the minimum, hence at most the values at both endpoints
  have hi0 : cfun q f i₁ ≤ f := by
    have h := hmin 0 hq0
    rwa [hc0] at h
  have hi1 : cfun q f i₁ ≤ 1 - f := by
    have h := hmin (q - 1) (by omega)
    rwa [hcq1] at h
  -- final numerical bound
  have hfin : 2 + 2 * harmR (q - 1) ≤ 4 * (1 + Real.log (q : ℝ)) := by
    have h1 : harmR q ≤ 1 + Real.log (q : ℝ) := harmR_le_one_add_log q
    have h2 : harmR (q - 1) ≤ harmR q := harmR_mono (by omega)
    have h3 : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq1)
    linarith
  rcases eq_or_ne i₁ 0 with h0 | h0
  · -- the minimum is attained at `0`
    subst h0
    have hf12 : f ≤ 1 / 2 := by
      have h := hmin (q - 1) (by omega)
      rw [hcq1, hc0] at h
      linarith
    -- rewrite the sum over `range q \ {0}` as a sum over `range (q-1)` of shifted terms
    have hsum : ∑ i ∈ (Finset.range q).erase 0, (cfun q f i)⁻¹ =
        ∑ i ∈ Finset.range (q - 1), (cfun q f (i + 1))⁻¹ := by
      have h1 := Finset.sum_range_succ' (fun i => (cfun q f i)⁻¹) (q - 1)
      rw [Nat.sub_add_cancel hq1] at h1
      have h2 := Finset.sum_erase_add (Finset.range q) (fun i => (cfun q f i)⁻¹)
        (Finset.mem_range.mpr hq0)
      linarith
    rw [hsum]
    have hbound : ∑ i ∈ Finset.range (q - 1), (cfun q f (i + 1))⁻¹ ≤ 2 + 2 * harmR (q - 1) := by
      have hsplit : ∑ i ∈ Finset.range (q - 1), (cfun q f (i + 1))⁻¹ ≤
          ∑ i ∈ Finset.range (q - 1),
            ((f + ((i : ℝ) + 1))⁻¹ + ((q : ℝ) - f - ((i : ℝ) + 1))⁻¹) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i < q - 1 := Finset.mem_range.mp hi
        have hle : i + 1 ≤ q - 1 := by omega
        have hiq : (i : ℝ) + 1 ≤ (q : ℝ) - 1 := by
          calc (i : ℝ) + 1 = ((i + 1 : ℕ) : ℝ) := by push_cast; ring
            _ ≤ ((q - 1 : ℕ) : ℝ) := by exact_mod_cast hle
            _ = (q : ℝ) - 1 := hcast1
        have h1 : 0 ≤ f + ((i : ℝ) + 1) := by linarith
        have h2 : 0 ≤ (q : ℝ) - f - ((i : ℝ) + 1) := by linarith
        have := inv_min_le (a := f + ((i : ℝ) + 1)) (b := (q : ℝ) - f - ((i : ℝ) + 1)) h1 h2
        simpa only [cfun, Nat.cast_add, Nat.cast_one] using this
      have hA : ∑ i ∈ Finset.range (q - 1), (f + ((i : ℝ) + 1))⁻¹ ≤ harmR (q - 1) :=
        sum_inv_add_one_le_harmR (q - 1) hf0
      have hB : ∑ i ∈ Finset.range (q - 1), ((q : ℝ) - f - ((i : ℝ) + 1))⁻¹ ≤
          (1 - f)⁻¹ + harmR (q - 1) := by
        have hrefl : ∑ i ∈ Finset.range (q - 1), ((q : ℝ) - f - ((i : ℝ) + 1))⁻¹ =
            ∑ i ∈ Finset.range (q - 1), ((1 - f) + (i : ℝ))⁻¹ := by
          rw [← Finset.sum_range_reflect (fun k => ((1 - f) + (k : ℝ))⁻¹) (q - 1)]
          apply Finset.sum_congr rfl
          intro j hj
          have hjle : j ≤ q - 2 := by
            have : j < q - 1 := Finset.mem_range.mp hj
            omega
          have hnat : (q - 1) - 1 - j = q - 2 - j := by omega
          have hcastj : ((q - 2 - j : ℕ) : ℝ) = (q : ℝ) - 2 - (j : ℝ) := by
            rw [Nat.cast_sub hjle, hcast2]
          have harg : (q : ℝ) - f - ((j : ℝ) + 1) = (1 - f) + ((q - 2 - j : ℕ) : ℝ) := by
            rw [hcastj]; ring
          rw [hnat, harg]
        rw [hrefl]
        exact sum_inv_le_inv_add_harmR (q - 1) (by linarith : 0 ≤ 1 - f)
      have h2f : (1 - f)⁻¹ ≤ 2 := by
        calc (1 - f)⁻¹ = 1 / (1 - f) := by rw [one_div]
          _ ≤ 1 / (1 / 2 : ℝ) := one_div_le_one_div_of_le (by norm_num) (by linarith)
          _ = 2 := by norm_num
      calc ∑ i ∈ Finset.range (q - 1), (cfun q f (i + 1))⁻¹
          ≤ ∑ i ∈ Finset.range (q - 1),
              ((f + ((i : ℝ) + 1))⁻¹ + ((q : ℝ) - f - ((i : ℝ) + 1))⁻¹) := hsplit
        _ = (∑ i ∈ Finset.range (q - 1), (f + ((i : ℝ) + 1))⁻¹) +
              (∑ i ∈ Finset.range (q - 1), ((q : ℝ) - f - ((i : ℝ) + 1))⁻¹) :=
              Finset.sum_add_distrib
        _ ≤ harmR (q - 1) + ((1 - f)⁻¹ + harmR (q - 1)) := add_le_add hA hB
        _ ≤ 2 + 2 * harmR (q - 1) := by linarith
    linarith
  · -- the minimum is attained at the other end: `i₁ = q-1` and `1/2 ≤ f`
    have hpos : 1 ≤ i₁ := by omega
    have hipos : (1 : ℝ) ≤ (i₁ : ℝ) := by exact_mod_cast hpos
    have hiq : (i₁ : ℝ) ≤ (q : ℝ) - 1 := by
      have hle : i₁ ≤ q - 1 := by omega
      calc (i₁ : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by exact_mod_cast hle
        _ = (q : ℝ) - 1 := hcast1
    have hfge : 1 / 2 ≤ f := by
      have hle : (1 : ℝ) - f ≤ cfun q f i₁ := by
        simp only [cfun]
        exact le_min (by linarith) (by linarith)
      linarith
    have hi₁_eq : i₁ = q - 1 := by
      by_contra hne
      have hle : i₁ ≤ q - 2 := by omega
      have hiq2 : (i₁ : ℝ) ≤ (q : ℝ) - 2 := by
        calc (i₁ : ℝ) ≤ ((q - 2 : ℕ) : ℝ) := by exact_mod_cast hle
          _ = (q : ℝ) - 2 := hcast2
      have hlt : (1 : ℝ) - f < cfun q f i₁ := by
        simp only [cfun]
        exact lt_min (by linarith) (by linarith)
      linarith
    subst hi₁_eq
    have hsum : ∑ i ∈ (Finset.range q).erase (q - 1), (cfun q f i)⁻¹ =
        ∑ i ∈ Finset.range (q - 1), (cfun q f i)⁻¹ := by
      have h1 := Finset.sum_range_succ (fun i => (cfun q f i)⁻¹) (q - 1)
      rw [Nat.sub_add_cancel hq1] at h1
      have h2 := Finset.sum_erase_add (Finset.range q) (fun i => (cfun q f i)⁻¹)
        (Finset.mem_range.mpr (by omega : q - 1 < q))
      linarith
    rw [hsum]
    have hbound : ∑ i ∈ Finset.range (q - 1), (cfun q f i)⁻¹ ≤ 2 + 2 * harmR (q - 1) := by
      have hsplit : ∑ i ∈ Finset.range (q - 1), (cfun q f i)⁻¹ ≤
          ∑ i ∈ Finset.range (q - 1),
            ((f + (i : ℝ))⁻¹ + ((q : ℝ) - f - (i : ℝ))⁻¹) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i < q - 1 := Finset.mem_range.mp hi
        have hiq' : (i : ℝ) ≤ (q : ℝ) - 1 := by
          have hle : i ≤ q - 1 := by omega
          calc (i : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by exact_mod_cast hle
            _ = (q : ℝ) - 1 := hcast1
        have h1 : 0 ≤ f + (i : ℝ) := by linarith
        have h2 : 0 ≤ (q : ℝ) - f - (i : ℝ) := by linarith
        have := inv_min_le (a := f + (i : ℝ)) (b := (q : ℝ) - f - (i : ℝ)) h1 h2
        simpa only [cfun] using this
      have hA : ∑ i ∈ Finset.range (q - 1), (f + (i : ℝ))⁻¹ ≤ f⁻¹ + harmR (q - 1) :=
        sum_inv_le_inv_add_harmR (q - 1) hf0
      have hfinv : f⁻¹ ≤ 2 := by
        calc f⁻¹ = 1 / f := by rw [one_div]
          _ ≤ 1 / (1 / 2 : ℝ) := one_div_le_one_div_of_le (by norm_num) hfge
          _ = 2 := by norm_num
      have hB : ∑ i ∈ Finset.range (q - 1), ((q : ℝ) - f - (i : ℝ))⁻¹ ≤ harmR (q - 1) := by
        have hrefl : ∑ i ∈ Finset.range (q - 1), ((q : ℝ) - f - (i : ℝ))⁻¹ =
            ∑ i ∈ Finset.range (q - 1), ((2 - f) + (i : ℝ))⁻¹ := by
          rw [← Finset.sum_range_reflect (fun k => ((2 - f) + (k : ℝ))⁻¹) (q - 1)]
          apply Finset.sum_congr rfl
          intro j hj
          have hjle : j ≤ q - 2 := by
            have : j < q - 1 := Finset.mem_range.mp hj
            omega
          have hnat : (q - 1) - 1 - j = q - 2 - j := by omega
          have hcastj : ((q - 2 - j : ℕ) : ℝ) = (q : ℝ) - 2 - (j : ℝ) := by
            rw [Nat.cast_sub hjle, hcast2]
          have harg : (q : ℝ) - f - (j : ℝ) = (2 - f) + ((q - 2 - j : ℕ) : ℝ) := by
            rw [hcastj]; ring
          rw [hnat, harg]
        rw [hrefl]
        exact sum_inv_le_harmR_of_one_le (q - 1) (by linarith : 1 ≤ 2 - f)
      calc ∑ i ∈ Finset.range (q - 1), (cfun q f i)⁻¹
          ≤ ∑ i ∈ Finset.range (q - 1),
              ((f + (i : ℝ))⁻¹ + ((q : ℝ) - f - (i : ℝ))⁻¹) := hsplit
        _ = (∑ i ∈ Finset.range (q - 1), (f + (i : ℝ))⁻¹) +
              (∑ i ∈ Finset.range (q - 1), ((q : ℝ) - f - (i : ℝ))⁻¹) :=
              Finset.sum_add_distrib
        _ ≤ (f⁻¹ + harmR (q - 1)) + harmR (q - 1) := add_le_add hA hB
        _ ≤ 2 + 2 * harmR (q - 1) := by linarith
    linarith

/-! ## `gridW` on the standard grid -/

/-- The three candidate distances appearing in `gridW`, for a point of the form
`x = s*q + y` with `s ≤ 1` and `y ∈ [0,q]`, reduce to `min y (q - y)`. -/
private lemma min_three_eq (q : ℕ) (hq : 0 < q) {x y : ℝ} {s : ℕ} (hs : s ≤ 1)
    (hy0 : 0 ≤ y) (hyq : y ≤ (q : ℝ)) (hx : x = (s : ℝ) * (q : ℝ) + y) :
    min (min x |x - (q : ℝ)|) (2 * (q : ℝ) - x) = min y ((q : ℝ) - y) := by
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
  rw [hx]
  rcases (by omega : s = 0 ∨ s = 1) with h | h
  · subst h
    simp only [Nat.cast_zero, zero_mul, zero_add]
    have habs : |y - (q : ℝ)| = (q : ℝ) - y := by
      rw [abs_of_nonpos (sub_nonpos.mpr hyq)]
      ring
    rw [habs]
    have hle : min y ((q : ℝ) - y) ≤ 2 * (q : ℝ) - y := by
      have h1 : min y ((q : ℝ) - y) ≤ (q : ℝ) - y := min_le_right _ _
      linarith
    exact min_eq_left hle
  · subst h
    simp only [Nat.cast_one, one_mul]
    have habs : |(q : ℝ) + y - (q : ℝ)| = y := by
      rw [add_sub_cancel_left, abs_of_nonneg hy0]
    rw [habs]
    rw [min_eq_right (show y ≤ (q : ℝ) + y by linarith)]
    rw [show 2 * (q : ℝ) - ((q : ℝ) + y) = (q : ℝ) - y by ring]

private lemma gridW_mod_eq {q : ℕ} (hq : 0 < q) {A : ℝ} (hA0 : 0 ≤ A) (hAq : A < (q : ℝ))
    {j : ℕ} (hj : j < q) :
    gridW q A j =
      min ((A - (⌊A⌋₊ : ℝ)) + (((j + ⌊A⌋₊) % q : ℕ) : ℝ))
        ((q : ℝ) - (A - (⌊A⌋₊ : ℝ)) - (((j + ⌊A⌋₊) % q : ℕ) : ℝ)) := by
  have hf0 : 0 ≤ A - (⌊A⌋₊ : ℝ) := by
    have h := Nat.floor_le hA0
    linarith
  have hf1 : A - (⌊A⌋₊ : ℝ) < 1 := by
    have h := Nat.lt_floor_add_one A
    linarith
  have hnq : ⌊A⌋₊ < q := (Nat.floor_lt hA0).2 hAq
  have hrq : (j + ⌊A⌋₊) % q < q := Nat.mod_lt _ hq
  have hsplit : j + ⌊A⌋₊ = (j + ⌊A⌋₊) / q * q + (j + ⌊A⌋₊) % q :=
    (Nat.div_add_mod' _ _).symm
  have hs1 : (j + ⌊A⌋₊) / q ≤ 1 := by
    by_contra h
    have h2 : 2 * q ≤ (j + ⌊A⌋₊) / q * q := by
      have h' : 2 ≤ (j + ⌊A⌋₊) / q := by omega
      exact Nat.mul_le_mul_right q h'
    have h3 : j + ⌊A⌋₊ < 2 * q := by omega
    have h4 : (j + ⌊A⌋₊) / q * q ≤ j + ⌊A⌋₊ := Nat.div_mul_le_self _ _
    omega
  have hrle : (((j + ⌊A⌋₊) % q : ℕ) : ℝ) ≤ (q : ℝ) - 1 := by
    have hle : (j + ⌊A⌋₊) % q ≤ q - 1 := by omega
    calc (((j + ⌊A⌋₊) % q : ℕ) : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by exact_mod_cast hle
      _ = (q : ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ q)]; norm_num
  have hx : (j : ℝ) + A = (((j + ⌊A⌋₊) / q : ℕ) : ℝ) * (q : ℝ) +
      ((A - (⌊A⌋₊ : ℝ)) + (((j + ⌊A⌋₊) % q : ℕ) : ℝ)) := by
    have h1 : (j : ℝ) + (⌊A⌋₊ : ℝ) = (((j + ⌊A⌋₊) / q : ℕ) : ℝ) * (q : ℝ) +
        (((j + ⌊A⌋₊) % q : ℕ) : ℝ) := by
      have h := congrArg (fun n : ℕ => (n : ℝ)) hsplit
      push_cast at h
      exact h
    have h2 : (j : ℝ) + A = (j : ℝ) + (⌊A⌋₊ : ℝ) + (A - (⌊A⌋₊ : ℝ)) := by
      ring
    rw [h2, h1]; ring
  have hy0 : 0 ≤ (A - (⌊A⌋₊ : ℝ)) + (((j + ⌊A⌋₊) % q : ℕ) : ℝ) := by
    have h : (0 : ℝ) ≤ (((j + ⌊A⌋₊) % q : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hyq : (A - (⌊A⌋₊ : ℝ)) + (((j + ⌊A⌋₊) % q : ℕ) : ℝ) ≤ (q : ℝ) := by
    linarith
  rw [gridW, sub_sub]
  rw [show (q : ℝ) - (A - (⌊A⌋₊ : ℝ)) - (((j + ⌊A⌋₊) % q : ℕ) : ℝ) =
      (q : ℝ) - ((A - (⌊A⌋₊ : ℝ)) + (((j + ⌊A⌋₊) % q : ℕ) : ℝ)) by ring]
  exact min_three_eq q hq hs1 hy0 hyq hx

/-! ## The shift `j ↦ (j + n) % q` is a permutation of `{0, …, q-1}` -/

private lemma shift_mod_inj {q : ℕ} (hq : 0 < q) (n : ℕ) :
    ∀ j < q, ∀ k < q, (j + n) % q = (k + n) % q → j = k := by
  intro j hj k hk h
  have h2 : Nat.ModEq q (j + n) (k + n) := h
  exact (Nat.ModEq.add_right_cancel' n h2).eq_of_lt_of_lt hj hk

private lemma shift_mod_bij {q : ℕ} (hq : 0 < q) (n : ℕ) :
    (∀ i < q, ∃ j < q, (j + n) % q = i) ∧
      (∀ j < q, ∀ k < q, (j + n) % q = (k + n) % q → j = k) := by
  refine ⟨?_, shift_mod_inj hq n⟩
  have hinj : Set.InjOn (fun j => (j + n) % q) ↑(Finset.range q) := by
    intro j hj k hk h
    exact shift_mod_inj hq n j (Finset.mem_range.mp hj) k (Finset.mem_range.mp hk) h
  have hsub : (Finset.range q).image (fun j => (j + n) % q) ⊆ Finset.range q := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, -, rfl⟩
    exact Finset.mem_range.mpr (Nat.mod_lt _ hq)
  have hcard : ((Finset.range q).image (fun j => (j + n) % q)).card = q := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have heq : (Finset.range q).image (fun j => (j + n) % q) = Finset.range q := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [hcard, Finset.card_range]
  intro i hi
  have : i ∈ (Finset.range q).image (fun j => (j + n) % q) := by
    rw [heq]
    exact Finset.mem_range.mpr hi
  rcases Finset.mem_image.mp this with ⟨j, hj, hjq⟩
  exact ⟨j, Finset.mem_range.mp hj, hjq⟩

private lemma sum_erase_shift_mod {q : ℕ} (hq : 0 < q) (n : ℕ) {j₁ : ℕ} (hj₁ : j₁ < q)
    (F : ℕ → ℝ) :
    ∑ j ∈ (Finset.range q).erase j₁, F ((j + n) % q) =
      ∑ i ∈ (Finset.range q).erase ((j₁ + n) % q), F i := by
  have hinj := shift_mod_inj hq n
  have hsurj := (shift_mod_bij hq n).1
  refine Finset.sum_bij (fun a _ => (a + n) % q) ?_ ?_ ?_ ?_
  · intro a ha
    have haq : a < q := Finset.mem_range.mp (Finset.mem_of_mem_erase ha)
    have hane : a ≠ j₁ := Finset.ne_of_mem_erase ha
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_range.mpr (Nat.mod_lt _ hq)⟩
    intro hcontra
    exact hane (hinj a haq j₁ hj₁ hcontra)
  · intro a₁ ha₁ a₂ ha₂ h
    have h1 : a₁ < q := Finset.mem_range.mp (Finset.mem_of_mem_erase ha₁)
    have h2 : a₂ < q := Finset.mem_range.mp (Finset.mem_of_mem_erase ha₂)
    exact hinj a₁ h1 a₂ h2 h
  · intro b hb
    have hbq : b < q := Finset.mem_range.mp (Finset.mem_of_mem_erase hb)
    have hbne : b ≠ (j₁ + n) % q := Finset.ne_of_mem_erase hb
    rcases hsurj b hbq with ⟨a, haq, ha⟩
    refine ⟨a, ?_, ha⟩
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_range.mpr haq⟩
    intro hcontra
    exact hbne (by rw [← ha, hcontra])
  · intro a _
    rfl

/-! ## The main estimate -/

theorem gridW_inv_sum_le {q : ℕ} (hq : 0 < q) {A : ℝ} (hA0 : 0 ≤ A) (hAq : A < (q : ℝ))
    {j₁ : ℕ} (hj₁ : j₁ < q)
    (hmin : ∀ j < q, Work.TMC16Core.Trig.gridW q A j₁ ≤ Work.TMC16Core.Trig.gridW q A j) :
    ∑ j ∈ (Finset.range q).erase j₁, (Work.TMC16Core.Trig.gridW q A j)⁻¹ ≤ 4 * (1 + Real.log (q : ℝ)) := by
  rcases (by omega : q = 1 ∨ 2 ≤ q) with hq1 | hq2
  · subst hq1
    have hj : j₁ = 0 := by omega
    subst hj
    have hempty : (Finset.range 1).erase 0 = (∅ : Finset ℕ) := by
      rw [Finset.range_one, Finset.erase_singleton]
    rw [hempty, Finset.sum_empty, show ((1 : ℕ) : ℝ) = 1 by norm_num, Real.log_one]
    norm_num
  · let f : ℝ := A - (⌊A⌋₊ : ℝ)
    have hf0 : 0 ≤ f := by
      have h := Nat.floor_le hA0
      show 0 ≤ A - (⌊A⌋₊ : ℝ)
      linarith
    have hf1 : f < 1 := by
      have h := Nat.lt_floor_add_one A
      show A - (⌊A⌋₊ : ℝ) < 1
      linarith
    have hgreq : ∀ j < q, gridW q A j = cfun q f ((j + ⌊A⌋₊) % q) :=
      fun j hj => gridW_mod_eq hq hA0 hAq hj
    have hminc : ∀ i < q, cfun q f ((j₁ + ⌊A⌋₊) % q) ≤ cfun q f i := by
      intro i hi
      obtain ⟨j, hj, hjq⟩ := (shift_mod_bij hq ⌊A⌋₊).1 i hi
      have h1 : cfun q f i = gridW q A j := by rw [← hjq, ← hgreq j hj]
      have h2 : cfun q f ((j₁ + ⌊A⌋₊) % q) = gridW q A j₁ := (hgreq j₁ hj₁).symm
      rw [h1, h2]
      exact hmin j hj
    have hsum : ∑ j ∈ (Finset.range q).erase j₁, (gridW q A j)⁻¹ =
        ∑ i ∈ (Finset.range q).erase ((j₁ + ⌊A⌋₊) % q), (cfun q f i)⁻¹ := by
      have h1 : ∑ j ∈ (Finset.range q).erase j₁, (gridW q A j)⁻¹ =
          ∑ j ∈ (Finset.range q).erase j₁, (cfun q f ((j + ⌊A⌋₊) % q))⁻¹ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hgreq j (Finset.mem_range.mp (Finset.mem_of_mem_erase hj))]
      have h2 : ∑ j ∈ (Finset.range q).erase j₁, (cfun q f ((j + ⌊A⌋₊) % q))⁻¹ =
          ∑ i ∈ (Finset.range q).erase ((j₁ + ⌊A⌋₊) % q), (cfun q f i)⁻¹ :=
        sum_erase_shift_mod hq ⌊A⌋₊ hj₁ (fun i => (cfun q f i)⁻¹)
      rw [h1, h2]
    rw [hsum]
    exact sum_inv_min_shift_le hq2 hf0 hf1 (Nat.mod_lt _ hq) hminc

end Work.TMC16Core.Trig
