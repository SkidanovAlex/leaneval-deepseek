import Mathlib
import Submission.Work.GM.S3.tail_defs

namespace Work.GM.S3

/-!
# Summation of the two-piece majorant `phiMaj`

`phiMaj L Az D m` is `Az` for `|m| ≤ L` and `D/m²` for `|m| > L`.  For `L ≥ 1`, `Az ≥ 0`,
`D ≥ 0` it is summable over `ℤ` with

`∑' m : ℤ, phiMaj L Az D m ≤ (3·Az + 4·D/L)·L`.

The proof proceeds by the "finite partial sums" criterion `Real.tsum_le_of_sum_le`
(which returns summability as a by-product): for every finite `u : Finset ℤ` we show
`∑_{m ∈ u} phiMaj L Az D m ≤ (3·Az + 4·D/L)·L`.

* On `u₁ = u.filter (|·| ≤ L)` the summand is constantly `Az`; the number of integers
  `|m| ≤ L` is at most `2⌊L⌋+1 ≤ 3L` and we bound the cardinality of `u₁` by that of
  `Finset.Icc (-⌊L⌋) ⌊L⌋`.
* On `u₂ = u.filter (¬ |·| ≤ L)` the summand is `D/m²`, and the tail bound
  `∑_{m ∈ u₂} 1/m² ≤ 4/L` is obtained by splitting `u₂` into its positive and negative
  parts and comparing with the telescoping estimate `∑_{n ≥ k+1} 1/n² ≤ 1/k`
  (`sum_Ioc_inv_sq_le_sub`) at `k = ⌊L⌋`, using `⌊L⌋ ≥ L/2` for `L ≥ 1`.
-/

/-- Tail estimate over `ℕ`: for `k ≥ 1`, a finite set of naturals all of which are `≥ k+1`
contributes at most `1/k` to `∑ 1/n²`.  This is the telescoping bound
`∑_{n > k} 1/n² ≤ ∑_{n > k} (1/(n-1) - 1/n) ≤ 1/k`. -/
theorem sum_inv_sq_le_inv_nat (k : ℕ) (hk : 1 ≤ k) (v : Finset ℕ) (hv : ∀ n ∈ v, k + 1 ≤ n) :
    ∑ n ∈ v, 1 / (n : ℝ) ^ 2 ≤ 1 / (k : ℝ) := by
  rcases v.eq_empty_or_nonempty with h | ⟨n₀, hn₀⟩
  · rw [h]; simp
  · set M : ℕ := v.sup id + 1 with hM
    have hk0 : k ≠ 0 := by omega
    have hMge : k ≤ M := by
      have h1 : k + 1 ≤ n₀ := hv n₀ hn₀
      have h2 : n₀ ≤ v.sup id := Finset.le_sup (f := id) hn₀
      simp only [hM]; omega
    have hsub : v ⊆ Finset.Ioc k M := by
      intro n hn
      have h1 : k + 1 ≤ n := hv n hn
      have h2 : n ≤ v.sup id := Finset.le_sup (f := id) hn
      simp only [Finset.mem_Ioc, hM] at *
      omega
    calc ∑ n ∈ v, 1 / (n : ℝ) ^ 2
        ≤ ∑ n ∈ Finset.Ioc k M, 1 / (n : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro i _ _; positivity)
      _ = ∑ n ∈ Finset.Ioc k M, ((n : ℝ) ^ 2)⁻¹ := by simp [one_div]
      _ ≤ (k : ℝ)⁻¹ - (M : ℝ)⁻¹ := sum_Ioc_inv_sq_le_sub hk0 hMge
      _ ≤ (k : ℝ)⁻¹ := by
          have : (0:ℝ) ≤ (M : ℝ)⁻¹ := by positivity
          linarith
      _ = 1 / (k : ℝ) := by rw [one_div]

/-- Tail estimate over `ℤ`, positive part: if every `m ∈ v` is a positive integer with
`L < m`, then `∑_{m ∈ v} 1/m² ≤ 1/⌊L⌋`. -/
theorem sum_inv_sq_le_inv_of_pos (L : ℝ) (hL : 1 ≤ L) (v : Finset ℤ)
    (hv : ∀ m ∈ v, 0 < m) (hvL : ∀ m ∈ v, L < (m : ℝ)) :
    ∑ m ∈ v, 1 / (m : ℝ) ^ 2 ≤ 1 / ((⌊L⌋₊ : ℕ) : ℝ) := by
  have hk1 : 1 ≤ ⌊L⌋₊ := Nat.le_floor (n := 1) (by push_cast; exact hL)
  have hinj : Set.InjOn Int.natAbs (↑v : Set ℤ) := by
    intro a ha b hb hab
    rcases Int.natAbs_eq_natAbs_iff.mp hab with h | h
    · exact h
    · have h1 : 0 < a := hv a ha
      have h2 : 0 < b := hv b hb
      omega
  have hsum : ∑ n ∈ v.image Int.natAbs, 1 / (n : ℝ) ^ 2 = ∑ m ∈ v, 1 / (m : ℝ) ^ 2 := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro m hm
    have hpos : 0 ≤ m := le_of_lt (hv m hm)
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast hpos : (0:ℝ) ≤ (m:ℝ))]
  rw [← hsum]
  exact sum_inv_sq_le_inv_nat ⌊L⌋₊ hk1 _ (by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨m, hm, rfl⟩ := hn
    have hpos : 0 ≤ m := le_of_lt (hv m hm)
    have hcast : ((m.natAbs : ℕ) : ℝ) = (m : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast hpos : (0:ℝ) ≤ (m:ℝ))]
    have hlt : L < ((m.natAbs : ℕ) : ℝ) := by rw [hcast]; exact hvL m hm
    have hfl : ((⌊L⌋₊ : ℕ) : ℝ) ≤ L := Nat.floor_le (le_trans zero_le_one hL)
    have : ((⌊L⌋₊ : ℕ) : ℝ) < ((m.natAbs : ℕ) : ℝ) := lt_of_le_of_lt hfl hlt
    have := Nat.cast_lt.mp this
    omega)

/-- Tail estimate over `ℤ`, negative part: if every `m ∈ v` is a negative integer with
`|m| > L`, then `∑_{m ∈ v} 1/m² ≤ 1/⌊L⌋` (apply the positive case to `-v`). -/
theorem sum_inv_sq_le_inv_of_neg (L : ℝ) (hL : 1 ≤ L) (v : Finset ℤ)
    (hv : ∀ m ∈ v, m < 0) (hvL : ∀ m ∈ v, L < |(m : ℝ)|) :
    ∑ m ∈ v, 1 / (m : ℝ) ^ 2 ≤ 1 / ((⌊L⌋₊ : ℕ) : ℝ) := by
  have hinj : Set.InjOn (fun m : ℤ => -m) (↑v : Set ℤ) := by
    intro a _ b _ hab
    simpa using hab
  have hsum : ∑ n ∈ v.image (fun m : ℤ => -m), 1 / (n : ℝ) ^ 2 = ∑ m ∈ v, 1 / (m : ℝ) ^ 2 := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro m hm
    simp
  rw [← hsum]
  apply sum_inv_sq_le_inv_of_pos L hL _ (by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨m, hm, rfl⟩ := hn
    have hmneg : m < 0 := hv m hm
    have h1 : (m : ℝ) < 0 := by exact_mod_cast hmneg
    have h2 : (0:ℝ) < -(m:ℝ) := by linarith
    simpa using h2) (by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨m, hm, rfl⟩ := hn
    have hmneg : m < 0 := hv m hm
    have h1 : (m : ℝ) < 0 := by exact_mod_cast hmneg
    have h2 := hvL m hm
    rw [abs_of_neg h1] at h2
    have h3 : (↑(-m) : ℝ) = -(m : ℝ) := Int.cast_neg m
    rw [h3]
    exact h2)

/-- The `1/m²` tail over `ℤ`: a finite set of integers all of modulus `> L ≥ 1` contributes
at most `4/L`.  The two signs give `1/⌊L⌋` each and `⌊L⌋ ≥ L/2` since `L ≥ 1`. -/
theorem sum_inv_sq_le_four_div (L : ℝ) (hL : 1 ≤ L) (u : Finset ℤ)
    (hu : ∀ m ∈ u, L < |(m : ℝ)|) :
    ∑ m ∈ u, 1 / (m : ℝ) ^ 2 ≤ 4 / L := by
  have hkn : 1 ≤ ⌊L⌋₊ := Nat.le_floor (n := 1) (by push_cast; exact hL)
  have hfilter : u.filter (fun m : ℤ => ¬ 0 < m) = u.filter (fun m : ℤ => m < 0) := by
    apply Finset.filter_congr
    intro m hm
    have hmne : m ≠ 0 := by
      rintro rfl
      have h := hu 0 hm
      rw [Int.cast_zero, abs_zero] at h
      linarith
    omega
  have hsplit : ∑ m ∈ u, 1 / (m : ℝ) ^ 2
      = (∑ m ∈ u.filter (fun m : ℤ => 0 < m), 1 / (m : ℝ) ^ 2)
        + (∑ m ∈ u.filter (fun m : ℤ => m < 0), 1 / (m : ℝ) ^ 2) := by
    rw [← Finset.sum_filter_add_sum_filter_not u (fun m : ℤ => 0 < m)
        (fun m : ℤ => 1 / (m : ℝ) ^ 2), hfilter]
  rw [hsplit]
  have h1 : ∑ m ∈ u.filter (fun m : ℤ => 0 < m), 1 / (m : ℝ) ^ 2
      ≤ 1 / ((⌊L⌋₊ : ℕ) : ℝ) :=
    sum_inv_sq_le_inv_of_pos L hL _ (fun m hm => (Finset.mem_filter.mp hm).2)
      (fun m hm => by
        have hm' := Finset.mem_filter.mp hm
        have h0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm'.2
        have h := hu m hm'.1
        rwa [abs_of_pos h0] at h)
  have h2 : ∑ m ∈ u.filter (fun m : ℤ => m < 0), 1 / (m : ℝ) ^ 2
      ≤ 1 / ((⌊L⌋₊ : ℕ) : ℝ) :=
    sum_inv_sq_le_inv_of_neg L hL _ (fun m hm => (Finset.mem_filter.mp hm).2)
      (fun m hm => hu m (Finset.mem_filter.mp hm).1)
  have h3 : 1 / ((⌊L⌋₊ : ℕ) : ℝ) + 1 / ((⌊L⌋₊ : ℕ) : ℝ) ≤ 4 / L := by
    have hlt : L < ((⌊L⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one L
    have hknpos : (0:ℝ) < (⌊L⌋₊ : ℝ) := by exact_mod_cast hkn
    have hLpos : (0:ℝ) < L := lt_of_lt_of_le zero_lt_one hL
    have h2kn : L ≤ 2 * (⌊L⌋₊ : ℝ) := by
      have hkn1 : (1:ℝ) ≤ (⌊L⌋₊ : ℝ) := by exact_mod_cast hkn
      linarith
    rw [← add_div, div_le_div_iff₀ hknpos hLpos]
    linarith
  linarith

/-- `Work.GM.S3.phiMaj L Az D m = if |m| ≤ L then Az else D/m²`.  For `L ≥ 1`, `Az ≥ 0`, `D ≥ 0`
this majorant is summable over `ℤ` with total sum at most `(3Az + 4D/L)·L`: the part with `|m| ≤ L`
has at most `2L+1` terms and the part with `|m| > L` is a `1/m²` tail bounded by `4D/L`
(again: `∑_{|m|>L} 1/m² ≤ 4/L` needs the integer trick, `⌊L⌋` and `L ≤ 2⌊L⌋` for `L ≥ 1`). -/
theorem phiMaj_sum (L Az D : ℝ) (hL : 1 ≤ L) (hAz : 0 ≤ Az) (hD : 0 ≤ D) :
    Summable (Work.GM.S3.phiMaj L Az D) ∧
      tsum (fun m : ℤ => Work.GM.S3.phiMaj L Az D m) ≤ (3 * Az + 4 * D / L) * L := by
  have hf : 0 ≤ phiMaj L Az D := by
    intro m
    rw [phiMaj]
    split_ifs with h
    · exact hAz
    · positivity
  have hkey : ∀ u : Finset ℤ, ∑ m ∈ u, phiMaj L Az D m ≤ (3 * Az + 4 * D / L) * L := by
    intro u
    set u₁ := u.filter (fun m : ℤ => |(m:ℝ)| ≤ L) with hu₁
    set u₂ := u.filter (fun m : ℤ => ¬ |(m:ℝ)| ≤ L) with hu₂
    have mem₁ : ∀ m : ℤ, m ∈ u₁ ↔ m ∈ u ∧ |(m:ℝ)| ≤ L := by
      intro m; rw [hu₁]; exact Finset.mem_filter
    have mem₂ : ∀ m : ℤ, m ∈ u₂ ↔ m ∈ u ∧ ¬ |(m:ℝ)| ≤ L := by
      intro m; rw [hu₂]; exact Finset.mem_filter
    have hdec : ∑ m ∈ u, phiMaj L Az D m
        = ∑ m ∈ u₁, phiMaj L Az D m + ∑ m ∈ u₂, phiMaj L Az D m := by
      rw [← Finset.sum_filter_add_sum_filter_not u (fun m : ℤ => |(m:ℝ)| ≤ L)
          (fun m : ℤ => phiMaj L Az D m), ← hu₁, ← hu₂]
    rw [hdec]
    have h1 : ∑ m ∈ u₁, phiMaj L Az D m ≤ 3 * Az * L := by
      have heq : ∑ m ∈ u₁, phiMaj L Az D m = ∑ m ∈ u₁, Az := by
        apply Finset.sum_congr rfl
        intro m hm
        have hcond : |(m:ℝ)| ≤ L := ((mem₁ m).mp hm).2
        rw [phiMaj, if_pos hcond]
      rw [heq, Finset.sum_const, nsmul_eq_mul]
      have hcard : u₁.card ≤ (Finset.Icc (-(⌊L⌋₊ : ℤ)) (⌊L⌋₊ : ℤ)).card :=
        Finset.card_le_card (by
          intro m hm
          have hmL : |(m:ℝ)| ≤ L := ((mem₁ m).mp hm).2
          have hnat : m.natAbs ≤ ⌊L⌋₊ := by
            apply Nat.le_floor
            rw [Nat.cast_natAbs, Int.cast_abs]
            exact hmL
          have hnatZ : ((m.natAbs : ℕ) : ℤ) ≤ (⌊L⌋₊ : ℤ) := by exact_mod_cast hnat
          rw [Finset.mem_Icc]
          exact ⟨by have h := Int.le_natAbs (a := -m); rw [Int.natAbs_neg] at h; omega,
                 by have h := Int.le_natAbs (a := m); omega⟩)
      have hc3 : (u₁.card : ℝ) ≤ 3 * L := by
        have h2 : (u₁.card : ℝ) ≤ ((Finset.Icc (-(⌊L⌋₊ : ℤ)) (⌊L⌋₊ : ℤ)).card : ℝ) := by
          exact_mod_cast hcard
        have h3 : ((Finset.Icc (-(⌊L⌋₊ : ℤ)) (⌊L⌋₊ : ℤ)).card : ℝ)
            = 2 * (⌊L⌋₊ : ℝ) + 1 := by
          have hZ := Int.card_Icc_of_le (-(⌊L⌋₊ : ℤ)) (⌊L⌋₊ : ℤ) (by omega)
          have hZR : (((Finset.Icc (-(⌊L⌋₊ : ℤ)) (⌊L⌋₊ : ℤ)).card : ℤ) : ℝ)
              = 2 * (⌊L⌋₊ : ℝ) + 1 := by
            rw [hZ]; push_cast; ring
          simpa only [Int.cast_natCast] using hZR
        have h4 : ((⌊L⌋₊ : ℕ) : ℝ) ≤ L := Nat.floor_le (le_trans zero_le_one hL)
        linarith
      calc (u₁.card : ℝ) * Az ≤ (3 * L) * Az := mul_le_mul_of_nonneg_right hc3 hAz
        _ = 3 * Az * L := by ring
    have h2 : ∑ m ∈ u₂, phiMaj L Az D m ≤ 4 * D / L := by
      have heq : ∑ m ∈ u₂, phiMaj L Az D m = D * ∑ m ∈ u₂, 1 / (m : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        have hcond : ¬ |(m:ℝ)| ≤ L := ((mem₂ m).mp hm).2
        rw [phiMaj, if_neg hcond, div_eq_mul_inv, one_div]
      rw [heq]
      have htail : ∑ m ∈ u₂, 1 / (m : ℝ) ^ 2 ≤ 4 / L :=
        sum_inv_sq_le_four_div L hL u₂ (fun m hm => lt_of_not_ge ((mem₂ m).mp hm).2)
      calc D * ∑ m ∈ u₂, 1 / (m : ℝ) ^ 2 ≤ D * (4 / L) := mul_le_mul_of_nonneg_left htail hD
        _ = 4 * D / L := by ring
    have h4 : (0:ℝ) ≤ 4 * D / L := div_nonneg (by linarith) (by linarith)
    have h5 : 4 * D / L ≤ (4 * D / L) * L := le_mul_of_one_le_right h4 hL
    have h6 : (3 * Az + 4 * D / L) * L = 3 * Az * L + (4 * D / L) * L := by ring
    linarith
  exact ⟨summable_of_sum_le hf hkey, Real.tsum_le_of_sum_le hf hkey⟩

end Work.GM.S3
