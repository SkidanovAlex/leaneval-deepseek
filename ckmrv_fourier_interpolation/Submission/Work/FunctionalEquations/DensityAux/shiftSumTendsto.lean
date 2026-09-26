import Mathlib

/-!
# The shifted-lattice Gaussian sum tends to zero

We prove that for `y > 0`, any real `R` and any `d : ℕ` the sums

`∑_{m ≠ 0} exp (-π y (2 N |m| - R)) * (1 + 2 N |m| + R) ^ d`

over the non-zero integers are summable for every `N ≥ 1` and tend to `0` as `N → ∞`.

The proof bounds each summand uniformly in `N` by a constant times the geometric
weight `exp (-π y N) ^ |m|`, and evaluates the resulting geometric series over the
non-zero integers.
-/

namespace Work.FunctionalEquations.DensityAux

/-! ## Elementary real bounds -/

/-- For `s ≥ 0` and `d : ℕ`, `(1 + s)^d ≤ 2^d (1 + s^d)`. -/
lemma one_add_pow_le (d : ℕ) {s : ℝ} (hs : 0 ≤ s) : (1 + s) ^ d ≤ 2 ^ d * (1 + s ^ d) := by
  have hmax : 1 + s ≤ 2 * max 1 s := by
    have h1 : (1:ℝ) ≤ max 1 s := le_max_left _ _
    have h2 : s ≤ max 1 s := le_max_right _ _
    linarith
  have hmaxd : (max 1 s) ^ d ≤ 1 + s ^ d := by
    rcases le_total 1 s with h | h
    · rw [max_eq_right h]
      have : (0:ℝ) ≤ s ^ d := pow_nonneg hs d
      linarith
    · rw [max_eq_left h, one_pow]
      have : (0:ℝ) ≤ s ^ d := pow_nonneg hs d
      linarith
  calc (1 + s) ^ d ≤ (2 * max 1 s) ^ d := pow_le_pow_left₀ (by linarith) hmax d
    _ = 2 ^ d * (max 1 s) ^ d := by rw [mul_pow]
    _ ≤ 2 ^ d * (1 + s ^ d) :=
        mul_le_mul_of_nonneg_left hmaxd (pow_nonneg (by norm_num) d)

/-- For `x ≥ 0` and `n : ℕ`, `x ^ n * exp (-x) ≤ n ^ n`. -/
lemma pow_mul_exp_neg_le_self (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ n * Real.exp (-x) ≤ (n : ℝ) ^ n := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    simp only [pow_zero, one_mul]
    rw [Real.exp_le_one_iff]
    linarith
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hle : (x / n) * Real.exp (-(x / n)) ≤ Real.exp (-1) := Real.mul_exp_neg_le_exp_neg_one _
  have h2 : x * Real.exp (-(x / n)) ≤ (n:ℝ) * Real.exp (-1) := by
    have h := mul_le_mul_of_nonneg_left hle hnR.le
    rw [← mul_assoc, mul_div_cancel₀ x hnR.ne'] at h
    exact h
  have h3 : (x * Real.exp (-(x / n))) ^ n ≤ ((n:ℝ) * Real.exp (-1)) ^ n :=
    pow_le_pow_left₀ (mul_nonneg hx (Real.exp_nonneg _)) h2 n
  have hL : (x * Real.exp (-(x / n))) ^ n = x ^ n * Real.exp (-x) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 1
    field_simp
  have hR : ((n:ℝ) * Real.exp (-1)) ^ n = (n:ℝ)^n * Real.exp (-(n:ℝ)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 1
    ring_nf
  have hexpn : Real.exp (-(n:ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith [hnR.le]
  calc x ^ n * Real.exp (-x) = (x * Real.exp (-(x / n))) ^ n := hL.symm
    _ ≤ ((n:ℝ) * Real.exp (-1)) ^ n := h3
    _ = (n:ℝ)^n * Real.exp (-(n:ℝ)) := hR
    _ ≤ (n:ℝ)^n * 1 := mul_le_mul_of_nonneg_left hexpn (pow_nonneg hnR.le n)
    _ = (n:ℝ)^n := mul_one _

/-- If `A, c, s ≥ 0` and `d : ℕ`, then `exp (-s) * (A + c s)^d ≤ (A+c)^d 2^d (1 + d^d)`. -/
lemma expNegMulAddPowLe {A c s : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c) (hs : 0 ≤ s) (d : ℕ) :
    Real.exp (-s) * (A + c * s) ^ d ≤ (A + c) ^ d * 2 ^ d * (1 + (d : ℝ) ^ d) := by
  have hAc : 0 ≤ A + c := add_nonneg hA hc
  have hAcs : 0 ≤ A + c * s := add_nonneg hA (mul_nonneg hc hs)
  have h1 : A + c * s ≤ (A + c) * (1 + s) := by
    have : 0 ≤ A * s + c := by positivity
    nlinarith [this]
  have h2 : (A + c * s) ^ d ≤ ((A + c) * (1 + s)) ^ d := pow_le_pow_left₀ hAcs h1 d
  have h3 : Real.exp (-s) * ((A + c) * (1 + s)) ^ d
      = (A + c) ^ d * (Real.exp (-s) * (1 + s) ^ d) := by rw [mul_pow]; ring
  have h4 : (1 + s) ^ d ≤ 2 ^ d * (1 + s ^ d) := one_add_pow_le d hs
  have h5 : Real.exp (-s) * (1 + s ^ d) ≤ 1 + (d:ℝ) ^ d := by
    have he : Real.exp (-s) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    have hp : s ^ d * Real.exp (-s) ≤ (d:ℝ) ^ d := pow_mul_exp_neg_le_self d hs
    have hrw : Real.exp (-s) * (1 + s ^ d) = Real.exp (-s) + s ^ d * Real.exp (-s) := by ring
    rw [hrw]; linarith
  calc Real.exp (-s) * (A + c * s) ^ d
      ≤ Real.exp (-s) * ((A + c) * (1 + s)) ^ d :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg _)
    _ = (A + c) ^ d * (Real.exp (-s) * (1 + s) ^ d) := h3
    _ ≤ (A + c) ^ d * (Real.exp (-s) * (2 ^ d * (1 + s ^ d))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 (Real.exp_nonneg _)) (pow_nonneg hAc d)
    _ = ((A + c) ^ d * 2 ^ d) * (Real.exp (-s) * (1 + s ^ d)) := by ring
    _ ≤ ((A + c) ^ d * 2 ^ d) * (1 + (d:ℝ) ^ d) :=
        mul_le_mul_of_nonneg_left h5 (mul_nonneg (pow_nonneg hAc d) (pow_nonneg (by norm_num) d))
    _ = (A + c) ^ d * 2 ^ d * (1 + (d : ℝ) ^ d) := by ring

/-! ## The geometric series over the non-zero integers -/

lemma int_natAbs_neg_succ (n : ℕ) : ((-(↑n + 1) : ℤ)).natAbs = n + 1 := by
  rw [Int.natAbs_neg]
  have h : ((↑n : ℤ) + 1) = ↑(n+1) := by push_cast; ring
  rw [h, Int.natAbs_natCast]

lemma summable_int_pow_natAbs {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun m : ℤ => r ^ m.natAbs) := by
  apply Summable.of_nat_of_neg_add_one
  · exact (summable_geometric_of_lt_one hr0 hr1).congr (fun n => by simp)
  · exact (summable_geometric_of_lt_one hr0 hr1).mul_left r |>.congr (fun n => by
      rw [int_natAbs_neg_succ, pow_succ'])

lemma tsum_int_pow_natAbs {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' m : ℤ, r ^ m.natAbs = (1 + r) / (1 - r) := by
  have h1 : Summable (fun n : ℕ => r ^ ((-(↑n + 1) : ℤ)).natAbs) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left r |>.congr (fun n => by
      rw [int_natAbs_neg_succ, pow_succ'])
  have h0 : Summable (fun n : ℕ => r ^ ((↑n : ℤ)).natAbs) :=
    (summable_geometric_of_lt_one hr0 hr1).congr (fun n => by simp)
  have h := tsum_of_nat_of_neg_add_one (f := fun m : ℤ => r ^ m.natAbs) h0 h1
  simp only [Int.natAbs_natCast, int_natAbs_neg_succ] at h
  have hsucc : ∑' n : ℕ, r ^ (n + 1) = r * (1 - r)⁻¹ := by
    rw [show (fun n : ℕ => r ^ (n+1)) = (fun n => r * r ^ n) by
      funext n; rw [pow_succ'], tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  rw [h, tsum_geometric_of_lt_one hr0 hr1, hsucc, div_eq_mul_inv]
  have hr : (1:ℝ) - r ≠ 0 := by linarith
  field_simp

/-- The geometric series over the non-zero integers. -/
lemma tsumSubtypeIntPowNatAbs {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun m : {m : ℤ // m ≠ 0} => r ^ (m : ℤ).natAbs) ∧
      (∑' m : {m : ℤ // m ≠ 0}, r ^ (m : ℤ).natAbs) = 2 * r / (1 - r) := by
  have hsum : Summable (fun m : ℤ => r ^ m.natAbs) := summable_int_pow_natAbs hr0 hr1
  refine ⟨hsum.subtype _, ?_⟩
  have hcompl : ∑' (x : ↑(({m : ℤ | m ≠ 0} : Set ℤ))ᶜ), r ^ (x : ℤ).natAbs = 1 := by
    have hmem : (0 : ℤ) ∈ (({m : ℤ | m ≠ 0} : Set ℤ))ᶜ := by simp
    let b : ↑(({m : ℤ | m ≠ 0} : Set ℤ))ᶜ := ⟨0, hmem⟩
    have huniq : ∀ b' : ↑(({m : ℤ | m ≠ 0} : Set ℤ))ᶜ, b' = b := by
      intro b'
      refine Subtype.ext ?_
      have h : (b' : ℤ) = 0 := by simpa using b'.2
      simpa [b] using h
    rw [tsum_eq_single b (fun b' hb' => absurd (huniq b') hb')]
    simp [b]
  have hsplit := hsum.tsum_subtype_add_tsum_subtype_compl (({m : ℤ | m ≠ 0} : Set ℤ))
  rw [hcompl, tsum_int_pow_natAbs hr0 hr1] at hsplit
  have hsplit' : (∑' m : {m : ℤ // m ≠ 0}, r ^ (m : ℤ).natAbs) + 1 = (1 + r) / (1 - r) :=
    hsplit
  have h2 : (1 + r) / (1 - r) - 1 = 2 * r / (1 - r) := by
    have hr : (1:ℝ) - r ≠ 0 := by linarith
    field_simp
    ring
  linarith

/-! ## The uniform pointwise bound -/

/-- The constant bounding the sum of the absolute values of the summands. -/
noncomputable def shiftBoundConst (y R : ℝ) (d : ℕ) : ℝ :=
  Real.exp (Real.pi * y * R) * ((1 + |R| + 2 / (Real.pi * y)) ^ d * 2 ^ d * (1 + (d : ℝ) ^ d))

lemma shiftBoundConst_def (y R : ℝ) (d : ℕ) : shiftBoundConst y R d =
    Real.exp (Real.pi * y * R) * ((1 + |R| + 2 / (Real.pi * y)) ^ d * 2 ^ d * (1 + (d : ℝ) ^ d)) := rfl

/-- Uniform pointwise bound: the absolute value of the `N`-th summand at `m` is at most
`shiftBoundConst y R d * exp (-π y N) ^ |m|`. -/
lemma termAbsLe (y R : ℝ) (hy : 0 < y) (d : ℕ) (N : ℕ) (m : ℤ) :
    |Real.exp (-(Real.pi * y * (2 * (N : ℝ) * |((m : ℤ) : ℝ)| - R)))
        * (1 + 2 * (N : ℝ) * |((m : ℤ) : ℝ)| + R) ^ d| ≤
      shiftBoundConst y R d * Real.exp (-(Real.pi * y * (N : ℝ))) ^ m.natAbs := by
  set t : ℝ := |((m : ℤ) : ℝ)| with ht
  have ht_eq : t = (m.natAbs : ℝ) := by rw [ht]; simp
  have ht0 : 0 ≤ t := by rw [ht]; exact abs_nonneg _
  set s : ℝ := Real.pi * y * (N : ℝ) * t with hs
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hbase : (2 / (Real.pi * y)) * s = 2 * (N : ℝ) * t := by
    rw [hs]; field_simp
  have hkey : Real.exp (-s) * (1 + |R| + 2 * (N : ℝ) * t) ^ d
      ≤ (1 + |R| + 2 / (Real.pi * y)) ^ d * 2 ^ d * (1 + (d : ℝ) ^ d) := by
    have h := expNegMulAddPowLe (A := 1 + |R|) (c := 2 / (Real.pi * y)) (s := s)
      (by positivity) (by positivity) hs0 d
    rwa [hbase] at h
  have hle1 : |1 + 2 * (N : ℝ) * t + R| ≤ 1 + |R| + 2 * (N : ℝ) * t := by
    have hx : 0 ≤ 2 * (N : ℝ) * t := by positivity
    calc |1 + 2 * (N : ℝ) * t + R| ≤ |1 + 2 * (N : ℝ) * t| + |R| := abs_add_le _ _
      _ = (1 + 2 * (N : ℝ) * t) + |R| := by rw [abs_of_nonneg (by linarith)]
      _ = 1 + |R| + 2 * (N : ℝ) * t := by ring
  have hpow : |1 + 2 * (N : ℝ) * t + R| ^ d ≤ (1 + |R| + 2 * (N : ℝ) * t) ^ d :=
    pow_le_pow_left₀ (abs_nonneg _) hle1 d
  have hexp : Real.exp (-(Real.pi * y * (2 * (N : ℝ) * t - R)))
      = Real.exp (Real.pi * y * R) * Real.exp (-s) * Real.exp (-s) := by
    rw [hs]
    rw [show -(Real.pi * y * (2 * (N : ℝ) * t - R))
        = Real.pi * y * R + (-(Real.pi * y * (N : ℝ) * t)) + (-(Real.pi * y * (N : ℝ) * t)) by ring]
    rw [Real.exp_add, Real.exp_add]
  have habs : |Real.exp (-(Real.pi * y * (2 * (N : ℝ) * t - R))) * (1 + 2 * (N : ℝ) * t + R) ^ d|
      = Real.exp (Real.pi * y * R) * Real.exp (-s)
          * (Real.exp (-s) * |1 + 2 * (N : ℝ) * t + R| ^ d) := by
    rw [hexp]
    simp only [abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
    ring
  rw [habs]
  calc Real.exp (Real.pi * y * R) * Real.exp (-s) * (Real.exp (-s) * |1 + 2 * (N : ℝ) * t + R| ^ d)
      ≤ Real.exp (Real.pi * y * R) * Real.exp (-s)
          * (Real.exp (-s) * (1 + |R| + 2 * (N : ℝ) * t) ^ d) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _))
          (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
    _ ≤ Real.exp (Real.pi * y * R) * Real.exp (-s)
          * ((1 + |R| + 2 / (Real.pi * y)) ^ d * 2 ^ d * (1 + (d : ℝ) ^ d)) :=
        mul_le_mul_of_nonneg_left hkey (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
    _ = shiftBoundConst y R d * Real.exp (-s) := by rw [shiftBoundConst_def]; ring
    _ = shiftBoundConst y R d * Real.exp (-(Real.pi * y * (N : ℝ))) ^ m.natAbs := by
        have h2eq : Real.exp (-s) = Real.exp (-(Real.pi * y * (N : ℝ))) ^ m.natAbs := by
          rw [hs, show -(Real.pi * y * (N : ℝ) * t)
              = (m.natAbs : ℝ) * (-(Real.pi * y * (N : ℝ))) by rw [ht_eq]; ring, Real.exp_nat_mul]
        rw [h2eq]

/-! ## The main statement -/

/-- The `N`-th summand, as a function of the non-zero integer `m`. -/
noncomputable def shiftTerm (y R : ℝ) (d : ℕ) (N : ℕ) (m : {m : ℤ // m ≠ 0}) : ℝ :=
  Real.exp (-(Real.pi * y * (2 * (N : ℝ) * |((m : ℤ) : ℝ)| - R)))
    * (1 + 2 * (N : ℝ) * |((m : ℤ) : ℝ)| + R) ^ d

theorem shiftSumTendsto (y R : ℝ) (hy : 0 < y) (d : ℕ) :
    (∀ N : ℕ, 1 ≤ N → Summable (fun m : {m : ℤ // m ≠ 0} =>
        Real.exp (-(Real.pi * y * (2 * (N : ℝ) * |((m : ℤ) : ℝ)| - R)))
          * (1 + 2 * (N : ℝ) * |((m : ℤ) : ℝ)| + R) ^ d)) ∧
    Filter.Tendsto (fun N : ℕ => ∑' m : {m : ℤ // m ≠ 0},
        Real.exp (-(Real.pi * y * (2 * (N : ℝ) * |((m : ℤ) : ℝ)| - R)))
          * (1 + 2 * (N : ℝ) * |((m : ℤ) : ℝ)| + R) ^ d) Filter.atTop (nhds 0) := by
  change (∀ N : ℕ, 1 ≤ N → Summable (shiftTerm y R d N)) ∧
    Filter.Tendsto (fun N : ℕ => ∑' m : {m : ℤ // m ≠ 0}, shiftTerm y R d N m)
      Filter.atTop (nhds 0)
  have key : ∀ N : ℕ, 1 ≤ N →
      Summable (shiftTerm y R d N) ∧
      |∑' m : {m : ℤ // m ≠ 0}, shiftTerm y R d N m| ≤
        shiftBoundConst y R d * (2 * Real.exp (-(Real.pi * y * (N : ℝ)))
          / (1 - Real.exp (-(Real.pi * y * (N : ℝ))))) := by
    intro N hN
    set r : ℝ := Real.exp (-(Real.pi * y * (N : ℝ))) with hr
    have hr0 : 0 ≤ r := by rw [hr]; exact Real.exp_nonneg _
    have hr1 : r < 1 := by
      rw [hr, Real.exp_lt_one_iff]
      have : (0:ℝ) < Real.pi * y * (N:ℝ) := by positivity
      linarith
    obtain ⟨hgeo, hgeosum⟩ := tsumSubtypeIntPowNatAbs hr0 hr1
    have hmaj : Summable (fun m : {m : ℤ // m ≠ 0} =>
        shiftBoundConst y R d * r ^ ((m : ℤ).natAbs)) :=
      hgeo.mul_left (shiftBoundConst y R d)
    have hpt : ∀ m : {m : ℤ // m ≠ 0},
        ‖shiftTerm y R d N m‖ ≤ shiftBoundConst y R d * r ^ ((m : ℤ).natAbs) := by
      intro m
      rw [Real.norm_eq_abs, shiftTerm, hr]
      exact termAbsLe y R hy d N (m : ℤ)
    have habs : Summable (fun m : {m : ℤ // m ≠ 0} => ‖shiftTerm y R d N m‖) :=
      Summable.of_nonneg_of_le (fun m => norm_nonneg _) hpt hmaj
    refine ⟨habs.of_norm, ?_⟩
    have h1 : ‖∑' m : {m : ℤ // m ≠ 0}, shiftTerm y R d N m‖
        ≤ ∑' m : {m : ℤ // m ≠ 0}, ‖shiftTerm y R d N m‖ :=
      norm_tsum_le_tsum_norm habs
    have h2 : ∑' m : {m : ℤ // m ≠ 0}, ‖shiftTerm y R d N m‖
        ≤ ∑' m : {m : ℤ // m ≠ 0}, shiftBoundConst y R d * r ^ ((m : ℤ).natAbs) :=
      Summable.tsum_le_tsum hpt habs hmaj
    have h3 : ∑' m : {m : ℤ // m ≠ 0}, shiftBoundConst y R d * r ^ ((m : ℤ).natAbs)
        = shiftBoundConst y R d * (2 * r / (1 - r)) := by
      rw [tsum_mul_left, hgeosum]
    rw [Real.norm_eq_abs] at h1
    rw [h3] at h2
    linarith
  refine ⟨fun N hN => (key N hN).1, ?_⟩
  have hlim : Filter.Tendsto (fun N : ℕ => shiftBoundConst y R d *
      (2 * Real.exp (-(Real.pi * y * (N : ℝ))) / (1 - Real.exp (-(Real.pi * y * (N : ℝ))))))
      Filter.atTop (nhds 0) := by
    have hr : Filter.Tendsto (fun N : ℕ => Real.exp (-(Real.pi * y * (N : ℝ))))
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun N : ℕ => Real.pi * y * (N:ℝ)) Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop (show (0:ℝ) < Real.pi * y by positivity)
          tendsto_natCast_atTop_atTop
      exact Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
    have h2 : Filter.Tendsto (fun N : ℕ =>
        2 * Real.exp (-(Real.pi * y * (N : ℝ))) / (1 - Real.exp (-(Real.pi * y * (N : ℝ)))))
        Filter.atTop (nhds 0) := by
      have hnum : Filter.Tendsto (fun N : ℕ => 2 * Real.exp (-(Real.pi * y * (N : ℝ))))
          Filter.atTop (nhds 0) := by
        simpa using hr.const_mul (2:ℝ)
      have hden : Filter.Tendsto (fun N : ℕ => (1:ℝ) - Real.exp (-(Real.pi * y * (N : ℝ))))
          Filter.atTop (nhds 1) := by
        simpa using ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1:ℝ))
          Filter.atTop (nhds 1)).sub hr)
      have h := hnum.div hden (by norm_num : (1:ℝ) ≠ 0)
      rw [show (0:ℝ)/1 = 0 by norm_num] at h
      exact h
    simpa using h2.const_mul (shiftBoundConst y R d)
  have hbd : ∀ᶠ N in Filter.atTop, |∑' m : {m : ℤ // m ≠ 0}, shiftTerm y R d N m| ≤
      shiftBoundConst y R d * (2 * Real.exp (-(Real.pi * y * (N : ℝ)))
        / (1 - Real.exp (-(Real.pi * y * (N : ℝ))))) :=
    Filter.eventually_atTop.2 ⟨1, fun N hN => (key N hN).2⟩
  have hres : Filter.Tendsto (fun N : ℕ => |∑' m : {m : ℤ // m ≠ 0}, shiftTerm y R d N m|)
      Filter.atTop (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall (fun N => abs_nonneg _)) hbd hlim
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using hres)

end Work.FunctionalEquations.DensityAux

