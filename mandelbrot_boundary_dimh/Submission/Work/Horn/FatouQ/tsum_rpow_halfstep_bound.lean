import Mathlib

namespace Work.Horn.FatouQ

open Filter

open scoped Topology

/-- Elementary comparison used for summability: if `x ≥ 0`, `δ > 1`, `B ≥ 0` and `i ≥ 1` then
`B / (x + i/2)^δ ≤ (B · 2^δ) · (i^δ)⁻¹`. -/
lemma div_add_half_rpow_le {B δ x : ℝ} (hB : 0 ≤ B) (hδ : 1 < δ) (hx : 0 ≤ x)
    {i : ℕ} (hi : 1 ≤ i) :
    B / (x + (i : ℝ) / 2) ^ δ ≤ (B * 2 ^ δ) * ((i : ℝ) ^ δ)⁻¹ := by
  have hi0 : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
  have hj2 : (0 : ℝ) < (i : ℝ) / 2 := by linarith
  have hx0 : (0 : ℝ) < x + (i : ℝ) / 2 := by linarith
  have hδnn : (0 : ℝ) ≤ δ := le_of_lt (lt_trans zero_lt_one hδ)
  have hle : ((i : ℝ) / 2) ^ δ ≤ (x + (i : ℝ) / 2) ^ δ :=
    Real.rpow_le_rpow (le_of_lt hj2) (by linarith) hδnn
  have hpos : (0 : ℝ) < ((i : ℝ) / 2) ^ δ := Real.rpow_pos_of_pos hj2 δ
  have hpos2 : (0 : ℝ) < (x + (i : ℝ) / 2) ^ δ := Real.rpow_pos_of_pos hx0 δ
  have hinv : ((x + (i : ℝ) / 2) ^ δ)⁻¹ ≤ (((i : ℝ) / 2) ^ δ)⁻¹ :=
    (inv_le_inv₀ hpos2 hpos).mpr hle
  calc B / (x + (i : ℝ) / 2) ^ δ = B * ((x + (i : ℝ) / 2) ^ δ)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ B * (((i : ℝ) / 2) ^ δ)⁻¹ := mul_le_mul_of_nonneg_left hinv hB
    _ = (B * 2 ^ δ) * ((i : ℝ) ^ δ)⁻¹ := by
        rw [Real.div_rpow (le_of_lt hi0) (by norm_num) δ, inv_div, div_eq_mul_inv]
        ring

/-- `i ↦ B / (x + i/2)^δ` is summable for `x ≥ 0`, `δ > 1`, `B ≥ 0`. -/
lemma summable_div_add_half_rpow {B δ x : ℝ} (hB : 0 ≤ B) (hδ : 1 < δ) (hx : 0 ≤ x) :
    Summable (fun i : ℕ => B / (x + (i : ℝ) / 2) ^ δ) := by
  have hZ : Summable (fun n : ℕ => ((n : ℝ) ^ δ)⁻¹) := Real.summable_nat_rpow_inv.mpr hδ
  have hZ' : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ δ)⁻¹) :=
    (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ δ)⁻¹) 1).mpr hZ
  refine (summable_nat_add_iff 1).mp ?_
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => (B * 2 ^ δ) * (((n + 1 : ℕ) : ℝ) ^ δ)⁻¹) ?_ ?_
  · exact hZ'.mul_left (B * 2 ^ δ)
  · intro n
    rw [Real.norm_of_nonneg (div_nonneg hB (Real.rpow_nonneg (by positivity) δ))]
    exact div_add_half_rpow_le hB hδ hx (Nat.le_add_left 1 n)

/-- Pointwise decay: for `x ≥ 1`, `δ > 1`, `B ≥ 0` and `i ≥ 1`,
`B / (x + i/2)^δ ≤ (B · x^{-(δ-1)/2} · 2^{(δ+1)/2}) · i^{-(δ+1)/2}`. -/
lemma div_add_half_rpow_le_decay {B δ x : ℝ} (hB : 0 ≤ B) (hδ : 1 < δ) (hx : 1 ≤ x)
    {i : ℕ} (hi : 1 ≤ i) :
    B / (x + (i : ℝ) / 2) ^ δ
      ≤ (B * x ^ (-((δ - 1) / 2)) * 2 ^ ((δ + 1) / 2)) * (i : ℝ) ^ (-((δ + 1) / 2)) := by
  have hi0 : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
  have hend : 0 < x + (i : ℝ) / 2 := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hd1nn : 0 ≤ (δ - 1) / 2 := by linarith
  have hd2nn : 0 ≤ (δ + 1) / 2 := by linarith
  have hδeq : (δ - 1) / 2 + (δ + 1) / 2 = δ := by ring
  have hpow : (x + (i : ℝ) / 2) ^ δ
      = (x + (i : ℝ) / 2) ^ ((δ - 1) / 2) * (x + (i : ℝ) / 2) ^ ((δ + 1) / 2) := by
    rw [← Real.rpow_add hend, hδeq]
  have hA : x ^ ((δ - 1) / 2) ≤ (x + (i : ℝ) / 2) ^ ((δ - 1) / 2) :=
    Real.rpow_le_rpow (le_of_lt hx0) (by linarith) hd1nn
  have hB2 : ((i : ℝ) / 2) ^ ((δ + 1) / 2) ≤ (x + (i : ℝ) / 2) ^ ((δ + 1) / 2) :=
    Real.rpow_le_rpow (by positivity) (by linarith) hd2nn
  have hprod : x ^ ((δ - 1) / 2) * ((i : ℝ) / 2) ^ ((δ + 1) / 2)
      ≤ (x + (i : ℝ) / 2) ^ ((δ - 1) / 2) * (x + (i : ℝ) / 2) ^ ((δ + 1) / 2) :=
    mul_le_mul hA hB2 (by positivity) (by positivity)
  have hq1 : 0 < x ^ ((δ - 1) / 2) := Real.rpow_pos_of_pos hx0 _
  have hq2 : 0 < ((i : ℝ) / 2) ^ ((δ + 1) / 2) := Real.rpow_pos_of_pos (by positivity) _
  have hq3 : 0 < (x + (i : ℝ) / 2) ^ ((δ - 1) / 2) := Real.rpow_pos_of_pos hend _
  have hq4 : 0 < (x + (i : ℝ) / 2) ^ ((δ + 1) / 2) := Real.rpow_pos_of_pos hend _
  have hinv : ((x + (i : ℝ) / 2) ^ δ)⁻¹
      ≤ (x ^ ((δ - 1) / 2) * ((i : ℝ) / 2) ^ ((δ + 1) / 2))⁻¹ := by
    rw [hpow]
    exact (inv_le_inv₀ (mul_pos hq3 hq4) (mul_pos hq1 hq2)).mpr hprod
  have hid1 : (x ^ ((δ - 1) / 2))⁻¹ = x ^ (-((δ - 1) / 2)) :=
    (Real.rpow_neg (le_of_lt hx0) _).symm
  have hid2 : (((i : ℝ) / 2) ^ ((δ + 1) / 2))⁻¹ = 2 ^ ((δ + 1) / 2) * (i : ℝ) ^ (-((δ + 1) / 2)) := by
    rw [← Real.rpow_neg (by positivity : (0 : ℝ) ≤ (i : ℝ) / 2)]
    rw [Real.div_rpow (by positivity : (0 : ℝ) ≤ (i : ℝ)) (by norm_num) (-((δ + 1) / 2))]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) ((δ + 1) / 2), div_eq_mul_inv, inv_inv]
    ring
  calc B / (x + (i : ℝ) / 2) ^ δ
      = B * ((x + (i : ℝ) / 2) ^ δ)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ B * (x ^ ((δ - 1) / 2) * ((i : ℝ) / 2) ^ ((δ + 1) / 2))⁻¹ :=
        mul_le_mul_of_nonneg_left hinv hB
    _ = (B * x ^ (-((δ - 1) / 2)) * 2 ^ ((δ + 1) / 2)) * (i : ℝ) ^ (-((δ + 1) / 2)) := by
        rw [mul_inv, hid1, hid2]
        ring

theorem tsum_rpow_halfstep_bound {B δ N : ℝ} (hB : 0 ≤ B) (hδ : 1 < δ) (hN : 0 < N) :
    Summable (fun i : ℕ => B / (N + (i : ℝ) / 2) ^ δ) ∧
    ∃ R : ℝ, N ≤ R ∧ ∀ x : ℝ, R ≤ x →
      (∑' i : ℕ, B / (x + (i : ℝ) / 2) ^ δ) ≤ 1 / 4 := by
  have hδ''gt : (1 : ℝ) < (δ + 1) / 2 := by linarith
  -- summability of the "zeta-like" series `ζ = ∑ i, (i+1)^{-(δ+1)/2}`
  have hζ : Summable (fun i : ℕ => ((i : ℝ) + 1) ^ (-((δ + 1) / 2))) := by
    have h0 : Summable (fun n : ℕ => (n : ℝ) ^ (-((δ + 1) / 2))) :=
      Real.summable_nat_rpow.mpr (by linarith)
    have h1 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-((δ + 1) / 2))) :=
      (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-((δ + 1) / 2))) 1).mpr h0
    simpa only [Nat.cast_add, Nat.cast_one] using h1
  let C : ℝ := B * 2 ^ ((δ + 1) / 2)
    * (∑' i : ℕ, ((i : ℝ) + 1) ^ (-((δ + 1) / 2)))
  constructor
  · exact summable_div_add_half_rpow hB hδ (le_of_lt hN)
  · -- uniform bound `∑ i, B/(x+i/2)^δ ≤ (B+C) · x^{-(δ-1)/2}` for `x ≥ 1`
    have hbound : ∀ x : ℝ, 1 ≤ x →
        (∑' i : ℕ, B / (x + (i : ℝ) / 2) ^ δ) ≤ (B + C) * x ^ (-((δ - 1) / 2)) := by
      intro x hx
      have hx0 : 0 < x := by linarith
      have hxs : Summable (fun i : ℕ => B / (x + (i : ℝ) / 2) ^ δ) :=
        summable_div_add_half_rpow hB hδ (by linarith)
      rw [hxs.tsum_eq_zero_add]
      simp only [Nat.cast_zero, zero_div, add_zero]
      have htail : (∑' i : ℕ, B / (x + ((i + 1 : ℕ) : ℝ) / 2) ^ δ)
          ≤ (B * x ^ (-((δ - 1) / 2)) * 2 ^ ((δ + 1) / 2))
              * (∑' i : ℕ, ((i : ℝ) + 1) ^ (-((δ + 1) / 2))) := by
        rw [← tsum_mul_left (f := fun i : ℕ => ((i : ℝ) + 1) ^ (-((δ + 1) / 2)))
              (a := B * x ^ (-((δ - 1) / 2)) * 2 ^ ((δ + 1) / 2))]
        refine Summable.tsum_le_tsum (fun i => ?_)
          ((summable_nat_add_iff 1).mpr hxs) (hζ.mul_left _)
        have h := div_add_half_rpow_le_decay hB hδ hx (i := i + 1) (Nat.le_add_left 1 i)
        simpa only [Nat.cast_add, Nat.cast_one] using h
      have hhead : B / x ^ δ ≤ B * x ^ (-((δ - 1) / 2)) := by
        have he1 : B / x ^ δ = B * x ^ (-δ) := by
          rw [div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hx0) δ]
        have he2 : x ^ (-δ) ≤ x ^ (-((δ - 1) / 2)) :=
          Real.rpow_le_rpow_of_exponent_le hx (by linarith)
        rw [he1]
        exact mul_le_mul_of_nonneg_left he2 hB
      have hCeq : (B * x ^ (-((δ - 1) / 2)) * 2 ^ ((δ + 1) / 2))
            * (∑' i : ℕ, ((i : ℝ) + 1) ^ (-((δ + 1) / 2)))
          = C * x ^ (-((δ - 1) / 2)) := by
        simp only [C]
        ring
      calc B / x ^ δ + (∑' i : ℕ, B / (x + ((i + 1 : ℕ) : ℝ) / 2) ^ δ)
          ≤ B * x ^ (-((δ - 1) / 2)) + C * x ^ (-((δ - 1) / 2)) :=
            add_le_add hhead (le_trans htail (le_of_eq hCeq))
        _ = (B + C) * x ^ (-((δ - 1) / 2)) := by ring
    -- the bound tends to `0`
    have hd1pos : (0 : ℝ) < (δ - 1) / 2 := by linarith
    have htend : Tendsto (fun x : ℝ => (B + C) * x ^ (-((δ - 1) / 2))) atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop hd1pos).const_mul (B + C)
      simpa using h
    have hev : ∀ᶠ x : ℝ in atTop, (B + C) * x ^ (-((δ - 1) / 2)) < 1 / 4 :=
      (tendsto_order.1 htend).2 (1 / 4) (by norm_num)
    have hev' : ∀ᶠ x : ℝ in atTop,
        1 ≤ x ∧ N ≤ x ∧ (∑' i : ℕ, B / (x + (i : ℝ) / 2) ^ δ) ≤ 1 / 4 := by
      filter_upwards [hev, eventually_ge_atTop (1 : ℝ), eventually_ge_atTop N] with x hlt h1 hNx
      exact ⟨h1, hNx, le_trans (hbound x h1) (le_of_lt hlt)⟩
    obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 hev'
    refine ⟨max R₀ N, le_max_right _ _, fun x hx => ?_⟩
    exact (hR₀ x (le_trans (le_max_left _ _) hx)).2.2

end Work.Horn.FatouQ
