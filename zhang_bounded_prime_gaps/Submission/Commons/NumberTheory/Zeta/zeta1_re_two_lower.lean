import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Submission.Commons.NumberTheory.Zeta.zeta1_logDeriv_pole_removal

noncomputable section
open Complex Filter Finset
open scoped BigOperators Topology

namespace Commons.NumberTheory.Zeta

/-- `1/(m+2) - 1/(m+3) = 1/((m+2)(m+3))`. -/
private lemma telescoping_term_eq (m : ℕ) :
    (1 : ℝ) / ((m : ℝ) + 2) - 1 / ((m : ℝ) + 3) = 1 / (((m : ℝ) + 2) * ((m : ℝ) + 3)) := by
  field_simp
  ring_nf

/-- The telescoping differences are nonnegative. -/
private lemma telescoping_term_nonneg (m : ℕ) :
    0 ≤ (1 : ℝ) / ((m : ℝ) + 2) - 1 / ((m : ℝ) + 3) := by
  rw [telescoping_term_eq]
  exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1)
    (mul_nonneg (by positivity : 0 ≤ (m : ℝ) + 2) (by positivity : 0 ≤ (m : ℝ) + 3))

/-- `1/((m+2)(m+3)) ≤ 1/(m+2)^2`. -/
private lemma telescoping_term_le (m : ℕ) :
    (1 : ℝ) / ((m : ℝ) + 2) - 1 / ((m : ℝ) + 3) ≤ 1 / ((m : ℝ) + 2) ^ 2 := by
  rw [telescoping_term_eq]
  have hle : ((m : ℝ) + 2) ^ 2 ≤ ((m : ℝ) + 2) * ((m : ℝ) + 3) := by nlinarith
  exact one_div_le_one_div_of_le (by positivity : 0 < ((m : ℝ) + 2) ^ 2) hle

/-- Summability of the telescoping differences. -/
private lemma summable_telescoping :
    Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 2) - 1 / ((m : ℝ) + 3)) := by
  have hps : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
  have hps2 : Summable (fun i : ℕ => 1 / ((i : ℝ) + 2) ^ 2) := by
    have hs : Summable (fun n : ℕ => (fun n : ℕ => 1 / (n : ℝ) ^ 2) (n + 2)) :=
      (summable_nat_add_iff 2).mpr hps
    simpa [Nat.cast_add] using hs
  exact Summable.of_nonneg_of_le (fun m => telescoping_term_nonneg m) (fun m => telescoping_term_le m) hps2

/-- `∑' m, (1/(m+2) - 1/(m+3)) = 1/2`, by telescoping. -/
private lemma tsum_telescoping :
    (∑' m : ℕ, ((1 : ℝ) / ((m : ℝ) + 2) - 1 / ((m : ℝ) + 3))) = 1 / 2 := by
  let a : ℕ → ℝ := fun i => 1 / ((i + 2 : ℕ) : ℝ)
  have ha (i : ℕ) : a i - a (i + 1) = (1 : ℝ) / ((i : ℝ) + 2) - 1 / ((i : ℝ) + 3) := by
    unfold a
    have h₁ : (i + 1 + 2 : ℕ) = i + 3 := by omega
    rw [h₁]
    norm_num [Nat.cast_add]
  have hsum : Summable (fun i : ℕ => a i - a (i + 1)) := by
    exact summable_telescoping.congr (fun i => (ha i).symm)
  have htend : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, (a i - a (i + 1))) atTop (𝓝 (1 / 2)) := by
    have htelesc : ∀ N : ℕ, (∑ i ∈ Finset.range N, (a i - a (i + 1))) = a 0 - a N :=
      Finset.sum_range_sub' a
    have hN0 : Tendsto (fun N : ℕ => a N) atTop (𝓝 0) := by
      unfold a
      have hc : Tendsto (fun N : ℕ => (((N + 2 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) :=
        (tendsto_inv_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 2))
      simpa [one_div] using hc
    have hconst : Tendsto (fun _ : ℕ => a 0) atTop (𝓝 (a 0)) := tendsto_const_nhds
    have hsub : Tendsto (fun N : ℕ => a 0 - a N) atTop (𝓝 (a 0 - 0)) := hconst.sub hN0
    have hcong : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, (a i - a (i + 1))) atTop (𝓝 (a 0 - 0)) :=
      hsub.congr' (Filter.Eventually.of_forall (fun N => (htelesc N).symm))
    simpa [a] using hcong
  have h := (Summable.hasSum_iff_tendsto_nat hsum).2 htend
  have hEqFun : (fun i : ℕ => a i - a (i + 1)) =
      fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 2) - 1 / ((m : ℝ) + 3) := by
    funext i
    exact ha i
  have h' : HasSum (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 2) - 1 / ((m : ℝ) + 3)) (1 / 2) := by
    simpa [hEqFun] using h
  exact h'.tsum_eq

/-- `1/((m+3)^2) ≤ 1/((m+2)(m+3))`, the termwise comparison. -/
private lemma sq_tail_term_le (m : ℕ) :
    (1 : ℝ) / ((m : ℝ) + 3) ^ 2 ≤ 1 / (((m : ℝ) + 2) * ((m : ℝ) + 3)) := by
  have hle : ((m : ℝ) + 2) * ((m : ℝ) + 3) ≤ ((m : ℝ) + 3) ^ 2 := by nlinarith
  exact one_div_le_one_div_of_le (by positivity : 0 < ((m : ℝ) + 2) * ((m : ℝ) + 3)) hle

/-- `∑' m, 1 / (m+3)^2 ≤ 1 / 2`. -/
private lemma tsum_sq_tail_le_half :
    (∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + 3) ^ 2) ≤ 1 / 2 := by
  have hterm : ∀ m : ℕ, (1 : ℝ) / ((m : ℝ) + 3) ^ 2 ≤
      (1 : ℝ) / ((m : ℝ) + 2) - 1 / ((m : ℝ) + 3) := by
    intro m
    rw [telescoping_term_eq m]
    exact sq_tail_term_le m
  have hsum : Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 3) ^ 2) := by
    have hps : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
      (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
    have hs : Summable (fun n : ℕ => (fun n : ℕ => 1 / (n : ℝ) ^ 2) (n + 3)) :=
      (summable_nat_add_iff 3).mpr hps
    simpa [Nat.cast_add, add_assoc] using hs
  calc
    (∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + 3) ^ 2)
        ≤ ∑' m : ℕ, ((1 : ℝ) / ((m : ℝ) + 2) - 1 / ((m : ℝ) + 3)) :=
          Summable.tsum_le_tsum hterm hsum summable_telescoping
    _ = 1 / 2 := tsum_telescoping

/-- `∑' m, 1 / (m+2)^2 ≤ 3 / 4`. -/
private lemma tsum_inv_sq_shift_le_three_quarters :
    (∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + 2) ^ 2) ≤ 3 / 4 := by
  have hsplit : (∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + 2) ^ 2) =
      (1 : ℝ) / 4 + ∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + 3) ^ 2 := by
    let g : ℕ → ℝ := fun m => (1 : ℝ) / ((m : ℝ) + 2) ^ 2
    have hsumg : Summable g := by
      have hps : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
        (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
      have hs : Summable (fun n : ℕ => (fun n : ℕ => 1 / (n : ℝ) ^ 2) (n + 2)) :=
        (summable_nat_add_iff 2).mpr hps
      refine hs.congr ?_
      intro n
      have h₁ : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by norm_num
      simp [g, h₁]
    have hsplit := Summable.tsum_eq_zero_add hsumg
    change (∑' m : ℕ, g m) = (1 : ℝ) / 4 + ∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + 3) ^ 2
    rw [hsplit]
    congr 1
    · norm_num [g]
    · apply tsum_congr
      intro m
      have h₁ : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by norm_num
      simp [g, h₁]
      ring_nf
  calc
    (∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + 2) ^ 2) = (1 : ℝ) / 4 + ∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + 3) ^ 2 := hsplit
    _ ≤ (1 : ℝ) / 4 + 1 / 2 := by
      have ht := tsum_sq_tail_le_half
      linarith
    _ = 3 / 4 := by norm_num

/-- `riemannZeta s = 1 + ∑' m, (m+2)^(-s)` for `1 < s.re`. -/
private lemma zeta_eq_one_add_tail {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = (1 : ℂ) + ∑' m : ℕ, 1 / (((m + 2 : ℕ) : ℂ) ^ s) := by
  let f : ℕ → ℂ := fun n => 1 / (((n + 1 : ℕ) : ℂ) ^ s)
  have hbase : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
    (Complex.summable_one_div_nat_cpow).mpr hs
  have hsumf : Summable f := by
    have hshift : Summable (fun n : ℕ => (fun n : ℕ => 1 / (n : ℂ) ^ s) (n + 1)) :=
      (summable_nat_add_iff 1).mpr hbase
    exact hshift.congr (fun n => rfl)
  calc
    riemannZeta s = ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s :=
      zeta_eq_tsum_one_div_nat_add_one_cpow hs
    _ = ∑' n : ℕ, f n := by
      apply tsum_congr
      intro n
      have hb : ((n : ℂ) + 1) = (((n + 1 : ℕ) : ℂ)) := by norm_num
      rw [hb]
    _ = f 0 + ∑' m : ℕ, f (m + 1) := Summable.tsum_eq_zero_add hsumf
    _ = (1 : ℂ) + ∑' m : ℕ, 1 / (((m + 2 : ℕ) : ℂ) ^ s) := by
      congr 1
      · simp [f, Complex.one_cpow]

/-- Norm of the shifted terms on the line `re s = 2`. -/
private lemma norm_sq_term {s : ℂ} (hsre : s.re = 2) (m : ℕ) :
    ‖(1 : ℂ) / (((m + 2 : ℕ) : ℂ) ^ s)‖ = (1 : ℝ) / ((m : ℝ) + 2) ^ 2 := by
  have hpos : 0 < (m + 2 : ℕ) := by omega
  rw [norm_div, norm_one]
  rw [Complex.norm_natCast_cpow_of_pos hpos]
  rw [hsre]
  rw [Real.rpow_two]
  norm_num [Nat.cast_add]

/-- On the line `re s = 2` the shifted tail has norm at most `3/4`. -/
private lemma tail_norm_le_three_quarters {s : ℂ} (hsre : s.re = 2) :
    (∑' m : ℕ, ‖(1 : ℂ) / (((m + 2 : ℕ) : ℂ) ^ s)‖) ≤ 3 / 4 := by
  calc
    (∑' m : ℕ, ‖(1 : ℂ) / (((m + 2 : ℕ) : ℂ) ^ s)‖)
        = ∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + 2) ^ 2 := by
          apply tsum_congr
          intro m
          exact norm_sq_term hsre m
    _ ≤ 3 / 4 := tsum_inv_sq_shift_le_three_quarters


/-- On the vertical line `re s = 2`, the zeta function has norm at least `1/4`. -/
private theorem zeta_norm_re_two_lower_quarter (T : ℝ) :
    (1 / 4 : ℝ) ≤ ‖riemannZeta ((2 : ℂ) + Complex.I * (T : ℂ))‖ := by
  let s : ℂ := (2 : ℂ) + Complex.I * (T : ℂ)
  have hsre : s.re = 2 := by simp [s]
  have hs1 : 1 < s.re := by rw [hsre]; norm_num
  have htail_le : ‖∑' m : ℕ, (1 : ℂ) / (((m + 2 : ℕ) : ℂ) ^ s)‖ ≤ 3 / 4 := by
    calc
      ‖∑' m : ℕ, (1 : ℂ) / (((m + 2 : ℕ) : ℂ) ^ s)‖
          ≤ ∑' m : ℕ, ‖(1 : ℂ) / (((m + 2 : ℕ) : ℂ) ^ s)‖ := by
            apply norm_tsum_le_tsum_norm
            -- Summable (fun m => ‖(1:ℂ)/(((m+2:ℕ):ℂ)^s)‖)
            have hps : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
              (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
            have hs2 : Summable (fun n : ℕ => (fun n : ℕ => 1 / (n : ℝ) ^ 2) (n + 2)) :=
              (summable_nat_add_iff 2).mpr hps
            have hfeq : (fun m : ℕ => ‖(1 : ℂ) / (((m + 2 : ℕ) : ℂ) ^ s)‖) =
                fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 2) ^ 2 := by
              funext m
              exact norm_sq_term hsre m
            rw [hfeq]
            simpa [Nat.cast_add] using hs2
      _ ≤ 3 / 4 := tail_norm_le_three_quarters hsre
  have hzeta : riemannZeta s = (1 : ℂ) + ∑' m : ℕ, 1 / (((m + 2 : ℕ) : ℂ) ^ s) :=
    zeta_eq_one_add_tail hs1
  have htri : (1 : ℝ) - ‖∑' m : ℕ, (1 : ℂ) / (((m + 2 : ℕ) : ℂ) ^ s)‖ ≤
      ‖(1 : ℂ) + ∑' m : ℕ, (1 : ℂ) / (((m + 2 : ℕ) : ℂ) ^ s)‖ := by
    let z : ℂ := ∑' m : ℕ, (1 : ℂ) / (((m + 2 : ℕ) : ℂ) ^ s)
    have hz : (1 : ℝ) ≤ ‖(1 : ℂ) + z‖ + ‖z‖ := by
      have hh := norm_sub_le ((1 : ℂ) + z) z
      simpa using hh
    dsimp [z] at hz
    linarith
  have hfinal : (1 : ℝ) / 4 ≤ ‖riemannZeta s‖ := by
    rw [hzeta]
    have h1 : (1 : ℝ) / 4 ≤ ‖(1 : ℂ) + ∑' m : ℕ, (1 : ℂ) / (((m + 2 : ℕ) : ℂ) ^ s)‖ := by
      linarith
    simpa using h1
  simpa [s] using hfinal

/-- `riemannZeta₁` is bounded away from zero on the vertical line `re s = 2`:
`‖ζ₁ (2 + i t)‖ ≥ 1/4` for every real `t`. -/
theorem zeta1_re_two_lower (t : ℝ) :
    (1 / 4 : ℝ) ≤ ‖riemannZeta₁ ((2 : ℂ) + Complex.I * (t : ℂ))‖ := by
  set s : ℂ := (2 : ℂ) + Complex.I * (t : ℂ) with hsdef
  have hsre : s.re = 2 := by simp [s]
  have hs1 : s ≠ 1 := by
    intro h
    have hre : s.re = (1 : ℂ).re := congrArg Complex.re h
    rw [hsre] at hre
    norm_num at hre
  have hrel : riemannZeta₁ s = (s - 1) * riemannZeta s := by
    calc
      riemannZeta₁ s = (s - 1) * ((s - 1)⁻¹ * riemannZeta₁ s) := by
        rw [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs1), one_mul]
      _ = (s - 1) * riemannZeta s := by
        rw [riemannZeta_eq_inv_sub_mul hs1]
  have hsm1 : (1 : ℝ) ≤ ‖s - 1‖ := by
    have hre1 : (s - 1).re = 1 := by dsimp [s]; norm_num
    have hle : |(s - 1).re| ≤ ‖s - 1‖ := Complex.abs_re_le_norm (s - 1)
    rw [hre1] at hle
    have : |(1 : ℝ)| = (1 : ℝ) := by norm_num
    rwa [this] at hle
  have hz : (1 / 4 : ℝ) ≤ ‖riemannZeta s‖ := by
    simpa [s] using (zeta_norm_re_two_lower_quarter t)
  have hnorm : ‖riemannZeta₁ s‖ = ‖s - 1‖ * ‖riemannZeta s‖ := by
    rw [hrel, norm_mul]
  simpa [s] using
    (calc
      (1 / 4 : ℝ) ≤ ‖riemannZeta s‖ := hz
      _ ≤ ‖s - 1‖ * ‖riemannZeta s‖ := le_mul_of_one_le_left (norm_nonneg _) hsm1
      _ = ‖riemannZeta₁ s‖ := hnorm.symm)

end Commons.NumberTheory.Zeta
