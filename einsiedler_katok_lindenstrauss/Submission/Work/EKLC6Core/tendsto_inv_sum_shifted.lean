import Mathlib

namespace Work.EKLC6Core

open Filter Topology

/-- If the Cesàro means `(1/n) ∑_{j<n} a_j` converge, then `a_n / n → 0`.
This is because `a_n = S_{n+1} - S_n = (n+1) c_{n+1} - n c_n` where
`c_m = S_m / m`, so `a_n / n = ((n+1)/n) c_{n+1} - c_n → c - c = 0`. -/
private lemma cesaro_inv_mul_tendsto_zero {a : ℕ → ℝ} {c : ℝ}
    (ha : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, a j) atTop (nhds c)) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * a n) atTop (nhds 0) := by
  let S : ℕ → ℝ := fun n => ∑ j ∈ Finset.range n, a j
  let G : ℕ → ℝ := fun n => (n : ℝ)⁻¹ * S n
  have haG : Tendsto G atTop (nhds c) := by simpa only [G, S] using ha
  have hG1 : Tendsto (fun n : ℕ => G (n + 1)) atTop (nhds c) :=
    haG.comp (Filter.tendsto_add_atTop_nat 1)
  have hfact : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * (n : ℝ)⁻¹) atTop (nhds 1) := by
    have h_inv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add h_inv
    refine Tendsto.congr' ?_ (by simpa using h)
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      have : n ≠ 0 := by omega
      exact_mod_cast this
    field_simp
  have hprod : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * (n : ℝ)⁻¹ * G (n + 1)) atTop (nhds c) := by
    have := hfact.mul hG1
    simpa using this
  have hmain := hprod.sub haG
  rw [sub_self] at hmain
  refine Tendsto.congr' ?_ hmain
  filter_upwards with n
  simp only [G, S]
  rw [Finset.sum_range_succ]
  push_cast
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- `((n + i) : ℝ) / n → 1`. -/
private lemma tendsto_coeff_add_mul_inv (i : ℕ) :
    Tendsto (fun n : ℕ => ((n + i : ℕ) : ℝ) * (n : ℝ)⁻¹) atTop (nhds 1) := by
  have h_inv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h : Tendsto (fun n : ℕ => 1 + (i : ℝ) * (n : ℝ)⁻¹) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_const_nhds (x := (i : ℝ))).mul h_inv)
  refine Tendsto.congr' ?_ h
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by
    have : n ≠ 0 := by omega
    exact_mod_cast this
  push_cast
  field_simp

/-- `((n - k + i) : ℝ) / n → 1`. -/
private lemma tendsto_coeff_sub_add_mul_inv (k i : ℕ) :
    Tendsto (fun n : ℕ => ((n - k + i : ℕ) : ℝ) * (n : ℝ)⁻¹) atTop (nhds 1) := by
  have h_inv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h : Tendsto (fun n : ℕ => 1 + ((i : ℝ) - k) * (n : ℝ)⁻¹) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_const_nhds (x := ((i : ℝ) - k))).mul h_inv)
  refine Tendsto.congr' ?_ h
  filter_upwards [Filter.eventually_ge_atTop (k + 1)] with n hn
  have hk : k ≤ n := by omega
  have hn0 : (n : ℝ) ≠ 0 := by
    have : n ≠ 0 := by omega
    exact_mod_cast this
  have hkam : ((n - k + i : ℕ) : ℝ) = (n : ℝ) - k + i := by
    rw [Nat.cast_add, Nat.cast_sub hk]
  rw [hkam]
  field_simp
  ring

theorem tendsto_inv_sum_shifted {a : ℕ → ℝ} {c : ℝ}
    (ha : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, a j)
      Filter.atTop (nhds c)) (k : ℕ) :
    Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.Icc 1 k, a (n + i))
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.Icc 1 k, a (n - k + i))
      Filter.atTop (nhds 0) := by
  let b : ℕ → ℝ := fun m => (m : ℝ)⁻¹ * a m
  have hb : Tendsto b atTop (nhds 0) := by
    simpa only [b] using cesaro_inv_mul_tendsto_zero ha
  constructor
  · have hsum : Tendsto (fun n : ℕ => ∑ i ∈ Finset.Icc 1 k, (n : ℝ)⁻¹ * a (n + i))
        atTop (nhds 0) := by
      have hterm : ∀ i ∈ Finset.Icc 1 k,
          Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * a (n + i)) atTop (nhds 0) := by
        intro i hi
        have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
        have hprod : Tendsto (fun n : ℕ => ((n + i : ℕ) : ℝ) * (n : ℝ)⁻¹ * b (n + i))
            atTop (nhds 0) := by
          have := (tendsto_coeff_add_mul_inv i).mul (hb.comp (Filter.tendsto_add_atTop_nat i))
          simpa using this
        refine Tendsto.congr' ?_ hprod
        filter_upwards with n
        simp only [b]
        have hne : ((n + i : ℕ) : ℝ) ≠ 0 := by
          have : n + i ≠ 0 := by omega
          exact_mod_cast this
        field_simp
      simpa using tendsto_finsetSum (Finset.Icc 1 k) hterm
    refine Tendsto.congr' ?_ hsum
    filter_upwards with n
    rw [Finset.mul_sum]
  · have hsum : Tendsto (fun n : ℕ => ∑ i ∈ Finset.Icc 1 k, (n : ℝ)⁻¹ * a (n - k + i))
        atTop (nhds 0) := by
      have hterm : ∀ i ∈ Finset.Icc 1 k,
          Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * a (n - k + i)) atTop (nhds 0) := by
        intro i hi
        have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
        have hm : Tendsto (fun n : ℕ => n - k + i) atTop atTop :=
          (Filter.tendsto_add_atTop_nat i).comp (Filter.tendsto_sub_atTop_nat k)
        have hprod : Tendsto (fun n : ℕ => ((n - k + i : ℕ) : ℝ) * (n : ℝ)⁻¹ * b (n - k + i))
            atTop (nhds 0) := by
          have := (tendsto_coeff_sub_add_mul_inv k i).mul (hb.comp hm)
          simpa using this
        refine Tendsto.congr' ?_ hprod
        filter_upwards [Filter.eventually_ge_atTop (k + 1)] with n hn
        simp only [b]
        have hne : ((n - k + i : ℕ) : ℝ) ≠ 0 := by
          have : n - k + i ≠ 0 := by omega
          exact_mod_cast this
        field_simp
      simpa using tendsto_finsetSum (Finset.Icc 1 k) hterm
    refine Tendsto.congr' ?_ hsum
    filter_upwards with n
    rw [Finset.mul_sum]

end Work.EKLC6Core
