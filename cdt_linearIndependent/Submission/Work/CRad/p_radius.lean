import Mathlib
import Submission.CDTPlan.InterfacesC
import Submission.Work.CRad.d_decay_cuspDisc
import Submission.Work.CRad.alphaF_ratio
import Submission.Work.CRad.rho_Rd_bounds

/-!
# Area CRad — the radius of `P` under the relation (`PRadius`)

Under an assumed relation `r_a·η_a + r_b·η_b + r_ab·η_aη_b = r₀` (paper eq.
`(rabc)`) with `a = 2m+1`, `b = 2n+1`, the unlikely `G`-function
`P = logP a b` (paper eq. `(defP)`, `Submission.CDT.logP`) has rational
coefficients whose size is controlled: `|cₖ| ≤ C·(3/2)^k`.  This is the
statement `Submission.CDTPlan.PRadius`, the analytic input that lets the
symmetrised `G = Sym⁺P` be continued by the §6 holonomy machinery.

The proof uses the decomposition

```
cₖ = r_a·dₖ(a)·uₖ(b) + r_b·uₖ(a)·dₖ(b)
     + r_ab·(η_a·uₖ(a)·dₖ(b) + η_b·dₖ(a)·uₖ(b) + dₖ(a)·dₖ(b))
```

(`beukersPabCoeff_decomp`), where `dₖ(a) = vₖ(a) − η_a·uₖ(a)`
(`beukersD`) and `uₖ(a) = beukersUR a k`, together with the two bounds

* `|uₖ(b)| ≤ C_b·r_b^{−k}` for every `r_b < ρ_b` (`beukersUR_cauchy_growth`),
* `|dₖ(a)| ≤ C_a·r_a^{−k}` for every `r_a < 2√(a²−1) − 1 − ρ_a`
  (`Work.CRad.d_decay_cuspDisc`, an upgrade of `beukersD_sharp_decay` to the
  full cusp-disc radius).

Each product then has geometric base `< 3/2`: with `ρ_x = x − √(x²−1)` one has
`ρ_x·(2√(x²−1) − 1 − ρ_x) ≥ 26√2 − 36` (`Work.CRad.rho_Rd_bounds`), while the
admissibility hypothesis `10⁶|m−n| ≤ n` forces `α_b/α_a ≤ 1.001`
(`Work.CRad.alphaF_ratio`) with `α_x = x + √(x²−1) = 1/ρ_x`.
-/

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.CRad

open Submission.CDTPlan
open Submission.CDT

/-- `α_x^{-1} = ρ_x`, i.e. `(x + √(x²−1))⁻¹ = x − √(x²−1)`. -/
lemma alpha_inv_rho (x : ℝ) (hx : 1 ≤ x) : (x + Real.sqrt (x^2 - 1))⁻¹ = beukersRho x := by
  rw [beukersRho]
  have h : (x + Real.sqrt (x ^ 2 - 1)) * (x - Real.sqrt (x ^ 2 - 1)) = 1 := by
    have hsq : (Real.sqrt (x ^ 2 - 1)) ^ 2 = x ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
    nlinarith [hsq]
  exact inv_eq_of_mul_eq_one_right h

/-- `α_b ≤ (1001/1000)·α_a` implies `ρ_a ≤ (1001/1000)·ρ_b`. -/
lemma rho_le_of_alpha_le {a b : ℝ} (ha : 3 ≤ a) (hb : 3 ≤ b)
    (h : b + Real.sqrt (b^2 - 1) ≤ (1001/1000) * (a + Real.sqrt (a^2 - 1))) :
    beukersRho a ≤ (1001/1000) * beukersRho b := by
  have hαa_pos : (0:ℝ) < a + Real.sqrt (a^2 - 1) := by
    have := beukers_sqrt_sq_sub_one_pos a ha; linarith
  have hαb_pos : (0:ℝ) < b + Real.sqrt (b^2 - 1) := by
    have := beukers_sqrt_sq_sub_one_pos b hb; linarith
  have key : (1:ℝ) / (a + Real.sqrt (a^2 - 1)) ≤ (1001/1000) / (b + Real.sqrt (b^2 - 1)) := by
    rw [div_le_div_iff₀ hαa_pos hαb_pos]; linarith
  rw [← alpha_inv_rho a (by linarith), ← alpha_inv_rho b (by linarith)]
  simpa [one_div, div_eq_mul_inv] using key

/-- A numerical lower bound for `√2` used to evaluate `26√2 − 36`. -/
lemma sqrt2_gt : (1.4142 : ℝ) < Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]

/-- The numeric constant entering the geometric base bound. -/
lemma const_bound : (2:ℝ)/3 < (99/100)^2 * ((1000/1001) * (26 * Real.sqrt 2 - 36)) := by
  have h2 := sqrt2_gt
  nlinarith [h2]

/-- The trivial numeric constant used for the `dₐ·d_b` product. -/
lemma const_bound_self : (2:ℝ)/3 < (99/100)^2 * ((1:ℝ) * 1) := by norm_num

/-- Coefficient-wise decomposition of `logPCoeff` into the exponentially
decaying parts `dₖ` (paper: `v_k − η u_k`) times the Beukers `u`-sequences. -/
lemma logPCoeff_decomp (a b : ℝ) (ra rb rab : ℤ) (n : ℕ) :
    logPCoeff a b ra rb rab n =
      (ra : ℝ) * (beukersD a n * beukersUR b n)
        + (rb : ℝ) * (beukersUR a n * beukersD b n)
        + (rab : ℝ) * (beukersEta a * beukersUR a n * beukersD b n
            + beukersEta b * beukersD a n * beukersUR b n
            + beukersD a n * beukersD b n) := by
  unfold logPCoeff beukersPaCoeff beukersPbCoeff beukersPabCoeff beukersD
  ring

/-- `C / r^n = C · (1/r)^n`. -/
lemma div_pow_eq (C r : ℝ) (n : ℕ) : C / r^n = C * (1/r)^n := by
  rw [div_eq_mul_inv, ← inv_pow, one_div]

theorem p_radius : PRadius := by
  intro m n ra rb rab r0 hAdm hRel
  obtain ⟨hm1, hn1, hmn, hgap⟩ := hAdm
  have hgap' : 10 ^ 6 * (((m : ℤ) - (n : ℤ)).natAbs) ≤ n := hgap
  set a : ℝ := 2 * (m : ℝ) + 1 with ha_def
  set b : ℝ := 2 * (n : ℝ) + 1 with hb_def
  have ha3 : 3 ≤ a := by
    rw [ha_def]
    have hm : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
    linarith
  have hb3 : 3 ≤ b := by
    rw [hb_def]
    have hn : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
    linarith
  -- the relation (rabc), in the form expected by `logPCoeff_logP`
  have hrelR : (ra : ℝ) * beukersEta ((2 * m + 1 : ℚ) : ℝ)
      + (rb : ℝ) * beukersEta ((2 * n + 1 : ℚ) : ℝ)
      + (rab : ℝ) * (beukersEta ((2 * m + 1 : ℚ) : ℝ) * beukersEta ((2 * n + 1 : ℚ) : ℝ))
      = (r0 : ℝ) := by
    push_cast
    exact hRel
  have hcoeff (k : ℕ) : ((PowerSeries.coeff k (PC m n ra rb rab r0) : ℚ) : ℝ)
      = logPCoeff a b ra rb rab k := by
    have h := (logPCoeff_logP (2 * m + 1 : ℚ) (2 * n + 1 : ℚ) ra rb rab r0 hrelR k).symm
    have h2 : ((PowerSeries.coeff k (PC m n ra rb rab r0) : ℚ) : ℝ)
        = ((PowerSeries.coeff k (Submission.CDT.logP (2 * m + 1 : ℚ) (2 * n + 1 : ℚ)
            ra rb rab r0) : ℚ) : ℝ) := rfl
    rw [h2, h]
    push_cast
    rw [ha_def, hb_def]
  have hρa_pos : 0 < beukersRho a := beukers_rho_pos a ha3
  have hρb_pos : 0 < beukersRho b := beukers_rho_pos b hb3
  set Ea : ℝ := 2 * Real.sqrt (a ^ 2 - 1) - 1 - beukersRho a with hEa_def
  set Eb : ℝ := 2 * Real.sqrt (b ^ 2 - 1) - 1 - beukersRho b with hEb_def
  have hRda_ge : 26 * Real.sqrt 2 - 36 ≤ beukersRho a * Ea := by
    simpa [hEa_def] using (rho_Rd_bounds a ha3).1
  have hRdb_ge : 26 * Real.sqrt 2 - 36 ≤ beukersRho b * Eb := by
    simpa [hEb_def] using (rho_Rd_bounds b hb3).1
  have hRda_gt1 : (1:ℝ) < Ea := by simpa [hEa_def] using (rho_Rd_bounds a ha3).2
  have hRdb_gt1 : (1:ℝ) < Eb := by simpa [hEb_def] using (rho_Rd_bounds b hb3).2
  have hEa_pos : 0 < Ea := by linarith
  have hEb_pos : 0 < Eb := by linarith
  -- the four coefficient bounds
  obtain ⟨Cda, hCda_pos, hDa0⟩ := d_decay_cuspDisc a ha3 (r := (99/100)*Ea)
      (by nlinarith) (by nlinarith)
  obtain ⟨Cdb, hCdb_pos, hDb0⟩ := d_decay_cuspDisc b hb3 (r := (99/100)*Eb)
      (by nlinarith) (by nlinarith)
  obtain ⟨Cua, hCua_pos, huA0⟩ := beukersUR_cauchy_growth a ha3 (r := (99/100)*beukersRho a)
      (by nlinarith) (by nlinarith)
  obtain ⟨Cub, hCub_pos, huB0⟩ := beukersUR_cauchy_growth b hb3 (r := (99/100)*beukersRho b)
      (by nlinarith) (by nlinarith)
  have hdabs_a : ∀ k, |beukersD a k| ≤ Cda * (1/((99/100)*Ea))^k := by
    intro k
    have h := hDa0 k
    rw [Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  have hdabs_b : ∀ k, |beukersD b k| ≤ Cdb * (1/((99/100)*Eb))^k := by
    intro k
    have h := hDb0 k
    rw [Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  have huabs_a : ∀ k, |beukersUR a k| ≤ Cua * (1/((99/100)*beukersRho a))^k := by
    intro k
    calc |beukersUR a k| ≤ Cua / ((99/100)*beukersRho a)^k := huA0 k
      _ = Cua * (1/((99/100)*beukersRho a))^k := by rw [div_pow_eq]
  have huabs_b : ∀ k, |beukersUR b k| ≤ Cub * (1/((99/100)*beukersRho b))^k := by
    intro k
    calc |beukersUR b k| ≤ Cub / ((99/100)*beukersRho b)^k := huB0 k
      _ = Cub * (1/((99/100)*beukersRho b))^k := by rw [div_pow_eq]
  -- the cusp ratio, transferred from α to ρ
  have hα1 : b + Real.sqrt (b^2 - 1) ≤ (1001/1000) * (a + Real.sqrt (a^2 - 1)) := by
    have h := (alphaF_ratio m n hm1 hn1 hgap').1
    have hab : ((2*m+1:ℕ):ℝ) = a := by rw [ha_def]; push_cast; ring
    have hbb : ((2*n+1:ℕ):ℝ) = b := by rw [hb_def]; push_cast; ring
    rw [hab, hbb] at h
    exact h
  have hα2 : a + Real.sqrt (a^2 - 1) ≤ (1001/1000) * (b + Real.sqrt (b^2 - 1)) := by
    have h := (alphaF_ratio m n hm1 hn1 hgap').2
    have hab : ((2*m+1:ℕ):ℝ) = a := by rw [ha_def]; push_cast; ring
    have hbb : ((2*n+1:ℕ):ℝ) = b := by rw [hb_def]; push_cast; ring
    rw [hab, hbb] at h
    exact h
  have hρ_ab : beukersRho a ≤ (1001/1000) * beukersRho b := rho_le_of_alpha_le ha3 hb3 hα1
  have hρ_ba : beukersRho b ≤ (1001/1000) * beukersRho a := rho_le_of_alpha_le hb3 ha3 hα2
  -- the three geometric bases are all `< 3/2`
  have hbase1 : (1/((99/100)*Ea)) * (1/((99/100)*beukersRho b)) < 3/2 := by
    have hb_ge : beukersRho b ≥ (1000/1001) * beukersRho a := by nlinarith [hρ_ab]
    have hkey : Ea * beukersRho b ≥ (1000/1001) * (26*Real.sqrt 2 - 36) := by
      have h1 := mul_le_mul_of_nonneg_left hb_ge (le_of_lt hEa_pos)
      linarith [hRda_ge, h1]
    have hstep : (99/100)^2 * ((1000/1001) * (26 * Real.sqrt 2 - 36)) ≤ (99/100)^2 * (Ea * beukersRho b) :=
      mul_le_mul_of_nonneg_left hkey (by norm_num)
    have hgoal : (99/100)^2 * (Ea * beukersRho b) > 2/3 := lt_of_lt_of_le const_bound hstep
    have hX : (1/((99/100)*Ea)) * (1/((99/100)*beukersRho b))
        = 1/(((99/100)*Ea) * ((99/100)*beukersRho b)) := by
      rw [div_mul_div_comm]; norm_num
    rw [hX, div_lt_iff₀ (by positivity)]
    nlinarith [hgoal]
  have hbase2 : (1/((99/100)*beukersRho a)) * (1/((99/100)*Eb)) < 3/2 := by
    have ha_ge : beukersRho a ≥ (1000/1001) * beukersRho b := by nlinarith [hρ_ba]
    have hkey : beukersRho a * Eb ≥ (1000/1001) * (26*Real.sqrt 2 - 36) := by
      have h1 := mul_le_mul_of_nonneg_left ha_ge (le_of_lt hEb_pos)
      linarith [hRdb_ge, h1]
    have hstep : (99/100)^2 * ((1000/1001) * (26 * Real.sqrt 2 - 36)) ≤ (99/100)^2 * (beukersRho a * Eb) :=
      mul_le_mul_of_nonneg_left hkey (by norm_num)
    have hgoal : (99/100)^2 * (beukersRho a * Eb) > 2/3 := lt_of_lt_of_le const_bound hstep
    have hX : (1/((99/100)*beukersRho a)) * (1/((99/100)*Eb))
        = 1/(((99/100)*beukersRho a) * ((99/100)*Eb)) := by
      rw [div_mul_div_comm]; norm_num
    rw [hX, div_lt_iff₀ (by positivity)]
    nlinarith [hgoal]
  have hbase3 : (1/((99/100)*Ea)) * (1/((99/100)*Eb)) < 3/2 := by
    have hstep : (99/100)^2 * ((1:ℝ) * 1) ≤ (99/100)^2 * (Ea * Eb) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (le_of_lt hRda_gt1) (le_of_lt hRdb_gt1) (by norm_num) (le_of_lt hEa_pos))
        (by norm_num)
    have hgoal : (99/100)^2 * (Ea * Eb) > 2/3 := lt_of_lt_of_le const_bound_self hstep
    have hX : (1/((99/100)*Ea)) * (1/((99/100)*Eb)) = 1/(((99/100)*Ea) * ((99/100)*Eb)) := by
      rw [div_mul_div_comm]; norm_num
    rw [hX, div_lt_iff₀ (by positivity)]
    nlinarith [hgoal]
  set K : ℝ := |(ra:ℝ)| * Cda * Cub + |(rb:ℝ)| * Cua * Cdb
      + |(rab:ℝ)| * (|beukersEta a| * Cua * Cdb + |beukersEta b| * Cda * Cub + Cda * Cdb) with hK_def
  refine ⟨K, ?_⟩
  intro k
  rw [hcoeff k]
  have ht_da_ub : |beukersD a k| * |beukersUR b k| ≤ Cda * Cub * (3/2)^k := by
    have h1 := hdabs_a k
    have h2 := huabs_b k
    calc |beukersD a k| * |beukersUR b k|
        ≤ (Cda * (1/((99/100)*Ea))^k) * (Cub * (1/((99/100)*beukersRho b))^k) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = Cda * Cub * ((1/((99/100)*Ea)) * (1/((99/100)*beukersRho b)))^k := by
          rw [mul_pow]; ring
      _ ≤ Cda * Cub * (3/2)^k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (le_of_lt hbase1) k) (by positivity)
  have ht_ua_db : |beukersUR a k| * |beukersD b k| ≤ Cua * Cdb * (3/2)^k := by
    have h1 := huabs_a k
    have h2 := hdabs_b k
    calc |beukersUR a k| * |beukersD b k|
        ≤ (Cua * (1/((99/100)*beukersRho a))^k) * (Cdb * (1/((99/100)*Eb))^k) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = Cua * Cdb * ((1/((99/100)*beukersRho a)) * (1/((99/100)*Eb)))^k := by
          rw [mul_pow]; ring
      _ ≤ Cua * Cdb * (3/2)^k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (le_of_lt hbase2) k) (by positivity)
  have ht_da_db : |beukersD a k| * |beukersD b k| ≤ Cda * Cdb * (3/2)^k := by
    have h1 := hdabs_a k
    have h2 := hdabs_b k
    calc |beukersD a k| * |beukersD b k|
        ≤ (Cda * (1/((99/100)*Ea))^k) * (Cdb * (1/((99/100)*Eb))^k) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = Cda * Cdb * ((1/((99/100)*Ea)) * (1/((99/100)*Eb)))^k := by
          rw [mul_pow]; ring
      _ ≤ Cda * Cdb * (3/2)^k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (le_of_lt hbase3) k) (by positivity)
  have habs_sum : |beukersEta a * beukersUR a k * beukersD b k
        + beukersEta b * beukersD a k * beukersUR b k + beukersD a k * beukersD b k|
      ≤ (|beukersEta a| * |beukersUR a k|) * |beukersD b k|
        + (|beukersEta b| * |beukersD a k|) * |beukersUR b k| + |beukersD a k| * |beukersD b k| := by
    have h := abs_add_three (beukersEta a * beukersUR a k * beukersD b k)
        (beukersEta b * beukersD a k * beukersUR b k) (beukersD a k * beukersD b k)
    simpa only [abs_mul] using h
  have hsum3 : (|beukersEta a| * |beukersUR a k|) * |beukersD b k|
      + (|beukersEta b| * |beukersD a k|) * |beukersUR b k| + |beukersD a k| * |beukersD b k|
      ≤ |beukersEta a| * (Cua * Cdb * (3/2)^k) + |beukersEta b| * (Cda * Cub * (3/2)^k)
        + Cda * Cdb * (3/2)^k := by
    have h1 : (|beukersEta a| * |beukersUR a k|) * |beukersD b k|
        ≤ |beukersEta a| * (Cua * Cdb * (3/2)^k) := by
      have h := mul_le_mul_of_nonneg_left ht_ua_db (abs_nonneg (beukersEta a))
      have e : (|beukersEta a| * |beukersUR a k|) * |beukersD b k|
          = |beukersEta a| * (|beukersUR a k| * |beukersD b k|) := by ring
      rw [e]; exact h
    have h2 : (|beukersEta b| * |beukersD a k|) * |beukersUR b k|
        ≤ |beukersEta b| * (Cda * Cub * (3/2)^k) := by
      have h := mul_le_mul_of_nonneg_left ht_da_ub (abs_nonneg (beukersEta b))
      have e : (|beukersEta b| * |beukersD a k|) * |beukersUR b k|
          = |beukersEta b| * (|beukersD a k| * |beukersUR b k|) := by ring
      rw [e]; exact h
    linarith [h1, h2, ht_da_db]
  have hA : |(ra:ℝ) * (beukersD a k * beukersUR b k)| ≤ |(ra:ℝ)| * (Cda * Cub * (3/2)^k) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left ht_da_ub (abs_nonneg _)
  have hB : |(rb:ℝ) * (beukersUR a k * beukersD b k)| ≤ |(rb:ℝ)| * (Cua * Cdb * (3/2)^k) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left ht_ua_db (abs_nonneg _)
  have hC : |(rab:ℝ) * (beukersEta a * beukersUR a k * beukersD b k
        + beukersEta b * beukersD a k * beukersUR b k + beukersD a k * beukersD b k)|
      ≤ |(rab:ℝ)| * (|beukersEta a| * (Cua * Cdb * (3/2)^k) + |beukersEta b| * (Cda * Cub * (3/2)^k)
          + Cda * Cdb * (3/2)^k) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (le_trans habs_sum hsum3) (abs_nonneg _)
  calc |logPCoeff a b ra rb rab k|
      = |(ra:ℝ)*(beukersD a k * beukersUR b k) + (rb:ℝ)*(beukersUR a k * beukersD b k)
          + (rab:ℝ)*(beukersEta a * beukersUR a k * beukersD b k
              + beukersEta b * beukersD a k * beukersUR b k + beukersD a k * beukersD b k)| := by
          rw [logPCoeff_decomp]
    _ ≤ |(ra:ℝ)*(beukersD a k * beukersUR b k)| + |(rb:ℝ)*(beukersUR a k * beukersD b k)|
          + |(rab:ℝ)*(beukersEta a * beukersUR a k * beukersD b k
              + beukersEta b * beukersD a k * beukersUR b k + beukersD a k * beukersD b k)| :=
          abs_add_three _ _ _
    _ ≤ |(ra:ℝ)| * (Cda * Cub * (3/2)^k) + |(rb:ℝ)| * (Cua * Cdb * (3/2)^k)
          + |(rab:ℝ)| * (|beukersEta a| * (Cua * Cdb * (3/2)^k) + |beukersEta b| * (Cda * Cub * (3/2)^k)
              + Cda * Cdb * (3/2)^k) := by
          linarith [hA, hB, hC]
    _ = K * (3/2)^k := by rw [hK_def]; ring

end Work.CRad
