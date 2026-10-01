/-
# ZeroFreeTables — HBTable4range_engine

**HB Table 4** (Heath-Brown, PLMS 64 (1992), p. 43) in the *middle range*
`2/5 ≤ λ₁ ≤ 1294/1000`, i.e. the `HBTable4range` input of `HB8Defs.lean`.

The statement is the one Lemma 8.4 needs: for a real character `χ₁` whose
exceptional zero `ρ₁` is real with `λ(ρ₁) ∈ [2/5, 1294/1000]`, every further zero
`ρ ≠ ρ₁` of the working region satisfies

  `λ(ρ) ≥ max((3/2) log(1/λ₁), 1.294)`.

The proof is the finite, rational part of HB Table 4; the analytic content is
carried by the two engine inequalities of `Table4Defs` (`HB Lemma 8.3`, the `P₃`
method of HB §8.2, for a *non-real* second zero; and the `µ⁰ = 0` case `HB Lemma
8.2`, for a *real* one):

* for a **non-real** zero `u` one applies HB Lemma 8.3 with the row `(lo,hi,v,a,K)`
  of the certificate `Table4Cert.t4certRows` whose interval contains `λ₁`, using
  monotonicity of (8.7) in `λ₀` and in `λ₁` (the latter through (8.8) at the left
  end `lo`) and the transfer of the side condition (8.6) from `(hi,v)` to
  `(λ₁, λ(u))`.  The `ε` of the analytic inequality is chosen as
  `-p83(hi,v,a,K) / (2 (K+1)² (a+hi)) > 0`, which makes the `ε`-term cancel half
  of the (strictly negative) certificate value at `(hi,v)`.  Since the certificate
  value is negative at `(hi,v)`, the pair `(λ₁, λ(u))` cannot satisfy both (8.6)
  and (8.7) whenever `λ(u) < v`;
* for a **real** zero nothing of the sort is available, so one first replaces the
  given zero `ρ` by the zero `u ≠ ρ₁` of minimal `λ` among the zeros with
  `λ ≤ λ(ρ)` (exists by `LinnikAreas.exists_minLam_zero`: the zero set is finite
  in the compact region).  If that `u` is non-real we are in the previous case; if
  it is real it is minimal among *all* the zeros `≠ ρ₁`, so HB Lemma 8.2 applies
  to it and gives `λ(u) ≥ 2.293 ≥ max((3/2)log(1/λ₁), 1.294)`.

The numerical content used here is elementary: the certificate arithmetic
(`norm_num`, in `Table4Cert`), the crude `log x ≤ x - 1` (which suffices for every
row except the first, where `log (5/2) ≤ log(5/4) + log 2 ≤ 1/4 + 1 = 5/4` is
used), and `2.293 ≥ 1.875 ≥ max((3/2)log(1/λ₁), 1.294)` for `λ₁ ≥ 2/5`.

The two analytic inputs are imported: HB Lemma 8.2 as `Table4.HB82` and HB Lemma
8.3 as `Table4.HB83`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HB8Defs
import Submission.Work.ZeroFreeTables.Table4Defs
import Submission.Work.ZeroFreeTables.Table4Cert
import Submission.Work.ZeroFreeTables.Table4.HB82
import Submission.Work.ZeroFreeTables.Table4.HB83
import Submission.Work.LinnikAreas.exists_minLam_zero
import Submission.Work.LinnikContract.API.isZ_lambda_nonneg

open DirichletCharacter Complex
open scoped Classical BigOperators

set_option maxHeartbeats 4000000
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-! ## The elementary numerical inputs -/

/-- `log (5/2) ≤ 5/4`, from `log x ≤ x - 1` at `x = 5/4` and `x = 2`. -/
lemma log_five_halves_le : Real.log (5 / 2) ≤ 5 / 4 := by
  have hmul : Real.log (5 / 2) = Real.log (5 / 4) + Real.log 2 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h1 : Real.log (5 / 4) ≤ 5 / 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  linarith

/-- For `λ₁ ≥ 2/5` the target constant of `HBTable4range` is at most `1.875`. -/
lemma target_le_1875 {x : ℝ} (hx : 2 / 5 ≤ x) :
    max ((3 / 2) * Real.log (1 / x)) (1294 / 1000) ≤ 1875 / 1000 := by
  refine max_le ?_ (by norm_num)
  have hxpos : 0 < x := by linarith
  have hinv : 1 / x ≤ 5 / 2 := by rw [div_le_iff₀ hxpos]; linarith
  have hlog : Real.log (1 / x) ≤ Real.log (5 / 2) :=
    Real.log_le_log (one_div_pos.mpr hxpos) hinv
  have h5 := log_five_halves_le
  linarith

/-- For `λ₁ ≥ 2/5` the target constant of `HBTable4range` is at most `2.293`. -/
lemma target_le_2293 {x : ℝ} (hx : 2 / 5 ≤ x) :
    max ((3 / 2) * Real.log (1 / x)) (1294 / 1000) ≤ 2293 / 1000 :=
  le_trans (target_le_1875 hx) (by norm_num)

/-- The target constant is `≤ v` whenever `(3/2)(1/lo - 1) ≤ v` and `1294/1000 ≤ v`
and `lo ≤ x`: this is `log (1/x) ≤ 1/x - 1 ≤ 1/lo - 1` together with `λ₁ ≥ 2/5 ≥ 0`. -/
lemma target_le_of {lo v x : ℝ} (hlo : 0 < lo) (hxlo : lo ≤ x) (hxpos : 0 < x)
    (hv : (3 / 2) * (1 / lo - 1) ≤ v) (hv2 : 1294 / 1000 ≤ v) :
    max ((3 / 2) * Real.log (1 / x)) (1294 / 1000) ≤ v := by
  refine max_le ?_ hv2
  have h1 : Real.log (1 / x) ≤ 1 / x - 1 := Real.log_le_sub_one_of_pos (one_div_pos.mpr hxpos)
  have h2 : 1 / x ≤ 1 / lo := one_div_le_one_div_of_le hlo hxlo
  have h3 : 1 / x - 1 ≤ 1 / lo - 1 := by linarith
  have h4 : (3 / 2) * Real.log (1 / x) ≤ (3 / 2) * (1 / x - 1) :=
    mul_le_mul_of_nonneg_left h1 (by norm_num)
  have h5 : (3 / 2) * (1 / x - 1) ≤ (3 / 2) * (1 / lo - 1) :=
    mul_le_mul_of_nonneg_left h3 (by norm_num)
  linarith

/-! ## One certificate row at work: HB Lemma 8.3 -/

/-- **A certificate row of Table 4 at work (non-real second zero).**  From HB
Lemma 8.3 and the certificate facts of the row `r`, every zero `ρ₀ ≠ ρ₁` of the
working region with `ρ₀.im ≠ 0` and `lo ≤ λ₁ ≤ hi` satisfies `λ(ρ₀) ≥ v`.

The `ε` of HB Lemma 8.3 is `-p83(hi,v,a,K)/(2(K+1)²(a+hi))`, chosen so that the
`ε`-term of (8.7) at `(λ₁, λ(ρ₀))` is at most `-p83(hi,v,a,K)/2`; monotonicity of
`p83` in `λ₀` and `λ₁` bounds `p83 (λ₁) (λ(ρ₀)) a K` by the certificate value
`p83 hi v a K < 0`, and (8.6) transfers by monotonicity to `(λ₁, λ(ρ₀))`. -/
theorem row_complex (h83 : HBLemma8_3) (r : T4Row) (ha : 0 < T4a r) (hK : 0 < T4K r)
    (hK4 : 1 / 4 ≤ T4K r) (hlo0 : 0 ≤ T4lo r) (hlohi : T4lo r ≤ T4hi r) (hhiv : T4hi r ≤ T4v r)
    (hc88 : cond88 (T4lo r) (T4a r) (T4K r)) (hc86 : cond86 (T4hi r) (T4v r) (T4a r))
    (hp83 : p83 (T4hi r) (T4v r) (T4a r) (T4K r) < 0) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ρ₁.im = 0 → IsZ χ₁ ρ₁ → IsZ χ₁ ρ₀ →
      ρ₀ ≠ ρ₁ → ρ₀.im ≠ 0 → T4lo r ≤ lamOf q ρ₁ → lamOf q ρ₁ ≤ T4hi r → T4v r ≤ lamOf q ρ₀ := by
  set e : ℝ := -(p83 (T4hi r) (T4v r) (T4a r) (T4K r))
      / (2 * (T4K r + 1) ^ 2 * (T4a r + T4hi r)) with he
  have hden : 0 < 2 * (T4K r + 1) ^ 2 * (T4a r + T4hi r) := by
    have h1 : 0 < T4a r + T4hi r := by linarith
    positivity
  have hepos : 0 < e := by rw [he]; exact div_pos (by linarith) hden
  obtain ⟨q₀, hq₀⟩ := h83 (T4a r) (T4K r) e ha hK4 hepos
  refine ⟨q₀, fun q hq _ χ₁ ρ₁ ρ₀ hw hsq hχ1 him1 hZ₁ hZ₀ hne hρ₀im hlo hhi => ?_⟩
  by_contra hcon
  push_neg at hcon
  have hlam1nn : 0 ≤ lamOf q ρ₁ := le_trans hlo0 hlo
  have hlamle : lamOf q ρ₁ ≤ lamOf q ρ₀ :=
    hw.2 χ₁ ρ₀ hχ1 hZ₀.2.1 (by linarith [hZ₀.2.2])
  have hcond : cond86 (lamOf q ρ₁) (lamOf q ρ₀) (T4a r) :=
    cond86_mono hc86 hhi hcon.le (by linarith) (by linarith)
  have hineq := hq₀ q hq χ₁ ρ₁ ρ₀ hw hsq hχ1 him1 hZ₁ hZ₀ hne hρ₀im hlamle hcond
  have hmono0 : p83 (lamOf q ρ₁) (lamOf q ρ₀) (T4a r) (T4K r)
      ≤ p83 (lamOf q ρ₁) (T4v r) (T4a r) (T4K r) :=
    p83_mono_lam₀ ha hK.le (by linarith) (by linarith) (by linarith) hcon.le
  have hc88' : cond88 (lamOf q ρ₁) (T4a r) (T4K r) :=
    cond88_mono_lam₁ hc88 hlo ha (by linarith) hK
  have hmono1 : p83 (lamOf q ρ₁) (T4v r) (T4a r) (T4K r)
      ≤ p83 (T4hi r) (T4v r) (T4a r) (T4K r) :=
    p83_mono_lam₁ hlam1nn hhi hhiv ha hK hc88'
  have heval : (T4K r + 1) ^ 2 * (T4a r + T4hi r) * e
      = -(p83 (T4hi r) (T4v r) (T4a r) (T4K r)) / 2 := by
    rw [he]
    have h1 : (0:ℝ) < T4K r + 1 := by linarith
    have h2 : (0:ℝ) < T4a r + T4hi r := by linarith
    field_simp
  have hterm : (T4K r + 1) ^ 2 * (T4a r + lamOf q ρ₁) * e
      ≤ (T4K r + 1) ^ 2 * (T4a r + T4hi r) * e := by
    have h1 : (0:ℝ) < (T4K r + 1) ^ 2 := by positivity
    have h2 : T4a r + lamOf q ρ₁ ≤ T4a r + T4hi r := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 h1.le) hepos.le
  linarith [hineq, hmono0, hmono1, heval, hterm, hp83]

/-! ## A certificate row covering `[2/5, 1294/1000]`, with its constant -/


/-- **Row selection.**  Every `x ∈ [2/5, 1294/1000]` lies in one of the
certificate rows of `Table4Cert.t4certRows`, and that row's target `v` dominates
`max((3/2) log(1/x), 1294/1000)`. -/
theorem row_cover (x : ℝ) (hx0 : 2 / 5 ≤ x) (hx1 : x ≤ 1294 / 1000) :
    ∃ r ∈ t4certRows, T4lo r ≤ x ∧ x ≤ T4hi r ∧
      max ((3 / 2) * Real.log (1 / x)) (1294 / 1000) ≤ T4v r := by
  by_cases h1 : x ≤ 45/100
  · refine ⟨((4/10 : ℝ), 45/100, 2030/1000, 42/10, 87/100), by norm_num [t4certRows], ?_, h1, ?_⟩
    · change ((4/10 : ℝ) ≤ x)
      linarith
    · exact le_trans (target_le_1875 hx0) (by norm_num)
  have h1' : (45/100 : ℝ) < x := not_le.mp h1
  by_cases h2 : x ≤ 5/10
  · refine ⟨((45/100 : ℝ), 5/10, 1958/1000, 43/10, 87/100), by norm_num [t4certRows], ?_, h2, ?_⟩
    · change ((45/100 : ℝ) ≤ x)
      linarith
    · exact target_le_of (lo := 45/100) (v := 1958/1000) (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num)
  have h2' : (5/10 : ℝ) < x := not_le.mp h2
  by_cases h3 : x ≤ 55/100
  · refine ⟨((5/10 : ℝ), 55/100, 1893/1000, 44/10, 86/100), by norm_num [t4certRows], ?_, h3, ?_⟩
    · change ((5/10 : ℝ) ≤ x)
      linarith
    · exact target_le_of (lo := 5/10) (v := 1893/1000) (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num)
  have h3' : (55/100 : ℝ) < x := not_le.mp h3
  by_cases h4 : x ≤ 6/10
  · refine ⟨((55/100 : ℝ), 6/10, 1832/1000, 44/10, 86/100), by norm_num [t4certRows], ?_, h4, ?_⟩
    · change ((55/100 : ℝ) ≤ x)
      linarith
    · exact target_le_of (lo := 55/100) (v := 1832/1000) (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num)
  have h4' : (6/10 : ℝ) < x := not_le.mp h4
  by_cases h5 : x ≤ 65/100
  · refine ⟨((6/10 : ℝ), 65/100, 1776/1000, 45/10, 85/100), by norm_num [t4certRows], ?_, h5, ?_⟩
    · change ((6/10 : ℝ) ≤ x)
      linarith
    · exact target_le_of (lo := 6/10) (v := 1776/1000) (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num)
  have h5' : (65/100 : ℝ) < x := not_le.mp h5
  by_cases h6 : x ≤ 7/10
  · refine ⟨((65/100 : ℝ), 7/10, 1724/1000, 45/10, 85/100), by norm_num [t4certRows], ?_, h6, ?_⟩
    · change ((65/100 : ℝ) ≤ x)
      linarith
    · exact target_le_of (lo := 65/100) (v := 1724/1000) (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num)
  have h6' : (7/10 : ℝ) < x := not_le.mp h6
  by_cases h7 : x ≤ 75/100
  · refine ⟨((7/10 : ℝ), 75/100, 1676/1000, 46/10, 84/100), by norm_num [t4certRows], ?_, h7, ?_⟩
    · change ((7/10 : ℝ) ≤ x)
      linarith
    · exact target_le_of (lo := 7/10) (v := 1676/1000) (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num)
  have h7' : (75/100 : ℝ) < x := not_le.mp h7
  by_cases h8 : x ≤ 8/10
  · refine ⟨((75/100 : ℝ), 8/10, 1630/1000, 46/10, 84/100), by norm_num [t4certRows], ?_, h8, ?_⟩
    · change ((75/100 : ℝ) ≤ x)
      linarith
    · exact target_le_of (lo := 75/100) (v := 1630/1000) (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num)
  have h8' : (8/10 : ℝ) < x := not_le.mp h8
  by_cases h9 : x ≤ 85/100
  · refine ⟨((8/10 : ℝ), 85/100, 1587/1000, 47/10, 84/100), by norm_num [t4certRows], ?_, h9, ?_⟩
    · change ((8/10 : ℝ) ≤ x)
      linarith
    · exact target_le_of (lo := 8/10) (v := 1587/1000) (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num)
  have h9' : (85/100 : ℝ) < x := not_le.mp h9
  by_cases h10 : x ≤ 9/10
  · refine ⟨((85/100 : ℝ), 9/10, 1547/1000, 47/10, 84/100), by norm_num [t4certRows], ?_, h10, ?_⟩
    · change ((85/100 : ℝ) ≤ x)
      linarith
    · exact target_le_of (lo := 85/100) (v := 1547/1000) (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num)
  have h10' : (9/10 : ℝ) < x := not_le.mp h10
  by_cases h11 : x ≤ 95/100
  · refine ⟨((9/10 : ℝ), 95/100, 1509/1000, 48/10, 83/100), by norm_num [t4certRows], ?_, h11, ?_⟩
    · change ((9/10 : ℝ) ≤ x)
      linarith
    · exact target_le_of (lo := 9/10) (v := 1509/1000) (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num)
  have h11' : (95/100 : ℝ) < x := not_le.mp h11
  by_cases h12 : x ≤ 1
  · refine ⟨((95/100 : ℝ), 1, 1473/1000, 48/10, 83/100), by norm_num [t4certRows], ?_, h12, ?_⟩
    · change ((95/100 : ℝ) ≤ x)
      linarith
    · exact target_le_of (lo := 95/100) (v := 1473/1000) (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num)
  have h12' : (1 : ℝ) < x := not_le.mp h12
  by_cases h13 : x ≤ 105/100
  · refine ⟨((1 : ℝ), 105/100, 1439/1000, 48/10, 83/100), by norm_num [t4certRows], ?_, h13, ?_⟩
    · change ((1 : ℝ) ≤ x)
      linarith
    · exact target_le_of (lo := 1) (v := 1439/1000) (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num)
  have h13' : (105/100 : ℝ) < x := not_le.mp h13
  by_cases h14 : x ≤ 11/10
  · refine ⟨((105/100 : ℝ), 11/10, 1406/1000, 49/10, 83/100), by norm_num [t4certRows], ?_, h14, ?_⟩
    · change ((105/100 : ℝ) ≤ x)
      linarith
    · exact target_le_of (lo := 105/100) (v := 1406/1000) (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num)
  have h14' : (11/10 : ℝ) < x := not_le.mp h14
  by_cases h15 : x ≤ 115/100
  · refine ⟨((11/10 : ℝ), 115/100, 1375/1000, 49/10, 83/100), by norm_num [t4certRows], ?_, h15, ?_⟩
    · change ((11/10 : ℝ) ≤ x)
      linarith
    · exact target_le_of (lo := 11/10) (v := 1375/1000) (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num)
  have h15' : (115/100 : ℝ) < x := not_le.mp h15
  by_cases h16 : x ≤ 1175/1000
  · refine ⟨((115/100 : ℝ), 1175/1000, 1360/1000, 49/10, 83/100), by norm_num [t4certRows], ?_, h16, ?_⟩
    · change ((115/100 : ℝ) ≤ x)
      linarith
    · exact target_le_of (lo := 115/100) (v := 1360/1000) (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num)
  have h16' : (1175/1000 : ℝ) < x := not_le.mp h16
  by_cases h17 : x ≤ 12/10
  · refine ⟨((1175/1000 : ℝ), 12/10, 1346/1000, 495/100, 83/100), by norm_num [t4certRows], ?_, h17, ?_⟩
    · change ((1175/1000 : ℝ) ≤ x)
      linarith
    · exact target_le_of (lo := 1175/1000) (v := 1346/1000) (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num)
  have h17' : (12/10 : ℝ) < x := not_le.mp h17
  by_cases h18 : x ≤ 1225/1000
  · refine ⟨((12/10 : ℝ), 1225/1000, 1331/1000, 5, 83/100), by norm_num [t4certRows], ?_, h18, ?_⟩
    · change ((12/10 : ℝ) ≤ x)
      linarith
    · exact target_le_of (lo := 12/10) (v := 1331/1000) (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num)
  have h18' : (1225/1000 : ℝ) < x := not_le.mp h18
  by_cases h19 : x ≤ 125/100
  · refine ⟨((1225/1000 : ℝ), 125/100, 1318/1000, 5, 83/100), by norm_num [t4certRows], ?_, h19, ?_⟩
    · change ((1225/1000 : ℝ) ≤ x)
      linarith
    · exact target_le_of (lo := 1225/1000) (v := 1318/1000) (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num)
  have h19' : (125/100 : ℝ) < x := not_le.mp h19
  by_cases h20 : x ≤ 1275/1000
  · refine ⟨((125/100 : ℝ), 1275/1000, 1304/1000, 5, 83/100), by norm_num [t4certRows], ?_, h20, ?_⟩
    · change ((125/100 : ℝ) ≤ x)
      linarith
    · exact target_le_of (lo := 125/100) (v := 1304/1000) (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num)
  have h20' : (1275/1000 : ℝ) < x := not_le.mp h20
  · refine ⟨((1275/1000 : ℝ), 1294/1000, 1294/1000, 5, 83/100), by norm_num [t4certRows], ?_, hx1, ?_⟩
    · change ((1275/1000 : ℝ) ≤ x)
      linarith
    · exact target_le_of (lo := 1275/1000) (v := 1294/1000) (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num)

/-! ## The main theorem -/

/-- **`HBTable4range` from the two engine inequalities.** -/
theorem hbTable4range_of_engines (h82 : HBLemma8_2) (h83 : HBLemma8_3) : HBTable4range := by
  obtain ⟨Nc, hNc⟩ := exists_threshold_of_forall_mem t4certRows
    (fun r N => ∀ (q : ℕ), N ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ρ₁.im = 0 → IsZ χ₁ ρ₁ → IsZ χ₁ ρ₀ →
      ρ₀ ≠ ρ₁ → ρ₀.im ≠ 0 → T4lo r ≤ lamOf q ρ₁ → lamOf q ρ₁ ≤ T4hi r → T4v r ≤ lamOf q ρ₀)
    (fun r hr => by
      obtain ⟨ha, hK, hK4, hlo0, hlohi, _hv, hhiv, hc88, hc86, hp83⟩ := t4certRows_facts r hr
      exact row_complex h83 r ha hK hK4 hlo0 hlohi hhiv hc88 hc86 hp83)
    (fun r hr n n' hn hpn q hq => hpn q (le_trans hn hq))
  obtain ⟨Nr, hNr⟩ := h82
  refine ⟨max (max Nc Nr) 2, ?_⟩
  intro q hq hqne χ₁ ρ₁ hw hsq him0 hlam_lo hlam_hi
  have hqNc : Nc ≤ q := by omega
  have hqNr : Nr ≤ q := by omega
  intro ρ hZρ hne _
  have hχ1 : χ₁ ≠ 1 := hZρ.1
  have hZ1 : IsZ χ₁ ρ₁ := hw.1.1
  -- replace the given zero by the zero of minimal `λ` among the zeros with `λ ≤ λ(ρ)`
  obtain ⟨u, huz, hue, huim, hule, hmin⟩ :=
    Work.LinnikAreas.exists_minLam_zero χ₁ hχ1 ρ₁ ρ 1 hZρ.2.1 hZρ.2.2 hne
  have hZu : IsZ χ₁ u := ⟨hχ1, huz, huim⟩
  have hmaxu : ∀ z : ℂ, IsZ χ₁ z → z ≠ ρ₁ → lamOf q u ≤ lamOf q z := by
    intro z hZz hz
    by_cases hzle : lamOf q z ≤ lamOf q ρ
    · exact hmin z hZz.2.1 hz hZz.2.2 hzle
    · push_neg at hzle
      linarith
  have key : max ((3 / 2) * Real.log (1 / lamOf q ρ₁)) (1294 / 1000) ≤ lamOf q u := by
    by_cases hu0 : u.im = 0
    · -- real second zero: HB Lemma 8.2 applied to the minimal zero
      have h2293 := (hNr q hqNr χ₁ ρ₁ hw hsq hχ1 him0 hZ1).2 u hZu hue hu0 hmaxu
      exact le_trans (target_le_2293 hlam_lo) h2293
    · -- non-real second zero: the certificate row containing `λ₁`
      obtain ⟨r, hr, hlo, hhi, hcv⟩ := row_cover (lamOf q ρ₁) hlam_lo hlam_hi
      have hrow := hNc r hr q hqNc χ₁ ρ₁ u hw hsq hχ1 him0 hZ1 hZu hue hu0 hlo hhi
      exact le_trans hcv hrow
  exact le_trans key hule


/-! ## The engine inputs, and the `pfP` import clash

The two analytic inputs are proved elsewhere.  **They must both live in the same
import "world"**, because the workspace contains two modules that both declare
`Commons.NumberTheory.Linnik.pfP`:

* `Submission.Commons.NumberTheory.Linnik.completedL_pf_identity_rect` (the
  partial-fraction identity used by the `F`-method chain: `scratch_l6*`,
  `lemma5_2_sigma_ge_one`, `DhRepel/dhTrianglePtLocal`, hence `Table4/HB64Local`
  and the proof of HB Lemma 8.2), and
* `Submission.Commons.NumberTheory.Linnik.logDeriv_pf_identity` (used by
  `ZeroFreeTables/P3/Imports.lean`, hence by the `P₃` chain `P3.DefsL`,
  `P3.WLBase`, `P3.CompletedDerivPF`, `P9.*`).

Lean refuses to load both in one environment (see
`Work/LinnikAreas/ownRepelNW/NOTE_pfP_import_clash.md`).  Since the `F`-method
side of HB Table 4 (HB Lemma 8.2, used for a **real** second zero) is naturally
built on the `..._rect` chain, the `P₃` side (HB Lemma 8.3, used for a
**non-real** second zero) has to be built on the same side: the rect-world
partial-fraction surface
`Work.LinnikAreas.P3Rect.LogDerivPfIdentityP3` /
`Work.LinnikAreas.P3Rect.Work_ZeroFreeTables_P3_CompletedDerivPF` exists for
exactly that purpose, and the remaining `P₃` ingredients (`P3Pos`, `P3.P3Bounds`,
`P3.CaseC_D`, `P3.Pointwise91`) are neutral.

So the second input below is imported from a rect-world proof of HB Lemma 8.3;
importing instead a proof built on `ZeroFreeTables/P3/Imports.lean` fails with
`environment already contains 'Commons.NumberTheory.Linnik.pfP'`.
-/

/-! ## The requested statement -/

theorem HBTable4range_engine : Work.ZeroFreeTables.HBTable4range :=
  hbTable4range_of_engines Table4.HB82 Table4.HB83

end Work.ZeroFreeTables
